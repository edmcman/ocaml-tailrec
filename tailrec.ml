open Asttypes
open Typedtree
open Lambda
open Path
open Ident

(*---------------------------------------------------------------------------*)
(*         Hacked version of Simplif.emit_tail_infos from the compiler       *)
(*---------------------------------------------------------------------------*)
let annots = ref []
let rec emit_tail_infos is_tail lambda =
  let call_kind args =
    if is_tail
    && ((not !Clflags.native_code)
        || (!Simplif.is_tail_native_heuristic (List.length args)))
   then `Tail
   else `Stack in
  match lambda with
  | Lvar _ -> ()
  | Lconst _ -> ()
  | Lapply {ap_func=func; ap_args=l; ap_loc=loc} ->
      list_emit_tail_infos false l;
      (* Stypes.record (Stypes.An_call (loc, call_kind l)) *)
      annots := (loc, call_kind l) :: !annots
  | Lfunction {body=lam} ->
      emit_tail_infos true lam
  | Llet (_, _, _, lam, body) ->
      emit_tail_infos false lam;
      emit_tail_infos is_tail body
  | Lletrec (bindings, body) ->
      List.iter (fun (_, lam) -> emit_tail_infos false lam) bindings;
      emit_tail_infos is_tail body
  | Lprim (Pidentity, [arg], _loc) ->
      emit_tail_infos is_tail arg
  | Lprim (Psequand, [arg1; arg2], _loc)
  | Lprim (Psequor, [arg1; arg2], _loc) ->
      emit_tail_infos false arg1;
      emit_tail_infos is_tail arg2
  | Lprim (_, l, _loc) ->
      list_emit_tail_infos false l
  | Lswitch (lam, sw) ->
      emit_tail_infos false lam;
      list_emit_tail_infos_fun snd is_tail sw.sw_consts;
      list_emit_tail_infos_fun snd is_tail sw.sw_blocks;
      Misc.may  (emit_tail_infos is_tail) sw.sw_failaction
  | Lstaticraise (_, l) ->
      list_emit_tail_infos false l
  | Lstaticcatch (body, _, handler) ->
      emit_tail_infos is_tail body;
      emit_tail_infos is_tail handler
  | Ltrywith (body, _, handler) ->
      emit_tail_infos false body;
      emit_tail_infos is_tail handler
  | Lifthenelse (cond, ifso, ifno) ->
      emit_tail_infos false cond;
      emit_tail_infos is_tail ifso;
      emit_tail_infos is_tail ifno
  | Lsequence (lam1, lam2) ->
      emit_tail_infos false lam1;
      emit_tail_infos is_tail lam2
  | Lwhile (cond, body) ->
      emit_tail_infos false cond;
      emit_tail_infos false body
  | Lfor (_, low, high, _, body) ->
      emit_tail_infos false low;
      emit_tail_infos false high;
      emit_tail_infos false body
  | Lassign (_, lam) ->
      emit_tail_infos false lam
  | Lsend (_, meth, obj, args, loc) ->
      emit_tail_infos false meth;
      emit_tail_infos false obj;
      list_emit_tail_infos false args;
      (* Stypes.record (Stypes.An_call (loc, call_kind (obj :: args))) *)
      annots := (loc, call_kind (obj :: args)) :: !annots
  | Levent (lam, _) ->
      emit_tail_infos is_tail lam
  | Lifused (_, lam) ->
      emit_tail_infos is_tail lam
and list_emit_tail_infos_fun f is_tail =
  List.iter (fun x -> emit_tail_infos is_tail (f x))
and list_emit_tail_infos is_tail =
  List.iter (emit_tail_infos is_tail)

(*---------------------------------------------------------------------------*)
(*                              Debug functions                              *)
(*---------------------------------------------------------------------------*)
let string_of_call_kind = function `Tail -> "tail" | `Stack -> "stack"

let rec dump_annot_list = function
  | [] -> ()
  | (l,ann)::anns ->
    Location.print Format.std_formatter l;
    Printf.printf "Annot: %s\n%!" (string_of_call_kind ann);
    dump_annot_list anns

(*---------------------------------------------------------------------------*)
(*                           Actual checking code                            *)
(*---------------------------------------------------------------------------*)
let assert_tail_calls_for (f_ident : Ident.t) body : bool =
  (* Printf.printf "    Generating annotations for lambda term...\n%!"; *)
  annots := [];
  emit_tail_infos true body;
  let rec iterlam f =  Lambda.iter (fun l -> f l; iterlam f l) in
  let retval = ref true in
  let assert_apply lam = match lam with
    | Lapply {ap_func=Lvar i; ap_args=args; ap_loc=loc} when i = f_ident ->
      (* Printf.printf "    Checking if the lambda term Lapply(%s, _, _) is a tail call...%!" (Ident.unique_name i); *)
      let (_, a) = List.find (fun (l, _) -> l = loc) !annots in
      begin match a with
      | `Tail -> 
	(* Printf.printf "OK!\n%!"; *)
	()
      | `Stack -> 
        (* Printf.printf "ERROR!\n%!"; *)
        (* Location.print_error Format.err_formatter loc; *)
        (* Format.eprintf "this call to %s is not a tail-call!\n%!" f_ident.Ident.name; *)
	retval := false
      end
    | _ -> ()
  in
  iterlam assert_apply body;
  !retval

let ident = ref ""

let check f vb_expr vbs =
  let fname = Ident.unique_name f in
  (* Printf.printf "  Compiling %s into Lletrec lambda term...\n%!" fname; *)
  let lam = Translcore.(transl_let Recursive vbs (transl_exp vb_expr)) in
  begin match lam with
    | Lletrec (bindings, body) ->
      if (assert_tail_calls_for f body) = false then
	Printf.printf "Non-tail-recursion function used: %s\n" !ident
    | _ -> failwith "Compiled value into something other than a Lletrec"
  end
  
  
module ExpressionIteratorArg = struct
  include TypedtreeIter.DefaultIteratorArgument

  let enter_expression = function
    | {exp_desc=Texp_let(Recursive, (({vb_pat = {pat_desc = Tpat_var(f,_)}; vb_expr; vb_attributes})::_ as vbs), _)} ->
      check f vb_expr vbs
    | {exp_desc=(Texp_while _|Texp_for _); exp_loc=l} ->
      Location.print Format.std_formatter l;
      Printf.printf "Loop used in: %s\n" !ident
    (* | {exp_desc=(Texp_instvar _|Texp_setinstvar _); exp_loc=l} -> *)
    | {exp_desc=Texp_apply ({exp_desc=Texp_ident (id, _, _); exp_loc=l}, _)} when List.mem (Path.name id) ["Pervasives.ref"; "Pervasives.:="; "Pervasives.!"] ->
      Location.print Format.std_formatter l;
      Printf.printf "Reference used in: %s\n" !ident
    | {exp_desc=(Texp_array _); exp_loc=l} ->
      Location.print Format.std_formatter l;
      Printf.printf "Array used in: %s\n" !ident
    | {exp_desc=(Texp_ifthenelse _); exp_loc=l} ->
      Location.print Format.std_formatter l;
      Printf.printf "If-then-else used in: %s\n" !ident
    | {exp_desc=(Texp_match _); exp_loc=l} ->
      Location.print Format.std_formatter l;
      Printf.printf "Pattern matching used in: %s\n" !ident
    | _ -> ()

  let enter_structure_item st =
    (match st.str_desc with
    | Tstr_value(_, (({vb_pat = {pat_desc = Tpat_var(f,_)}}::_))) ->
      ident := f.Ident.name;
    | _ -> ());

    (match st.str_desc with
    | Tstr_value(Recursive, (({vb_pat = {pat_desc = Tpat_var(f,_)}; vb_expr; vb_attributes})::_ as vbs)) ->
      check f vb_expr vbs
    | _ -> ());

    TypedtreeIter.DefaultIteratorArgument.enter_structure_item st
      
   
end

(*---------------------------------------------------------------------------*)
(*                                Entry point                                *)
(*---------------------------------------------------------------------------*)
let () =
  let open Cmt_format in
  for i = 1 to Array.length Sys.argv - 1 do
    let fn = Sys.argv.(i) in
    try
      let {cmt_annots; cmt_modname; _} = read_cmt fn in
      begin match cmt_annots with
      | Implementation st ->
        print_endline "Found implementation annotation in cmt.";
        let module I = TypedtreeIter.MakeIterator(ExpressionIteratorArg) in
        I.iter_structure st;
      | _ -> ()
      end;
    with exn ->
      Format.printf "Cannot read '%s': %s@." fn (Printexc.to_string exn)
  done
