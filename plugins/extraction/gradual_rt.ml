(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Runtime support for casts in OCaml code extracted from gradual Rocq
   (GCIC^G, see GRADUAL.md). Extraction prints this file as a module
   [Gradual_rt] at the top of every extracted file that contains casts.

   Extraction erases types, so every cast [cast A B t] is extracted with
   runtime descriptions of [A] and [B]. A value of the unknown type [?] is
   a [dyn]: the value together with the description of the type it was
   injected from. The rules are the ones of the kernel (kernel/gradual.ml).

   This file must only depend on the OCaml standard library, so that the
   extracted code also builds for MirageOS unikernels. *)

exception Cast_error of string
(** The error [err_A] was reached: a cast failed at run time. *)

exception Unknown_term of string
(** The unknown term [?_A] at an inductive type was evaluated. Extracted
    code is call-by-value and cannot represent [?_A] as a value of [A], so
    this is raised instead. *)

type ty =
  | Unknown
  | Err
  | Erased  (* propositions and their proofs: nothing to check *)
  | Sort of int  (* 0 = Prop, 1 = Set, 2 = Type *)
  | Pi of ty * (Obj.t -> ty)
  | Ind of ind

and ind = {
  name : string;
  args : arg array;  (* parameters, then indices *)
}

and arg =
  | Ty of ty
  | Val of Obj.t
  | Unk
  | Error

type dyn = { dty : ty; dv : Obj.t }

(* For each inductive type, by name, the function [f] such that [f src tgt v]
   rebuilds [v : src] at [tgt], two instances of the type. Extraction
   generates them and passes them to [cast_with]. *)
let casts : (string, ind -> ind -> Obj.t -> Obj.t) Hashtbl.t = Hashtbl.create 17

(* Same representation as the [__] of extracted code. *)
let dummy = let rec f _ = Obj.repr f in Obj.repr f

let rec to_string = function
  | Unknown -> "?"
  | Err -> "err"
  | Erased -> "_"
  | Sort 0 -> "Prop"
  | Sort 1 -> "Set"
  | Sort _ -> "Type"
  | Pi (a, _) -> to_string a ^ " -> _"
  | Ind { name; args; _ } ->
    if Array.length args = 0 then name
    else
      "(" ^ String.concat " " (name :: Array.to_list (Array.map arg_to_string args)) ^ ")"

and arg_to_string = function
  | Ty t -> to_string t
  | Val _ -> "_"
  | Unk -> "?"
  | Error -> "err"

let fail a b =
  raise (Cast_error ("cannot cast from " ^ to_string a ^ " to " ^ to_string b))

let same_value (a : Obj.t) (b : Obj.t) =
  a == b || (try compare a b = 0 with Invalid_argument _ -> false)

(* Syntactic equality of descriptions; functions are never equal. *)
let rec equal a b =
  a == b ||
  match a, b with
  | Unknown, Unknown | Err, Err | Erased, Erased -> true
  | Sort s1, Sort s2 -> s1 = s2
  | Ind i1, Ind i2 ->
    String.equal i1.name i2.name
    && Array.length i1.args = Array.length i2.args
    && Array.for_all2 equal_arg i1.args i2.args
  | _ -> false

and equal_arg a b = match a, b with
  | Ty a, Ty b -> equal a b
  | Val a, Val b -> same_value a b
  | Unk, Unk | Error, Error -> true
  | _ -> false

let rec unknown_term ty : Obj.t = match ty with
  | Unknown -> Obj.repr { dty = Unknown; dv = dummy }
  | Erased | Sort _ -> dummy
  | Pi (_, b) -> Obj.repr (fun x -> unknown_term (b x))
  | Ind i -> raise (Unknown_term i.name)
  | Err -> raise (Cast_error "unknown term of the error type")

let rec err_term ty : Obj.t = match ty with
  | Unknown -> Obj.repr { dty = Err; dv = dummy }
  | Erased | Sort _ -> dummy
  | Pi (_, b) -> Obj.repr (fun x -> err_term (b x))
  | Ind _ | Err -> raise (Cast_error ("error at type " ^ to_string ty))

let rec cast a b (v : Obj.t) : Obj.t =
  if equal a b then v
  else match a, b with
    | Err, _ | _, Err -> fail a b
    | Erased, Erased -> v
    | Unknown, Unknown -> v
    | Unknown, _ ->
      let d : dyn = Obj.obj v in
      begin match d.dty with
        | Unknown -> unknown_term b
        | Err -> err_term b
        | a -> cast a b d.dv
      end
    | _, Unknown -> Obj.repr { dty = a; dv = v }
    | Pi (a1, b1), Pi (a2, b2) ->
      let f : Obj.t -> Obj.t = Obj.obj v in
      Obj.repr (fun x ->
          let x' = cast a2 a1 x in
          let b1 = b1 x' and b2 = b2 x in
          (* A tail call when there is nothing to cast, so that loops through
             casts (like Omega) run in constant stack. *)
          if equal b1 b2 then f x' else cast b1 b2 (f x'))
    | Sort s1, Sort s2 -> if s1 <= s2 then v else fail a b
    | Ind i1, Ind i2 when String.equal i1.name i2.name ->
      begin match Hashtbl.find_opt casts i1.name with
        | Some f -> f i1 i2 v
        | None -> raise (Cast_error ("no cast function for " ^ i1.name))
      end
    | _ -> fail a b

let cast_with fs a b v =
  List.iter (fun (name, f) ->
      if not (Hashtbl.mem casts name) then Hashtbl.add casts name f) fs;
  cast a b v

(* The indices computed for a rebuilt constructor must be compatible with
   the indices of the target type ([?] is compatible with anything). *)
let check_indices tgt nparams computed v =
  List.iteri (fun k c ->
      match tgt.args.(nparams + k), c with
      | Unk, _ | _, Unk | Ty _, _ | _, Ty _ -> ()
      | Val i, Val c when same_value i c -> ()
      | _ -> raise (Cast_error ("index mismatch at type " ^ to_string (Ind tgt))))
    computed;
  v

(* Builders used by the extracted code. *)
let unknown_ty = Unknown
let err_ty = Err
let erased = Erased
let sort n = Sort n
let pi a b = Pi (a, b)
let ind name args = Ind { name; args = Array.of_list args }
let rnil : (string * (ind -> ind -> Obj.t -> Obj.t)) list = []
let rcons name f l = (name, f) :: l
let anil : arg list = []
let acons (a : arg) l = a :: l
let ty_arg t = Ty t
let val_arg v = Val (Obj.repr v)
let unk_arg = Unk
let err_arg = Error
let erased_arg = Ty Erased

let param_ty (i : ind) k = match i.args.(k) with
  | Ty t -> t
  | Unk -> Unknown
  | Error -> Err
  | Val _ -> Erased

let param_val (i : ind) k = match i.args.(k) with
  | Val v -> v
  | Unk -> raise (Unknown_term (i.name ^ " (parameter)"))
  | Error | Ty _ -> raise (Cast_error ("bad parameter of " ^ i.name))
