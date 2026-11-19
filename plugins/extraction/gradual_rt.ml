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
(** The error [err_A] was eliminated: a cast failed at run time. *)

exception Unknown_term of string
(** The unknown term [?_A] at an inductive type was eliminated. *)

(* As in the kernel, [?_I] and [err_I] at an inductive type [I] are values:
   [cons raise nil] is a list, and [2 + ?] is [S (S ?)]. They are blocks
   with a tag that no extracted constructor uses, holding their kind and a
   message, and they raise only when eliminated: every [match] of a file
   that uses this runtime goes through [check]. Types whose values cannot
   hold them (mapped to OCaml types by Extract Inductive, singleton and
   coinductive types) raise at once instead. *)
let exc_tag = 245

(* The first field of these blocks, which no other value has: testing it
   needs no call to the C function behind [Obj.tag], so that the test
   guarding every match stays cheap. *)
let marker = Obj.repr (ref ())

let make_exc (unknown : bool) (msg : string) : Obj.t =
  Obj.with_tag exc_tag (Obj.repr (marker, (unknown, msg)))

let is_exc (v : Obj.t) = Obj.is_block v && Obj.size v = 2 && Obj.field v 0 == marker

let exc_payload (v : Obj.t) : bool * string = Obj.obj (Obj.field v 1)

let raise_exc (v : Obj.t) =
  let (unknown, msg) = exc_payload v in
  if unknown then raise (Unknown_term msg) else raise (Cast_error msg)

(** [check v] is [v], unless [v] is [?] or [err] at an inductive type, which
    it raises. Extracted code calls it on everything it matches on. *)
let check (v : 'a) : 'a = let r = Obj.repr v in if is_exc r then raise_exc r else v

let is_unknown (v : 'a) = let r = Obj.repr v in is_exc r && fst (exc_payload r)
let is_error (v : 'a) = let r = Obj.repr v in is_exc r && not (is_unknown v)

(** [force v] is [v], unless [?] or [err] occurs in the data of [v] (not
    under functions), which it raises. *)
let force (v : 'a) : 'a =
  let rec go r =
    if Obj.is_block r then
      let t = Obj.tag r in
      if is_exc r then raise_exc r
      else if t < exc_tag then for i = 0 to Obj.size r - 1 do go (Obj.field r i) done
  in
  go (Obj.repr v); v

type ty =
  | Unknown
  | Err
  | Erased  (* propositions and their proofs: nothing to check *)
  | Sort of int  (* 0 = Prop, 1 = Set, 2 = Type *)
  | Pi of ty * (Obj.t -> ty)
  | Ind of ind
  | Prim of string * ty list  (* int, float, string, array (of its elements) *)

and ind = {
  name : string;
  data : bool;  (* its values can be [?] and [err] (see [exc_tag]) *)
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
  | Prim (name, []) -> name
  | Prim (name, args) -> "(" ^ String.concat " " (name :: List.map to_string args) ^ ")"

and arg_to_string = function
  | Ty t -> to_string t
  | Val _ -> "_"
  | Unk -> "?"
  | Error -> "err"

(* A type in an error message, by short names: "nat", "a function",
   "(vec nat _)" *)
let rec describe = function
  | Pi _ -> "a function"
  | Ind { name; args; _ } ->
    let short = match String.rindex_opt name '.' with
      | Some i -> String.sub name (i + 1) (String.length name - i - 1)
      | None -> name
    in
    let args = Array.to_list (Array.map describe_arg args) in
    "a " ^ String.concat " " (short :: args)
  | t -> "a " ^ to_string t

and describe_arg = function
  | Ty (Pi _ as t) -> "(" ^ to_string t ^ ")"
  | Ty t ->
    let s = describe t in
    let s = if String.length s > 2 && String.sub s 0 2 = "a " then String.sub s 2 (String.length s - 2) else s in
    if String.contains s ' ' then "(" ^ s ^ ")" else s
  | a -> arg_to_string a

(* "a nat", "an option nat" *)
let describe t =
  let s = describe t in
  let n = String.length s in
  (* "an int", "an N": a vowel, or a letter read as one *)
  let letter_vowel = n > 2 && String.contains "AEFHILMNORSX" s.[2] &&
                     (n = 3 || not (Char.lowercase_ascii s.[3] = s.[3] && Char.uppercase_ascii s.[3] <> s.[3])) in
  if n > 2 && String.sub s 0 2 = "a " && (String.contains "aeiou" s.[2] || letter_vowel) then "an " ^ String.sub s 2 (n - 2)
  else s

(* [err] at type [b]: a value when [b] is an inductive type that can hold
   it. *)
let error_at b msg = match b with
  | Ind { data = true; _ } -> make_exc false msg
  | _ -> raise (Cast_error msg)

(* worded as the errors of terms evaluated by Rocq
   (vernac/gradualErrors.ml) *)
let fail a b = error_at b ("expected " ^ describe b ^ ", but got " ^ describe a)

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
  | Prim (p1, a1), Prim (p2, a2) ->
    String.equal p1 p2 && List.length a1 = List.length a2 && List.for_all2 equal a1 a2
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
  | Ind i -> if i.data then make_exc true i.name else raise (Unknown_term i.name)
  | Prim (name, _) -> raise (Unknown_term name)
  | Err -> raise (Cast_error "unknown term of the error type")

let rec err_term ty : Obj.t = match ty with
  | Unknown -> Obj.repr { dty = Err; dv = dummy }
  | Erased | Sort _ -> dummy
  | Pi (_, b) -> Obj.repr (fun x -> err_term (b x))
  | Ind _ | Prim _ | Err -> error_at ty ("raise, at type " ^ to_string ty)

let rec cast a b (v : Obj.t) : Obj.t =
  if equal a b then v
  else if is_exc v then
    (* [?_A] and [err_A] cast to [B] are [?_B] and [err_B] *)
    begin match b with
      | Ind { data = true; _ } -> v
      | Unknown -> Obj.repr { dty = (if is_unknown v then Unknown else Err); dv = dummy }
      | _ -> raise_exc v
    end
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
    | Prim (p1, _), Prim (p2, _) when String.equal p1 p2 ->
      (* arrays of different element types: elements are not cast, as in
         the kernel, where such a cast is stuck *)
      raise (Cast_error ("cast between " ^ to_string a ^ " and " ^ to_string b ^ " is not supported"))
    | Ind i1, Ind i2 when String.equal i1.name i2.name ->
      begin match Hashtbl.find_opt casts i1.name with
        | Some f -> f i1 i2 v
        | None -> raise (Cast_error ("no cast function for " ^ i1.name))
      end
    | _ -> fail a b

(* A [match] on a value [x] that may be [?] or [err] at an inductive type
   is extracted to [if is_exc_value x then propagate ty x else match x
   with ...], where [ty] is the type of the match: as in the kernel, the
   match is then [?] or [err] at [ty], which raises when [ty] cannot hold
   it. *)
let is_exc_value (v : 'a) = is_exc (Obj.repr v)

let propagate (ty : ty) (v : 'a) : Obj.t =
  match ty with
  | Ind { data = true; _ } -> Obj.repr v
  (* an error, at a type that cannot hold it ([string], as OCaml's [char
     list]): it is raised, saying what it says ("expected an N, but got a
     string"), rather than as a new [err] at [ty], which would say only
     where it ended up. ([?] is [?] at [ty], as in the kernel.) *)
  | Ind _ | Prim _ | Err when is_error v -> raise_exc (Obj.repr v)
  | ty -> if is_unknown v then unknown_term ty else err_term ty

let cast_with fs a b v =
  List.iter (fun (name, f) ->
      if not (Hashtbl.mem casts name) then Hashtbl.add casts name f) fs;
  cast a b v

(* The indices computed for a rebuilt constructor must be compatible with
   the indices of the target type ([?] is compatible with anything). *)
let check_indices tgt nparams computed v =
  let nargs = Array.length tgt.args in
  let compatible k c = match tgt.args.(nparams + k), c with
    | Unk, _ | _, Unk | Ty _, _ | _, Ty _ -> true
    | Val i, Val c ->
      (* an index computed as [?] is compatible with anything *)
      if is_exc c || is_exc i then is_unknown c || is_unknown i
      else same_value i c
    | (Val _ | Error), _ -> false
  in
  if nparams < 0 || nparams > nargs || List.length computed <> nargs - nparams then
    error_at (Ind tgt) ("incompatible number of indices for " ^ describe (Ind tgt))
  else if List.for_all Fun.id (List.mapi compatible computed) then v
  else error_at (Ind tgt) ("expected " ^ describe (Ind tgt) ^ ", but got one at other indices")

(* Builders used by the extracted code. *)
let unknown_ty = Unknown
let err_ty = Err
let erased = Erased
let sort n = Sort n
let pi a b = Pi (a, b)
let ind name data args = Ind { name; data; args = Array.of_list args }
let prim name = Prim (name, [])
let prim_array t = Prim ("array", [t])
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
