(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let step : (Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t option) ref =
  ref (fun _ _ _ -> None)

let describe : (Names.Constant.t -> Pp.t option) ref = ref (fun _ -> None)

type image_call = {
  module_file : string;
  export : string;
  params : (string * string) list;
  result : string * string;
}

let image : (Names.Constant.t -> image_call option) ref = ref (fun _ -> None)

let evaluate ~reduce env sigma c =
  (* each round computes at least one call: a bound on them, not on time,
     which the gradual step budget and the module's own fuel see to *)
  let rec go c rounds =
    if rounds = 0 then c
    else match !step env sigma c with
      | None -> c
      | Some c' -> go (reduce c') (rounds - 1)
  in
  go c 100000

type native_operation =
  | NativeValue of string
  | NativeGet of string
  | NativeSet of string
  | NativeBuild of string list
  | NativeCopy of string list

type native_callback = {
  namespace : string;
  name : string;
  arguments : string list;
  result : string;
  labels : string option list;
  operation : native_operation;
}

type ocaml_item =
  | OCamlType of int
  | OCamlValue of string * string option list
  | OCamlNativeType of string
  | OCamlNativeCallback of native_callback

type ocaml_module = {
  ml_file : string option;
  top : string;
  libraries : string list;
  items : (Names.Constant.t * string * ocaml_item) list;
}

let ocaml_modules : (unit -> ocaml_module list) ref = ref (fun () -> [])

let native_identity = function
 | OCamlNativeType path -> "native-type " ^ Printf.sprintf "%S" path
 | OCamlNativeCallback n ->
   let operation=match n.operation with
    | NativeValue p->"call "^Printf.sprintf "%S" p
    | NativeGet p->"get "^Printf.sprintf "%S" p
    | NativeSet p->"set "^Printf.sprintf "%S" p
    | NativeBuild fs->"build "^String.concat " "(List.map(Printf.sprintf "%S")fs)
    | NativeCopy fs->"copy "^String.concat " "(List.map(Printf.sprintf "%S")fs) in
   String.concat "\n" (["native-callback";n.namespace;n.name;operation;n.result] @
    List.map2(fun t l->Printf.sprintf "%S %S" t (Option.default "" l))n.arguments n.labels)
 | _ -> invalid_arg "not a native declaration"
