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

type ocaml_item =
  | OCamlType of int
  | OCamlValue of string * string option list

type ocaml_module = {
  ml_file : string option;
  top : string;
  libraries : string list;
  items : (Names.Constant.t * string * ocaml_item) list;
}

let ocaml_modules : (unit -> ocaml_module list) ref = ref (fun () -> [])
