(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

let macros = Summary.ref ~name:"soma-macros" Cset_env.empty

let any () = not (Cset_env.is_empty !macros)

let is_macro c = Cset_env.mem c !macros

let add c = macros := Cset_env.add c !macros

let in_macro : Constant.t -> Libobject.obj =
  let open Libobject in
  declare_object { (default_object "SOMA-MACRO") with
                   cache_function = add;
                   open_function = simple_open add;
                   subst_function = (fun (subst, c) -> Mod_subst.subst_constant subst c);
                   classify_function = (fun _ -> Substitute) }

(* Readers ([Reader name text := body.]), in scope as macros are *)

let readers = Summary.ref ~name:"soma-readers" Cset_env.empty

let is_reader c = Cset_env.mem c !readers

let add_reader c = readers := Cset_env.add c !readers

let in_reader : Constant.t -> Libobject.obj =
  let open Libobject in
  declare_object { (default_object "SOMA-READER") with
                   cache_function = add_reader;
                   open_function = simple_open add_reader;
                   subst_function = (fun (subst, c) -> Mod_subst.subst_constant subst c);
                   classify_function = (fun _ -> Substitute) }

let max_depth = 1000
let depth = ref 0

let nested ?loc c f =
  if !depth >= max_depth then
    CErrors.user_err ?loc Pp.(str "The macro "
                              ++ Libnames.pr_qualid (Nametab.shortest_qualid_of_global Id.Set.empty (GlobRef.ConstRef c))
                              ++ str " was expanded "
                              ++ int max_depth ++ str " times within itself: it does not stop expanding.");
  incr depth;
  Fun.protect ~finally:(fun () -> decr depth) f

let expand = ref (fun _ ?loc _ _ ->
    CErrors.anomaly (Pp.str "Soma macros are expanded by vernac/somaMacro.ml."))
