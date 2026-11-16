(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Coqargs

(******************************************************************************)
(* Interactive Load File Simulation                                           *)
(******************************************************************************)

let load_init_file opts ~state =
  if opts.pre.load_rcfile then
    Topfmt.(in_phase ~phase:LoadingRcFile) (fun () ->
        Coqrc.load_rcfile ~rcfile:opts.config.rcfile ~state) ()
  else begin
    Flags.if_verbose Feedback.msg_info (str"Skipping rcfile loading.");
    state
  end

(* Soma: [Load "FILE.ext".], which loads a .ext file in a module of its
   own (vernac/somaMacro.ml). Run as a compiled file's sentences are, not
   as the interactive loop's: Vernac.process_expr rolls the document back
   on an error (Stm.edit_at), which is only for an interactive session,
   and turned any error in the .ext file into an anomaly with no
   location. *)
let load_ext ~state f =
  let load = Vernacexpr.{ control = []; attrs = []; expr = VernacSynterp (VernacLoad (false, f)) } in
  Vernac.interp_vernac ~check:true ~state (CAst.make load)

let ext_of_program f =
  if Filename.check_suffix f ".soma" then
    let l = Filename.chop_suffix f ".soma" ^ SomaMacro.ext_suffix in
    if Sys.file_exists l then Some l else None
  else None

(* A .ext file is loaded as by [Load], and FILE.soma after FILE.ext *)
let load_vernacular opts ~state =
  List.fold_left
    (fun state f_in ->
      let s = Loadpath.locate_source_file f_in in
      if SomaMacro.is_ext_file s then load_ext ~state s
      else
        let state = Option.fold_left (fun state l -> load_ext ~state l) state (ext_of_program s) in
        Vernac.load_vernac ~check:true ~state s
    ) state opts.pre.load_vernacular_list

let load_init_vernaculars opts ~state =
  let state = load_init_file opts ~state in
  let state = load_vernacular opts ~state in
  state
