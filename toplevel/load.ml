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

(* Soma: [Load "FILE.lang".], which loads a .lang file in a module of its
   own (vernac/somaMacro.ml) *)
let load_lang ~state f =
  let load = Vernacexpr.{ control = []; attrs = []; expr = VernacSynterp (VernacLoad (false, f)) } in
  Vernac.process_expr ~state (CAst.make load)

let lang_of_program f =
  if Filename.check_suffix f ".soma" then
    let l = Filename.chop_suffix f ".soma" ^ SomaMacro.lang_suffix in
    if Sys.file_exists l then Some l else None
  else None

(* A .lang file is loaded as by [Load], and FILE.soma after FILE.lang *)
let load_vernacular opts ~state =
  List.fold_left
    (fun state f_in ->
      let s = Loadpath.locate_source_file f_in in
      if SomaMacro.is_lang_file s then load_lang ~state s
      else
        let state = Option.fold_left (fun state l -> load_lang ~state l) state (lang_of_program s) in
        Vernac.load_vernac ~check:true ~state s
    ) state opts.pre.load_vernacular_list

let load_init_vernaculars opts ~state =
  let state = load_init_file opts ~state in
  let state = load_vernacular opts ~state in
  state
