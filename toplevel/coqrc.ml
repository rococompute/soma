(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let ( / ) s1 s2 = Filename.concat s1 s2

(* Loading of the resource file.
   rcfile is either $XDG_CONFIG_HOME/.coqrc.VERSION, or $XDG_CONFIG_HOME/.coqrc if the first one
  does not exist. *)

let rcdefaultname = "coqrc"

(* Keep selection and conservative freshness checks on the same candidates,
   including currently absent higher-priority files. *)
let default_candidates ~warn = [
  Envars.xdg_config_home warn / rcdefaultname^"."^Coq_config.version;
  Envars.xdg_config_home warn / rcdefaultname;
  Envars.home ~warn / "."^rcdefaultname^"."^Coq_config.version;
  Envars.home ~warn / "."^rcdefaultname
]

let load_rcfile ~rcfile ~state =
  let load file =
    SomaImport.note_loaded_source file;
    Vernac.load_vernac ~check:true ~state file in
  try
    match rcfile with
    | Some rcfile ->
      if CUnix.file_readable_p rcfile then
        load rcfile
      else raise (Sys_error ("Cannot read rcfile: "^ rcfile))
    | None ->
      let warn x = Feedback.msg_warning (Pp.str x) in
      let inferedrc = List.find_opt CUnix.file_readable_p (default_candidates ~warn) in
      match inferedrc with
      | None -> state
      | Some inferedrc ->
        load inferedrc
  with reraise ->
    let reraise = Exninfo.capture reraise in
    let () = Feedback.msg_info (Pp.str"Load of rcfile failed.") in
    Exninfo.iraise reraise
