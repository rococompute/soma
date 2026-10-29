(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Coqargs
open Coqcargs
open Common_compile

(******************************************************************************)
(* File Compilation                                                           *)
(******************************************************************************)

let source ldir file = Loc.InFile {
    dirpath=Some (Names.DirPath.to_string ldir);
    file = file;
  }

(* Soma: the properties of a program FILE.soma (its lemmas and
   theorems) are in FILE.proof next to it, which is read after the
   program, in its environment: the proofs see what the program defines
   and imports, and the program is only built once they are checked. *)
let proof_file f =
  if Filename.check_suffix f ".soma" then
    let p = Filename.chop_suffix f ".soma" ^ ".proof" in
    if Sys.file_exists p then Some p else None
  else None

(* The commands of [s], run in [state] *)
let process_string ~state s =
  let pa = Procq.Parsable.make (Gramlib.Stream.of_string s) in
  let rec loop state = match Procq.Entry.parse (Pvernac.main_entry None) pa with
    | Some cmd -> loop (Vernac.process_expr ~state cmd)
    | None -> state
  in
  loop state

(* FILE.proof is written in the proof language of theories/Soma/Proof.v,
   which is imported for it, and only for it *)
let load_proof_file ~beautify ~check ~state ldir f =
  match proof_file f with
  | None -> state
  | Some p ->
    let state = process_string ~state "Require Import Soma.Proof." in
    (* the .glob is the program's: positions in p would not be its *)
    Dumpglob.push_output Dumpglob.NoGlob;
    Fun.protect ~finally:Dumpglob.pop_output (fun () ->
        Vernac.load_vernac ~beautify ~check ~state ~source:(source ldir p) p)

(* Soma: the macros of a program FILE.soma are in FILE.lang next to it,
   which is loaded before the program, as by [Load "FILE.lang".]: they
   are in scope in the program and in FILE.proof. A .lang file compiled
   by itself, for other files to [Require Import], imports the Macro
   library. (vernac/somaMacro.ml) *)
let load_lang_file ~state f =
  if SomaMacro.is_lang_file f then process_string ~state "Require Import Soma.Macro."
  else match Load.lang_of_program f with
  | None -> state
  | Some l -> Load.load_lang ~state l

(* Compile a vernac file *)
let compile opts stm_options injections copts ~f_in ~f_out =
  let open Vernac.State in
  let output_native_objects = match opts.config.native_compiler with
    | NativeOff -> false | NativeOn {ondemand} -> not ondemand
  in
  let mode = copts.compilation_mode in
  let ext_out =
     match mode with
     | BuildVo -> ".vo"
     | BuildVos -> ".vos"
     | BuildVok -> ".vok"
  in
  let long_f_dot_in, long_f_dot_out =
    ensure_exists_with_prefix ~src:f_in ~tgt:f_out ~tgt_ext:ext_out in
  let beautify = copts.beautify in
  let () = if beautify then CLexer.record_comments := true in
  match mode with
  | BuildVo | BuildVok ->
      let doc, sid = Topfmt.(in_phase ~phase:LoadingPrelude)
          Stm.new_doc
          Stm.{ doc_type = VoDoc long_f_dot_out; injections; } in
      let state = { doc; sid; proof = None; time = Option.map Vernac.make_time_output opts.config.time } in
      let state = Load.load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      Aux_file.(start_aux_file
        ~aux_file:(aux_file_name_for long_f_dot_out)
        ~v_file:long_f_dot_in);

      let dump = match copts.glob_out with
      | None -> Dumpglob.MultFiles { vofile = long_f_dot_out; vfile = long_f_dot_in }
      | Some NoGlob -> Dumpglob.NoGlob
      | Some (GlobFile f) -> Dumpglob.File f
      in
      Dumpglob.push_output dump;
      Dumpglob.dump_string ("F" ^ Names.DirPath.to_string ldir ^ "\n");

      let wall_clock1 = Unix.gettimeofday () in
      let check = Stm.AsyncOpts.(stm_options.async_proofs_mode = APoff) in
      let source = source ldir long_f_dot_in in
      let state = load_lang_file ~state long_f_dot_in in
      let state = Vernac.load_vernac ~beautify ~check ~state ~source long_f_dot_in in
      let state = load_proof_file ~beautify ~check ~state ldir long_f_dot_in in
      let fullstate = Stm.finish ~doc:state.doc in
      ensure_no_pending_proofs ~filename:long_f_dot_in fullstate;
      let () = Stm.join ~doc:state.doc in
      let wall_clock2 = Unix.gettimeofday () in
      (* In .vo production, dump a complete .vo file. *)
      let () = if mode = BuildVo then
          Library.save_library_to ~output_native_objects Library.ProofsTodoNone ldir long_f_dot_out
      in
      (* Soma: a program that requires Mirage is also built as a
         MirageOS image, next to the .vo *)
      let () = if mode = BuildVo then
          SomaMirage.build ~state ~vo_file:long_f_dot_out
      in
      let () = Aux_file.record_in_aux_at "vo_compile_time"
          (Printf.sprintf "%.3f" (wall_clock2 -. wall_clock1))
      in
      let () = Aux_file.stop_aux_file () in
      ()

  | BuildVos ->
      let doc, sid = Topfmt.(in_phase ~phase:LoadingPrelude)
          Stm.new_doc
          Stm.{ doc_type = VosDoc long_f_dot_out; injections;
              } in

      let state = { doc; sid; proof = None; time = Option.map Vernac.make_time_output opts.config.time } in
      let state = Load.load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      let source = source ldir long_f_dot_in in
      let state = load_lang_file ~state long_f_dot_in in
      let state = Vernac.load_vernac ~beautify ~check:false ~source ~state long_f_dot_in in
      let state = load_proof_file ~beautify ~check:false ~state ldir long_f_dot_in in
      let state = Stm.finish ~doc:state.doc in
      ensure_no_pending_proofs state ~filename:long_f_dot_in;
      let () = Stm.snapshot_vos ~doc ~output_native_objects ldir long_f_dot_out in
      Stm.reset_task_queue ();
      ()

let compile opts stm_opts copts injections ~f_in ~f_out =
  ignore(CoqworkmgrApi.get 1);
  compile opts stm_opts injections copts ~f_in ~f_out;
  CoqworkmgrApi.giveback 1

let compile_file opts stm_opts copts injections f_in =
  let f_out = copts.compilation_output_name in
  compile opts stm_opts copts injections ~f_in ~f_out

let compile_file opts stm_opts copts injections =
  Option.iter (compile_file opts stm_opts copts injections) copts.compile_file
