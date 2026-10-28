(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* light: Lightlang's command line, a front end to rocq.

   [light build FILE [OPTIONS]] checks and builds a Lightlang program, as
   [rocq c]: its bare terms are evaluated and printed, and a program that
   requires Mirage is also built into an image. *)

open Rocqshim

let usage = {|Usage: light COMMAND [ARGUMENTS]

Commands:
  build FILE [OPTIONS]   check and build a Lightlang program (FILE.light),
                         printing what its bare terms evaluate to; a program
                         that requires Mirage is also built into FILE.hvt.
                         The options are those of rocq c (rocq c --help).
  help                   this message
|}

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [] | ("help" | "--help" | "-h") :: _ -> print_string usage
  | ["build"] ->
    prerr_string "light build: no file given\n\n";
    prerr_string usage;
    exit 2
  | "build" :: args ->
    let opts, args = parse_opts args in
    let () = init opts args in
    let prog = get_worker_path { package = "rocq-runtime"; basename = "rocqworker" } in
    let () = if opts.debug_shim then Printf.eprintf "Using %s\n%!" prog in
    exec_or_create_process prog (Array.of_list (prog :: "--kind=compile" :: args))
  | command :: _ ->
    Printf.eprintf "light: unknown command %s\n\n" command;
    prerr_string usage;
    exit 2
