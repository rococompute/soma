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
   [rocq c], and prints the names of the files it created (a program that
   requires Mirage is also built into an image). *)

open Rocqshim

let usage = {|Usage: light COMMAND [ARGUMENTS]

Commands:
  build FILE [OPTIONS]   check and build a Lightlang program (FILE.light),
                         and print the names of the files created: FILE.vo
                         and the others rocq c makes, and FILE.hvt, the
                         MirageOS image, for a program that requires
                         Mirage. The options are those of rocq c
                         (rocq c --help).
  help                   this message
|}

let usage_error fmt =
  Printf.ksprintf (fun msg -> prerr_string (msg ^ "\n\n" ^ usage); exit 2) fmt

(* [rocq c ARGS], with what it prints on stdout (the values of bare terms,
   Mirage's messages) returned instead of shown; errors and warnings, on
   stderr, are shown *)
let compile args =
  let prog = get_worker_path { package = "rocq-runtime"; basename = "rocqworker" } in
  let argv = Array.of_list (prog :: "--kind=compile" :: args) in
  let out_r, out_w = Unix.pipe ~cloexec:true () in
  let pid = Unix.create_process prog argv Unix.stdin out_w Unix.stderr in
  Unix.close out_w;
  let output = In_channel.input_all (Unix.in_channel_of_descr out_r) in
  Unix.close out_r;
  let _, status = Unix.waitpid [] pid in
  let code = match status with
    | Unix.WEXITED n -> n | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> 1 in
  code, output

(* The output directory: that of [-o FILE.vo], or else the source's *)
let output_dir file args =
  let rec find = function
    | "-o" :: out :: _ -> Some (Filename.dirname out)
    | _ :: rest -> find rest
    | [] -> None
  in
  match find args with Some d -> d | None -> Filename.dirname file

let modification_times dir =
  try
    Sys.readdir dir |> Array.to_list
    |> List.filter_map (fun name ->
        try Some (name, (Unix.stat (Filename.concat dir name)).Unix.st_mtime)
        with Unix.Unix_error _ -> None)
  with Sys_error _ -> []

(* The files of [dir] that are new or changed since [before], but [source] *)
let created ~before ~source dir =
  modification_times dir
  |> List.filter (fun (name, time) ->
      Filename.concat dir name <> source &&
      match List.assoc_opt name before with
      | None -> true
      | Some old -> time > old)
  |> List.map (fun (name, _) -> Filename.concat dir name)
  |> List.sort compare

let lines s = String.split_on_char '\n' s

let starts_with ~prefix s =
  String.length s >= String.length prefix &&
  String.sub s 0 (String.length prefix) = prefix

let build file args =
  let dir = output_dir file args in
  let before = modification_times dir in
  let code, output = compile (file :: args) in
  (* The values of bare terms are not shown; the notice that the MirageOS
     project is being set up is, as it takes a while *)
  List.iter (fun l -> if starts_with ~prefix:"Mirage: setting up" l then print_endline l)
    (lines output);
  if code <> 0 then exit code;
  List.iter print_endline (created ~before ~source:file dir)

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [] | ("help" | "--help" | "-h") :: _ -> print_string usage
  | ["build"] -> usage_error "light build: no file given"
  | "build" :: file :: args ->
    let opts, args = parse_opts args in
    let () = init opts (file :: args) in
    build file args
  | command :: _ -> usage_error "light: unknown command %s" command
