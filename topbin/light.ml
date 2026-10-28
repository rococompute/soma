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
   requires Mirage is also built into an image).

   [light run FILE [OPTIONS] [-- ARGUMENTS]] checks a program in a
   temporary directory, so that it leaves no files, and prints the value of
   its last bare term; a program that requires Mirage is built into an
   image, which is run, with ARGUMENTS. *)

open Rocqshim

let usage = {|Usage: light COMMAND [ARGUMENTS]

Commands:
  build [-v] FILE [OPTIONS]
                         check and build a Lightlang program (FILE.light),
                         and print the names of the files created: FILE.vo
                         and the others rocq c makes, and FILE.hvt, the
                         MirageOS image, for a program that requires
                         Mirage. With -v (--verbose), first print what
                         rocq c prints: the values of the program's bare
                         terms. The options are those of rocq c
                         (rocq c --help).
  run FILE [OPTIONS] [-- ARGUMENTS]
                         check a Lightlang program and print the value of
                         its last bare term; for a program that requires
                         Mirage, build its image and run it (solo5-hvt, or
                         solo5-vmnet -- solo5-hvt for one that uses the
                         network), with ARGUMENTS (as --arg=...). Leaves no
                         files.
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

(* The files of [dir] that are new since [before], or written since
   [start], but [source]. Modification times may only count seconds, so a
   file rewritten in the second it was last written is caught by [start],
   rounded down. *)
let created ~before ~start ~source dir =
  let start = Float.of_int (truncate start) in
  modification_times dir
  |> List.filter (fun (name, time) ->
      Filename.concat dir name <> source &&
      (time >= start || not (List.mem_assoc name before)))
  |> List.map (fun (name, _) -> Filename.concat dir name)
  |> List.sort compare

let lines s = String.split_on_char '\n' s

let starts_with ~prefix s =
  String.length s >= String.length prefix &&
  String.sub s 0 (String.length prefix) = prefix

let build ~verbose file args =
  let dir = output_dir file args in
  let before = modification_times dir in
  let start = Unix.gettimeofday () in
  let code, output = compile (file :: args) in
  (* Without -v, the values of bare terms are not shown; the notice that
     the MirageOS project is being set up is, as it takes a while *)
  if verbose then print_string output
  else
    List.iter (fun l -> if starts_with ~prefix:"Mirage: setting up" l then print_endline l)
      (lines output);
  if code <> 0 then exit code;
  List.iter print_endline (created ~before ~start ~source:file dir)

let rec remove_tree path =
  if Sys.is_directory path then begin
    Array.iter (fun name -> remove_tree (Filename.concat path name)) (Sys.readdir path);
    Sys.rmdir path
  end else Sys.remove path

let temp_dir () =
  let file = Filename.temp_file "light-run" "" in
  Sys.remove file;
  Unix.mkdir file 0o700;
  file

(* The value of the last bare term in what [rocq c] printed: a line
   ["     = value"] and the indented lines after it, up to the type *)
let last_value output =
  let rec from_last = function
    | [] -> []
    | l :: rest ->
      match from_last rest with
      | [] when starts_with ~prefix:"     = " l -> l :: rest
      | found -> found
  in
  let rec block = function
    | l :: rest when l <> "" && (l.[0] = ' ' || l.[0] = '\t') -> l :: block rest
    | _ -> []
  in
  match from_last (lines output) with
  | [] -> None
  | first :: rest -> Some (String.concat "\n" (first :: block rest))

(* The command Mirage's build says runs the image:
   ["Mirage: built IMAGE; run it with: COMMAND"] *)
let mirage_command output =
  let marker = "; run it with: " in
  List.find_map (fun l ->
      if starts_with ~prefix:"Mirage: built " l then
        let rec at i =
          if i + String.length marker > String.length l then None
          else if String.sub l i (String.length marker) = marker then
            Some (String.sub l (i + String.length marker) (String.length l - i - String.length marker))
          else at (i + 1)
        in
        Option.map (fun c -> List.filter (( <> ) "") (String.split_on_char ' ' c)) (at 0)
      else None)
    (lines output)

let run file args image_args =
  let dir = temp_dir () in
  let finish code = (try remove_tree dir with Sys_error _ -> ()); exit code in
  let vo = Filename.concat dir (Filename.remove_extension (Filename.basename file) ^ ".vo") in
  let code, output = compile (file :: "-o" :: vo :: args) in
  List.iter (fun l -> if starts_with ~prefix:"Mirage: setting up" l then print_endline l)
    (lines output);
  if code <> 0 then finish code;
  match mirage_command output with
  | Some command ->
    (* the image's tools come from the same opam switch as its build *)
    let switch = match Sys.getenv_opt "LIGHTLANG_MIRAGE_SWITCH" with
      | Some s when s <> "" -> s | _ -> "hvf" in
    let argv = "opam" :: "exec" :: ("--switch=" ^ switch) :: "--" :: command @ image_args in
    (* Ctrl-C stops the image, which then exits; light waits for it to
       remove the temporary directory *)
    Sys.set_signal Sys.sigint Sys.Signal_ignore;
    let pid = Unix.create_process "opam" (Array.of_list argv) Unix.stdin Unix.stdout Unix.stderr in
    let _, status = Unix.waitpid [] pid in
    finish (match status with Unix.WEXITED n -> n | _ -> 1)
  | None ->
    if image_args <> [] then begin
      prerr_endline "light run: arguments after -- are for a program that requires Mirage";
      finish 2
    end;
    Option.iter print_endline (last_value output);
    finish 0

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [] | ("help" | "--help" | "-h") :: _ -> print_string usage
  | "build" :: rest ->
    (* -v is light's (rocq c's -v prints its version), before or after FILE *)
    let is_verbose a = a = "-v" || a = "--verbose" in
    let verbose = List.exists is_verbose rest in
    begin match List.filter (fun a -> not (is_verbose a)) rest with
      | [] -> usage_error "light build: no file given"
      | file :: args ->
        let opts, args = parse_opts args in
        let () = init opts (file :: args) in
        build ~verbose file args
    end
  | ["run"] -> usage_error "light run: no file given"
  | "run" :: file :: rest ->
    let rec split = function
      | "--" :: image_args -> [], image_args
      | a :: rest -> let args, image_args = split rest in a :: args, image_args
      | [] -> [], []
    in
    let args, image_args = split rest in
    let opts, args = parse_opts args in
    let () = init opts (file :: args) in
    run file args image_args
  | command :: _ -> usage_error "light: unknown command %s" command
