(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* soma: Soma's command line, a front end to rocq.

   [soma build FILE [OPTIONS]] checks and builds a Soma program, as
   [rocq c], and prints the names of the files it created (a program that
   requires Sandbox is also built into an image).

   [soma run FILE [OPTIONS] [-- ARGUMENTS]] checks a program in a
   temporary directory, so that it leaves no files, and prints the value of
   its last bare term; a program that requires Sandbox is built into an
   image, which is run, with ARGUMENTS. *)

open Rocqshim

let usage = {|Usage:
  soma <command> FILE [options]

Commands:
  build                       Check a program and keep its MirageOS image, if any.
  run                         Check a program and print its result, or run its image.
  repl                        Start an interactive session, with FILE loaded if given.
  help                        Show help.

Options:
  -v, --verbose               (build) Print the value of each bare term, and the
                              proofs that "The rest follows." found.
  --fill                      (build) Write the proofs that "The rest follows."
                              found in its place in FILE.proof.
  -- ARGUMENTS                (run) Pass ARGUMENTS to the MirageOS image.

soma build --help lists the other options. Proofs about FILE.soma go in
FILE.proof, which build and run also check.
|}

let usage_error fmt =
  Printf.ksprintf (fun msg -> prerr_string (msg ^ "\n\n" ^ usage); exit 2) fmt

(* [rocq c ARGS], with what it prints on stdout (the values of bare terms,
   Mirage's messages) returned instead of shown; errors and warnings, on
   stderr, are shown *)
(* The process soma is waiting for, to which [pass_signals] passes the
   signals soma receives *)
let child = ref None

(* [kill] (SIGTERM) and closing the terminal (SIGHUP) stop the process
   soma is waiting for, rather than soma: soma then exits as it does
   when the process ends, cleaning up after it *)
let pass_signals () =
  let pass = Sys.Signal_handle (fun signal ->
      Option.iter (fun pid -> try Unix.kill pid signal with Unix.Unix_error _ -> ()) !child) in
  Sys.set_signal Sys.sigterm pass;
  Sys.set_signal Sys.sighup pass

let rec wait pid =
  try snd (Unix.waitpid [] pid)
  with Unix.Unix_error (Unix.EINTR, _, _) -> wait pid

let exit_code = function
  | Unix.WEXITED n -> n
  | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> 1

let compile args =
  let prog = get_worker_path { package = "soma-runtime"; basename = "rocqworker" } in
  let argv = Array.of_list (prog :: "--kind=compile" :: args) in
  let out_r, out_w = Unix.pipe ~cloexec:true () in
  let pid = Unix.create_process prog argv Unix.stdin out_w Unix.stderr in
  child := Some pid;
  Unix.close out_w;
  let output = In_channel.input_all (Unix.in_channel_of_descr out_r) in
  Unix.close out_r;
  let code = exit_code (wait pid) in
  child := None;
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
      (* sources are not outputs, even when edited just before *)
      not (List.exists (Filename.check_suffix name) [".soma"; ".v"; ".proof"; ".lang"]) &&
      (time >= start || not (List.mem_assoc name before)))
  |> List.map (fun (name, _) -> Filename.concat dir name)
  |> List.sort compare

let lines s = String.split_on_char '\n' s

let starts_with ~prefix s =
  String.length s >= String.length prefix &&
  String.sub s 0 (String.length prefix) = prefix

(* The proofs that [The rest follows.] found (theories/Soma/Proof.v,
   plugins/soma_proof), in the order of the sentences: rocq c reports each
   as "The rest follows, by:" and its sentences, one on each line indented
   by 4 *)
let rest_follows = "The rest follows."

let found_proofs output =
  let close current acc = match current with Some c -> List.rev c :: acc | None -> acc in
  let rec go acc current = function
    | [] -> List.rev (close current acc)
    | l :: rest when l = "The rest follows, by:" -> go (close current acc) (Some []) rest
    | l :: rest ->
      match current with
      | Some c when starts_with ~prefix:"    " l ->
        go acc (Some (String.sub l 4 (String.length l - 4) :: c)) rest
      | Some _ -> go (close current acc) None (l :: rest)
      | None -> go acc None rest
  in
  go [] None (lines output)

(* Where [The rest follows.] is in a .proof file's text: outside comments
   and strings *)
let occurrences text =
  let n = String.length text in
  let at i s = i + String.length s <= n && String.sub text i (String.length s) = s in
  let rec go i depth in_string acc =
    if i >= n then List.rev acc
    else if in_string then
      if at i "\"\"" then go (i + 2) depth true acc
      else go (i + 1) depth (text.[i] <> '"') acc
    else if at i "(*" then go (i + 2) (depth + 1) false acc
    else if depth > 0 && at i "*)" then go (i + 2) (depth - 1) false acc
    else if depth > 0 then go (i + 1) depth false acc
    else if text.[i] = '"' then go (i + 1) depth true acc
    else if at i rest_follows then go (i + String.length rest_follows) depth false (i :: acc)
    else go (i + 1) depth false acc
  in
  go 0 0 false []

(* Write the proofs found in place of the sentences that found them, the
   first proof for the first sentence, and so on, each sentence of a proof
   on a line of its own, indented as the sentence was. A build stops at a
   sentence whose search fails, so the proofs found are those of the first
   sentences. *)
let fill_proofs proof_file proofs =
  let text = In_channel.with_open_bin proof_file In_channel.input_all in
  let positions = List.filteri (fun i _ -> i < List.length proofs) (occurrences text) in
  let indent i =
    let line_start = match String.rindex_from_opt text (i - 1) '\n' with
      | Some j -> j + 1 | None -> 0 in
    String.make (i - line_start) ' ' in
  let text = List.fold_right2 (fun i proof text ->
      let after = i + String.length rest_follows in
      String.sub text 0 i ^ String.concat ("\n" ^ indent i) proof
      ^ String.sub text after (String.length text - after))
      positions (List.filteri (fun i _ -> i < List.length positions) proofs) text in
  Out_channel.with_open_bin proof_file (fun oc -> output_string oc text);
  List.length positions

let plural n word = if n = 1 then "1 " ^ word else string_of_int n ^ " " ^ word ^ "s"

let build ~verbose ~fill file args =
  let dir = output_dir file args in
  let before = modification_times dir in
  let start = Unix.gettimeofday () in
  let code, output = compile (file :: args) in
  let proofs = found_proofs output in
  let proof_file = Filename.remove_extension file ^ ".proof" in
  (* Without -v, the values of bare terms are not shown; the notice that
     the MirageOS project is being set up is, as it takes a while *)
  if verbose then print_string output
  else
    List.iter (fun l -> if starts_with ~prefix:"Mirage: setting up" l then print_endline l)
      (lines output);
  (* rocq c's files are of no use to a program once it is checked: they
     are deleted, also when checking failed partway. The rest (a MirageOS
     image) is kept. *)
  let compiled f = List.exists (Filename.check_suffix f) [".vo"; ".vos"; ".vok"; ".glob"; ".aux"] in
  List.iter (fun f ->
      if compiled f then Sys.remove f else print_endline f)
    (created ~before ~start ~source:file dir);
  if proofs <> [] then begin
    if fill then
      Printf.printf "%s: %s written in, in place of \"The rest follows.\"\n%!"
        proof_file (plural (fill_proofs proof_file proofs) "proof")
    else if not verbose then
      Printf.printf "%s: %s found by \"The rest follows.\" (soma build -v prints %s, soma build --fill writes %s in)\n%!"
        proof_file (plural (List.length proofs) "proof")
        (if List.length proofs = 1 then "it" else "them") (if List.length proofs = 1 then "it" else "them")
  end;
  if code <> 0 then exit code

(* FILE.proof, the properties of FILE.soma, stands for the program *)
let program_of file =
  if Filename.check_suffix file ".proof" then Filename.chop_suffix file ".proof" ^ ".soma"
  else file

let rec remove_tree path =
  if Sys.is_directory path then begin
    Array.iter (fun name -> remove_tree (Filename.concat path name)) (Sys.readdir path);
    Sys.rmdir path
  end else Sys.remove path

let temp_dir () =
  let file = Filename.temp_file "soma-run" "" in
  Sys.remove file;
  Unix.mkdir file 0o700;
  file

(* What follows the value of a term that failed at run time *)
let runtime_error = "Run-time error: "

(* The value of the last bare term in what [rocq c] printed: a line
   ["     = value"] and the indented lines after it, up to the type, and
   the run-time error that the value ends in, if any *)
let last_value output =
  let rec from_last = function
    | [] -> []
    | l :: rest ->
      match from_last rest with
      | [] when starts_with ~prefix:"     = " l -> l :: rest
      | found -> found
  in
  let rec block = function
    | l :: rest when l <> "" && (l.[0] = ' ' || l.[0] = '\t' || starts_with ~prefix:runtime_error l) ->
      l :: block rest
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
  (* the temporary directory holds the program's image: it is removed
     however the program ends *)
  let finish code = (try remove_tree dir with Sys_error _ -> ()); exit code in
  pass_signals ();
  let vo = Filename.concat dir (Filename.remove_extension (Filename.basename file) ^ ".vo") in
  let code, output = compile (file :: "-o" :: vo :: args) in
  List.iter (fun l -> if starts_with ~prefix:"Mirage: setting up" l then print_endline l)
    (lines output);
  if code <> 0 then finish code;
  match mirage_command output with
  | Some command ->
    (* the image's tools come from the same opam switch as its build *)
    let switch = match Sys.getenv_opt "SOMA_MIRAGE_SWITCH" with
      | Some s when s <> "" -> s | _ -> "hvf" in
    let argv = "opam" :: "exec" :: ("--switch=" ^ switch) :: "--" :: command @ image_args in
    (* Ctrl-C stops the image, which then exits; soma waits for it to
       remove the temporary directory. opam exec runs the image in its
       place, so the signals passed on reach it. *)
    Sys.set_signal Sys.sigint Sys.Signal_ignore;
    let pid = Unix.create_process "opam" (Array.of_list argv) Unix.stdin Unix.stdout Unix.stderr in
    child := Some pid;
    finish (exit_code (wait pid))
  | None ->
    if image_args <> [] then begin
      prerr_endline "soma run: arguments after -- are for a program that requires Sandbox";
      finish 2
    end;
    let value = last_value output in
    Option.iter print_endline value;
    (* a program whose result is a run-time error fails *)
    let failed = match value with
      | Some v -> List.exists (starts_with ~prefix:runtime_error) (lines v)
      | None -> false
    in
    finish (if failed then 1 else 0)

let is_help a = a = "-h" || a = "-help" || a = "--help"

(* the arguments of soma, not those after -- for a MirageOS image *)
let rec before_image_args = function
  | "--" :: _ | [] -> []
  | a :: rest -> a :: before_image_args rest

(* The options of build and run are rocq c's, whose list is reworded for
   soma *)
let options_help command =
  let opts, _ = parse_opts [] in
  init opts [];
  (* rocq c prints them on stderr *)
  let prog = get_worker_path { package = "soma-runtime"; basename = "rocqworker" } in
  let out_r, out_w = Unix.pipe ~cloexec:true () in
  let pid = Unix.create_process prog [| prog; "--kind=compile"; "--help" |] Unix.stdin out_w out_w in
  Unix.close out_w;
  let output = In_channel.input_all (Unix.in_channel_of_descr out_r) in
  Unix.close out_r;
  let code = exit_code (wait pid) in
  let reword l =
    if starts_with ~prefix:"Usage: rocq compile" l then "Usage: soma " ^ command ^ " FILE [options]"
    else if l = "Rocq options are:" then "Options:"
    else if l = "rocq compile specific options:" then "Output options:"
    else l
  in
  print_string (String.concat "\n" (List.map reword (lines output)));
  exit code

(* Rocq's read-eval-print loop, with FILE's definitions loaded first *)
let repl args =
  let opts, args = parse_opts args in
  init opts args;
  let args = match args with
    | file :: rest when file <> "" && file.[0] <> '-' -> "-l" :: file :: rest
    | args -> args
  in
  let prog = get_worker_path { package = "soma-runtime"; basename = "rocqworker" } in
  exec_or_create_process prog (Array.of_list (prog :: "--kind=repl" :: args))

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [] | ("help" | "--help" | "-h") :: _ -> print_string usage
  | ("build" | "run" as command) :: rest when List.exists is_help (before_image_args rest) ->
    options_help command
  | "repl" :: args -> repl args
  | "build" :: rest ->
    (* -v is soma's (rocq c's -v prints its version), before or after FILE *)
    let is_verbose a = a = "-v" || a = "--verbose" in
    let is_fill a = a = "--fill" || a = "-fill" in
    let verbose = List.exists is_verbose rest in
    let fill = List.exists is_fill rest in
    begin match List.filter (fun a -> not (is_verbose a || is_fill a)) rest with
      | [] -> usage_error "soma build: no file given"
      | file :: args ->
        let opts, args = parse_opts args in
        let () = init opts (file :: args) in
        build ~verbose ~fill (program_of file) args
    end
  | ["run"] -> usage_error "soma run: no file given"
  | "run" :: file :: rest ->
    let rec split = function
      | "--" :: image_args -> [], image_args
      | a :: rest -> let args, image_args = split rest in a :: args, image_args
      | [] -> [], []
    in
    let args, image_args = split rest in
    let opts, args = parse_opts args in
    let () = init opts (file :: args) in
    run (program_of file) args image_args
  | command :: _ -> usage_error "soma: unknown command %s" command
