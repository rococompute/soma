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
   requires Sandbox is also built into an image; one that uses OCaml
   modules, with them, into an executable or a page and its script).

   [soma compile FILE [OPTIONS]] does both [soma build] and [soma explore]:
   it builds FILE as [soma build] does, in the same check reviewing it as
   [soma explore] does, and fails when the review finds an issue.

   [soma run FILE [OPTIONS] [-- ARGUMENTS]] checks a program in a
   temporary directory, so that it leaves no files, and prints the value of
   its last bare term; a program that requires Sandbox is built into an
   image, which is run, with ARGUMENTS; one that uses OCaml modules into
   an executable, which is run, with ARGUMENTS, or a page, which is
   served on localhost ($SOMA_PORT, or 8080).

   [soma extract FILE [-o DIR]] checks a program, as [soma run] does, and
   writes it as an OCaml project into DIR: its main extracted to OCaml,
   with the OCaml modules and libraries it uses, which dune builds. *)

open Rocqshim

let usage = {|Usage:
  soma <command> FILE [options]

Commands:
  build                       Check a program and keep what it is built into, if anything:
                              its MirageOS image, or, with OCaml modules, its executable
                              or its page.
  run                         Check a program and print its result, or run its image or
                              its executable, or serve its page on localhost.
  explore                     Review a program and the project files it imports: explore
                              its models, and list its escape hatches and its issues.
  compile                     Build, then review: soma build and soma explore, in one
                              check; fails if the review finds an issue.
  extract                     Check a program and write it as an OCaml project, with the
                              OCaml modules and libraries it uses, that dune builds.
  repl                        Start an interactive session, with FILE loaded if given.
  help                        Show help.

Options:
  -v, --verbose               (build, compile) Print the value of each bare term, and the
                              proofs that "The rest follows." found.
  --fill                      (build, compile) Write the proofs that "The rest follows."
                              found in its place in FILE.proof.
  -- ARGUMENTS                (run) Pass ARGUMENTS to the MirageOS image, or the executable.
  -o DIR                      (extract) Write the OCaml project into DIR (FILE-ocaml next
                              to FILE by default).
  --events                    (run) Show the image's events, and what its run came
                              to, as JSON lines (soma-event, soma-outcome).
  --supervise                 (run) Run the image again when its restart_policy
                              says so (Orchestrate; default_policy 3 1024).

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
      (* the cache of what the program imports (vernac/somaImport.ml) *)
      name <> ".soma-cache" &&
      not (Sys.is_directory (Filename.concat dir name)) &&
      (* sources are not outputs, even when edited just before *)
      not (List.exists (Filename.check_suffix name) [".soma"; ".v"; ".proof"; ".lang"; ".definition"; ".wasm"]) &&
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

(* The review that [soma explore] and [soma compile] print, from the line
   it starts with (plugins/soma_explore), and what precedes it *)
let split_review output =
  let rec split before = function
    | [] -> List.rev before, []
    | l :: rest when starts_with ~prefix:"Review of " l -> List.rev before, l :: rest
    | l :: rest -> split (l :: before) rest in
  let program, review = split [] (lines output) in
  (* the image is built after the review: what Mirage says is the build's,
     and so is what OCaml says *)
  let mirage l = starts_with ~prefix:"Mirage: " l || starts_with ~prefix:"OCaml: " l in
  program @ List.filter mirage review, List.filter (fun l -> not (mirage l)) review

(* a review that found nothing ends so *)
let clean_review review =
  match List.rev (List.filter (fun l -> String.trim l <> "") review) with
  | last :: _ -> String.trim last = "No issue, and no violation."
  | [] -> false

(* [soma build FILE]; with [~review], [soma compile FILE]: the same, and
   then FILE reviewed as by [soma explore] (SOMA_REVIEW), which fails it
   when the review finds an issue or a violation *)
let build ?(review=false) ~verbose ~fill file args =
  let dir = output_dir file args in
  let before = modification_times dir in
  let start = Unix.gettimeofday () in
  if review then Unix.putenv "SOMA_REVIEW" "1";
  (* what the review says, the build does not say again *)
  let args = if review then "-w" :: "-gradual-may-fail" :: args else args in
  let code, output = compile (file :: args) in
  let program_output, review_lines = split_review output in
  let output = String.concat "" (List.map (fun l -> l ^ "\n") program_output) in
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
  if code <> 0 then exit code;
  if review then begin
    if review_lines <> [] then print_newline ();
    List.iter print_endline review_lines;
    if not (clean_review review_lines) then exit 1
  end

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

(* What OCaml's build says it built (toplevel/somaOcaml.ml): ["OCaml:
   built PROG.html, with PROG.js; ..."], a page, or ["OCaml: built
   PROG.exe; ..."], an executable *)
type built = Page of string | Executable of string

let ocaml_built output =
  let prefix = "OCaml: built " in
  List.find_map (fun l ->
      if starts_with ~prefix l then
        let rest = String.sub l (String.length prefix) (String.length l - String.length prefix) in
        let file = List.hd (String.split_on_char ';' (List.hd (String.split_on_char ',' rest))) in
        if Filename.check_suffix file ".html" then Some (Page file)
        else if Filename.check_suffix file ".exe" then Some (Executable file)
        else None
      else None)
    (lines output)

(* [soma run] of a page: [dir] served on localhost, at $SOMA_PORT or 8080,
   or the next port that is free, until Ctrl-C. "/" is the page; the other
   files are those of [dir], by name. *)
let serve_page page =
  let dir = Filename.dirname page in
  let content_type f =
    if Filename.check_suffix f ".html" then "text/html; charset=utf-8"
    else if Filename.check_suffix f ".js" then "text/javascript"
    else if Filename.check_suffix f ".css" then "text/css"
    else "application/octet-stream" in
  let respond fd status ctype body =
    let head = Printf.sprintf "HTTP/1.1 %s\r\nContent-Type: %s\r\nContent-Length: %d\r\n\
                               Cache-Control: no-store\r\nConnection: close\r\n\r\n"
        status ctype (String.length body) in
    let send s = let b = Bytes.of_string s in
      let rec go o = if o < Bytes.length b then go (o + Unix.write fd b o (Bytes.length b - o)) in go 0 in
    (try send head; send body with Unix.Unix_error _ -> ()) in
  let first = match Option.bind (Sys.getenv_opt "SOMA_PORT") int_of_string_opt with
    | Some p when p > 0 -> p | _ -> 8080 in
  let sock = Unix.socket ~cloexec:true Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt sock Unix.SO_REUSEADDR true;
  let rec bind port =
    try Unix.bind sock (Unix.ADDR_INET (Unix.inet_addr_loopback, port)); port
    with Unix.Unix_error (Unix.EADDRINUSE, _, _) when port < first + 20 -> bind (port + 1) in
  let port = bind first in
  Unix.listen sock 16;
  Printf.printf "Serving %s at http://localhost:%d/ (Ctrl-C stops)\n%!" (Filename.basename page) port;
  let buf = Bytes.create 8192 in
  while true do
    match Unix.accept ~cloexec:true sock with
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> ()
    | fd, _ ->
      let n = try Unix.read fd buf 0 (Bytes.length buf) with Unix.Unix_error _ -> 0 in
      let request = Bytes.sub_string buf 0 n in
      (match String.split_on_char ' ' (List.hd (String.split_on_char '\r' request)) with
       | "GET" :: path :: _ ->
         let path = List.hd (String.split_on_char '?' path) in
         let name = if path = "/" then Filename.basename page
           else String.sub path 1 (String.length path - 1) in
         let file = Filename.concat dir name in
         if name <> "" && not (String.contains name '/') && name.[0] <> '.' && Sys.file_exists file
            && not (Sys.is_directory file) then
           respond fd "200 OK" (content_type name) (In_channel.with_open_bin file In_channel.input_all)
         else respond fd "404 Not Found" "text/plain" "Not found\n"
       | _ -> respond fd "405 Method Not Allowed" "text/plain" "Only GET\n");
      (try Unix.close fd with Unix.Unix_error _ -> ())
  done

(* Running an image: its console, with the events of its runtime
   (toplevel/somaMirage.ml, "soma-event {...}" lines) read rather than
   shown, and what the run came to said at its end *)

(* The fields of an event: a flat JSON object of strings, numbers and
   booleans, as the runtime writes them *)
let event_fields line =
  let n = String.length line in
  let rec skip i = if i < n && (line.[i] = ' ' || line.[i] = ',' || line.[i] = '{') then skip (i + 1) else i in
  let string_at i =
    let b = Buffer.create 16 in
    let rec go i =
      if i >= n then i
      else match line.[i] with
        | '"' -> i + 1
        | '\\' when i + 1 < n ->
          (match line.[i + 1] with
           | 'n' -> Buffer.add_char b '\n'
           | 'u' when i + 5 < n ->
             Buffer.add_char b (Char.chr (int_of_string ("0x" ^ String.sub line (i + 2) 4) land 255));
             ignore (go (i + 6))
           | c -> Buffer.add_char b c);
          if line.[i + 1] = 'u' then go (i + 6) else go (i + 2)
        | c -> Buffer.add_char b c; go (i + 1)
    in
    let stop = go (i + 1) in
    Buffer.contents b, stop
  in
  let rec fields i acc =
    let i = skip i in
    if i >= n || line.[i] = '}' || line.[i] <> '"' then List.rev acc
    else
      let key, i = string_at i in
      let i = if i < n && line.[i] = ':' then i + 1 else i in
      if i < n && line.[i] = '"' then
        let v, i = string_at i in fields i ((key, v) :: acc)
      else
        let j = ref i in
        while !j < n && line.[!j] <> ',' && line.[!j] <> '}' do incr j done;
        fields !j ((key, String.sub line i (!j - i)) :: acc)
  in
  fields 0 []

let event_prefix = "soma-event "

(* What a run came to *)
type failure = { kind : string; message : string option; expected : string option; actual : string option }

type outcome =
  | Finished
  | Exited of int                              (* the program's [exit n] *)
  | Failed of failure                          (* a run-time error in [main]: the image stopped *)
  | Out_of_memory of { memory_kb : int option; live_kb : int option }
  | Aborted of { code : int; last_line : string option }   (* stopped, saying nothing of why *)
  | Signaled of int

let failure_of fields =
  let get k = List.assoc_opt k fields in
  { kind = (match get "kind" with Some k -> k | None -> "unknown"); message = get "message";
    expected = get "expected"; actual = get "actual" }

let describe_failure f = match f.kind, f.message with
  | "cast", Some m -> "a run-time error: " ^ m
  | "raise", _ -> "a run-time error: the program reached raise"
  | "stack_overflow", _ -> "a stack overflow (a recursion too deep for the image's stack)"
  | "unknown", _ -> "a run-time error: the program reached unk"
  | _, Some m -> "an exception: " ^ m
  | k, None -> k

let diagnosis = function
  | Finished -> None
  | Exited 0 -> None
  | Exited n -> Some (Printf.sprintf "the program exited with code %d." n)
  | Failed f -> Some ("the program stopped on " ^ describe_failure f ^ ".")
  | Out_of_memory { memory_kb; live_kb } ->
    let mb kb = (kb + 512) / 1024 in
    Some (Printf.sprintf "the image ran out of memory%s%s."
            (match memory_kb with Some m -> Printf.sprintf " (%d MB of heap" (mb m) | None -> "")
            (match memory_kb, live_kb with
             | Some _, Some l -> Printf.sprintf "; %d MB live at the last report)" (mb l)
             | Some _, None -> ")" | None, _ -> ""))
  | Aborted { code; last_line } ->
    Some (Printf.sprintf "the image stopped without saying why (exit code %d)%s" code
            (match last_line with Some l -> "; its last line: " ^ l | None -> "."))
  | Signaled _ -> Some "the image was stopped."

let json_of_outcome o =
  let str s = "\"" ^ String.concat "\\\"" (String.split_on_char '"' s) ^ "\"" in
  let opt k = function Some v -> Printf.sprintf ",%s:%s" (str k) v | None -> "" in
  match o with
  | Finished -> "{\"outcome\":\"finished\"}"
  | Exited n -> Printf.sprintf "{\"outcome\":\"exited\",\"code\":%d}" n
  | Failed f ->
    Printf.sprintf "{\"outcome\":\"failed\",\"kind\":%s%s%s%s}" (str f.kind)
      (opt "message" (Option.map str f.message)) (opt "expected" (Option.map str f.expected))
      (opt "actual" (Option.map str f.actual))
  | Out_of_memory { memory_kb; live_kb } ->
    Printf.sprintf "{\"outcome\":\"out_of_memory\"%s%s}"
      (opt "memory_kb" (Option.map string_of_int memory_kb)) (opt "live_kb" (Option.map string_of_int live_kb))
  | Aborted { code; last_line } ->
    Printf.sprintf "{\"outcome\":\"aborted\",\"code\":%d%s}" code (opt "last_line" (Option.map str last_line))
  | Signaled n -> Printf.sprintf "{\"outcome\":\"signaled\",\"signal\":%d}" n

(* Runs the image, showing its console (and, with [events], its events),
   and says what the run came to *)
let run_image ~events argv =
  let out_r, out_w = Unix.pipe ~cloexec:true () in
  let pid = Unix.create_process "opam" (Array.of_list argv) Unix.stdin out_w out_w in
  child := Some pid;
  Unix.close out_w;
  let ic = Unix.in_channel_of_descr out_r in
  let memory_kb = ref None and live_kb = ref None and ended = ref None
  and in_main = ref None and request_failures = ref 0 and last_request_failure = ref None
  and last_line = ref None and out_of_memory = ref false and signal = ref None in
  let int_field fields k = Option.bind (List.assoc_opt k fields) int_of_string_opt in
  let rec read () =
    match In_channel.input_line ic with
    | None -> ()
    | Some l ->
      if starts_with ~prefix:event_prefix l then begin
        if events then print_endline l;
        let fields = event_fields (String.sub l (String.length event_prefix) (String.length l - String.length event_prefix)) in
        (match List.assoc_opt "event" fields with
         | Some "start" -> memory_kb := int_field fields "memory_kb"
         | Some ("alive" | "memory_pressure") ->
           (match int_field fields "live_kb" with Some k -> live_kb := Some k | None -> ())
         | Some "failure" ->
           if List.assoc_opt "during" fields = Some "request" then begin
             incr request_failures; last_request_failure := Some (failure_of fields)
           end else in_main := Some (failure_of fields)
         | Some "exit" -> ended := Some fields
         | _ -> ())
      end else begin
        print_endline l;
        if String.trim l <> "" && not (starts_with ~prefix:"Solo5:" l) then last_line := Some l;
        (* the allocator gives up: OCaml's "allocation failure" or
           Out_of_memory, before the unikernel aborts *)
        let has sub = let n = String.length sub in
          let rec at i = i + n <= String.length l && (String.sub l i n = sub || at (i + 1)) in at 0 in
        if has "allocation failure" || has "Out_of_memory" || has "out of memory" then out_of_memory := true;
        (* solo5-hvt, stopped (kill, Ctrl-C), says so and exits 1 *)
        let stopped = "solo5-hvt: Exiting on signal " in
        if starts_with ~prefix:stopped l then
          signal := int_of_string_opt (String.trim (String.sub l (String.length stopped) (String.length l - String.length stopped)))
      end;
      read ()
  in
  read ();
  close_in ic;
  let status = wait pid in
  let out_of_memory = !out_of_memory ||
    (match !in_main with Some { kind = "out_of_memory"; _ } -> true | _ -> false) in
  let outcome = match !ended, status with
    | _, _ when out_of_memory -> Out_of_memory { memory_kb = !memory_kb; live_kb = !live_kb }
    | Some fields, _ ->
      (match List.assoc_opt "reason" fields, int_field fields "code" with
       | Some "finished", _ -> Finished
       | Some "program", Some n -> Exited n
       | _, _ -> (match !in_main with Some f -> Failed f | None -> Aborted { code = exit_code status; last_line = !last_line }))
    | None, Unix.WSIGNALED n -> Signaled n
    | None, _ when Option.has_some !signal -> Signaled (Option.get !signal)
    | None, _ ->
      (match !in_main with
       | Some f -> Failed f
       | None when exit_code status = 0 -> Finished
       | None -> Aborted { code = exit_code status; last_line = !last_line })
  in
  if !request_failures > 0 then
    Printf.eprintf "soma run: %s with a run-time error, the server going on; the last: %s.\n%!"
      (if !request_failures = 1 then "1 request failed" else string_of_int !request_failures ^ " requests failed")
      (match !last_request_failure with Some f -> describe_failure f | None -> "");
  Option.iter (fun d -> Printf.eprintf "soma run: %s\n%!" d) (diagnosis outcome);
  if events then Printf.printf "soma-outcome %s\n%!" (json_of_outcome outcome);
  outcome, exit_code status

(* Supervision (theories/Soma/Orchestrate.v): the outcome, as a term of
   Soma, is given to the program's [restart_policy], or to
   [default_policy 3 1024], which decides whether to run the image again *)

let soma_string s = "\"" ^ String.concat "\"\"" (String.split_on_char '"' s) ^ "\""

let outcome_term ~memory_mb = function
  | Finished -> "Finished"
  | Exited n -> Printf.sprintf "(Exited %d)" n
  | Failed f ->
    let failure = match f.kind, f.expected, f.actual with
      | "cast", Some e, Some a -> Printf.sprintf "(CastFailure %s %s)" (soma_string e) (soma_string a)
      | "raise", _, _ -> "Raised"
      | "unknown", _, _ -> "Unknown"
      | "stack_overflow", _, _ -> "StackOverflow"
      | _ -> Printf.sprintf "(Crashed %s)" (soma_string (describe_failure f)) in
    "(Failed " ^ failure ^ ")"
  | Out_of_memory { live_kb; _ } ->
    Printf.sprintf "(Failed (OutOfMemory %d %d))" memory_mb
      (match live_kb with Some k -> k / 1024 | None -> 0)
  | Aborted { last_line; _ } ->
    Printf.sprintf "(Failed (Crashed %s))"
      (soma_string (match last_line with Some l -> l | None -> "stopped without saying why"))
  | Signaled _ -> "Stopped"

type decision = Done | Restart | Restart_with of int

(* What the policy decides, evaluated by checking a file that requires the
   program's library, compiled to [dir]/[name].vo *)
let decide ~dir ~name ~memory_mb ~restarts outcome =
  let evaluate policy imports =
    let file = Filename.concat dir "soma_decide.soma" in
    Out_channel.with_open_bin file (fun oc ->
        Printf.fprintf oc "Require Import Orchestrate%s.\n%s %s %d %d.\n" imports policy
          (outcome_term ~memory_mb outcome) memory_mb restarts);
    let previous = Sys.getenv_opt "SOMA_MIRAGE_BUILD" in
    Unix.putenv "SOMA_MIRAGE_BUILD" "0";
    let code, output = compile [file; "-Q"; dir; ""; "-o"; Filename.concat dir "soma_decide.vo"] in
    Unix.putenv "SOMA_MIRAGE_BUILD" (match previous with Some v -> v | None -> "1");
    if code <> 0 then None
    else match last_value output with
      | None -> None
      | Some v ->
        let words = List.filter (( <> ) "") (String.split_on_char ' '
            (String.concat " " (String.split_on_char '\n' v))) in
        match words with
        | "=" :: "Done" :: _ -> Some Done
        | "=" :: "Restart" :: _ -> Some Restart
        | "=" :: "RestartWith" :: m :: _ -> Option.map (fun m -> Restart_with m) (int_of_string_opt m)
        | _ -> None
  in
  match evaluate "restart_policy" (" " ^ name) with
  | Some d -> d
  | None -> match evaluate "default_policy 3 1024" "" with Some d -> d | None -> Done

let with_memory memory_mb command =
  List.map (fun a -> if starts_with ~prefix:"--mem=" a then "--mem=" ^ string_of_int memory_mb else a) command

let memory_of command =
  List.fold_left (fun m a ->
      if starts_with ~prefix:"--mem=" a then
        (match int_of_string_opt (String.sub a 6 (String.length a - 6)) with Some n -> n | None -> m)
      else m) 256 command

(* [soma explore FILE]: FILE checked in a temporary directory, as by
   [soma run], without an image, and then reviewed (SOMA_REVIEW, which
   toplevel/ccompile.ml reads; plugins/soma_explore): its models explored,
   its escape hatches and its issues listed. It fails when there is a
   violation or an issue. *)
let explore file args =
  let dir = temp_dir () in
  let finish code = (try remove_tree dir with Sys_error _ -> ()); exit code in
  pass_signals ();
  Unix.putenv "SOMA_REVIEW" "1";
  Unix.putenv "SOMA_MIRAGE_BUILD" "0";
  Unix.putenv "SOMA_OCAML_BUILD" "0";
  let vo = Filename.concat dir (Filename.remove_extension (Filename.basename file) ^ ".vo") in
  (* what the review says, the build does not say again *)
  let code, output = compile (file :: "-o" :: vo :: "-w" :: "-gradual-may-fail" :: args) in
  (* the review, and not the values of the program's bare terms *)
  let _, review = split_review output in
  List.iter print_endline review;
  finish (if code <> 0 then code else if clean_review review then 0 else 1)

(* [soma extract FILE [-o DIR]]: FILE checked in a temporary directory,
   as by [soma run], and its program extracted to OCaml, into DIR
   (FILE-ocaml next to it by default): an OCaml project that dune builds,
   with the OCaml modules and libraries the program uses
   (SOMA_OCAML_EXTRACT, which toplevel/somaOcaml.ml reads) *)
let extract file args =
  let rec split out = function
    | "-o" :: dir :: rest -> split (Some dir) rest
    | a :: rest -> let out, rest = split out rest in out, a :: rest
    | [] -> out, [] in
  let out, args = split None args in
  let absolute f = if Filename.is_relative f then Filename.concat (Sys.getcwd ()) f else f in
  let out = match out with
    | Some d -> absolute d
    | None ->
      let file = absolute file in
      let dir = Filename.dirname file in
      let dir = if Filename.basename dir = Filename.current_dir_name then Filename.dirname dir else dir in
      Filename.concat dir (Filename.remove_extension (Filename.basename file) ^ "-ocaml") in
  let dir = temp_dir () in
  let finish code = (try remove_tree dir with Sys_error _ -> ()); exit code in
  pass_signals ();
  Unix.putenv "SOMA_OCAML_EXTRACT" out;
  Unix.putenv "SOMA_MIRAGE_BUILD" "0";
  let vo = Filename.concat dir (Filename.remove_extension (Filename.basename file) ^ ".vo") in
  let code, output = compile (file :: "-o" :: vo :: args) in
  List.iter (fun l -> if starts_with ~prefix:"OCaml: " l then print_endline l) (lines output);
  finish code

let run ~events ~supervise file args image_args =
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
    if not supervise then finish (snd (run_image ~events argv))
    else begin
      let name = Filename.remove_extension (Filename.basename vo) in
      let rec loop memory_mb restarts =
        let outcome, code = run_image ~events (with_memory memory_mb argv) in
        match outcome with
        | Signaled _ -> finish code   (* stopped from outside: supervision ends too *)
        | _ ->
          match decide ~dir ~name ~memory_mb ~restarts outcome with
          | Done ->
            if restarts > 0 then
              Printf.eprintf "soma run: the restart policy is done, after %s.\n%!" (plural restarts "restart");
            finish code
          | Restart ->
            Printf.eprintf "soma run: restarting (restart %d).\n%!" (restarts + 1);
            loop memory_mb (restarts + 1)
          | Restart_with m ->
            Printf.eprintf "soma run: restarting with %d MB (restart %d).\n%!" m (restarts + 1);
            loop m (restarts + 1)
      in
      loop (memory_of command) 0
    end
  | None ->
    match ocaml_built output with
    | Some (Executable exe) ->
      (* a program built with OCaml modules: run, with ARGUMENTS; Ctrl-C
         stops it, and then soma *)
      Sys.set_signal Sys.sigint Sys.Signal_ignore;
      let argv = Array.of_list (exe :: image_args) in
      let pid = Unix.create_process exe argv Unix.stdin Unix.stdout Unix.stderr in
      child := Some pid;
      finish (exit_code (wait pid))
    | Some (Page page) ->
      if image_args <> [] then begin
        prerr_endline "soma run: arguments after -- are for a program, and not for a page";
        finish 2
      end;
      Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> finish 0));
      serve_page page
    | None ->
    if image_args <> [] then begin
      prerr_endline "soma run: arguments after -- are for a program that requires Sandbox or uses OCaml modules";
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

(* soma run FILE [OPTIONS] [-- ARGUMENTS], --events taken out *)
let run_command ~events ~supervise = function
  | [] -> usage_error "soma run: no file given"
  | file :: rest ->
    let rec split = function
      | "--" :: image_args -> [], image_args
      | a :: rest -> let args, image_args = split rest in a :: args, image_args
      | [] -> [], []
    in
    let args, image_args = split rest in
    let opts, args = parse_opts args in
    let () = init opts (file :: args) in
    run ~events ~supervise (program_of file) args image_args

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [] | ("help" | "--help" | "-h") :: _ -> print_string usage
  | ("build" | "compile" | "run" as command) :: rest when List.exists is_help (before_image_args rest) ->
    options_help command
  | "repl" :: args -> repl args
  | ("build" | "compile" as command) :: rest ->
    (* -v is soma's (rocq c's -v prints its version), before or after FILE *)
    let is_verbose a = a = "-v" || a = "--verbose" in
    let is_fill a = a = "--fill" || a = "-fill" in
    let verbose = List.exists is_verbose rest in
    let fill = List.exists is_fill rest in
    begin match List.filter (fun a -> not (is_verbose a || is_fill a)) rest with
      | [] -> usage_error "soma %s: no file given" command
      | file :: args ->
        let opts, args = parse_opts args in
        let () = init opts (file :: args) in
        build ~review:(command = "compile") ~verbose ~fill (program_of file) args
    end
  | "extract" :: rest ->
    begin match rest with
      | [] -> usage_error "soma extract: no file given"
      | file :: args ->
        let opts, args = parse_opts args in
        let () = init opts (file :: args) in
        extract (program_of file) args
    end
  | "explore" :: rest ->
    begin match rest with
      | [] -> usage_error "soma explore: no file given"
      | file :: args ->
        let opts, args = parse_opts args in
        let () = init opts (file :: args) in
        explore (program_of file) args
    end
  | "run" :: rest ->
    (* --events and --supervise are soma's, anywhere before -- *)
    let ours a = a = "--events" || a = "--supervise" in
    let rec drop = function
      | a :: l when ours a -> drop l
      | "--" :: _ as l -> l
      | a :: l -> a :: drop l
      | [] -> [] in
    let given = before_image_args rest in
    run_command ~events:(List.mem "--events" given) ~supervise:(List.mem "--supervise" given) (drop rest)
  | command :: _ -> usage_error "soma: unknown command %s" command
