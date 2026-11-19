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
   with the OCaml modules and libraries it uses, which dune builds.

   [soma hash FILE] checks a program, as [soma run] does, and prints the hash
   of each definition of it, and of what it imports of its project and its
   dependencies: of what the kernel checked, not of the file.

   [soma search QUERY [FILE]] finds definitions and theorems by name, or by
   the shape of their types, in a project and what it depends on, with where
   each is and what it assumes (vernac/somaSearch.ml).

   [soma diff OLD NEW] compares two versions of a project, each a tag
   (PATH@VERSION) or a folder, by those hashes (vernac/somaDiff.ml).

   [soma get [PATH[@VERSION]]] writes a dependency into soma.toml, and
   resolves the project's dependencies into soma.lock (vernac/somaDeps.ml). *)

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
  test [PATH ...]             Check Soma test entry points and their .exp expectations.
                              Select affected tests automatically; --full runs all.
                              --changedSince REF overrides the diff; --listTests
                              lists them without building. soma test --help has details.
  extract                     Check a program and write it as an OCaml project, with the
                              OCaml modules and libraries it uses, that dune builds.
  hash                        Check a program and print each definition's hashes: CONTRACT
                              WITNESS NAME, and what it assumes. Comments and layout do not
                              change them; another proof changes only the witness.
  search QUERY [FILE]         Find definitions and theorems, in the project and the
                              dependencies it names, or in what FILE sees: by a name
                              (discount), part of a name, or a type ('list nat -> nat',
                              '_ <= _'). --limit N, --no-assumptions, --json.
  diff OLD NEW                Compare two versions of a project, each PATH@VERSION or a
                              folder: what was edited, what has another proof, and what
                              now assumes more. Writes nothing to the project.
  get [PATH[@VERSION]]        Add a dependency to soma.toml ("owner/repo" = "1.2.3"; its
                              greatest tag without a version), and resolve the project's
                              dependencies into soma.lock.
  repl                        Start an interactive session, with FILE loaded if given.
  help                        Show help.

Options:
  -v, --verbose               (build, compile) Print the value of each bare term, and the
                              proofs that "The rest follows." found.
  --no-image                  Check Sandbox OCaml without building an image
  --no-module-cache           (build, compile) Do not read or write the shared module
                              store. The project's .soma-cache is still used.
  --fill                      (build, compile) Write the proofs that "The rest follows."
                              found in its place in FILE.exp.
  --check-fresh               (build) Say, from metadata alone, whether FILE is as its last
                              successful build left it ("unchanged", exit 0) or not
                              ("stale: REASON", exit 1). Builds nothing.
  -- ARGUMENTS                (run) Pass ARGUMENTS to the MirageOS image, or the executable.
  -o DIR                      (extract) Write the OCaml project into DIR (FILE-ocaml next
                              to FILE by default).
  --events                    (run) Show the image's events, and what its run came
                              to, as JSON lines (soma-event, soma-outcome).
  --supervise                 (run) Run the image again when its restart_policy
                              says so (Orchestrate; default_policy 3 1024).

soma build --help lists the other options. Next to FILE.soma, FILE.ext has
its extensions (macros, readers), read before it, and FILE.exp its
expectations (lemmas and theorems), which build and run also check.
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

let cache_toolchain = ref (fun () -> "")

let compile args =
  ignore (!cache_toolchain ());
  let prog = get_worker_path { package = "soma-runtime"; basename = "rocqworker" } in
  let argv = Array.of_list (prog :: "--kind=compile" :: args) in
  let out_r, out_w = Unix.pipe ~cloexec:true () in
  let pid = Unix.create_process prog argv Unix.stdin out_w Unix.stderr in
  child := Some pid;
  Unix.close out_w;
  let output = In_channel.input_all (Unix.in_channel_of_descr out_r) in
  Unix.close out_r;
  let status = wait pid in
  let code = exit_code status in
  child := None;
  (match List.find_opt (fun a -> a = "" || a.[0] <> '-') args with
   | Some file -> CUnix.report_compile_signal file status
   | None -> CUnix.report_compile_signal "compilation" status);
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

(* The files of [dir] that are new since [before], or whose modification
   time changed since [before], but [source] *)
let created ~before ~source dir =
  modification_times dir
  |> List.filter (fun (name, time) ->
      Filename.concat dir name <> source &&
      (* the cache of what the program imports (vernac/somaImport.ml) *)
      name <> ".soma-cache" &&
      (* and of the versions of its dependencies (vernac/somaDeps.ml) *)
      name <> "soma.lock" &&
      not (Sys.is_directory (Filename.concat dir name)) &&
      (* sources are not outputs, even when edited just before *)
      not (List.exists (Filename.check_suffix name) [".soma"; ".v"; ".exp"; ".ext"; ".definition"; ".wasm"]) &&
      (match List.assoc_opt name before with
       | Some old -> time <> old
       | None -> true))
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

(* Where [The rest follows.] is in a .exp file's text: outside comments
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
let fill_proofs exp_file proofs =
  let text = In_channel.with_open_bin exp_file In_channel.input_all in
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
  Out_channel.with_open_bin exp_file (fun oc -> output_string oc text);
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

(* Shared compiled-artifact store: $SOMA_CACHE, or else $XDG_CACHE_HOME/soma
   (~/.cache/soma without it), keyed by a hash of the project sources that
   determine compilation (every .soma, .exp, .ext, .definition, .wasm,
   .ml and .lean of the project by its path and bytes, soma.toml, soma.lock,
   and the toolchain). After a successful build the checkout's .soma-cache
   is published under its key; at the start of a build, an absent local
   .soma-cache is restored from the store when the same key is present. A
   restored .definition's .vo names its FILE.ml relative to the project, so
   it is the .ml of the checkout being built (SomaImport.project_file).
   [soma build --no-module-cache] skips the store both ways. *)
let shared_cache_dir () =
  match Sys.getenv_opt "SOMA_CACHE" with
  | Some d when d <> "" -> Some d
  | _ ->
    match Sys.getenv_opt "XDG_CACHE_HOME" with
    | Some x when x <> "" -> Some (Filename.concat x "soma")
    | _ ->
      (match Sys.getenv_opt "HOME" with
       | Some h when h <> "" -> Some (Filename.concat (Filename.concat h ".cache") "soma")
       | _ -> None)

let rec mkdir_p d =
  if d <> "" && d <> "." && not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

let copy_file src dst =
  In_channel.with_open_bin src (fun ic ->
      Out_channel.with_open_bin dst (fun oc ->
          Out_channel.output_string oc (In_channel.input_all ic)))

let rec copy_tree src dst =
  mkdir_p dst;
  Array.iter (fun name ->
      if name <> ".tests" then begin
        let s = Filename.concat src name and d = Filename.concat dst name in
        if (Unix.lstat s).Unix.st_kind = Unix.S_DIR then copy_tree s d
        else if SomaCache.trusted s then copy_file s d
      end)
    (Sys.readdir src)

let is_directory_opt p = try Sys.is_directory p with Sys_error _ -> false

(* The source files of the project, as (path relative to the root, digest).
   Symbolic links are followed, so a link to a directory already on the
   current path ([ln -s . loop.soma]) is not entered again: its files are
   already in the list under the path that reached it, and following it
   would recurse until the kernel reported ELOOP, which [Digest.file] then
   raised on the path it could not follow. A link that cannot be stat'ed,
   and a file that cannot be read, contribute a marker instead of an
   exception, so that repairing them changes the key. *)
let project_cache_sources root =
  let source name =
    name = "soma.lock" ||
    List.exists (Filename.check_suffix name)
      [".soma"; ".exp"; ".ext"; ".definition"; ".wasm"; ".ml"; ".lean"; ".toml"] in
  let stat_opt p = try Some (Unix.stat p) with Unix.Unix_error _ | Sys_error _ -> None in
  let dir_id st = st.Unix.st_dev, st.Unix.st_ino in
  let digest p =
    match (try Some (Digest.file p) with Sys_error _ | Unix.Unix_error _ -> None) with
    | Some d -> Digest.to_hex d
    | None -> "<unreadable>" in
  let rec walk rel dir ancestors acc =
    Array.fold_left (fun acc name ->
        if List.mem name [".soma-cache"; ".git"; "_build"] then acc
        else
          let full = Filename.concat dir name in
          let r = if rel = "" then name else rel ^ "/" ^ name in
          match stat_opt full with
          | Some st when st.Unix.st_kind = Unix.S_DIR ->
            let id = dir_id st in
            if List.mem id ancestors then acc
            else walk r full (id :: ancestors) acc
          | Some _ -> if source name then (r, digest full) :: acc else acc
          | None -> if source name then (r, "<unreadable>") :: acc else acc)
      acc (try Sys.readdir dir with Sys_error _ -> [||]) in
  let ancestors = match stat_opt root with Some st -> [dir_id st] | None -> [] in
  List.sort compare (walk "" root ancestors [])

let project_cache_key file =
  let abs_file = if Filename.is_relative file then Filename.concat (Sys.getcwd ()) file else file in
  let start_dir = Filename.dirname abs_file in
  let rec find_root dir =
    if Sys.file_exists (Filename.concat dir "soma.toml") then dir
    else let up = Filename.dirname dir in if up = dir then start_dir else find_root up in
  let root = find_root start_dir in
  let files = project_cache_sources root in
  let key = Digest.to_hex (Digest.string (String.concat "\n"
      (!cache_toolchain () :: List.map (fun (rel, digest) -> rel ^ " " ^ digest) files))) in
  root, Filename.concat root ".soma-cache", key

(* A dependency on a folder ({ path = "../wip" }) is compiled from sources
   outside the project, which the key does not cover, and its .vo names its
   FILE.ml by its absolute path: such a project is not shared through the
   store. Any line of soma.toml that sets a [path] counts (a false one only
   keeps the project out of the store). *)
let has_path_dependency root =
  let toml = Filename.concat root "soma.toml" in
  let squeeze l = String.concat "" (String.split_on_char ' ' (String.concat "" (String.split_on_char '\t' l))) in
  let sets_path l =
    let l = squeeze l in
    let rec at i =
      i + 5 <= String.length l &&
      ((String.sub l i 5 = "path=" &&
        (i = 0 || not (match l.[i - 1] with 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '-' -> true | _ -> false)))
       || at (i + 1)) in
    at 0 in
  try List.exists sets_path (String.split_on_char '\n' (In_channel.with_open_bin toml In_channel.input_all))
  with Sys_error _ -> false

let shared_store_for file =
  match shared_cache_dir () with
  | None -> None
  | Some store ->
    let (root, _, _) as k = project_cache_key file in
    if has_path_dependency root then None else Some (store, k)

let restore_shared_cache file =
  match shared_store_for file with
  | None -> ()
  | Some (store, (_, cache_dir, key)) ->
    let stored = Filename.concat store key in
    if not (Sys.file_exists cache_dir) && is_directory_opt stored then
      (try copy_tree stored cache_dir with Sys_error _ | Unix.Unix_error _ -> ())

let publish_shared_cache file =
  match shared_store_for file with
  | None -> ()
  | Some (store, (_, cache_dir, key)) ->
    let stored = Filename.concat store key in
    if is_directory_opt cache_dir && not (Sys.file_exists stored) then
      (try
         mkdir_p store;
         let tmp = Filename.temp_file ~temp_dir:store ".publish-" "" in
         Sys.remove tmp;
         let rec publish src dst =
           mkdir_p dst;
           Array.iter (fun name ->
               if name <> ".tests" then begin
                 let s = Filename.concat src name and d = Filename.concat dst name in
                 match (Unix.lstat s).Unix.st_kind with
                 | Unix.S_DIR -> publish s d
                 | Unix.S_REG when SomaCache.trusted s -> copy_file s d
                 | _ -> ()
               end) (Sys.readdir src) in
         publish cache_dir tmp;
         (try Sys.rename tmp stored with Unix.Unix_error (Unix.EEXIST, _, _) -> ())
       with Sys_error _ | Unix.Unix_error _ -> ())

(* [soma build FILE]; with [~review], [soma compile FILE]: the same, and
   then FILE reviewed as by [soma explore] (SOMA_REVIEW), which fails it
   when the review finds an issue or a violation *)
let build ?(review=false) ?(timings=false) ?(share=true) ~verbose ~fill file args =
  ignore (!cache_toolchain ());
  if share then restore_shared_cache file;
  let dir = output_dir file args in
  let before = modification_times dir in
  let start = Unix.gettimeofday () in
  if review then Unix.putenv "SOMA_REVIEW" "1";
  (* what the review says, the build does not say again *)
  let args = if review then "-w" :: "-gradual-may-fail" :: args else args in
  let timing_file = if timings then Some (Filename.temp_file "soma-timings" ".log") else None in
  Option.iter (Unix.putenv "SOMA_BUILD_TIMINGS") timing_file;
  let code, output = Fun.protect
      ~finally:(fun () -> Option.iter (fun _ -> Unix.putenv "SOMA_BUILD_TIMINGS" "") timing_file)
      (fun () -> compile (file :: args)) in
  let program_output, review_lines = split_review output in
  let output = String.concat "" (List.map (fun l -> l ^ "\n") program_output) in
  let proofs = found_proofs output in
  let exp_file = Filename.remove_extension file ^ ".exp" in
  (* Without -v, the values of bare terms are not shown; the notice that
     the MirageOS project is being set up is, as it takes a while, and so
     are the times that -time asks for ("Chars 0 - 26 [Definition~...]
     0.002 secs") *)
  let time = List.mem "-time" args in
  if verbose then print_string output
  else
    List.iter (fun l -> if starts_with ~prefix:"Mirage: setting up" l ||
          starts_with ~prefix:"Mirage: checked" l ||
          (time && starts_with ~prefix:"Chars " l) then print_endline l)
      (lines output);
  (* rocq c's files are of no use to a program once it is checked: they
     are deleted, also when checking failed partway. The rest (a MirageOS
     image) is kept. *)
  let compiled f = List.exists (Filename.check_suffix f) [".vo"; ".vos"; ".vok"; ".glob"; ".aux"] in
  List.iter (fun f ->
      if compiled f then Sys.remove f else print_endline f)
    (created ~before ~source:file dir);
  if proofs <> [] then begin
    if fill then
      Printf.printf "%s: %s written in, in place of \"The rest follows.\"\n%!"
        exp_file (plural (fill_proofs exp_file proofs) "proof")
    else if not verbose then
      Printf.printf "%s: %s found by \"The rest follows.\" (soma build -v prints %s, soma build --fill writes %s in)\n%!"
        exp_file (plural (List.length proofs) "proof")
        (if List.length proofs = 1 then "it" else "them") (if List.length proofs = 1 then "it" else "them")
  end;
  Option.iter (fun path ->
      Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
          let reports = In_channel.with_open_bin path In_channel.input_all in
          print_string reports;
          let peak = List.fold_left (fun peak line ->
              match String.split_on_char '\t' line with
              | [_; _; memory] -> max peak (int_of_string (List.hd (String.split_on_char ' ' memory)))
              | _ -> peak) 0 (String.split_on_char '\n' reports) in
          Printf.printf "Total: %.3f s\t%d KiB peak heap memory\n%!"
            (Unix.gettimeofday () -. start) peak)) timing_file;
  if code = 0 && share then publish_shared_cache file;
  if code <> 0 then exit code;
  if review then begin
    if review_lines <> [] then print_newline ();
    List.iter print_endline review_lines;
    if not (clean_review review_lines) then exit 1
  end

(* FILE.exp, the properties of FILE.soma, stands for the program *)
let program_of file =
  List.iter (fun (old_ext, new_ext) ->
      if Filename.check_suffix file old_ext then begin
        Printf.eprintf "soma: %s is not read: %s files are %s files now. Rename it: git mv %s %s\n"
          file old_ext new_ext file (Filename.chop_suffix file old_ext ^ new_ext);
        exit 2
      end) [".proof", ".exp"; ".lang", ".ext"];
  if Filename.check_suffix file ".exp" then Filename.chop_suffix file ".exp" ^ ".soma"
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

(* [soma hash FILE]: FILE checked in a temporary directory, as by [soma run],
   and the hashes of what was checked (SOMA_HASH, vernac/somaHash.ml) *)
let hash file args =
  let dir = temp_dir () in
  let finish code = (try remove_tree dir with Sys_error _ -> ()); exit code in
  pass_signals ();
  let hashes = Filename.concat dir "hashes" in
  Unix.putenv "SOMA_HASH" hashes;
  Unix.putenv "SOMA_MIRAGE_BUILD" "0";
  Unix.putenv "SOMA_OCAML_BUILD" "0";
  let vo = Filename.concat dir (Filename.remove_extension (Filename.basename file) ^ ".vo") in
  let code, _ = compile (file :: "-o" :: vo :: args) in
  if code = 0 then print_string (In_channel.with_open_bin hashes In_channel.input_all);
  finish code

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
  List.iter (fun l -> if starts_with ~prefix:"Mirage: setting up" l ||
          starts_with ~prefix:"Mirage: checked" l then print_endline l)
    (lines output);
  if code <> 0 then finish code;
  match mirage_command output with
  | Some command ->
    (* the image's tools come from the same opam switch as its build *)
    let switch = match Sys.getenv_opt "SOMA_MIRAGE_SWITCH" with
      | Some s when s <> "" -> s | _ -> "hvf" in
    (* a program that keeps files (Sandbox's read_file, write_file,
       append_file) gets the disk its build names, storage.img in the
       current directory: created zeroed (8 MiB) the first time, and kept,
       so the next run reads what this one wrote *)
    let block = "--block:storage=" in
    List.iter (fun a ->
        if starts_with ~prefix:block a then begin
          let disk = String.sub a (String.length block) (String.length a - String.length block) in
          if not (Sys.file_exists disk) then begin
            let fd = Unix.openfile disk [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL] 0o600 in
            Unix.LargeFile.ftruncate fd (Int64.of_int (8 * 1024 * 1024));
            Unix.close fd;
            Printf.eprintf "soma run: created %s, an empty 8 MiB disk for the program's files.\n%!" disk
          end
        end) command;
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

(* Freshness: [soma build --check-fresh FILE [OPTIONS]] says whether
   [soma build FILE [OPTIONS]] would find FILE as its last successful build
   left it, from metadata alone, without loading a library or the prelude:
   "FILE: unchanged" (exit 0) or "FILE: stale: REASON" (exit 1).

   Each successful [soma build] writes a record into the project's cache,
   .soma-cache/.freshness/ (a folder with a . is no library of the cache):
   the build's configuration (the file, the folder it was built from, its
   options, the environment that soma, rocq and opam read), digests of soma,
   its worker and the libraries installed with them, digests of every file of
   the project (which have its import graph), and then digests of every file
   of the cache, what was compiled, with its stamps. Per-module interface
   digests are also recorded, for observation only. The check computes the
   same but the last part, which it compares file by file. A record is
   written only when what it can say is certain: no dependency outside the
   project (soma.lock, .soma-cache/.deps, Rocq libraries that a dependency
   named), no option that names files elsewhere or writes into FILE.exp, no
   kept output (an image, an executable, a page, built with tools outside
   soma), and the project not changed while it was built. Anything missing,
   unreadable or unexpected is stale. *)

exception Uncertain of string

let uncertain fmt = Printf.ksprintf (fun s -> raise (Uncertain s)) fmt

(* the environment soma was started with, before [init] adds to it *)
let initial_env = Array.to_list (Unix.environment ())

let freshness_format = "soma-freshness 2"
let fingerprint_writes = ref true

let fresh_error path e = uncertain "cannot read %s: %s" path (Unix.error_message e)

let fresh_digest path =
  try Digest.to_hex (Digest.file path)
  with Sys_error e -> uncertain "cannot read %s" e

let fresh_readdir dir =
  match Sys.readdir dir with
  | names -> let names = Array.to_list names in List.sort compare names
  | exception Sys_error e -> uncertain "cannot list %s" e

(* Every file under [dir], [prefix/relative path, digest], following
   symbolic links (an installation's files are), but those named [skip] *)
let fresh_tree ?(skip = []) ~prefix dir =
  let rec walk depth dir rel acc =
    if depth > 64 then uncertain "%s is too deep, or a cycle of links" dir;
    List.fold_left (fun acc name ->
        if List.mem name skip then acc else
        let full = Filename.concat dir name in
        let r = rel ^ "/" ^ name in
        match (Unix.stat full).Unix.st_kind with
        | exception Unix.Unix_error (e, _, _) -> fresh_error full e
        | Unix.S_DIR -> walk (depth + 1) full r acc
        | Unix.S_REG -> (r, fresh_digest full) :: acc
        | _ -> uncertain "%s is not a regular file" full)
      acc (fresh_readdir dir) in
  List.sort compare (walk 0 dir prefix [])

let env_matters entry =
  let name = match String.index_opt entry '=' with
    | Some i -> String.sub entry 0 i | None -> entry in
  not (starts_with ~prefix:"SOMA_TEST_" name) &&
  (List.mem name ["PATH"; "HOME"; "LD_LIBRARY_PATH"; "DYLD_LIBRARY_PATH"] ||
  List.exists (fun prefix -> starts_with ~prefix name)
    ["SOMA_"; "ROCQ"; "COQ"; "OCAML"; "CAML_"; "OPAM"; "DUNE_"; "XDG_"])

let initial_getenv name =
  List.find_map (fun entry ->
      if starts_with ~prefix:(name ^ "=") entry then
        Some (String.sub entry (String.length name + 1) (String.length entry - String.length name - 1))
      else None) initial_env

(* The project of [file]: its canonical path, and its root, the folder of
   the nearest soma.toml above it (vernac/somaProject.ml), or else its own *)
let fresh_project file =
  let canonical = try Unix.realpath file with Unix.Unix_error (e, _, _) -> fresh_error file e in
  let start = Filename.dirname canonical in
  let rec find dir =
    if Sys.file_exists (Filename.concat dir "soma.toml") then dir
    else let up = Filename.dirname dir in if up = dir then start else find up in
  canonical, find start

(* soma, its worker, and the libraries and plugins they load *)
let fresh_toolchain () =
  let env = match Boot.Env.initialized () with
    | Some (Boot.Env.Env env) -> env
    | Some Boot.Env.Boot | None -> uncertain "the location of Rocq's libraries is unknown" in
  let worker_dir =
    try Findlib.package_directory "soma-runtime"
    with Findlib.No_such_package _ | Not_found -> uncertain "the package soma-runtime is not found" in
  let exe = if Sys.(os_type = "Win32" || os_type = "Cygwin") then ".exe" else "" in
  let worker = Filename.concat worker_dir ("rocqworker" ^ exe) in
  let soma_env = Filename.concat (Filename.dirname Sys.executable_name) "coq_environment.txt" in
  let tool name path = Printf.sprintf "tool %s %s %s" name (String.escaped path) (fresh_digest path) in
  let tree label dir =
    let snapshot = try SomaMerkle.scan ~write:!fingerprint_writes dir with
      | Failure reason -> uncertain "%s" reason in
    [Printf.sprintf "library %s sha256:%s" label snapshot.SomaMerkle.digest] in
  [ tool "soma" Sys.executable_name; tool "worker" worker ] @
  (if Sys.file_exists soma_env then [ tool "environment" soma_env ] else []) @
  [ "coqlib " ^ String.escaped (Boot.Env.Path.to_string (Boot.Env.coqlib env));
    "runtimelib " ^ String.escaped (Boot.Env.Path.to_string (Boot.Env.runtimelib env)) ] @
  tree "coqlib" (Boot.Env.Path.to_string (Boot.Env.coqlib env)) @
  tree "runtimelib" (Boot.Env.Path.to_string (Boot.Env.runtimelib env))

let () =
  let identity = lazy (SomaMerkle.string (String.concat "\n" (fresh_toolchain ()))) in
  cache_toolchain := (fun () ->
    let id = Lazy.force identity in
    Unix.putenv "SOMA_CACHE_ID" id;
    id)

(* --no-image is consumed before compiler arguments are formed, and its
   environment override is absent from initial_env. Keep it in the record
   so an image build and a check cannot reuse each other's freshness. *)
type fresh_config = { verbose : bool; fill : bool; timings : bool; no_image : bool; file : string; args : string list }

(* What a build of [c] reads of its project, and how it was asked for; with
   [~toolchain], of soma's installation too *)
let fresh_inputs ~toolchain c =
  let canonical, root = fresh_project c.file in
  let cache = Filename.concat root ".soma-cache" in
  if c.fill then uncertain "--fill writes into the program's .exp";
  let rec allowed = function
    | [] -> ()
    | "-w" :: _ :: rest -> allowed rest
    | a :: _ -> uncertain "the option %s may name files outside the project" a in
  allowed c.args;
  List.iter (fun v -> match initial_getenv v with
      | Some s when s <> "" -> uncertain "%s is set" v
      | _ -> ()) ["SOMA_PROJECT_ROOT"; "SOMA_PROJECT_CACHE"; "SOMA_BUILD_ROOT"; "ROCQPATH"; "COQPATH"];
  List.iter (fun f -> if Sys.file_exists f then
                uncertain "%s: the project has dependencies outside its folder" f)
    [Filename.concat root "soma.lock"; Filename.concat cache ".deps"; Filename.concat cache "load-paths"];
  let cwd = try Sys.getcwd () with Sys_error e -> uncertain "cannot read the current folder: %s" e in
  let config =
    [ freshness_format;
      "file " ^ String.escaped c.file;
      "canonical " ^ String.escaped canonical;
      "root " ^ String.escaped root;
      "cwd " ^ String.escaped cwd;
      Printf.sprintf "flags verbose=%b timings=%b no_image=%b" c.verbose c.timings c.no_image ] @
    List.map (fun a -> "arg " ^ String.escaped a) c.args @
    List.map (fun e -> "env " ^ String.escaped e) (List.sort compare (List.filter env_matters initial_env)) in
  let sources = List.map (fun (r, d) -> Printf.sprintf "source %s %s" (String.escaped r) d)
      (fresh_tree ~skip:[".soma-cache"; ".git"] ~prefix:"." root) in
  root, cache, config @ (if toolchain then fresh_toolchain () else []) @ sources

let freshness_record cache canonical =
  Filename.concat (Filename.concat cache ".freshness") (Digest.to_hex (Digest.string canonical))

let fresh_outputs cache =
  if not (is_directory_opt cache) then uncertain "%s does not exist" cache;
  List.map (fun (r, d) -> Printf.sprintf "output %s %s" (String.escaped r) d)
    (fresh_tree ~skip:[".freshness"; ".interfaces"; ".tests"] ~prefix:"." cache)

(* Before a build: its record is no longer that of the last successful
   build. What the project is, to compare with after it. *)
let forget_freshness c =
  try
    let canonical, root = fresh_project c.file in
    let record = freshness_record (Filename.concat root ".soma-cache") canonical in
    (try Sys.remove record with Sys_error _ -> ());
    if Sys.file_exists record then None else Some (fresh_inputs ~toolchain:false c)
  with Uncertain _ | Sys_error _ | Unix.Unix_error _ -> None

(* After a successful build [c]: its record, when it is certain. [before] is
   what [forget_freshness] saw, and [kept] the outputs the build kept. *)
let record_freshness c before ~kept =
  match before with
  | None -> ()
  | Some (_, _, before_lines) ->
    try
      if kept <> [] then uncertain "the build kept outputs";
      let _, cache, during = fresh_inputs ~toolchain:false c in
      if during <> before_lines then uncertain "the project changed during the build";
      let _, _, inputs = fresh_inputs ~toolchain:true c in
      let outputs = fresh_outputs cache in
      let dir = Filename.concat cache ".interfaces" in
      let interfaces = if not (is_directory_opt dir) then [] else
        List.map (fun name -> String.trim (In_channel.with_open_bin
            (Filename.concat dir name) In_channel.input_all)) (fresh_readdir dir) in
      let canonical, _ = fresh_project c.file in
      let record = freshness_record cache canonical in
      mkdir_p (Filename.dirname record);
      let tmp = record ^ ".tmp" in
      Out_channel.with_open_bin tmp (fun oc ->
          List.iter (fun l -> output_string oc (l ^ "\n")) (inputs @ outputs @ interfaces));
      Sys.rename tmp record;
      SomaCache.record record
    with Uncertain _ | Sys_error _ | Unix.Unix_error _ -> ()

(* [Ok ()] when unchanged, or why not *)
let freshness_verdict c =
    try
      ignore (!cache_toolchain ());
      let canonical, root = fresh_project c.file in
      let record = freshness_record (Filename.concat root ".soma-cache") canonical in
      let recorded =
        try List.filter (( <> ) "") (lines (In_channel.with_open_bin record In_channel.input_all))
        with Sys_error _ -> uncertain "no record of a successful build" in
      (match recorded with
       | first :: _ when first = freshness_format -> ()
       | _ -> uncertain "the record of the last build is of another format");
      if not (SomaCache.trusted record) then uncertain "no record of a successful build";
      (* Interface digests do not participate in freshness or import stamps. *)
      let is_output l = starts_with ~prefix:"output " l in
      let recorded_inputs = List.filter (fun l -> not (is_output l || starts_with ~prefix:"interface " l)) recorded in
      let recorded_outputs = List.filter is_output recorded in
      let _, cache, inputs = fresh_inputs ~toolchain:true c in
      if inputs <> recorded_inputs then begin
        let kind l = match String.index_opt l ' ' with Some i -> String.sub l 0 i | None -> l in
        let name l = match String.split_on_char ' ' l with _ :: n :: _ -> n | _ -> l in
        let changed = List.filter (fun l -> not (List.mem l recorded_inputs)) inputs
                      @ List.filter (fun l -> not (List.mem l inputs)) recorded_inputs in
        match changed with
        | l :: _ when List.mem (kind l) ["source"; "library"; "tool"] ->
          uncertain "%s %s changed" (kind l) (name l)
        | _ -> uncertain "the build configuration changed"
      end;
      if recorded_outputs = [] then uncertain "no compiled output recorded";
      List.iter (fun l ->
          match String.split_on_char ' ' l with
          | ["output"; r; d] ->
            let path = Filename.concat cache (Scanf.unescaped r) in
            if not (Sys.file_exists path) then uncertain "compiled output %s is missing" r;
            if fresh_digest path <> d then uncertain "compiled output %s changed" r
          | _ -> uncertain "the record of the last build is unreadable") recorded_outputs;
      List.iter (fun l -> match String.split_on_char ' ' l with
          | ["output"; r; _] ->
            let path = Filename.concat cache (Scanf.unescaped r) in
            if List.exists (Filename.check_suffix path) [".vo"; ".stamp"] &&
               not (SomaCache.trusted path) then uncertain "compiled output %s has no provenance" r
          | _ -> ()) recorded_outputs;
      Ok ()
    with
    | Uncertain reason -> Error reason
    | Sys_error e -> Error e
    | Unix.Unix_error (e, _, _) -> Error (Unix.error_message e)
    | Scanf.Scan_failure _ | Failure _ | End_of_file -> Error "the record of the last build is unreadable"

(* "unchanged", or why not *)
let check_freshness c =
  match freshness_verdict c with
  | Ok () -> Printf.printf "%s: unchanged\n%!" c.file; exit 0
  | Error reason -> Printf.printf "%s: stale: %s\n%!" c.file reason; exit 1

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
  if command = "build" || command = "compile" then
    print_endline "  --no-module-cache      Do not read or write the shared module store";
  if command = "build" then print_endline "  --timings              Print module times, total time and peak heap memory";
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
  | "test" :: [arg] when is_help arg -> print_string SomaTest.help
  | "test" :: args ->
    if List.exists (fun a -> a = "--listTests" || a = "--list-tests") args then
      fingerprint_writes := false;
    let initialized = ref false in
    let initialize () = if not !initialized then begin
        let opts, _ = parse_opts [] in
        init opts [];
        initialized := true
      end in
    let identity no_image =
      initialize ();
      let env = List.filter env_matters initial_env |> List.sort String.compare in
      Digest.to_hex (Digest.string (String.concat "\n"
          ((!cache_toolchain) () :: string_of_bool no_image :: env))) in
    let build_test ~source ~trace ~no_image =
      let prog = Sys.executable_name in
      let args = prog :: "build" :: source :: (if no_image then ["--no-image"] else []) in
      let env = Array.to_list (Unix.environment ()) |> List.filter (fun entry ->
          not (starts_with ~prefix:"SOMA_TEST_SOURCE=" entry ||
               starts_with ~prefix:"SOMA_TEST_DEPENDENCIES=" entry)) in
      let env = Array.of_list (("SOMA_TEST_SOURCE=" ^ source) ::
          ("SOMA_TEST_DEPENDENCIES=" ^ trace) :: env) in
      pass_signals ();
      let pid = Unix.create_process_env prog (Array.of_list args) env Unix.stdin Unix.stdout Unix.stderr in
      child := Some pid;
      let status = wait pid in
      child := None;
      exit_code status in
    (try SomaTest.run ~identity ~build:build_test args with
     | SomaTest.Error reason -> Printf.eprintf "soma test: %s\n%!" reason; exit 2
     | SomaTest.Test_failure code -> exit code
     | Sys_error reason -> Printf.eprintf "soma test: %s\n%!" reason; exit 2
     | Unix.Unix_error (e, call, path) ->
       Printf.eprintf "soma test: %s %s: %s\n%!" call path (Unix.error_message e); exit 2)
  | ("build" | "compile" | "run" as command) :: rest when List.exists is_help (before_image_args rest) ->
    options_help command
  | "repl" :: args -> repl args
  | ("get" | "diff" | "search" as command) :: args ->
    let opts, _ = parse_opts [] in
    let () = init opts [] in
    let prog = get_worker_path { package = "soma-runtime"; basename = "rocqworker" } in
    let pid = Unix.create_process prog (Array.of_list (prog :: ("--kind=" ^ command) :: args))
        Unix.stdin Unix.stdout Unix.stderr in
    exit (exit_code (wait pid))
  | ("build" | "compile" as command) :: rest ->
    (* -v is soma's (rocq c's -v prints its version), before or after FILE *)
    let is_verbose a = a = "-v" || a = "--verbose" in
    let no_image = List.mem "--no-image" rest in
    if no_image then Unix.putenv "SOMA_MIRAGE_NO_IMAGE" "1";
    let rest = List.filter ((<>) "--no-image") rest in
    let no_module_cache = List.mem "--no-module-cache" rest in
    let rest = List.filter ((<>) "--no-module-cache") rest in
    let is_fill a = a = "--fill" || a = "-fill" in
    let verbose = List.exists is_verbose rest in
    let fill = List.exists is_fill rest in
    let check_fresh = command = "build" && List.mem "--check-fresh" rest in
    let rest = if check_fresh then List.filter ((<>) "--check-fresh") rest else rest in
    let timings = command = "build" && List.mem "--timings" rest in
    let rest = if timings then List.filter ((<>) "--timings") rest else rest in
    let rest = if timings && rest = [] then ["main.soma"] else rest in
    begin match List.filter (fun a -> not (is_verbose a || is_fill a)) rest with
      | [] -> usage_error "soma %s: no file given" command
      | file :: args ->
        let config = { verbose; fill; timings; no_image; file = program_of file; args } in
        let opts, args = parse_opts args in
        let () = init opts (file :: args) in
        if check_fresh then check_freshness config;
        (* the record of a successful soma build, for --check-fresh *)
        let record = command = "build" in
        (* a build that would find FILE as its last successful build left
           it has nothing to do: it ends here, before rocq c loads a library
           or the prelude. With -v, the values of bare terms are to be
           printed again, which only the build does. *)
        if record && not verbose && Sys.getenv_opt "SOMA_TEST_DEPENDENCIES" = None then begin
          let start = Unix.gettimeofday () in
          match (try freshness_verdict config with _ -> Error "") with
          | Ok () ->
            (* said, so that a caller can tell a build with nothing to do
               from one that printed nothing (a check that greps for
               what the build says otherwise fails the second time) *)
            Printf.printf "%s: unchanged since its last build\n%!" config.file;
            if timings then
              Printf.printf "Total: %.3f s\t%d KiB peak heap memory\n%!"
                (Unix.gettimeofday () -. start) 0;
            exit 0
          | Error _ -> ()
        end;
        let dir = output_dir (program_of file) args in
        let before_build = if record then modification_times dir else [] in
        let before = if record then forget_freshness config else None in
        build ~review:(command = "compile") ~timings ~share:(not no_module_cache) ~verbose ~fill (program_of file) args;
        if record then
          record_freshness config before ~kept:(created ~before:before_build ~source:(program_of file) dir)
    end
  | "extract" :: rest ->
    begin match rest with
      | [] -> usage_error "soma extract: no file given"
      | file :: args ->
        let opts, args = parse_opts args in
        let () = init opts (file :: args) in
        extract (program_of file) args
    end
  | "hash" :: rest ->
    begin match rest with
      | [] -> usage_error "soma hash: no file given"
      | file :: args ->
        let opts, args = parse_opts args in
        let () = init opts (file :: args) in
        hash (program_of file) args
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
