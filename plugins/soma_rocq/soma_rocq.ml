(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: Rocq libraries, [Rocq Library "rocq-stdpp".] (theories/Soma/Soma.v
   loads this plugin in every Soma program).

   A Rocq library is Rocq: Soma takes it as it is, with no definition and
   nothing translated. Its terms are Soma's, which the kernel checks,
   evaluation computes, and proofs go through. What Soma cannot take is
   a library compiled by another Rocq: the kernel of Soma, gradual, is not
   theirs, so the compiled files of opam's packages do not load. So a
   library is compiled from its source by Soma itself, once, into the
   project's cache, [.soma-cache/rocq], in a directory named after the
   package, its version, and Soma's own Corelib, whose change makes what
   was compiled with it inconsistent.

   The source is opam's: [opam source] of the package, from the
   repository of Rocq's packages (coq-released), which Soma adds to its
   own switch (SomaOpam). [Rocq Library "lib" in "DIR".] takes it from a
   directory instead, relative to the file. The theories of a source are
   those its dune files declare, [(rocq.theory (name stdpp) (package
   rocq-stdpp))], of the package, or else the -Q and -R of its
   _RocqProject or _CoqProject. They are compiled in the order [rocq dep]
   gives, by Soma's [rocq c], as Rocq: without Soma's prelude, and so
   without gradual typing; nothing else of the source runs (its scripts
   and Makefiles do not). A library that loads an OCaml plugin is refused:
   a plugin would have to be built against Soma. A library's own
   dependencies are libraries too, each named by a [Rocq Library] before
   it.

   Once compiled, the theories are in the load path, under their names:
   [From stdpp Require Import gmap.] *)

open Pp

let error msg = CErrors.user_err (str "Rocq Library: " ++ msg)

(* in the project's cache: what a project uses stays in it *)
let cache () = Filename.concat (SomaImport.project_cache ()) "rocq"

let read_file f = In_channel.with_open_bin f In_channel.input_all

let contains s sub =
  let n = String.length sub in
  let rec at i = i + n <= String.length s && (String.sub s i n = sub || at (i + 1)) in
  at 0

(* the first index of [sub] in [s] from [from] *)
let index_from s from sub =
  let n = String.length sub in
  let rec at i = if i + n > String.length s then None else if String.sub s i n = sub then Some i else at (i + 1) in
  at from

(* The driver's complete toolchain identity includes compiler and plugins.
   Raw rocq invocations fall back to the worker and prelude bytes. Never
   truncate this identity: a Corelib-only key misses compiler upgrades. *)
let soma_key () =
  let lib path = Names.DirPath.make (List.rev_map Names.Id.of_string path) in
  match List.find_map (fun p -> match Loadpath.locate_absolute_library (lib p) with
      | Ok f -> Some f | Error _ -> None) [["Soma"; "Soma"]; ["Corelib"; "Init"; "Prelude"]] with
  | Some f -> SomaMerkle.string
      ("soma-rocq-toolchain 3\000" ^ SomaCache.identity () ^ "\000" ^ SomaMerkle.file_hash f)
  | None -> error (str "Soma's Corelib is not found.")

(* * The theories of a source *)

type theory = {
  dir : string;           (* absolute *)
  logical : string;       (* stdpp *)
  subdirs : bool;         (* its subdirectories are its too (include_subdirs) *)
}

let rec files_under dir =
  match Sys.readdir dir with
  | exception Sys_error _ -> []
  | entries ->
    Array.to_list entries |> List.sort compare |> List.concat_map (fun e ->
        let f = Filename.concat dir e in
        if e = "_build" || e = "_opam" || (e <> "" && e.[0] = '.') then []
        else if Sys.is_directory f then files_under f
        else [f])

(* Precisely the source files copied into a Rocq library build. Ignore
   local .vo/build products so compiling a checkout does not change its key. *)
let is_source_file file =
  Filename.check_suffix file ".v" ||
  List.mem (Filename.basename file) ["dune"; "_RocqProject"; "_CoqProject"]

let source_files root = List.filter is_source_file (files_under root)

let source_key root =
  let root = Unix.realpath root in
  let prefix = root ^ "/" in
  let rows = source_files root |> List.map (fun f ->
      let relative = String.sub f (String.length prefix) (String.length f - String.length prefix) in
      Printf.sprintf "%S %s" relative (SomaMerkle.file_hash f)) in
  SomaMerkle.string ("soma-rocq-source 2\n" ^ String.concat "\n" rows)

(* the word after [key] in the s-expression [s] from [from]: [(name stdpp)] *)
let field s from key =
  match index_from s from ("(" ^ key) with
  | None -> None
  | Some i ->
    let j = ref (i + String.length key + 1) in
    while !j < String.length s && (s.[!j] = ' ' || s.[!j] = '\n' || s.[!j] = '\t') do incr j done;
    let k = ref !j in
    while !k < String.length s && not (List.mem s.[!k] [' '; ')'; '\n'; '\t']) do incr k done;
    if !k > !j then Some (String.sub s !j (!k - !j)) else None

(* [(rocq.theory ...)] or [(coq.theory ...)] stanzas of a dune file, of the
   package (or of no package) *)
let dune_theories ~package file =
  let s = read_file file in
  let dir = Filename.dirname file in
  let subdirs = contains s "(include_subdirs qualified)" || contains s "(include_subdirs unqualified)" in
  let rec stanzas from acc =
    let next = List.filter_map (fun k -> index_from s from k) ["(rocq.theory"; "(coq.theory"] in
    match List.sort compare next with
    | [] -> List.rev acc
    | i :: _ ->
      let ends = Option.default (String.length s)
          (List.fold_left (fun m k -> match index_from s (i + 1) k with
               | Some j -> Some (match m with Some m -> min m j | None -> j)
               | None -> m) None ["(rocq.theory"; "(coq.theory"]) in
      let stanza = String.sub s i (ends - i) in
      let acc = match field stanza 0 "name", field stanza 0 "package" with
        | Some name, (None | Some _ as p) when p = None || p = Some package ->
          { dir; logical = name; subdirs } :: acc
        | _ -> acc in
      stanzas (i + 1) acc
  in
  stanzas 0 []

(* -Q DIR NAME and -R DIR NAME of a _RocqProject or _CoqProject *)
let project_theories root file =
  let words = List.concat_map (fun l -> List.filter (( <> ) "") (String.split_on_char ' ' l))
      (List.filter (fun l -> l <> "" && l.[0] <> '#') (String.split_on_char '\n' (read_file file))) in
  let rec go acc = function
    | ("-Q" | "-R") :: d :: name :: rest ->
      let d = if d = "." then root else Filename.concat root d in
      go ({ dir = d; logical = name; subdirs = true } :: acc) rest
    | _ :: rest -> go acc rest
    | [] -> List.rev acc in
  go [] words

let theories ~package root =
  let files = files_under root in
  match List.concat_map (dune_theories ~package)
          (List.filter (fun f -> Filename.basename f = "dune") files) with
  | _ :: _ as ts -> ts
  | [] ->
    match List.find_opt Sys.file_exists
            [Filename.concat root "_RocqProject"; Filename.concat root "_CoqProject"] with
    | Some f -> project_theories root f
    | None -> []

let sources t =
  List.filter (fun f -> Filename.check_suffix f ".v")
    (if t.subdirs then files_under t.dir
     else List.filter (fun f -> not (Sys.is_directory f))
         (List.map (Filename.concat t.dir) (List.sort compare (Array.to_list (Sys.readdir t.dir)))))

(* * Compiling *)

(* Soma's [rocq], for [rocq dep]. A developer build names the binary
   [rocq.exe] beside this worker ([topbin/rocqworker.exe]). An installation
   puts the worker in [lib/soma-runtime] and [rocq] in [bin], two directories
   above it. [Sys.executable_name] follows the symlink of dune's install
   directory, so that [bin] is also tried from the directory the worker was
   invoked as ([Boot.Env.rocqbin]), which does not. *)
let rocq_binary () =
  let worker_dir = Filename.dirname Sys.executable_name in
  let install_bin dir =
    List.fold_left Filename.concat dir
      [Filename.parent_dir_name; Filename.parent_dir_name; "bin"; "rocq"]
  in
  (* dune's native binary is [rocq.exe]; an installation's is [rocq], or
     [rocq.exe] on Windows *)
  let with_exe base = [base; base ^ ".exe"] in
  let candidates = List.concat_map with_exe [
    Filename.concat Boot.Env.rocqbin "rocq";
    Filename.concat worker_dir "rocq";
    install_bin worker_dir;
    install_bin Boot.Env.rocqbin;
  ] in
  match List.find_opt Sys.file_exists candidates with
  | Some r -> r
  | None -> error (str "Soma's rocq is not found (looked for " ++ str (String.concat ", " candidates) ++ str ").")

(* the environment of a compilation: none of Soma's own variables, which
   are about the program *)
let clean_env () =
  Array.of_list (List.filter (fun v -> not (String.starts_with ~prefix:"SOMA_" v)
                                       (* a library a dependency names is compiled as a dependency *)
                                       || String.starts_with ~prefix:(SomaImport.prefix_var ^ "=") v)
                   (Array.to_list (Unix.environment ())))

let wait pid =
  let rec go () = try snd (Unix.waitpid [] pid) with Unix.Unix_error (Unix.EINTR, _, _) -> go () in
  match go () with Unix.WEXITED 0 -> true | _ -> false

(* [args] run in [dir] (what they write there, lia's cache, stays with the
   library), their output in [out] *)
let run_to ?(env = []) ~dir ~out args =
  let fd = Unix.openfile out [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o644 in
  let here = Sys.getcwd () in
  Sys.chdir dir;
  let env = Array.append (clean_env ()) (Array.of_list env) in
  let pid = Fun.protect ~finally:(fun () -> Sys.chdir here)
      (fun () -> Unix.create_process_env (List.hd args) (Array.of_list args) env Unix.stdin fd fd) in
  Unix.close fd;
  wait pid

let load_args ts =
  List.concat_map (fun t -> ["-Q"; t.dir; t.logical]) ts

(* rocq dep -sort writes raw filenames separated by spaces, not shell
   quoting and not one record per line (tools/coqdep/lib/common.ml). Match
   complete filenames from its input set rather than splitting their bytes.
   If two input names make the stream ambiguous, refuse rather than compile
   a silently truncated or invented path. *)
let dependency_order files text =
  let files = List.sort_uniq String.compare files in
  let length = String.length text in
  let space = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false in
  let rec skip i = if i < length && space text.[i] then skip (i + 1) else i in
  let seen = Hashtbl.create 31 in
  let rec parse i acc =
    let i = skip i in
    if i = length then List.rev acc else
    let candidates = List.filter (fun file ->
        let n = String.length file in
        i + n <= length && String.sub text i n = file &&
        (i + n = length || space text.[i + n])) files in
    match candidates with
    | [file] when not (Hashtbl.mem seen file) ->
      Hashtbl.add seen file ();
      parse (i + String.length file) (file :: acc)
    | _ ->
      error (str "rocq dep -sort returned an unknown, repeated or ambiguous filename near " ++
             qstring (String.sub text i (min 120 (length - i))) ++
             str "; filenames are matched against the library's source files.") in
  parse 0 []

(* [ts] compiled by Soma, in dependency order *)
let compile ~name ~log ts =
  let files = List.concat_map sources ts in
  if files = [] then error (str name ++ str " has no Rocq file in its theories.");
  let order = Filename.concat (Filename.dirname log) "order" in
  let dir = Filename.dirname log in
  if not (run_to ~dir ~out:order ([rocq_binary (); "dep"; "-sort"] @ load_args ts @ files)) then
    error (str "rocq dep failed on " ++ str name ++ str "; the end of " ++ str order ++ str ":" ++ fnl () ++
           str (SomaOpam.tail_of_file order));
  let order = dependency_order files (read_file order) in
  let total = List.length order in
  List.iteri (fun i f ->
      let rel = match List.find_opt (fun t -> String.starts_with ~prefix:(t.dir ^ "/") f) ts with
        | Some t -> t.logical ^ "/" ^ String.sub f (String.length t.dir + 1) (String.length f - String.length t.dir - 1)
        | None -> f in
      Printf.eprintf "Rocq: compiling %s: %d/%d %s\n%!" name (i + 1) total rel;
      (* a Rocq library is Rocq: compiled as Rocq does, without Soma's
         prelude, whose names ([R], the reals) and gradual typing it does
         not expect *)
      (* a plugin would have to be built against Soma: the compilation
         refuses the parsed [Declare ML Module] (SomaImport), before it
         loads anything, however it is spaced or commented *)
      let env = [SomaImport.rocq_library_var ^ "=" ^ name] in
      if not (run_to ~env ~dir ~out:log ([Boot.Env.self; "--kind=compile"; "-q"; "-no-soma-prelude"] @ load_args ts @ [f])) then
        error (str "Soma could not compile " ++ str rel ++ str ", of " ++ str name ++ str "; the end of " ++
               str log ++ str ":" ++ fnl () ++ str (SomaOpam.tail_of_file log)))
    order

(* * The source *)

let rec copy_tree src dst =
  SomaOpam.mkdir_p dst;
  Array.iter (fun e ->
      let s = Filename.concat src e and d = Filename.concat dst e in
      if e = "_build" || e = "_opam" || (e <> "" && e.[0] = '.') then ()
      else if Sys.is_directory s then copy_tree s d
      else if is_source_file e then
        Out_channel.with_open_bin d (fun oc -> output_string oc (read_file s)))
    (Sys.readdir src)

let coq_released = "https://rocq-prover.org/opam/released"

(* the repository of Rocq's packages, in Soma's switch *)
let ensure_repository ~switch ~log =
  let listed = Filename.concat (Filename.dirname log) "repositories" in
  ignore (SomaOpam.run ~log:listed ["opam"; "repo"; "list"; "--switch=" ^ switch; "--short"]);
  if not (List.mem "coq-released" (SomaOpam.read_lines listed)) then begin
    Printf.eprintf "Rocq: adding opam's repository of Rocq's packages to the switch %s (once)\n%!" switch;
    if not (SomaOpam.run ~log ["opam"; "repo"; "add"; "coq-released"; coq_released;
                               "--switch=" ^ switch; "--this-switch"; "-y"]) then
      error (str "adding the repository " ++ str coq_released ++ str " failed; the end of " ++ str log ++
             str ":" ++ fnl () ++ str (SomaOpam.tail_of_file log))
  end

(* the version of [package] that opam's repositories have last *)
let latest ~switch ~log package =
  let out = Filename.concat (Filename.dirname log) "versions" in
  if not (SomaOpam.run ~log:out ["opam"; "show"; "--switch=" ^ switch; package; "--field=all-versions"]) then
    error (str "opam knows no package " ++ str package ++ str " (" ++ str (SomaOpam.tail_of_file ~lines:3 out) ++
           str "): Rocq's packages are named as in " ++ str coq_released ++ str ".");
  match List.rev (List.concat_map (fun l -> List.filter (( <> ) "") (String.split_on_char ' ' l))
                    (SomaOpam.read_lines out)) with
  | v :: _ -> v
  | [] -> error (str "opam has no version of " ++ str package ++ str ".")

type source = Opam of string option | Local of string

(* A package and a version each become one directory name under the cache
   and, for an opam library, one argument of [opam]. Only a single safe
   path component is accepted: [../] would leave the cache, and a leading
   [-] would be an option to opam. *)
let safe_component s =
  let n = String.length s in
  if n = 0 || s = "." || s = ".." || s.[0] = '-' then false
  else
    let rec loop i =
      if i = n then true
      else
        match s.[i] with
        | 'a'..'z' | 'A'..'Z' | '0'..'9' | '.' | '_' | '+' | '~' | '-' -> loop (i + 1)
        | _ -> false
    in
    loop 0

let require_component kind s =
  if not (safe_component s) then
    error (str kind ++ str " " ++ qstring s ++ str " is not one safe path component.")

(* * One compilation of one library at a time *)

(* A library compiles into a directory of the cache that a compilation
   removes and makes again, so the lock that says who compiles it is beside
   it: [DIR.lock], in the cache, which is never removed. Without it, the two
   compilations of one library that [Import left right.] starts (each a
   process of its own) both find no [theories], both remove the directory,
   and one takes the other's [order] and sources away. A lock (lockf) is a
   process's: the system releases it when the process ends, however it ends,
   and [with_lock] releases it on an error too. *)
let lock_file root name = Filename.concat root (name ^ ".lock")

(* The locks this process holds: lockf grants one it holds again, and
   closing either fd releases it, so a nested [with_lock] of the same
   library runs under the lock its caller holds instead of taking it again *)
let locks_held : (string, unit) Hashtbl.t = Hashtbl.create 7

let with_lock file f =
  if Hashtbl.mem locks_held file then f () else begin
    let fd = Unix.openfile file [Unix.O_RDWR; Unix.O_CREAT; Unix.O_CLOEXEC] 0o644 in
    Fun.protect ~finally:(fun () ->
        Hashtbl.remove locks_held file;
        Unix.close fd) (fun () ->
        let rec lock () =
          match Unix.lockf fd Unix.F_LOCK 0 with
          | () -> ()
          | exception Unix.Unix_error (Unix.EINTR, _, _) -> lock () in
        lock ();
        Hashtbl.replace locks_held file ();
        f ())
  end

(* What a compiled library's [theories] says: its theories, in the order it
   compiled them. None when the compilation did not finish: the file is
   written last, and renamed into place, so a partial one is no [theories]. *)
let compiled_theories ~key directory =
  match SomaRocqCache.load ~key ~directory ~resolve_input:SomaImport.resolve_project_file with
  | Some entry -> Some entry.SomaRocqCache.theories
  | None -> None

(* [package], compiled: its theories, from [cache ()] or else compiled now *)
let ensure ~package source =
  (match source with
   | Opam None -> SomaImport.note_uncertified_rocq_library ()
   | Local path when not (SomaImport.rocq_source_in_project path) ->
     (* File hashes cannot observe added .v/dune/configuration files in an
        external source tree. Until tree traces exist, keep it uncertified. *)
     SomaImport.note_uncertified_rocq_library ()
   | _ -> ());
  (* before a cache directory is created or removed, and before opam *)
  require_component "package" package;
  (match source with Opam (Some version) -> require_component "version" version | Opam None | Local _ -> ());
  let root = cache () in
  SomaOpam.mkdir_p root;
  let key = soma_key () in
  let dir, fetch, local_key = match source with
    | Local path ->
      if not (Sys.file_exists path && Sys.is_directory path) then
        error (str path ++ str ", where " ++ str package ++ str " is said to be, is no directory.");
      (* its sources are part of its name: a change compiles it again *)
      let digest = source_key path in
      Filename.concat root (package ^ "-local-" ^ SomaMerkle.string (digest ^ "\000" ^ key)),
      (fun src -> copy_tree path src), Some digest
    | Opam version ->
      let log = Filename.concat root "opam.log" in
      let switch = SomaOpam.ensure_switch ~who:"Rocq" ~log in
      ensure_repository ~switch ~log;
      let version = match version with
        | Some v -> v
        | None ->
          let v = latest ~switch ~log package in
          require_component "version" v;
          v
      in
      Filename.concat root (package ^ "." ^ version ^ "-" ^ key),
      (fun src ->
         Printf.eprintf "Rocq: fetching %s %s (opam source)\n%!" package version;
         if not (SomaOpam.run ~log ["opam"; "source"; "--switch=" ^ switch; package ^ "." ^ version; "--dir=" ^ src])
         then error (str "opam source " ++ str package ++ str "." ++ str version ++ str " failed; the end of " ++
                     str log ++ str ":" ++ fnl () ++ str (SomaOpam.tail_of_file log))), None
  in
  let name = Filename.basename dir in
  let done_file = Filename.concat dir "theories" in
  let src = Filename.concat dir "src" in
  (* The lock is taken before the directory is looked at, and held until
     what it holds is published: what another compilation of the same
     library did while this one waited for it is then seen, not undone. The
     lock of another library is another file, so libraries whose keys differ
     still compile at the same time. *)
  with_lock (lock_file root name) (fun () ->
      match compiled_theories ~key:name dir with
      | Some ts -> ts
      | None ->
        (* Never delete a completed entry a build/REPL may still be using.
           Altered/untrusted completed entries fail closed; only unpublished
           partial compilations may be cleaned under this entry's lock. *)
        let exists path =
          try ignore (Unix.lstat path); true with
          | Unix.Unix_error (Unix.ENOENT, _, _) -> false in
        if exists done_file || exists (Filename.concat dir SomaRocqCache.marker) then
          error (str "the completed Rocq library cache entry " ++ qstring dir ++
                 str " has changed or lacks compiler provenance; use a clean project cache.");
        if Sys.file_exists dir then ignore (Sys.command (Filename.quote_command "rm" ["-rf"; dir]));
        SomaOpam.mkdir_p dir;
        fetch src;
        let ts = theories ~package src in
        if ts = [] then
          error (str package ++ str " declares no theory: no dune file has a (rocq.theory ...) of the package," ++
                 spc () ++ str "and there is no _RocqProject or _CoqProject.");
        let snapshot = SomaRocqCache.source_snapshot ~directory:dir in
        compile ~name ~log:(Filename.concat dir "compile.log") ts;
        (match source, local_key with
         | Local path, Some expected when source_key src <> expected || source_key path <> expected ->
           error (str "the local library's sources changed while it was compiled; build again.")
         | _ -> ());
        let input_files = List.map (fun (relative, digest) ->
            let prefix = "src/" in
            if not (String.starts_with ~prefix relative) then
              error (str "a Rocq library source is outside its copied source tree.");
            let relative = String.sub relative (String.length prefix) (String.length relative - String.length prefix) in
            let root = match source with Local path -> Unix.realpath path | Opam _ -> src in
            Filename.concat root relative, digest) snapshot in
        (* Coverage describes the compiled snapshot. Selection policy (a
           floating version or external tree) is attached to this use above. *)
        SomaImport.record_rocq_inputs ~directory:dir ~complete:true input_files;
        SomaRocqCache.publish ~key:name ~directory:dir ~sources:snapshot
          ~theories:(List.map (fun t -> t.logical, t.dir) ts);
        (* Completed entries stay immutable and are kept until the project
           cache is explicitly removed. A build or REPL can still be loading
           a different key after its compilation lock has been released, so
           even taking that key's lock would not make its deletion safe. *)
        List.map (fun t -> (t.logical, t.dir)) ts)

(* [Rocq Library "package".]: in the load path, compiled if need be *)
let library package source =
  let source = match source with
    | Local path when Filename.is_relative path ->
      (* relative to the file that names it *)
      let base = match !SomaImport.source_file with
        | Some f -> Filename.dirname f
        | None -> Sys.getcwd () in
      Local (if Filename.is_relative base then Filename.concat (Sys.getcwd ()) (Filename.concat base path)
             else Filename.concat base path)
    | s -> s in
  List.iter (fun (logical, dir) ->
      SomaImport.record_load_path logical dir;
      Loadpath.add_vo_path { Loadpath.unix_path = dir; coq_path = Libnames.dirpath_of_string logical;
                             implicit = false; recursive = true; installed = false })
    (ensure ~package source)
