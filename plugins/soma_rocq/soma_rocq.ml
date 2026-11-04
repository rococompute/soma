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

(* What the compiled files depend on: Soma's Corelib and Stdlib, as
   compiled, which the compiled prelude, Soma.Soma, has the digests of *)
let soma_key () =
  let lib path = Names.DirPath.make (List.rev_map Names.Id.of_string path) in
  match List.find_map (fun p -> match Loadpath.locate_absolute_library (lib p) with
      | Ok f -> Some f | Error _ -> None) [["Soma"; "Soma"]; ["Corelib"; "Init"; "Prelude"]] with
  | Some f -> String.sub (Digest.to_hex (Digest.file f)) 0 8
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
let run_to ~dir ~out args =
  let fd = Unix.openfile out [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o644 in
  let here = Sys.getcwd () in
  Sys.chdir dir;
  let pid = Fun.protect ~finally:(fun () -> Sys.chdir here)
      (fun () -> Unix.create_process_env (List.hd args) (Array.of_list args) (clean_env ()) Unix.stdin fd fd) in
  Unix.close fd;
  wait pid

let load_args ts =
  List.concat_map (fun t -> ["-Q"; t.dir; t.logical]) ts

(* [ts] compiled by Soma, in dependency order *)
let compile ~name ~log ts =
  let files = List.concat_map sources ts in
  if files = [] then error (str name ++ str " has no Rocq file in its theories.");
  List.iter (fun f ->
      if contains (read_file f) "Declare ML Module" then
        error (str name ++ str " loads an OCaml plugin (" ++ str (Filename.basename f) ++ str "),"
               ++ spc () ++ str "which Soma cannot load yet: a plugin is built against the Rocq it extends."))
    files;
  let order = Filename.concat (Filename.dirname log) "order" in
  let dir = Filename.dirname log in
  if not (run_to ~dir ~out:order ([rocq_binary (); "dep"; "-sort"] @ load_args ts @ files)) then
    error (str "rocq dep failed on " ++ str name ++ str "; the end of " ++ str order ++ str ":" ++ fnl () ++
           str (SomaOpam.tail_of_file order));
  let order = List.filter (fun f -> Filename.check_suffix f ".v")
      (List.concat_map (String.split_on_char ' ') (SomaOpam.read_lines order)) in
  let total = List.length order in
  List.iteri (fun i f ->
      let rel = match List.find_opt (fun t -> String.starts_with ~prefix:(t.dir ^ "/") f) ts with
        | Some t -> t.logical ^ "/" ^ String.sub f (String.length t.dir + 1) (String.length f - String.length t.dir - 1)
        | None -> f in
      Printf.eprintf "Rocq: compiling %s: %d/%d %s\n%!" name (i + 1) total rel;
      (* a Rocq library is Rocq: compiled as Rocq does, without Soma's
         prelude, whose names ([R], the reals) and gradual typing it does
         not expect *)
      if not (run_to ~dir ~out:log ([Sys.executable_name; "--kind=compile"; "-q"; "-no-soma-prelude"] @ load_args ts @ [f])) then
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
      else if Filename.check_suffix e ".v" || List.mem e ["dune"; "_RocqProject"; "_CoqProject"] then
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

(* [package], compiled: its theories, from [cache ()] or else compiled now *)
let ensure ~package source =
  let root = cache () in
  SomaOpam.mkdir_p root;
  let key = soma_key () in
  let dir, fetch = match source with
    | Local path ->
      if not (Sys.file_exists path && Sys.is_directory path) then
        error (str path ++ str ", where " ++ str package ++ str " is said to be, is no directory.");
      (* its sources are part of its name: a change compiles it again *)
      let digest = Digest.to_hex (Digest.string (String.concat "\n" (List.map (fun f ->
          f ^ " " ^ Digest.to_hex (Digest.file f)) (files_under path)))) in
      Filename.concat root (package ^ "-local-" ^ String.sub digest 0 8 ^ "-" ^ key),
      (fun src -> copy_tree path src)
    | Opam version ->
      let log = Filename.concat root "opam.log" in
      let switch = SomaOpam.ensure_switch ~who:"Rocq" ~log in
      ensure_repository ~switch ~log;
      let version = match version with Some v -> v | None -> latest ~switch ~log package in
      Filename.concat root (package ^ "." ^ version ^ "-" ^ key),
      (fun src ->
         Printf.eprintf "Rocq: fetching %s %s (opam source)\n%!" package version;
         if not (SomaOpam.run ~log ["opam"; "source"; "--switch=" ^ switch; package ^ "." ^ version; "--dir=" ^ src])
         then error (str "opam source " ++ str package ++ str "." ++ str version ++ str " failed; the end of " ++
                     str log ++ str ":" ++ fnl () ++ str (SomaOpam.tail_of_file log)))
  in
  let done_file = Filename.concat dir "theories" in
  let src = Filename.concat dir "src" in
  if not (Sys.file_exists done_file) then begin
    (* a compilation stopped halfway starts again *)
    if Sys.file_exists dir then ignore (Sys.command (Filename.quote_command "rm" ["-rf"; dir]));
    SomaOpam.mkdir_p dir;
    fetch src;
    let ts = theories ~package src in
    if ts = [] then
      error (str package ++ str " declares no theory: no dune file has a (rocq.theory ...) of the package," ++
             spc () ++ str "and there is no _RocqProject or _CoqProject.");
    let name = Filename.basename dir in
    compile ~name ~log:(Filename.concat dir "compile.log") ts;
    Out_channel.with_open_bin done_file (fun oc ->
        List.iter (fun t -> Printf.fprintf oc "%s %s\n" t.logical t.dir) ts);
    (* the package compiled before, by another Soma or from other sources,
       is of no use any more *)
    let prefix = match source with Local _ -> package ^ "-local-" | Opam _ -> package ^ "." in
    Array.iter (fun e ->
        let d = Filename.concat root e in
        if String.starts_with ~prefix e && d <> dir && Sys.is_directory d then
          ignore (Sys.command (Filename.quote_command "rm" ["-rf"; d])))
      (Sys.readdir root)
  end;
  List.filter_map (fun l -> match String.index_opt l ' ' with
      | Some i -> Some (String.sub l 0 i, String.sub l (i + 1) (String.length l - i - 1))
      | None -> None) (SomaOpam.read_lines done_file)

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
