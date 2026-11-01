(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: [Import] compiles what it imports. In a Soma file (.soma, .proof,
   .lang), [Import X], where [X] is no module in scope, is the file
   [X.soma] (or [X.lang]) of the program's project, compiled first when it
   is not compiled yet or changed since, then loaded and opened as by
   [Require Import X]; or else a compiled library ([Import Sandbox]), as by
   [Require Import]. [X.Y] is the file [X/Y.soma].

   The project is the folder of the nearest soma.toml above the program
   being built (vernac/somaProject.ml), or else the program's folder
   ($SOMA_PROJECT_ROOT for the compilations it starts). What is compiled
   goes to its .soma-cache, with a stamp: the hash of the source (with
   its .proof and .lang) and the digests of what it imports, as compiled.
   A cached file is used while its stamp holds: its source unchanged, and
   what it imports up to date and the same as when it was compiled. A
   file is compiled by a process of its own, which compiles what it
   imports in the same way.

   After the project's own files, [Import maps.gmap] is a dependency of the
   project (vernac/somaDeps.ml) when one is named maps: the file gmap.soma
   of its source. A dependency is compiled as a project of its own, with its
   rules and its proofs, into the .soma-cache of the project being built, as
   the library maps.gmap, so that the util.soma of two projects are two
   libraries. So the root of a project (where its files are), its cache and
   its prefix (maps) are three things. *)

open Names

let cache_name = ".soma-cache"

let root_var = "SOMA_PROJECT_ROOT"
let stack_var = "SOMA_IMPORT_STACK"
let stamp_var = "SOMA_IMPORT_STAMP"
let source_var = "SOMA_IMPORT_SOURCE"
let cache_var = "SOMA_PROJECT_CACHE"
let prefix_var = "SOMA_PROJECT_PREFIX"
let build_var = "SOMA_BUILD_ROOT"

let is_soma_file f = List.exists (Filename.check_suffix f) [".soma"; ".proof"; ".lang"; ".definition"]

let file_of_loc = function
  | Some { Loc.fname = Loc.InFile { file; _ }; _ } -> Some file
  | _ -> None

let applies ?loc () = match file_of_loc loc with
  | Some f -> is_soma_file f
  | None -> false

let absolute f = if Filename.is_relative f then Filename.concat (Sys.getcwd ()) f else f

(* Paths are as the load path has them: absolute, without "." *)

(* $SOMA_PROJECT_ROOT, set by [compile] for what it compiles, or by hand *)
let env_root () = match Sys.getenv_opt root_var with
  | Some r when r <> "" -> Some (CUnix.canonical_path_name r)
  | _ -> None

(* The root of the project of the folder [dir]: that of its soma.toml,
   checked, or else [dir] *)
let root_of_dir dir =
  let dir = CUnix.canonical_path_name dir in
  match SomaProject.find_root dir with
  | Some root -> (SomaProject.load root).root
  | None -> dir

(* The rules of a project's root are NAME.lang, by its soma.toml, which a
   copy of it elsewhere still has; without one, FOLDER/FOLDER.lang *)
let root_rules_name root =
  if Sys.file_exists (Filename.concat root SomaProject.file_name)
  then (SomaProject.load root).name
  else Filename.basename root

let project_root ?loc () =
  match env_root () with
  | Some r -> r
  | None -> root_of_dir (match file_of_loc loc with
    | Some f -> Filename.dirname (absolute f)
    | None -> Sys.getcwd ())

let cache root = Filename.concat root cache_name

(* A project being compiled: where its files are, where they compile to,
   and the name its libraries are under (none for the one being built) *)
type project = { root : string; cache_dir : string; prefix : string }

let env_value var = match Sys.getenv_opt var with
  | Some v when v <> "" -> Some v
  | _ -> None

let current ?loc () =
  let root = project_root ?loc () in
  { root;
    cache_dir = Option.default (cache root) (env_value cache_var);
    prefix = Option.default "" (env_value prefix_var) }

(* The project being built, whose build this is *)
let build_root ?loc () = Option.default (project_root ?loc ()) (env_value build_var)

(* The dependencies of the build, once: the compilation that started it
   resolves them, before any file is compiled, and the others read soma.lock *)
let selected = ref None

let dependencies ?loc () = match !selected with
  | Some s -> s
  | None ->
    let root = build_root ?loc () in
    let s =
      if not (Sys.file_exists (Filename.concat root SomaProject.file_name)) then []
      else
        let top = SomaProject.load root in
        if Option.has_some (env_value build_var) then SomaDeps.locked top else SomaDeps.ensure top in
    selected := Some s;
    s

let project_of_dependency ?loc (s : SomaDeps.selected) =
  { root = s.project.root;
    cache_dir = SomaDeps.cache_of ~root:(build_root ?loc ()) s;
    prefix = s.project.name }

(* The dependencies that [p]'s soma.toml names *)
let is_direct (p : project) (s : SomaDeps.selected) =
  Sys.file_exists (Filename.concat p.root SomaProject.file_name) &&
  List.exists (fun (d : SomaProject.dependency) -> d.path.canonical = s.path)
    (SomaProject.load p.root).dependencies

(* [path] of [p], as all of the build know it: maps/a/b *)
let qualified p path = if p.prefix = "" then path else p.prefix ^ "/" ^ path

(* A compilation of a dependency, fetched or a checkout, or of what it
   compiles (the Rocq libraries it names), is someone else's [Import], which
   asked for definitions and not for files. Commands whose argument says where
   to write are refused there, by their role and not by what they say: the
   same file built on its own, as a project, runs them. It is no sandbox: a
   plugin already installed does what it does. *)
let refuse_in_dependency ?(does = "writes a file") command =
  if Option.has_some (env_value prefix_var) then begin
    let loc = Loc.get_current_command_loc () in
    let name = DirPath.to_string (Lib.library_dp ()) in
    (* the program and its .proof are one library; say which *)
    let where = match Option.bind loc (fun l -> file_of_loc (Some l)) with
      | Some f when not (List.exists (Filename.check_suffix f) [".soma"; ".v"]) -> name ^ Filename.extension f
      | _ -> name in
    let at = match loc with Some l -> Printf.sprintf ":%d" l.Loc.line_nb | None -> "" in
    CErrors.user_err ?loc Pp.(
        str where ++ str at ++ str ": " ++ str command ++ str " " ++ str does ++ str "." ++ spc () ++
        str "A dependency is checked, not run." ++ spc () ++
        str command ++ str " works when that project is built on its own.")
  end

(* [X.Y] as a path in the project: X/Y *)
let path_of_qualid qid =
  let dir, id = Libnames.repr_qualid qid in
  String.concat "/" (List.rev_map Id.to_string (DirPath.repr dir) @ [Id.to_string id])

(* FILE.wasm alone, without FILE.definition, is a module whose exports are
   all of type Any: compiled from an empty definition (see [compile]) *)
let source_of root path =
  List.find_map (fun ext ->
      let f = Filename.concat root (path ^ ext) in
      if Sys.file_exists f then Some f else None) [".soma"; ".lang"; ".definition"; ".wasm"]

let vo_of p path = Filename.concat p.cache_dir (path ^ ".vo")
let stamp_of p path = Filename.concat p.cache_dir (path ^ ".stamp")

(* [path], as [p] imports it: its file, or that of a dependency it names,
   and the project that has it. None when it is neither, a library's. *)
let locate ?loc p path =
  match source_of p.root path with
  | Some src -> Some (p, path, src)
  | None ->
    let first, rest = match String.index_opt path '/' with
      | Some i -> String.sub path 0 i, Some (String.sub path (i + 1) (String.length path - i - 1))
      | None -> path, None in
    (* a project's file by its whole name, as its folder's rules are *)
    match rest with
    | Some inside when first = p.prefix && Option.has_some (source_of p.root inside) ->
      Some (p, inside, Option.get (source_of p.root inside))
    | _ ->
    match List.find_opt (fun (s : SomaDeps.selected) -> s.project.name = first) (dependencies ?loc ()) with
    | None -> None
    | Some s when not (is_direct p s) ->
      CErrors.user_err ?loc Pp.(
          str "Import " ++ str (String.map (function '/' -> '.' | c -> c) path) ++ str ": " ++ str first ++
          str " is " ++ str s.path ++ str ", a dependency of a dependency, which this project's " ++
          str SomaProject.file_name ++ str " does not name:" ++ spc () ++
          str (Printf.sprintf "%S = %S" s.path (SomaProject.version_to_string s.version)))
    | Some s ->
      let d = project_of_dependency ?loc s in
      (* [Import maps] is maps.soma of the dependency *)
      let inside = Option.default first rest in
      match source_of d.root inside with
      | Some src -> Some (d, inside, src)
      | None ->
        let files = List.filter (fun f -> Filename.check_suffix f ".soma")
            (Array.to_list (Sys.readdir d.root)) in
        let files = List.sort compare (List.map Filename.remove_extension files) in
        let example = match files with f :: _ -> first ^ "." ^ f | [] -> first ^ ".X" in
        CErrors.user_err ?loc Pp.(
            str first ++ str " is " ++ str s.path ++ str ", which has no " ++ str inside ++ str ".soma." ++ spc () ++
            str (if files = [] then "It has no .soma file at its root."
                 else "Import " ^ example ^ ". Its root has " ^ String.concat ", " files ^ "."))

(* What a compilation reads of a program: its source, .proof and .lang *)
let source_hash src =
  let base = Filename.remove_extension src in
  let one f = if Sys.file_exists f then Digest.to_hex (Digest.file f) else "-" in
  (* and FILE.wasm, FILE.ml or FILE.lean, which FILE.definition declares *)
  Digest.to_hex (Digest.string (String.concat " " (List.map one [src; base ^ ".proof"; base ^ ".lang"; base ^ ".wasm"; base ^ ".ml"; base ^ ".lean"])))

let digest f = Digest.to_hex (Digest.file f)

(* The digests of the files of libraries, each read once *)
let digests : (string, string) Hashtbl.t = Hashtbl.create 97

let file_digest f = match Hashtbl.find_opt digests f with
  | Some d -> d
  | None -> let d = digest f in Hashtbl.add digests f d; d

let library_file dir = match Loadpath.locate_absolute_library dir with
  | Ok f -> Some f
  | Error _ -> None

let stamp_format = "soma-stamp 2"

(* A stamp: its format, "source HASH", then "import PATH DIGEST" for each import of
   the project, and "library NAME DIGEST" for each library from elsewhere
   (Stdlib, Soma.JSX, ...), whose change, by an upgrade of Soma, makes
   what was compiled with it inconsistent *)
let read_stamp file =
  try
    let lines = String.split_on_char '\n' (In_channel.with_open_bin file In_channel.input_all) in
    let source = ref None and imports = ref [] and libraries = ref [] in
    (* the first line is the format: an older stamp is out of date *)
    if List.hd lines <> stamp_format then None else begin
    List.iter (fun l -> match String.split_on_char ' ' l with
        | ["source"; h] -> source := Some h
        | ["import"; p; d] -> imports := (p, d) :: !imports
        | ["library"; l; d] -> libraries := (l, d) :: !libraries
        | _ -> ()) lines;
    Option.map (fun h -> h, List.rev !imports, !libraries) !source
    end
  with Sys_error _ -> None

let rec mkdir_p d =
  if not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

(* What this compilation imported from its project, for its stamp *)
let imported : (string * string) list ref = ref []

(* Files of the project checked to be up to date by this compilation *)
let ensured : (string, unit) Hashtbl.t = Hashtbl.create 17

(* The files being compiled, each importing the next: from the program
   being built (when it is in the project) to the one at [loc] *)
let stack ?loc () = match Sys.getenv_opt stack_var with
  | Some s when s <> "" -> String.split_on_char ':' s
  | _ ->
    let root = project_root ?loc () in
    match file_of_loc loc with
    | Some f ->
      let f = Filename.concat (CUnix.canonical_path_name (Filename.dirname (absolute f)))
          (Filename.remove_extension (Filename.basename f)) in
      if CString.is_prefix (root ^ "/") f
      then [String.sub f (String.length root + 1) (String.length f - String.length root - 1)]
      else []
    | None -> []

(* The file being compiled, set by toplevel/ccompile.ml *)
let source_file = ref None

(* The build's: the Rocq libraries of two dependencies are one library,
   compiled once *)
let project_cache () =
  match env_value build_var, env_root () with
  | Some r, _ | None, Some r -> cache r
  | None, None -> cache (root_of_dir (match !source_file with
      | Some f -> Filename.dirname (absolute f)
      | None -> Sys.getcwd ()))

(* What the Rocq libraries of the build's files need in the load path, for
   what imports them: logical name, folder, one a line *)
let load_paths_file () = Filename.concat (project_cache ()) "load-paths"

let record_load_path logical dir =
  let file = load_paths_file () in
  let line = logical ^ " " ^ dir in
  if not (List.mem line (SomaOpam.read_lines file)) then begin
    mkdir_p (Filename.dirname file);
    Out_channel.with_open_gen [Open_append; Open_creat; Open_binary] 0o644 file (fun oc ->
        output_string oc (line ^ "\n"))
  end

let add_load_path unix_path coq_path =
  Loadpath.add_vo_path { Loadpath.unix_path; coq_path; implicit = false; recursive = true; installed = false }

(* The project's cache, and what its libraries may need: every dependency of
   the build, and the Rocq libraries of its files *)
let add_cache_to_loadpath ?loc p =
  add_load_path p.cache_dir (if p.prefix = "" then DirPath.empty else Libnames.dirpath_of_string p.prefix);
  List.iter (fun (s : SomaDeps.selected) ->
      let d = project_of_dependency ?loc s in
      if d.cache_dir <> p.cache_dir && Sys.file_exists d.cache_dir then
        add_load_path d.cache_dir (Libnames.dirpath_of_string d.prefix))
    (dependencies ?loc ());
  List.iter (fun l -> match String.index_opt l ' ' with
      | Some i ->
        let dir = String.sub l (i + 1) (String.length l - i - 1) in
        if Sys.file_exists dir then
          add_load_path dir (Libnames.dirpath_of_string (String.sub l 0 i))
      | None -> ()) (SomaOpam.read_lines (load_paths_file ()))

let compile ?loc p path src =
  let vo = vo_of p path in
  mkdir_p (Filename.dirname vo);
  (* a module without a definition: an empty one, in the cache, for the
     module (SOMA_WASM_FILE, which toplevel/ccompile.ml reads) *)
  let module_file, input =
    if Filename.check_suffix src ".wasm" then begin
      let definition = Filename.concat p.cache_dir (path ^ ".definition") in
      Out_channel.with_open_bin definition (fun oc ->
          output_string oc ("(* " ^ Filename.basename src ^
                            " has no .definition: its exports are all of type Any *)\n"));
      [ "SOMA_WASM_FILE=" ^ src ], definition
    end else [], src in
  Printf.eprintf "Compiling %s (into %s)\n%!" (qualified p path ^ Filename.extension src) cache_name;
  let env = Array.of_list (
      List.filter (fun v -> not (List.exists (fun k -> String.starts_with ~prefix:(k ^ "=") v)
                                   [root_var; stack_var; stamp_var; source_var; cache_var; prefix_var; build_var; "SOMA_MIRAGE_BUILD"; "SOMA_OCAML_BUILD"; "SOMA_OCAML_EXTRACT"; "SOMA_REVIEW"; "SOMA_HASH"; "SOMA_WASM_FILE"]))
        (Array.to_list (Unix.environment ()))
      @ [ root_var ^ "=" ^ p.root;
          cache_var ^ "=" ^ p.cache_dir;
          prefix_var ^ "=" ^ p.prefix;
          build_var ^ "=" ^ build_root ?loc ();
          stack_var ^ "=" ^ String.concat ":" (stack ?loc () @ [qualified p path]);
          stamp_var ^ "=" ^ stamp_of p path;
          source_var ^ "=" ^ src;
          (* what a program imports is not a unikernel of its own *)
          "SOMA_MIRAGE_BUILD=0"; "SOMA_OCAML_BUILD=0" ] @ module_file) in
  let prog = Sys.executable_name in
  (* the cache in the load path names the library by its place there:
     .soma-cache/models/task.vo is models.task; that of a dependency, by
     its name too: maps.a.b *)
  let argv = [| prog; "--kind=compile"; input; "-o"; vo; "-Q"; p.cache_dir; p.prefix |] in
  let null = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
  let pid = Unix.create_process_env prog argv env Unix.stdin null Unix.stderr in
  Unix.close null;
  let rec wait () = try snd (Unix.waitpid [] pid)
    with Unix.Unix_error (Unix.EINTR, _, _) -> wait () in
  match wait () with
  | Unix.WEXITED 0 ->
    (* the folder's listing, if read before, does not have the new file *)
    System.forget_dir p.cache_dir
  | _ ->
    CErrors.user_err ?loc Pp.(str "Cannot import " ++ str (String.map (function '/' -> '.' | c -> c) (qualified p path)) ++
                              str ": " ++ str (qualified p path ^ Filename.extension src) ++
                              str " does not compile (its errors are above).")

(* [path] (whose source is [src]) compiled and up to date in the cache *)
let rec ensure ?loc p path src =
  let id = qualified p path in
  if not (Hashtbl.mem ensured id) then begin
    let stack = stack ?loc () in
    if List.mem id stack then
      CErrors.user_err ?loc Pp.(str "Import cycle: " ++
                                str (String.concat " -> " (stack @ [id])) ++ str ".");
    let vo = vo_of p path in
    let fresh = Sys.file_exists vo && match read_stamp (stamp_of p path) with
      | None -> false
      | Some (hash, imports, libraries) ->
        hash = source_hash src &&
        List.for_all (fun (l, d) -> match library_file (Libnames.dirpath_of_string l) with
            | Some f -> file_digest f = d
            | None -> false) libraries &&
        List.for_all (fun (i, d) -> match locate ?loc p i with
            | None -> false
            | Some (q, i, s) -> ensure ?loc q i s; digest (vo_of q i) = d) imports
    in
    if not fresh then compile ?loc p path src;
    Hashtbl.replace ensured id ()
  end

(* [Import] of these names, which are no modules in scope: those that are
   files of the project or of a dependency are compiled when needed. The
   names to require: those of the libraries. *)
let prepare ?loc qids =
  let p = current ?loc () in
  let any = ref false in
  let names = List.map (fun qid ->
      let path = path_of_qualid qid in
      match locate ?loc p path with
      | Some (q, inside, src) ->
        ensure ?loc q inside src;
        if not (List.mem_assoc path !imported) then
          imported := (path, vo_of q inside) :: !imported;
        any := true;
        let name = qualified q inside in
        if name = path then qid
        else Libnames.qualid_of_string ?loc (String.map (function '/' -> '.' | c -> c) name)
      | None ->
        (* an OCaml module is what its definition says it is *)
        if Sys.file_exists (Filename.concat p.root (path ^ ".ml")) then
          CErrors.user_err ?loc Pp.(str "Import " ++ Libnames.pr_qualid qid ++ str ": " ++ str path ++
                                    str ".ml has no " ++ str (Filename.basename path) ++ str ".definition next to it," ++ spc () ++
                                    str "which declares the types of its values that Soma uses (name : type.).");
        qid) qids in
  if !any then add_cache_to_loadpath ?loc p;
  names

(* The library [mp] is another's of the same last name, when [qid] is a file
   of this project: a dependency's util is not this project's util.soma *)
let names_another_library ?loc qid mp = match mp with
  | ModPath.MPfile dir ->
    let p = current ?loc () in
    let path = path_of_qualid qid in
    Option.has_some (source_of p.root path) &&
    DirPath.to_string dir <> String.map (function '/' -> '.' | c -> c) (qualified p path)
  | ModPath.MPbound _ | ModPath.MPdot _ -> false

(* A folder's rules: X/X.lang, with its proofs in X/X.proof, apply to every
   Soma file under X/, as if each started with [Import X.X]; so they are
   compiled once, into the cache, and what they define, macros and
   theorems included, is the same for all. Unless X/X.soma exists: then
   they are its own, as for any program. *)
let is_folder_rules f =
  Filename.check_suffix f ".lang" &&
  let base = Filename.remove_extension f in
  let dir = CUnix.canonical_path_name (Filename.dirname (absolute f)) in
  Filename.basename base = (if SomaProject.find_root dir = Some dir then root_rules_name dir else Filename.basename dir) &&
  not (Sys.file_exists (base ^ ".soma"))

(* The rules of the folders of the project from its root to [file]'s,
   outermost first, compiled when needed: the libraries to import *)
let folder_rules file =
  if not (is_soma_file file) then [] else
  let file = absolute file in
  let dir = CUnix.canonical_path_name (Filename.dirname file) in
  let loc = Loc.initial (Loc.InFile { dirpath = None; file }) in
  let root = match env_root () with
    | Some r -> r
    | None when SomaProject.find_root dir <> None -> root_of_dir dir
    | None ->
      (* without soma.toml, a file built by itself is the program; the
         rules of the folders above it are not its project's *)
      let rec above d =
        let up = Filename.dirname d in
        if up = d then ()
        else if Sys.file_exists (Filename.concat up (Filename.basename up ^ ".lang"))
             && not (Sys.file_exists (Filename.concat up (Filename.basename up ^ ".soma")))
        then Feedback.msg_warning Pp.(
            str (Filename.basename up ^ "/" ^ Filename.basename up ^ ".lang") ++
            str ", the rules of the folder " ++ str (Filename.basename up ^ "/") ++
            str " this file is under, does not apply to it when it is built by itself: build the program that imports it, " ++
            str "or give the project a " ++ str SomaProject.file_name ++ str " (its root), or set " ++
            str root_var ++ str " to the folder of that program.")
        else above up in
      above dir;
      dir in
  (* what the build depends on is known before anything is compiled *)
  ignore (dependencies ~loc ());
  let p = current ~loc () in
  let folders =
    if dir = root then Some []
    else if CString.is_prefix (root ^ "/") dir then
      Some (String.split_on_char '/' (String.sub dir (String.length root + 1)
                                        (String.length dir - String.length root - 1)))
    else None in
  match folders with
  | None -> []
  | Some folders ->
    (* the root's rules are ROOT/ROOT.lang, a folder X's X/X.lang *)
    let rec paths prefix = function
      | [] -> []
      | x :: rest -> let p = prefix ^ x in (p ^ "/" ^ x) :: paths (p ^ "/") rest in
    let self = Filename.concat dir (Filename.remove_extension (Filename.basename file)) in
    let rules = List.filter_map (fun path ->
        let base = Filename.concat root path in
        let lang = base ^ ".lang" in
        if base = self || Sys.file_exists (base ^ ".soma") then None
        else if Sys.file_exists lang then Some (path, lang)
        else if Sys.file_exists (base ^ ".proof") then
          CErrors.user_err Pp.(str (path ^ ".proof") ++ str " has the proofs of the rules of its folder, " ++
                               str (path ^ ".lang") ++ str ", which does not exist.")
        else None) (root_rules_name root :: paths "" folders) in
    List.iter (fun (path, src) ->
        ensure p path src;
        if not (List.mem_assoc path !imported) then
          imported := (path, vo_of p path) :: !imported) rules;
    if rules <> [] then add_cache_to_loadpath ~loc p;
    List.map (fun (path, _) -> String.map (function '/' -> '.' | c -> c) (qualified p path)) rules

(* A compilation started by [compile] writes its stamp once it succeeded *)
let write_stamp () =
  match Sys.getenv_opt stamp_var, Sys.getenv_opt source_var with
  | Some stamp, Some src when stamp <> "" ->
    let in_cache f = match env_value build_var, env_root () with
      | Some root, _ | None, Some root -> CString.is_prefix (cache root ^ "/") f
      | None, None -> false in
    let libraries = List.filter_map (fun dir -> match library_file dir with
        | Some f when not (in_cache f) -> Some ("library " ^ DirPath.to_string dir ^ " " ^ file_digest f)
        | _ -> None) (Library.loaded_libraries ()) in
    let lines = stamp_format :: ("source " ^ source_hash src) ::
                List.rev_map (fun (p, vo) -> "import " ^ p ^ " " ^ digest vo) !imported @ libraries in
    Out_channel.with_open_bin stamp (fun oc -> output_string oc (String.concat "\n" lines ^ "\n"))
  | _ -> ()
