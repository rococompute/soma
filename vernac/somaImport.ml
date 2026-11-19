(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: [Import] compiles what it imports. In a Soma file (.soma, .exp,
   .ext), [Import X], where [X] is no module in scope, is the file
   [X.soma] (or [X.ext]) of the program's project, compiled first when it
   is not compiled yet or changed since, then loaded and opened as by
   [Require Import X]; or else a compiled library ([Import Sandbox]), as by
   [Require Import]. [X.Y] is the file [X/Y.soma].

   The project is the folder of the nearest soma.toml above the program
   being built (vernac/somaProject.ml), or else the program's folder
   ($SOMA_PROJECT_ROOT for the compilations it starts). What is compiled
   goes to its .soma-cache, with a stamp: the hash of the source (with
   its .exp and .ext) and the digests of what it imports, as compiled,
   without their proofs.
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
let expected_source_var = "SOMA_IMPORT_EXPECTED_SOURCE"
let cache_var = "SOMA_PROJECT_CACHE"
let prefix_var = "SOMA_PROJECT_PREFIX"
let build_var = "SOMA_BUILD_ROOT"
let rocq_library_var = "SOMA_ROCQ_LIBRARY"
let loaded_source_inputs_var = "SOMA_LOADED_SOURCE_INPUTS"
let loaded_source_request_var = "SOMA_LOADED_SOURCE_REQUEST"

let is_soma_file f = List.exists (Filename.check_suffix f) [".soma"; ".exp"; ".ext"; ".definition"]

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

(* The rules of a project's root are NAME.ext, by its soma.toml, which a
   copy of it elsewhere still has; without one, FOLDER/FOLDER.ext *)
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
    (* the program and its .exp are one library; say which *)
    let where = match Option.bind loc (fun l -> file_of_loc (Some l)) with
      | Some f when not (List.exists (Filename.check_suffix f) [".soma"; ".v"]) -> name ^ Filename.extension f
      | _ -> name in
    let at = match loc with Some l -> Printf.sprintf ":%d" l.Loc.line_nb | None -> "" in
    CErrors.user_err ?loc Pp.(
        str where ++ str at ++ str ": " ++ str command ++ str " " ++ str does ++ str "." ++ spc () ++
        str "A dependency is checked, not run." ++ spc () ++
        str command ++ str " works when that project is built on its own.")
  end

(* A Rocq library (plugins/soma_rocq) is compiled with [rocq_library_var]
   set to its name. Whatever the spacing or comments, the parsed command
   is what is refused, before any plugin is loaded. *)
let refuse_ml_module_in_rocq_library () =
  match env_value rocq_library_var with
  | None -> ()
  | Some name ->
    let loc = Loc.get_current_command_loc () in
    let file = match file_of_loc loc with Some f -> Filename.basename f | None -> "?" in
    CErrors.user_err ?loc Pp.(
        str ("Rocq Library: " ^ name ^ " loads an OCaml plugin (" ^ file ^ "),") ++ spc () ++
        str "which Soma cannot load yet: a plugin is built against the Rocq it extends.")

(* [X.Y] as a path in the project: X/Y *)
let path_of_qualid qid =
  let dir, id = Libnames.repr_qualid qid in
  String.concat "/" (List.rev_map Id.to_string (DirPath.repr dir) @ [Id.to_string id])

(* FILE.wasm alone, without FILE.definition, is a module whose exports are
   all of type Any: compiled from an empty definition (see [compile]) *)
let source_of root path =
  List.find_map (fun ext ->
      let f = Filename.concat root (path ^ ext) in
      if Sys.file_exists f then Some f else None) [".soma"; ".ext"; ".definition"; ".wasm"]

let vo_of p path = Filename.concat p.cache_dir (path ^ ".vo")
let stamp_of p path = Filename.concat p.cache_dir (path ^ ".stamp")

(* A project uses the dependencies it names. One that another brings along is
   loaded, and on the load path for what needs it, and is not this project's
   to import: its version is what others ask for, and they can stop asking. *)
let undeclared ?loc ~shown first (s : SomaDeps.selected) =
  CErrors.user_err ?loc Pp.(
      str "Import " ++ str shown ++ str ": " ++ str first ++
      str " is " ++ str s.path ++ str ", a dependency of a dependency, which this project's " ++
      str SomaProject.file_name ++ str " does not name:" ++ spc () ++
      str (Printf.sprintf "%S = %S" s.path (SomaProject.version_to_string s.version)))

(* The refusal, for a library named by [first], its first component *)
let refuse_undeclared ?loc ~shown first =
  let p = current ?loc () in
  if first <> p.prefix then
    match List.find_opt (fun (s : SomaDeps.selected) -> s.project.name = first) (dependencies ?loc ()) with
    | Some s when not (is_direct p s) -> undeclared ?loc ~shown first s
    | _ -> ()

let shown_qualid qid = Pp.string_of_ppcmds (Libnames.pr_qualid qid)

let first_component qid =
  match DirPath.repr (fst (Libnames.repr_qualid qid)) with
  | [] -> Id.to_string (snd (Libnames.repr_qualid qid))
  | dir -> Id.to_string (List.hd (List.rev dir))

(* [Require c.c] and [From c Require Import c], which do not go through [prepare] *)
let refuse_undeclared_require ?loc from qids =
  match from with
  | Some dir -> refuse_undeclared ?loc ~shown:(shown_qualid dir) (first_component dir)
  | None -> List.iter (fun q -> refuse_undeclared ?loc ~shown:(shown_qualid q) (first_component q)) qids

(* [Import c.c] of a module in scope: what matters is the library it resolved to,
   however it is written, so that a project's own [Module c] is its own *)
let refuse_undeclared_module ?loc qid mp =
  let rec library = function
    | ModPath.MPfile dir -> Some dir
    | ModPath.MPdot (mp, _) -> library mp
    | ModPath.MPbound _ -> None in
  match Option.map (fun d -> List.rev (DirPath.repr d)) (library mp) with
  | Some (first :: _) when not (DirPath.equal (Option.get (library mp)) (Lib.library_dp ())) ->
    refuse_undeclared ?loc ~shown:(shown_qualid qid) (Id.to_string first)
  | _ -> ()

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
      undeclared ?loc ~shown:(String.map (function '/' -> '.' | c -> c) path) first s
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

(* What a compilation reads of a program: its source, .exp and .ext *)
let source_hash src = SomaModuleStore.source_hash src

let digest f = SomaMerkle.file_hash f

(* What an importer of a compiled file depends on: all but its proofs. Its
   "library" segment has what Rocq identifies a library by, and will not load
   an importer with another of: its definitions, statements, notations,
   instances and hints, with their locations. Its "summary" segment has the same
   digests of what it imports, so a change goes on through a file that was
   compiled again to the same result. Its "opaques" segment has the proofs, whose
   bodies no importer sees: another proof of a statement compiles nothing else. *)
let interface_digest vo =
  match ObjFile.open_in ~file:vo with
  | exception (Sys_error _ | CErrors.UserError _) -> digest vo
  | ch ->
    Fun.protect ~finally:(fun () -> ObjFile.close_in ch) (fun () ->
        let segments = ObjFile.segments ch in
        In_channel.with_open_bin vo (fun ic ->
            let hash name =
              let segment = CString.Map.get name segments in
              LargeFile.seek_in ic segment.ObjFile.pos;
              SomaMerkle.channel ~len:segment.ObjFile.len ic in
            SomaMerkle.string ("soma-interface 4\000" ^ hash "summary" ^ hash "library")))

(* Import workers keep the snapshot selected before their process started.
   A later source edit must never be adopted by the stamp of older code. *)
let import_outputs : (string, string) Hashtbl.t = Hashtbl.create 3
let published_import_outputs : (string, Unix.stats) Hashtbl.t = Hashtbl.create 3

let same_output a b =
  a.Unix.st_dev = b.Unix.st_dev && a.Unix.st_ino = b.Unix.st_ino &&
  a.Unix.st_kind = b.Unix.st_kind && a.Unix.st_size = b.Unix.st_size &&
  a.Unix.st_mtime = b.Unix.st_mtime && a.Unix.st_ctime = b.Unix.st_ctime

let remove_if_present file = try Sys.remove file with Sys_error _ -> ()

let discard_import_outputs () =
  Hashtbl.iter (fun _ tmp -> remove_if_present tmp) import_outputs;
  Hashtbl.clear import_outputs;
  Hashtbl.iter (fun file identity ->
      try if same_output identity (Unix.lstat file) then remove_if_present file
      with Unix.Unix_error _ -> ()) published_import_outputs;
  Hashtbl.clear published_import_outputs

let () = at_exit (fun () ->
    Hashtbl.iter (fun _ tmp -> remove_if_present tmp) import_outputs)

let require_source_snapshot src expected =
  let matches = try SomaMerkle.valid_hash expected && source_hash src = expected
    with Sys_error _ | Unix.Unix_error _ -> false in
  if not matches then begin
    discard_import_outputs ();
    CErrors.user_err Pp.(str (Filename.basename src) ++
      str ": source or companion files changed while compiling; retry the build.")
  end

let expected_import_source () =
  match Sys.getenv_opt stamp_var, Sys.getenv_opt source_var,
        Sys.getenv_opt expected_source_var with
  | Some stamp, Some src, Some expected when stamp <> "" ->
    require_source_snapshot src expected;
    Some expected
  | Some stamp, _, _ when stamp <> "" ->
    discard_import_outputs ();
    CErrors.user_err Pp.(str "Import compilation has no pre-compilation source snapshot; retry the build.")
  | _ -> None

let require_published_import_output file =
  let matches = match Hashtbl.find_opt published_import_outputs file with
    | Some identity ->
      (try same_output identity (Unix.lstat file) with Unix.Unix_error _ -> false)
    | None -> false in
  if not matches then begin
    discard_import_outputs ();
    CErrors.user_err Pp.(str (Filename.basename file) ++
      str ": compiled output changed before certification; retry the build.")
  end

let publish_import_output ~tmp ~file =
  ignore (expected_import_source ());
  Sys.rename tmp file;
  Hashtbl.remove import_outputs file;
  Hashtbl.replace published_import_outputs file (Unix.lstat file)

(* The digests of the files of libraries, each read once *)
let digests : (string, string) Hashtbl.t = Hashtbl.create 97

let file_digest f = match Hashtbl.find_opt digests f with
  | Some d -> d
  | None -> let d = digest f in Hashtbl.add digests f d; d

let library_file dir = match Loadpath.locate_absolute_library dir with
  | Ok f -> Some f
  | Error _ -> None

let stamp_format = "soma-stamp 4"

(* A stamp: its format, "source HASH", then "import PATH DIGEST" for each import of
   the project, and "library NAME DIGEST" for each library from elsewhere
   (Stdlib, Soma.JSX, ...), whose change, by an upgrade of Soma, makes
   what was compiled with it inconsistent *)
let read_stamp file =
  let valid_name s = s <> "" && String.for_all (fun c -> c > ' ' && c <> '\127') s in
  try
    let contents = In_channel.with_open_bin file In_channel.input_all in
    (* A writer always terminates every row. A cut-off final row, an unknown
       field, duplicate keys or a malformed digest invalidates the whole stamp. *)
    if contents = "" || contents.[String.length contents - 1] <> '\n' then None else
    match String.split_on_char '\n' contents with
    | format :: source :: rows when format = stamp_format ->
      (match String.split_on_char ' ' source with
       | ["source"; h] when SomaMerkle.valid_hash h ->
         let rec read imports libraries inputs = function
           | [""] -> Some (h, List.rev imports, List.rev libraries, List.rev inputs)
           | row :: rows ->
             (match String.split_on_char ' ' row with
              | ["import"; p; d] when valid_name p && SomaMerkle.valid_hash d && not (List.mem_assoc p imports) ->
                read ((p, d) :: imports) libraries inputs rows
              | ["library"; name; d] when valid_name name && SomaMerkle.valid_hash d && not (List.mem_assoc name libraries) ->
                read imports ((name, d) :: libraries) inputs rows
              | "input" :: _ ->
                (match Scanf.sscanf row "input %S %s%!" (fun p d -> p, d) with
                 | p, d when p <> "" && SomaMerkle.valid_hash d && not (List.mem_assoc p inputs) ->
                   read imports libraries ((p, d) :: inputs) rows
                 | _ -> None
                 | exception (Scanf.Scan_failure _ | Failure _ | End_of_file) -> None)
              | _ -> None)
           | [] -> None in
         read [] [] [] rows
       | _ -> None)
    | _ -> None
  with Sys_error _ | Unix.Unix_error _ | Failure _ | End_of_file -> None

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
let generated_output = ref false

(* The build's: the Rocq libraries of two dependencies are one library,
   compiled once *)
let project_cache () =
  match env_value build_var, env_root () with
  | Some r, _ | None, Some r -> cache r
  | None, None -> cache (root_of_dir (match !source_file with
      | Some f -> Filename.dirname (absolute f)
      | None -> Sys.getcwd ()))

(* The root of the project being built, as [project_cache] finds it *)
let built_root () =
  match env_value build_var, env_root () with
  | Some r, _ -> CUnix.canonical_path_name r
  | None, Some r -> r
  | None, None -> root_of_dir (match !source_file with
      | Some f -> Filename.dirname (absolute f)
      | None -> Sys.getcwd ())

(* A file of this project (FILE.ml beside a FILE.definition), as a compiled
   library records it: relative to the project's root, so that a .vo shared
   between two checkouts of one project (topbin/soma.ml's store) names the
   file of the checkout being built, and not that of the one it was compiled
   in. A dependency's file stays absolute: its sources are its own. *)
let project_file file =
  let file = absolute file in
  if env_value prefix_var <> None then file else
  let canonical =
    try Filename.concat (CUnix.canonical_path_name (Filename.dirname file)) (Filename.basename file)
    with Sys_error _ | Unix.Unix_error _ -> file in
  let root = match env_root () with
    | Some r -> r
    | None -> (try root_of_dir (Filename.dirname canonical) with e when CErrors.noncritical e -> "") in
  if root <> "" && CString.is_prefix (root ^ "/") canonical
  then String.sub canonical (String.length root + 1) (String.length canonical - String.length root - 1)
  else file

let resolve_project_file file =
  if Filename.is_relative file then Filename.concat (built_root ()) file else file

(* What the Rocq libraries of the build's files need in the load path, for
   what imports them: logical name, folder, one a line *)
let load_paths_file () = Filename.concat (project_cache ()) "load-paths"

(* The receipt covers the whole file. A writer must not mistake another
   writer's append, before its receipt is recorded, for untrusted contents
   and remove it. Readers take the same stable sibling lock so the trust
   check and the bytes read belong to one completed transaction. *)
let with_load_paths_lock file f =
  mkdir_p (Filename.dirname file);
  let fd = Unix.openfile (file ^ ".lock") [Unix.O_RDWR; Unix.O_CREAT; Unix.O_CLOEXEC] 0o600 in
  Fun.protect ~finally:(fun () -> Unix.close fd) (fun () ->
      let rec lock () =
        match Unix.lockf fd Unix.F_LOCK 0 with
        | () -> ()
        | exception Unix.Unix_error (Unix.EINTR, _, _) -> lock () in
      lock ();
      f ())

let parse_load_path line =
  match String.index_opt line ' ' with
  | Some i when i > 0 && i + 1 < String.length line ->
    Some (String.sub line 0 i, String.sub line (i + 1) (String.length line - i - 1))
  | _ -> None

(* Older ledgers could contain several versions of the same exact prefix.
   Keep the most recent choice; independent nested theories keep their rows. *)
let current_load_paths lines =
  List.fold_left (fun paths line -> match parse_load_path line with
      | None -> paths
      | Some (logical, _) ->
        List.filter (fun row -> match parse_load_path row with
            | Some (other, _) -> logical <> other | None -> false) paths @ [line]) [] lines

let retire_load_paths ~logical ~dir ~other_choices old =
  let within root path = path = root || CString.is_prefix (root ^ "/") path in
  let logical_within prefix name = name = prefix || CString.is_prefix (prefix ^ ".") name in
  let paths = Loadpath.get_load_paths () in
  let old = List.fold_left (fun old path ->
      if DirPath.to_string (Loadpath.logical path) = logical && Loadpath.physical path <> dir
      then Loadpath.physical path :: old else old) old paths |> List.sort_uniq compare in
  List.iter (fun path ->
      let physical = Loadpath.physical path in
      let name = DirPath.to_string (Loadpath.logical path) in
      if logical_within logical name && List.exists (fun root -> within root physical) old &&
         not (List.exists (fun (prefix, root) ->
             logical_within prefix name && within root physical) other_choices)
      then Loadpath.remove_load_path physical) paths

let record_load_path logical dir =
  let file = load_paths_file () in
  with_load_paths_lock file (fun () ->
      let previous = if SomaCache.trusted file then SomaOpam.read_lines file else [] in
      let old = List.filter_map (fun row -> match parse_load_path row with
          | Some (name, physical) when name = logical && physical <> dir -> Some physical
          | _ -> None) previous in
      let line = logical ^ " " ^ dir in
      let lines = current_load_paths (previous @ [line]) in
      let other_choices = List.filter_map (fun row -> match parse_load_path row with
          | Some (name, physical) when name <> logical -> Some (name, physical)
          | _ -> None) lines in
      retire_load_paths ~logical ~dir ~other_choices old;
      if previous <> lines then begin
        let tmp = Filename.temp_file ~temp_dir:(Filename.dirname file) ".soma-load-paths-" ".tmp" in
        Fun.protect ~finally:(fun () -> remove_if_present tmp) (fun () ->
            Out_channel.with_open_bin tmp (fun oc ->
                List.iter (fun line -> output_string oc (line ^ "\n")) lines);
            Sys.rename tmp file);
        SomaCache.record file
      end)

let read_load_paths () =
  let file = load_paths_file () in
  with_load_paths_lock file (fun () ->
      if SomaCache.trusted file then current_load_paths (SomaOpam.read_lines file) else [])

(* A Rocq library records the exact source/configuration inputs it compiled.
   Paths inside this project are relative so copied project caches retain
   their meaning; other paths are explicitly fingerprinted by test receipts. *)
(* Selection policies belong to this compilation, not to a reusable cache
   entry. A floating request or an external source tree must remain uncertain
   even when it reuses an entry first compiled by a pinned/local request. *)
let rocq_selection_uncertified = ref false
let note_uncertified_rocq_library () = rocq_selection_uncertified := true

(* [Load] reads source directly, outside the compiled-library table. Until
   those bytes have a producer-verified dependency receipt, arbitrary loads
   cannot certify a reusable import stamp or an affected-test/build skip.
   The current source's companions are already covered by [source_hash]. *)
let loaded_source_inputs : (string, string) Hashtbl.t = Hashtbl.create 7
let loaded_sources_uncertain = ref false

let loaded_source_captured file =
  let known = match env_value source_var with Some source -> Some source | None -> !source_file in
  match known with
    | None -> false
    | Some source ->
      let base = Filename.remove_extension source in
      (try
         let file = Unix.realpath file in
         List.exists (fun candidate ->
             try Unix.realpath candidate = file with Unix.Unix_error _ -> false)
           [source; base ^ ".ext"; base ^ ".exp"]
       with Unix.Unix_error _ -> false)

let note_source_load_attempt file =
  if not (loaded_source_captured file) then begin
    loaded_sources_uncertain := true;
    note_uncertified_rocq_library ()
  end

let note_loaded_source file =
  let file = absolute file in
  let hash = SomaMerkle.file_hash file in
  (match Hashtbl.find_opt loaded_source_inputs file with
   | Some old when old <> hash ->
     CErrors.user_err Pp.(str "A loaded source changed during compilation; rebuild.")
   | _ -> Hashtbl.replace loaded_source_inputs file hash);
  note_source_load_attempt file

(* RC selection is implicit state, even when its bytes alias a captured
   companion. It must always prevent reuse under a different RC context. *)
let note_rc_source file =
  note_loaded_source file;
  loaded_sources_uncertain := true;
  note_uncertified_rocq_library ()

let write_loaded_source_inputs () =
  match env_value loaded_source_inputs_var with
  | None -> ()
  | Some output ->
    let request = match env_value loaded_source_request_var with
      | Some request when SomaMerkle.valid_hash request -> request
      | _ -> CErrors.user_err Pp.(str "Loaded-source metadata has no current compiler request.") in
    let rows = Hashtbl.fold (fun file expected rows ->
        if SomaMerkle.file_hash file <> expected then
          CErrors.user_err Pp.(str "A loaded source changed during compilation; rebuild.");
        Printf.sprintf "input %S %s\n" file expected :: rows) loaded_source_inputs [] |> List.sort compare in
    Out_channel.with_open_bin output (fun oc ->
        Printf.fprintf oc "soma-loaded-inputs 2\nrequest %S\nuncertain %b\n%s" request !loaded_sources_uncertain (String.concat "" rows));
    SomaCache.record output

let rocq_source_in_project directory =
  try
    let root = Unix.realpath (built_root ()) in
    let directory = Unix.realpath directory in
    directory = root || CString.is_prefix (root ^ "/") directory
  with Sys_error _ | Unix.Unix_error _ -> false

let rocq_inputs_name = ".soma-inputs"

let record_rocq_inputs ~directory ~complete files =
  let file = Filename.concat directory rocq_inputs_name in
  let rows = List.sort_uniq compare files |> List.map (fun (f, expected) ->
      if SomaMerkle.file_hash f <> expected then
        CErrors.user_err Pp.(str "Rocq library source changed while recording its inputs; build again.");
      (* Input metadata is resolved against the build root, not the root
         discovered by walking upward from each external library source. *)
      let root = Unix.realpath (built_root ()) and file = Unix.realpath f in
      let path = if CString.is_prefix (root ^ "/") file then
          String.sub file (String.length root + 1) (String.length file - String.length root - 1)
        else file in
      Printf.sprintf "input %S %s" path expected) in
  Out_channel.with_open_bin file (fun oc ->
      output_string oc ((if complete then "soma-rocq-inputs 1" else "incomplete") ^ "\n" ^
                        String.concat "\n" rows ^ "\n"));
  SomaCache.record file

let rocq_entry file =
  if not (CString.is_prefix (project_cache () ^ "/") file) then None else
  let rec find dir =
    let parent = Filename.dirname dir in
    if Filename.basename parent = "rocq" then Some dir
    else if dir = parent then None else find parent in
  find (Filename.dirname file)

let rocq_inputs checked file =
  match rocq_entry file with
  | None -> None
  | Some directory ->
    let entry = match Hashtbl.find_opt checked directory with
      | Some entry -> entry
      | None ->
        let entry = SomaRocqCache.load ~key:(Filename.basename directory) ~directory ~resolve_input:resolve_project_file in
        Hashtbl.add checked directory entry;
        entry in
    (match entry with
     | Some entry when entry.SomaRocqCache.inputs_complete ->
       (match SomaRocqCache.artifact_digest entry ~directory ~file with
        | Some digest -> Some (entry.SomaRocqCache.inputs, digest)
        | None -> None)
     | _ -> None)

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
      | None -> ()) (read_load_paths ())

let is_folder_rules f =
  Filename.check_suffix f ".ext" &&
  let base = Filename.remove_extension f in
  let dir = CUnix.canonical_path_name (Filename.dirname (absolute f)) in
  Filename.basename base = (if SomaProject.find_root dir = Some dir then root_rules_name dir else Filename.basename dir) &&
  not (Sys.file_exists (base ^ ".soma"))

(* Soma: proofs checked beside the build.

   A file with a FILE.exp is compiled twice. First without the proofs of its
   lemmas, left delayed and unchecked: what its importers need, its definitions and the
   statements of its lemmas, ready in the time its program takes. Then,
   beside the build, whole, into the same .vo. The two are the same library:
   a .vo has its proofs in a segment of their own ("opaques"), and Rocq
   identifies a library by the rest ("library"). So the build goes on to
   the importers at once, while proofs are checked, as many at a time as
   there are processors ($SOMA_PROOF_JOBS; 0 checks each file's proofs
   before going on, as one compilation).

   The compilation that starts a build (toplevel/ccompile.ml) makes a
   folder for it, $SOMA_PROOF_JOBS_DIR, which every compilation of the build
   shares:
   - ready-ID: ID is compiled for this build, whether or not its proofs are
     checked yet (its stamp comes from the compilation that checks them);
   - lock-ID: held by the compilation compiling ID, so that two compiling at
     once (see [ensure_all]) don't both compile it;
   - job-ID, log-ID, status-ID: a proof check, its output, and how it ended;
   - slot-N: one for each proof check that runs at once.
   The build waits for every proof check before it is done, and fails with
   the errors of one that failed. Only a compilation that checked the proofs
   writes a stamp, so a build stopped before its checks are done leaves no
   file that looks up to date without them. *)

let jobs_var = "SOMA_PROOF_JOBS_DIR"
let slots_var = "SOMA_PROOF_JOBS"
let proof_job_var = "SOMA_PROOF_JOB"
let interface_var = "SOMA_INTERFACE"
let interface_digest_var = "SOMA_INTERFACE_DIGEST"

let jobs_dir () = env_value jobs_var
let is_interface () = env_value interface_var <> None
let proof_job () = env_value proof_job_var

let job_file dir kind id =
  Filename.concat dir (kind ^ "-" ^ String.map (function '/' -> '+' | c -> c) id)

let is_ready dir id = Sys.file_exists (job_file dir "ready" id)
let mark_ready dir id = close_out (open_out_bin (job_file dir "ready" id))

(* The locks this compilation holds. A lock (lockf) is a process's: taken
   again by the same process, it is granted, and closing either releases
   it. So one held here is busy here too, until [unlock]. *)
let held : (string, Unix.file_descr) Hashtbl.t = Hashtbl.create 17

(* The lock [file], if no compilation holds it, this one included *)
let try_lock file =
  if Hashtbl.mem held file then None else
  match Unix.openfile file [Unix.O_RDWR; Unix.O_CREAT; Unix.O_CLOEXEC] 0o600 with
  | exception Unix.Unix_error (Unix.ENOENT, _, _) ->
    (* the build's folder is gone: the build that started this compilation
       is over, and has said why *)
    exit 1
  | fd ->
    match Unix.lockf fd Unix.F_TLOCK 0 with
    | () -> Hashtbl.replace held file fd; Some (file, fd)
    | exception Unix.Unix_error ((Unix.EAGAIN | Unix.EACCES | Unix.EWOULDBLOCK), _, _) ->
      Unix.close fd; None

let unlock (file, fd) =
  Hashtbl.remove held file;
  Unix.close fd

(* A file whose proofs are checked beside the build: one with a .exp, when
   $SOMA_DEFER_PROOFS is 1. Not by default: a library compiled without its
   proofs is the same library only when its proofs add no universe
   constraints between global universes, which Rocq keeps in the library,
   and many proofs about gradual programs add some. Importers compiled
   against it would then not load with it; a proof check that finds its
   library different fails the build, and says so. *)
let has_proofs src =
  env_value "SOMA_DEFER_PROOFS" = Some "1" &&
  (Filename.check_suffix src ".soma" || Filename.check_suffix src ".definition" || is_folder_rules src)
  && Sys.file_exists (Filename.remove_extension src ^ ".exp")

(* What compiles [path]: the program, its arguments and its environment.
   [interface]: without the proofs of its lemmas, into PATH.vos. *)
let compile_command ?loc ?(delayed=false) ?expected_source ~interface p path src =
  let expected_source = match expected_source with
    | Some expected -> require_source_snapshot src expected; expected
    | None -> source_hash src in
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
  let env = Array.of_list (
      List.filter (fun v -> not (List.exists (fun k -> String.starts_with ~prefix:(k ^ "=") v)
                                   [loaded_source_inputs_var; loaded_source_request_var; root_var; stack_var; stamp_var; source_var; expected_source_var; cache_var; prefix_var; build_var; "SOMA_MIRAGE_BUILD"; "SOMA_OCAML_BUILD"; "SOMA_OCAML_EXTRACT"; "SOMA_REVIEW"; "SOMA_HASH"; "SOMA_HASH_FIELDS"; "SOMA_SEARCH"; "SOMA_SEARCH_OUT"; "SOMA_SEARCH_OPTIONS"; "SOMA_WASM_FILE"; "SOMA_BUILD_CHECKED_IMPORTS"; "SOMA_BUILD_PRODUCTS"; "SOMA_BUILD_INPUTS"; "SOMA_BUILD_EXTERNAL"; "SOMA_MIRAGE_ARGV"; proof_job_var; interface_var; interface_digest_var]))
        (Array.to_list (Unix.environment ()))
      @ [ root_var ^ "=" ^ p.root;
          cache_var ^ "=" ^ p.cache_dir;
          prefix_var ^ "=" ^ p.prefix;
          build_var ^ "=" ^ build_root ?loc ();
          stack_var ^ "=" ^ String.concat ":" (stack ?loc () @ [qualified p path]);
          stamp_var ^ "=" ^ stamp_of p path;
          source_var ^ "=" ^ src;
          expected_source_var ^ "=" ^ expected_source;
          (* what a program imports is not a unikernel of its own *)
          "SOMA_MIRAGE_BUILD=0"; "SOMA_OCAML_BUILD=0" ] @ module_file
      @ (if interface then [ interface_var ^ "=1" ] else [])) in
  let prog = Boot.Env.self in
  (* the cache in the load path names the library by its place there:
     .soma-cache/models/task.vo is models.task; that of a dependency, by
     its name too: maps.a.b *)
  (* without its proofs: they are delayed, and never forced (Rocq's lazy
     asynchronous proofs), and its .vo is saved without them, as PATH.vos
     (toplevel/ccompile.ml). Its proof check delays them the same way, and
     forces them at the end: the universes of its statements are then the
     same as without them, and so is its library. *)
  let argv = Array.of_list ([ prog; "--kind=compile"; input; "-o"; vo; "-Q"; p.cache_dir; p.prefix ]
                            @ (if interface || delayed then [ "-async-proofs"; "lazy" ] else [])) in
  prog, argv, env, expected_source

(* Starts a compilation, its output discarded and its errors shown *)
let start_compile_process prog argv env =
  let null = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
  let pid = Unix.create_process_env prog argv env Unix.stdin null Unix.stderr in
  Unix.close null;
  pid

let rec wait_pid pid = try snd (Unix.waitpid [] pid)
  with Unix.Unix_error (Unix.EINTR, _, _) -> wait_pid pid

(* How the compilation of [path] ended: nothing when it succeeded *)
let compiled ?loc p path src status =
  let import_name = String.map (function '/' -> '.' | c -> c) (qualified p path) in
  let file = qualified p path ^ Filename.extension src in
  match status with
  | Unix.WEXITED 0 ->
    (* the folder's listing, if read before, does not have the new file *)
    System.forget_dir p.cache_dir
  | Unix.WSIGNALED _ as status ->
    CUnix.report_compile_signal file status;
    CErrors.user_err ?loc Pp.(str "Cannot import " ++ str import_name ++
                              str ": " ++ str file ++ str " was killed while compiling (see the line above).")
  | Unix.WSTOPPED _ as status ->
    CUnix.report_compile_signal file status;
    CErrors.user_err ?loc Pp.(str "Cannot import " ++ str import_name ++
                              str ": " ++ str file ++ str " was stopped while compiling (see the line above).")
  | Unix.WEXITED _ ->
    CErrors.user_err ?loc Pp.(str "Cannot import " ++ str import_name ++
                              str ": " ++ str file ++
                              str " does not compile (its errors are above).")

let say_compiling p path src =
  Printf.eprintf "Compiling %s (into %s)\n%!" (qualified p path ^ Filename.extension src) cache_name

(* [path] compiled without its proofs is what its importers need: in place,
   as PATH.vo, and its proofs checked beside the build, into the same .vo *)
let check_proofs_beside dir ?loc ~expected_source p path src =
  require_source_snapshot src expected_source;
  let vo = vo_of p path in
  Sys.rename (vo ^ "s") vo;
  let id = qualified p path in
  let prog, argv, env, _ = compile_command ?loc ~delayed:true ~expected_source ~interface:false p path src in
  let env = Array.append env
      [| proof_job_var ^ "=" ^ id; interface_digest_var ^ "=" ^ interface_digest vo |] in
  let flags = [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC; Unix.O_CLOEXEC] in
  let log = Unix.openfile (job_file dir "log" id) flags 0o600 in
  let null = Unix.openfile "/dev/null" [Unix.O_RDONLY; Unix.O_CLOEXEC] 0 in
  let pid = Unix.create_process_env prog argv env null log log in
  Unix.close log;
  Unix.close null;
  Out_channel.with_open_bin (job_file dir "job" id) (fun oc ->
      Printf.fprintf oc "%d\n%s\n" pid (qualified p path ^ ".exp"))

let compile ?loc p path src =
  say_compiling p path src;
  match jobs_dir () with
  | Some dir when has_proofs src ->
    let prog, argv, env, expected_source = compile_command ?loc ~interface:true p path src in
    compiled ?loc p path src (wait_pid (start_compile_process prog argv env));
    check_proofs_beside dir ?loc ~expected_source p path src
  | _ ->
    let prog, argv, env, _ = compile_command ?loc ~interface:false p path src in
    compiled ?loc p path src (wait_pid (start_compile_process prog argv env))

(* Compilations this one started and has not waited for ([ensure_all]): what
   to do when each ends, and the lock it releases then *)
type running = { pid : int; lock : string * Unix.file_descr; finish : Unix.process_status -> unit }

let running : running list ref = ref []

(* A compilation that ends early (an error) stops those it started *)
let () = at_exit (fun () ->
    List.iter (fun r -> try Unix.kill r.pid Sys.sigterm with Unix.Unix_error _ -> ()) !running)

(* Waits for one of [running] to end, or, without [block], only takes one
   that has: whether one did *)
let rec reap ~block =
  match !running with
  | [] -> false
  | rs ->
    let ended = List.find_map (fun r ->
        match Unix.waitpid [Unix.WNOHANG] r.pid with
        | 0, _ -> None
        | _, status -> Some (r, status)
        | exception Unix.Unix_error (Unix.EINTR, _, _) -> None) rs in
    match ended with
    | Some (r, status) ->
      running := List.filter (fun x -> x.pid <> r.pid) !running;
      (* what it compiled is in place, and ready, before another takes the lock *)
      Fun.protect ~finally:(fun () -> unlock r.lock) (fun () -> r.finish status);
      true
    | None ->
      if block then (Unix.sleepf 0.01; reap ~block) else false

(* The lock of [id], once no other compilation holds it; None when [id] is
   ready meanwhile. Waiting, this one still takes what it started that
   ended: one may be what the holder of the lock waits for. *)
let rec acquire dir id =
  if is_ready dir id then None
  else match try_lock (job_file dir "lock" id) with
    | Some lock -> if is_ready dir id then (unlock lock; None) else Some lock
    | None -> ignore (reap ~block:false); Unix.sleepf 0.01; acquire dir id

(* [path] (whose source is [src]) compiled and up to date in the cache *)
let rec ensure ?loc p path src =
  let id = qualified p path in
  if not (Hashtbl.mem ensured id) then begin
    let stack = stack ?loc () in
    if List.mem id stack then
      CErrors.user_err ?loc Pp.(str "Import cycle: " ++
                                str (String.concat " -> " (stack @ [id])) ++ str ".");
    begin match jobs_dir () with
      | None -> if not (fresh ?loc p path src) then compile ?loc p path src
      | Some dir ->
        match acquire dir id with
        | None -> ()
        | Some lock ->
          Fun.protect ~finally:(fun () -> unlock lock) (fun () ->
              if not (fresh ?loc p path src) then compile ?loc p path src;
              mark_ready dir id)
    end;
    Hashtbl.replace ensured id ()
  end

(* Whether the cache has [path] as its stamp says, and up to date: its
   source unchanged, and what it imports as it was *)
and fresh ?loc p path src =
  let vo = vo_of p path in
  not !loaded_sources_uncertain && SomaCache.trusted vo && SomaCache.trusted (stamp_of p path) && match read_stamp (stamp_of p path) with
  | None -> false
  | Some (hash, imports, libraries, inputs) ->
    hash = source_hash src &&
    List.for_all (fun (path, expected) ->
        try SomaMerkle.file_hash (resolve_project_file path) = expected
        with Sys_error _ | Unix.Unix_error _ -> false) inputs &&
    List.for_all (fun (l, d) -> match library_file (Libnames.dirpath_of_string l) with
        | Some f -> file_digest f = d
        | None -> false) libraries &&
    List.for_all (fun (i, d) -> match locate ?loc p i with
        | None -> false
        | Some (q, i, s) -> ensure ?loc q i s; interface_digest (vo_of q i) = d) imports

(* The files of one [Import], compiled at once when they need to be. One
   whose lock another compilation holds is left for after, when this one
   holds no lock: two waiting on each other's would wait forever. *)
let ensure_all ?loc targets =
  match jobs_dir (), targets with
  | None, _ | _, ([] | [_]) -> List.iter (fun (q, i, s) -> ensure ?loc q i s) targets
  | Some dir, _ ->
    let later = ref [] in
    List.iter (fun (q, i, s) ->
        let id = qualified q i in
        if Hashtbl.mem ensured id then ()
        else if List.mem id (stack ?loc ()) || is_ready dir id then ensure ?loc q i s
        else match try_lock (job_file dir "lock" id) with
          | None -> later := (q, i, s) :: !later
          | Some lock ->
            let started = ref false in
            Fun.protect ~finally:(fun () -> if not !started then unlock lock) (fun () ->
                if is_ready dir id then Hashtbl.replace ensured id ()
                else if fresh ?loc q i s then begin
                  mark_ready dir id;
                  Hashtbl.replace ensured id ()
                end else begin
                  say_compiling q i s;
                  let interface = has_proofs s in
                  let prog, argv, env, expected_source = compile_command ?loc ~interface q i s in
                  let pid = start_compile_process prog argv env in
                  started := true;
                  let finish status =
                    compiled ?loc q i s status;
                    if interface then check_proofs_beside dir ?loc ~expected_source q i s;
                    mark_ready dir id;
                    Hashtbl.replace ensured id () in
                  running := { pid; lock; finish } :: !running
                end)) targets;
    while reap ~block:true do () done;
    List.iter (fun (q, i, s) -> ensure ?loc q i s) (List.rev !later)

(* [Import] of these names, which are no modules in scope: those that are
   files of the project or of a dependency are compiled when needed. The
   names to require: those of the libraries. *)
let prepare ?loc qids =
  let p = current ?loc () in
  let found = List.map (fun qid -> qid, locate ?loc p (path_of_qualid qid)) qids in
  ensure_all ?loc (List.filter_map snd found);
  let any = ref false in
  let names = List.map (fun (qid, located) ->
      let path = path_of_qualid qid in
      match located with
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
        qid) found in
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

(* A program's extensions (macros and readers) were in FILE.lang and its
   expectations (lemmas and theorems) in FILE.proof; they are FILE.ext,
   read before the program, and FILE.exp, checked after it. A file left
   with its old name would be passed over without a word, its theorems
   unchecked, so one is an error that says how to rename it. *)
let renamed_extensions =
  [".lang", ".ext", "extensions (macros and readers)";
   ".proof", ".exp", "expectations (lemmas and theorems)"]

let refuse_old_names base =
  let base = if CString.is_prefix "./" base then String.sub base 2 (String.length base - 2) else base in
  List.iter (fun (old_ext, new_ext, what) ->
      let old_f = base ^ old_ext and new_f = base ^ new_ext in
      if Sys.file_exists old_f then
        CErrors.user_err Pp.(
          str old_f ++ str " is not read: a program's " ++ str what ++ str " are in " ++
          str (Filename.basename new_f) ++ str " now. " ++
          (if Sys.file_exists new_f
           then str "Move what it has into " ++ str new_f ++ str " and delete it."
           else str "Rename it: git mv " ++ str old_f ++ str " " ++ str new_f)))
    renamed_extensions

(* A folder's rules: X/X.ext, with its proofs in X/X.exp, apply to every
   Soma file under X/, as if each started with [Import X.X]; so they are
   compiled once, into the cache, and what they define, macros and
   theorems included, is the same for all. Unless X/X.soma exists: then
   they are its own, as for any program. *)
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
        else if Sys.file_exists (Filename.concat up (Filename.basename up ^ ".ext"))
             && not (Sys.file_exists (Filename.concat up (Filename.basename up ^ ".soma")))
        then Feedback.msg_warning Pp.(
            str (Filename.basename up ^ "/" ^ Filename.basename up ^ ".ext") ++
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
    (* the root's rules are ROOT/ROOT.ext, a folder X's X/X.ext *)
    let rec paths prefix = function
      | [] -> []
      | x :: rest -> let p = prefix ^ x in (p ^ "/" ^ x) :: paths (p ^ "/") rest in
    let self = Filename.concat dir (Filename.remove_extension (Filename.basename file)) in
    let rules = List.filter_map (fun path ->
        let base = Filename.concat root path in
        let lang = base ^ ".ext" in
        refuse_old_names base;
        if base = self || Sys.file_exists (base ^ ".soma") then None
        else if Sys.file_exists lang then Some (path, lang)
        else if Sys.file_exists (base ^ ".exp") then
          CErrors.user_err Pp.(str (path ^ ".exp") ++ str " has the proofs of the rules of its folder, " ++
                               str (path ^ ".ext") ++ str ", which does not exist.")
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
  | Some stamp, Some _src when stamp <> "" ->
    let expected = match expected_import_source () with Some h -> h | None -> assert false in
    let in_cache f = match env_value build_var, env_root () with
      | Some root, _ | None, Some root -> CString.is_prefix (cache root ^ "/") f
      | None, None -> false in
    let inputs = ref [] and complete = ref (not !rocq_selection_uncertified) in
    let checked_rocq = Hashtbl.create 7 and seen_inputs = Hashtbl.create 97 in
    let remember_input (path, digest) =
      match Hashtbl.find_opt seen_inputs path with
      | Some old when old <> digest -> complete := false
      | Some _ -> ()
      | None -> Hashtbl.add seen_inputs path digest; inputs := (path, digest) :: !inputs in
    let libraries = List.filter_map (fun (dir, file) ->
        if file = "<unavailable filename>" then (complete := false; None) else
        let f = absolute file in
        (match rocq_entry f with
         | Some _ ->
           (match rocq_inputs checked_rocq f with
            | Some (files, digest) ->
              List.iter remember_input files;
              Some ("library " ^ DirPath.to_string dir ^ " " ^ digest)
            | None -> complete := false; None)
         | None when not (in_cache f) -> Some ("library " ^ DirPath.to_string dir ^ " " ^ file_digest f)
         | None -> None)) (Library.loaded_library_files ()) in
    let input_lines = List.sort_uniq compare !inputs |> List.map (fun (path, hash) ->
        Printf.sprintf "input %S %s" path hash) in
    let lines = (if !complete then stamp_format else "soma-stamp incomplete") :: ("source " ^ expected) ::
                List.rev_map (fun (p, vo) -> "import " ^ p ^ " " ^ interface_digest vo) !imported @
                libraries @ input_lines in
    let tmp = Filename.temp_file ~temp_dir:(Filename.dirname stamp) ".soma-stamp-" ".tmp" in
    Fun.protect ~finally:(fun () -> remove_if_present tmp) (fun () ->
        Out_channel.with_open_bin tmp (fun oc -> output_string oc (String.concat "\n" lines ^ "\n"));
        publish_import_output ~tmp ~file:stamp);
    let vo = Filename.chop_suffix stamp ".stamp" ^ ".vo" in
    ignore (expected_import_source ());
    require_published_import_output vo;
    require_published_import_output stamp;
    SomaCache.record stamp;
    SomaCache.record vo;
    ignore (expected_import_source ());
    require_published_import_output vo;
    require_published_import_output stamp;
    if !complete then begin
      (match env_value root_var, env_value cache_var with
       | Some root, Some cache ->
         SomaModuleStore.record ~root ~cache
           ~prefix:(match env_value prefix_var with Some p -> p | None -> "") ~source:_src
           ~vo ~stamp ~expected
       | _ -> ());
      ignore (expected_import_source ());
      require_published_import_output vo;
      require_published_import_output stamp
    end
  | _ -> ()

(* Observational metadata only: the import stamps above keep their existing
   digests and continue to make exactly the same recompilation decisions. *)
let record_interface ~source ~dirpath ~vo_file =
  if is_soma_file source then begin
    let dir = Filename.concat (project_cache ()) ".interfaces" in
    mkdir_p dir;
    let name = DirPath.to_string dirpath in
    let file = Filename.concat dir name in
    let digest = Library.compiled_interface_digest vo_file in
    Out_channel.with_open_bin (file ^ ".tmp") (fun oc ->
        output_string oc ("interface " ^ name ^ " " ^ digest ^ "\n"));
    Sys.rename (file ^ ".tmp") file
  end

(* The test runner asks the compiler, rather than a second source parser,
   which project files it loaded. loaded_libraries includes indirect imports,
   imports from expectations, and those introduced by folder rules/macros.
   Only the requested entry point writes the trace; its imported compilers
   inherit the request too. This metadata never participates in compilation. *)
let collect_loaded_dependencies ~source =
  let p = current () in
  let prefix = p.cache_dir ^ "/" in
  let sources = ref [absolute source] and external_inputs = ref [] in
  let complete = ref (not !rocq_selection_uncertified) in
  let checked_rocq = Hashtbl.create 7 and seen_inputs = Hashtbl.create 97 in
  let add_input (path, hash) =
    let file = resolve_project_file path in
    match Hashtbl.find_opt seen_inputs file with
    | Some old -> if old <> hash then complete := false
    | None ->
    Hashtbl.add seen_inputs file hash;
    (try if SomaMerkle.file_hash file <> hash then complete := false
     with Sys_error _ | Unix.Unix_error _ -> complete := false);
    if CString.is_prefix (p.root ^ "/") file && not (CString.is_prefix prefix file)
    then sources := file :: !sources
    else external_inputs := (file, hash) :: !external_inputs in
  let visited = Hashtbl.create 17 in
  let rec visit path =
    if not (Hashtbl.mem visited path) then begin
      Hashtbl.add visited path ();
      (match source_of p.root path with
       | Some src -> sources := absolute src :: !sources
       | None -> complete := false);
      (* Untrusted or truncated stamps cannot certify a smaller graph.
         Deferred proof stamps also include expectation-only imports. *)
      match if SomaCache.trusted (stamp_of p path) && SomaCache.trusted (vo_of p path)
            then read_stamp (stamp_of p path) else None with
      | Some (_, imports, _, inputs) ->
        List.iter add_input inputs;
        List.iter (fun (path, _) -> visit path) imports
      | None -> complete := false
    end in
  let installed file = match Boot.Env.initialized () with
    | Some (Boot.Env.Env env) ->
      List.exists (fun dir -> CString.is_prefix (Boot.Env.Path.to_string dir ^ "/") file)
        [Boot.Env.coqlib env; Boot.Env.runtimelib env]
    | _ -> false in
  List.iter (fun (_, file) ->
      if file = "<unavailable filename>" then complete := false else
      let file = absolute file in
      if rocq_entry file <> None then
        (match rocq_inputs checked_rocq file with
         | Some (inputs, digest) -> List.iter add_input inputs; add_input (file, digest)
         | None -> complete := false)
      else if CString.is_prefix prefix file then
        let relative = String.sub file (String.length prefix)
            (String.length file - String.length prefix) |> Filename.remove_extension in
        visit relative
      else if not (installed file) then complete := false)
    (Library.loaded_library_files ());
  (* External project dependencies still require their own complete graph.
     Floating opam libraries likewise have no immutable resolution to certify. *)
  if dependencies () <> [] then complete := false;
  List.sort_uniq String.compare !sources, List.sort_uniq compare !external_inputs, !complete

let loaded_dependencies_certified ~source =
  let _, _, complete = collect_loaded_dependencies ~source in complete

let record_test_dependencies ~source =
  match Sys.getenv_opt "SOMA_TEST_SOURCE", Sys.getenv_opt "SOMA_TEST_DEPENDENCIES" with
  | Some requested, Some output when absolute source = requested ->
    let sources, external_inputs, complete = collect_loaded_dependencies ~source in
    Out_channel.with_open_bin output (fun oc ->
        output_string oc (if complete then "soma-test-dependencies 2\n" else "incomplete\n");
        List.iter (fun file -> Printf.fprintf oc "source %S\n" file) sources;
        List.iter (fun (file, hash) -> Printf.fprintf oc "external %S %s\n" file hash) external_inputs)
  | _ -> ()

(* Soma: proofs checked beside the build (see [check_proofs_beside]), as the
   compilations of a build see them *)

(* Whether this compilation made the build's folder of proof checks *)
let owns_jobs = ref false

let processors () =
  try
    let ic = Unix.open_process_args_in "getconf" [| "getconf"; "_NPROCESSORS_ONLN" |] in
    let n = Fun.protect ~finally:(fun () -> ignore (Unix.close_process_in ic))
        (fun () -> int_of_string_opt (String.trim (In_channel.input_all ic))) in
    match n with Some n when n > 0 -> n | _ -> 4
  with Unix.Unix_error _ | Sys_error _ -> 4

let jobs_of_dir dir =
  Array.to_list (try Sys.readdir dir with Sys_error _ -> [||])
  |> List.filter (String.starts_with ~prefix:"job-")
  |> List.filter_map (fun name ->
      let id = String.sub name 4 (String.length name - 4) in
      match In_channel.with_open_bin (Filename.concat dir name) In_channel.input_all
            |> String.split_on_char '\n' with
      | pid :: label :: _ -> Option.map (fun pid -> id, pid, label) (int_of_string_opt pid)
      | _ | exception Sys_error _ -> None)

let read_status dir id =
  let f = Filename.concat dir ("status-" ^ id) in
  if Sys.file_exists f then Some (String.trim (In_channel.with_open_bin f In_channel.input_all)) else None

let remove_tree dir =
  Array.iter (fun f -> try Sys.remove (Filename.concat dir f) with Sys_error _ -> ())
    (try Sys.readdir dir with Sys_error _ -> [||]);
  try Unix.rmdir dir with Unix.Unix_error _ -> ()

(* The compilation that starts a build (that of the program, not one that an
   [Import] started) makes the build's folder, unless $SOMA_PROOF_JOBS is 0.
   Leaving early, it stops the checks it waits for. *)
let start_proof_jobs () =
  let starts_build = env_value stamp_var = None && jobs_dir () = None in
  let slots = match Option.bind (env_value slots_var) int_of_string_opt with
    | Some n -> n
    | None -> processors () in
  if starts_build && slots > 0 then begin
    let dir = Filename.concat (Filename.get_temp_dir_name ())
        (Printf.sprintf "soma-proofs-%d-%06x" (Unix.getpid ()) (Random.State.bits (Random.State.make_self_init ()))) in
    Unix.mkdir dir 0o700;
    Unix.putenv jobs_var dir;
    Unix.putenv slots_var (string_of_int slots);
    owns_jobs := true;
    at_exit (fun () ->
        if !owns_jobs then begin
          List.iter (fun (id, pid, _) ->
              if read_status dir id = None then (try Unix.kill pid Sys.sigterm with Unix.Unix_error _ -> ()))
            (jobs_of_dir dir);
          (* $SOMA_PROOF_JOBS_KEEP: the folder is kept, to read its logs *)
          if env_value "SOMA_PROOF_JOBS_KEEP" = None then remove_tree dir
          else Printf.eprintf "Proof checks kept in %s\n%!" dir
        end)
  end

(* Whether the process [pid] is gone; one of this compilation's, taken *)
let gone pid =
  match Unix.waitpid [Unix.WNOHANG] pid with
  | 0, _ -> false
  | _ -> true
  | exception Unix.Unix_error (Unix.ECHILD, _, _) ->
    (try Unix.kill pid 0; false with Unix.Unix_error (Unix.ESRCH, _, _) -> true)
  | exception Unix.Unix_error (Unix.EINTR, _, _) -> false

(* The build waits for its proof checks, before what reads proofs (the
   program's assumptions, its build), and fails if one failed, with its
   errors *)
let wait_proof_jobs () =
  match jobs_dir () with
  | Some dir when !owns_jobs ->
    let jobs = jobs_of_dir dir in
    let pending () = List.filter (fun (id, _, _) -> read_status dir id = None) jobs in
    (match pending () with
     | [] -> ()
     | p -> Printf.eprintf "Checking the proofs of %s\n%!"
              (String.concat ", " (List.rev_map (fun (_, _, label) -> label) p)));
    let rec wait () =
      let p = pending () in
      (* a check that ended without a status was killed *)
      let p = List.filter (fun (_, pid, _) -> not (gone pid)) p in
      if p <> [] then (Unix.sleepf 0.02; wait ()) in
    wait ();
    let failed = List.filter (fun (id, _, _) -> read_status dir id <> Some "ok") jobs in
    List.iter (fun (id, _, _) ->
        let log = Filename.concat dir ("log-" ^ id) in
        (try prerr_string (In_channel.with_open_bin log In_channel.input_all) with Sys_error _ -> ()))
      failed;
    flush stderr;
    (match failed with
     | [] -> ()
     | (id, _, label) :: _ ->
       let why = match read_status dir id with
         | Some "different" -> "its library is not the same with its proofs as without them: build again with SOMA_PROOF_JOBS=0, and report it"
         | Some _ -> "its proofs do not check (its errors are above)"
         | None -> "it was killed while its proofs were checked" in
       CErrors.user_err Pp.(str label ++ str ": " ++ str why ++ str "."))
  | _ -> ()

let job_status status =
  match jobs_dir (), proof_job () with
  | Some dir, Some id ->
    (try Out_channel.with_open_bin (job_file dir "status" id) (fun oc -> output_string oc status)
     with Sys_error _ -> ())
  | _ -> ()

(* A proof check runs once a slot is free, and says how it ended *)
let acquire_proof_slot () =
  match jobs_dir (), proof_job () with
  | Some dir, Some _ ->
    let done_ = ref false in
    at_exit (fun () -> if not !done_ then job_status "failed");
    let slots = match Option.bind (env_value slots_var) int_of_string_opt with
      | Some n when n > 0 -> n | _ -> 1 in
    let rec take () =
      match List.find_map (fun i -> try_lock (Filename.concat dir ("slot-" ^ string_of_int i)))
              (List.init slots Fun.id) with
      | Some _ -> () (* held until this compilation ends *)
      | None -> Unix.sleepf 0.05; take () in
    take ();
    fun () -> done_ := true; job_status "ok"
  | _ -> fun () -> ()

(* Where a proof check writes its .vo first, to put it in place whole:
   importers may be reading the one without proofs *)
let checked_output vo =
  match Sys.getenv_opt stamp_var, proof_job () with
  | Some stamp, _ when stamp <> "" ->
    (match Hashtbl.find_opt import_outputs vo with
     | Some tmp -> tmp
     | None ->
       let tmp = Filename.temp_file ~temp_dir:(Filename.dirname vo)
           ".soma-import-" (Filename.extension vo) in
       Hashtbl.add import_outputs vo tmp;
       tmp)
  | _, Some _ -> Filename.chop_suffix vo ".vo" ^ ".checking.vo"
  | _ -> vo

(* The .vo of a proof check in place, if it is the library its importers
   compiled against: the same values, though not always the same bytes (two
   compilations share values differently in memory, and Marshal writes
   what is shared once). So it is put in place with the bytes of the one
   they compiled against, which Rocq identifies the library by, and its
   own proofs and VM code. *)
let install_checked ~vo =
  let tmp = checked_output vo in
  if tmp <> vo then begin
    ignore (expected_import_source ());
    if proof_job () = None then publish_import_output ~tmp ~file:vo
    else begin
    let segments = ["summary"; "library"] in
    if not (Sys.file_exists vo && ObjFile.same_values tmp vo segments) then begin
      job_status "different";
      CErrors.user_err Pp.(str (Filename.basename vo) ++ str ": the library with its proofs is not the one without them: its proofs add universe constraints, which Rocq keeps in the library. Build without SOMA_DEFER_PROOFS=1.")
    end;
    let spliced = Filename.temp_file ~temp_dir:(Filename.dirname vo) ".soma-spliced-" ".vo" in
    Hashtbl.replace import_outputs tmp tmp;
    Hashtbl.replace import_outputs vo spliced;
    ObjFile.splice ~base:tmp ~from:vo segments ~out:spliced;
    Sys.remove tmp;
    Hashtbl.remove import_outputs tmp;
    (* what importers compiled against, by construction *)
    (match env_value interface_digest_var with
     | Some d when interface_digest spliced <> d ->
       job_status "different";
       CErrors.user_err Pp.(str (Filename.basename vo) ++ str ": the library with its proofs is not the one without them: its proofs add universe constraints, which Rocq keeps in the library. Build without SOMA_DEFER_PROOFS=1.")
     | _ -> ());
    publish_import_output ~tmp:spliced ~file:vo
    end
  end
