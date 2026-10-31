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

   The project is the folder of the program being built
   ($SOMA_PROJECT_ROOT for the compilations it starts). What is compiled
   goes to its .soma-cache, with a stamp: the hash of the source (with
   its .proof and .lang) and the digests of what it imports, as compiled.
   A cached file is used while its stamp holds: its source unchanged, and
   what it imports up to date and the same as when it was compiled. A
   file is compiled by a process of its own, which compiles what it
   imports in the same way. *)

open Names

let cache_name = ".soma-cache"

let root_var = "SOMA_PROJECT_ROOT"
let stack_var = "SOMA_IMPORT_STACK"
let stamp_var = "SOMA_IMPORT_STAMP"
let source_var = "SOMA_IMPORT_SOURCE"

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

let project_root ?loc () =
  match env_root () with
  | Some r -> r
  | None -> CUnix.canonical_path_name (match file_of_loc loc with
    | Some f -> Filename.dirname (absolute f)
    | None -> Sys.getcwd ())

let cache root = Filename.concat root cache_name

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

let vo_of root path = Filename.concat (cache root) (path ^ ".vo")
let stamp_of root path = Filename.concat (cache root) (path ^ ".stamp")

(* What a compilation reads of a program: its source, .proof and .lang *)
let source_hash src =
  let base = Filename.remove_extension src in
  let one f = if Sys.file_exists f then Digest.to_hex (Digest.file f) else "-" in
  (* and FILE.wasm, which FILE.definition declares *)
  Digest.to_hex (Digest.string (String.concat " " (List.map one [src; base ^ ".proof"; base ^ ".lang"; base ^ ".wasm"])))

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
let stack ?loc root = match Sys.getenv_opt stack_var with
  | Some s when s <> "" -> String.split_on_char ':' s
  | _ ->
    match file_of_loc loc with
    | Some f ->
      let f = Filename.concat (CUnix.canonical_path_name (Filename.dirname (absolute f)))
          (Filename.remove_extension (Filename.basename f)) in
      if CString.is_prefix (root ^ "/") f
      then [String.sub f (String.length root + 1) (String.length f - String.length root - 1)]
      else []
    | None -> []

let add_cache_to_loadpath root =
  Loadpath.add_vo_path { Loadpath.unix_path = cache root; coq_path = DirPath.empty;
                         implicit = false; recursive = true; installed = false }

let compile ?loc root path src =
  let vo = vo_of root path in
  mkdir_p (Filename.dirname vo);
  (* a module without a definition: an empty one, in the cache, for the
     module (SOMA_WASM_FILE, which toplevel/ccompile.ml reads) *)
  let module_file, input =
    if Filename.check_suffix src ".wasm" then begin
      let definition = Filename.concat (cache root) (path ^ ".definition") in
      Out_channel.with_open_bin definition (fun oc ->
          output_string oc ("(* " ^ Filename.basename src ^
                            " has no .definition: its exports are all of type Any *)\n"));
      [ "SOMA_WASM_FILE=" ^ src ], definition
    end else [], src in
  Printf.eprintf "Compiling %s (into %s)\n%!" (path ^ Filename.extension src) cache_name;
  let env = Array.of_list (
      List.filter (fun v -> not (List.exists (fun k -> String.starts_with ~prefix:(k ^ "=") v)
                                   [root_var; stack_var; stamp_var; source_var; "SOMA_MIRAGE_BUILD"; "SOMA_REVIEW"; "SOMA_WASM_FILE"]))
        (Array.to_list (Unix.environment ()))
      @ [ root_var ^ "=" ^ root;
          stack_var ^ "=" ^ String.concat ":" (stack ?loc root @ [path]);
          stamp_var ^ "=" ^ stamp_of root path;
          source_var ^ "=" ^ src;
          (* what a program imports is not a unikernel of its own *)
          "SOMA_MIRAGE_BUILD=0" ] @ module_file) in
  let prog = Sys.executable_name in
  (* the cache in the load path names the library by its place there:
     .soma-cache/models/task.vo is models.task *)
  let argv = [| prog; "--kind=compile"; input; "-o"; vo; "-Q"; cache root; "" |] in
  let null = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
  let pid = Unix.create_process_env prog argv env Unix.stdin null Unix.stderr in
  Unix.close null;
  let rec wait () = try snd (Unix.waitpid [] pid)
    with Unix.Unix_error (Unix.EINTR, _, _) -> wait () in
  match wait () with
  | Unix.WEXITED 0 ->
    (* the folder's listing, if read before, does not have the new file *)
    System.forget_dir (cache root)
  | _ ->
    CErrors.user_err ?loc Pp.(str "Cannot import " ++ str (String.map (function '/' -> '.' | c -> c) path) ++
                              str ": " ++ str (path ^ Filename.extension src) ++
                              str " does not compile (its errors are above).")

(* [path] (whose source is [src]) compiled and up to date in the cache *)
let rec ensure ?loc root path src =
  if not (Hashtbl.mem ensured path) then begin
    let stack = stack ?loc root in
    if List.mem path stack then
      CErrors.user_err ?loc Pp.(str "Import cycle: " ++
                                str (String.concat " -> " (stack @ [path])) ++ str ".");
    let vo = vo_of root path in
    let fresh = Sys.file_exists vo && match read_stamp (stamp_of root path) with
      | None -> false
      | Some (hash, imports, libraries) ->
        hash = source_hash src &&
        List.for_all (fun (l, d) -> match library_file (Libnames.dirpath_of_string l) with
            | Some f -> file_digest f = d
            | None -> false) libraries &&
        List.for_all (fun (p, d) -> match source_of root p with
            | None -> false
            | Some s -> ensure ?loc root p s; digest (vo_of root p) = d) imports
    in
    if not fresh then compile ?loc root path src;
    Hashtbl.replace ensured path ()
  end

(* [Import] of these names, which are no modules in scope: those that are
   files of the project are compiled when needed. True when any is. *)
let prepare ?loc qids =
  let root = project_root ?loc () in
  let any = List.fold_left (fun any qid ->
      let path = path_of_qualid qid in
      match source_of root path with
      | Some src ->
        ensure ?loc root path src;
        if not (List.mem_assoc path !imported) then
          imported := (path, vo_of root path) :: !imported;
        true
      | None -> any) false qids in
  if any then add_cache_to_loadpath root;
  any

(* A folder's rules: X/X.lang, with its proofs in X/X.proof, apply to every
   Soma file under X/, as if each started with [Import X.X]; so they are
   compiled once, into the cache, and what they define, macros and
   theorems included, is the same for all. Unless X/X.soma exists: then
   they are its own, as for any program. *)
let is_folder_rules f =
  Filename.check_suffix f ".lang" &&
  let base = Filename.remove_extension f in
  Filename.basename base = Filename.basename (Filename.dirname (absolute f)) &&
  not (Sys.file_exists (base ^ ".soma"))

(* The rules of the folders of the project from its root to [file]'s,
   outermost first, compiled when needed: the libraries to import *)
let folder_rules file =
  if not (is_soma_file file) then [] else
  let file = absolute file in
  let dir = CUnix.canonical_path_name (Filename.dirname file) in
  let root = match env_root () with
    | Some r -> r
    | None ->
      (* a file built by itself is the program; the rules of the folders
         above it are not its project's *)
      let rec above d =
        let up = Filename.dirname d in
        if up = d then ()
        else if Sys.file_exists (Filename.concat up (Filename.basename up ^ ".lang"))
             && not (Sys.file_exists (Filename.concat up (Filename.basename up ^ ".soma")))
        then Feedback.msg_warning Pp.(
            str (Filename.basename up ^ "/" ^ Filename.basename up ^ ".lang") ++
            str ", the rules of the folder " ++ str (Filename.basename up ^ "/") ++
            str " this file is under, does not apply to it when it is built by itself: build the program that imports it, or set " ++
            str root_var ++ str " to the folder of that program.")
        else above up in
      above dir;
      dir in
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
        else None) (Filename.basename root :: paths "" folders) in
    List.iter (fun (path, src) ->
        ensure root path src;
        if not (List.mem_assoc path !imported) then
          imported := (path, vo_of root path) :: !imported) rules;
    if rules <> [] then add_cache_to_loadpath root;
    List.map (fun (path, _) -> String.map (function '/' -> '.' | c -> c) path) rules

(* A compilation started by [compile] writes its stamp once it succeeded *)
let write_stamp () =
  match Sys.getenv_opt stamp_var, Sys.getenv_opt source_var with
  | Some stamp, Some src when stamp <> "" ->
    let in_cache f = match env_root () with
      | Some root -> CString.is_prefix (cache root ^ "/") f
      | None -> false in
    let libraries = List.filter_map (fun dir -> match library_file dir with
        | Some f when not (in_cache f) -> Some ("library " ^ DirPath.to_string dir ^ " " ^ file_digest f)
        | _ -> None) (Library.loaded_libraries ()) in
    let lines = stamp_format :: ("source " ^ source_hash src) ::
                List.rev_map (fun (p, vo) -> "import " ^ p ^ " " ^ digest vo) !imported @ libraries in
    Out_channel.with_open_bin stamp (fun oc -> output_string oc (String.concat "\n" lines ^ "\n"))
  | _ -> ()
