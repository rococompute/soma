(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: a project's dependencies, the [dependencies] of its soma.toml
   (vernac/somaProject.ml): other Soma projects, fetched from git by tag, as
   Go fetches modules.

   Which version of each path: minimal version selection, the greatest
   that anything asks for, except that a version this project names is the
   one used, and must be at least what its dependencies ask for, and that
   a checkout on disk is used whatever they ask for. Resolving runs once,
   before any file is compiled, so that no later dependency can ask for a
   version already compiled.

   soma.lock, next to soma.toml, has the commit of each version selected,
   as tags move and commits do not. A build whose soma.lock matches its
   soma.toml uses those commits, and no network unless a commit is not on
   disk. Otherwise it resolves the tags and writes soma.lock.

   Sources are in $XDG_CACHE_HOME/soma/src (or ~/.cache/soma/src), one
   folder for each commit, without .git, shared by all projects. What they
   compile to is the project's, in its .soma-cache (vernac/somaImport.ml).
   Fetching runs nothing of the repository: no hooks, and no submodules. *)

open Pp

open SomaProject

type selected = {
  path : string;
  version : version;
  commit : string option;
  project : t;
}

let error msg = CErrors.user_err msg

(* an error at a line of the soma.toml of the project being built *)
let error_at line fmt =
  Printf.ksprintf (fun m -> error (str file_name ++ str ":" ++ int line ++ str ": " ++ str m)) fmt

let lock_name = "soma.lock"
let lock_marker = "# written by soma"

let read_file f = In_channel.with_open_bin f In_channel.input_all
let write_file f s = Out_channel.with_open_bin f (fun oc -> output_string oc s)

(* on stderr, which is the terminal for soma get and for a build alike *)
let warn fmt = Printf.ksprintf (fun m -> Printf.eprintf "Warning: %s\n%!" m) fmt

let short commit = String.sub commit 0 (min 7 (String.length commit))

(* * git *)

let git_failed args out =
  error (str "git failed: " ++ str (Filename.quote_command "git" args) ++ fnl () ++
         str (SomaOpam.tail_of_file out))

let check_git () =
  if not (SomaOpam.command_exists "git") then
    error (str "git is not installed, and Soma fetches dependencies with it." ++ spc () ++
           str "Install git, or depend on a checkout: \"owner/repo\" = { path = \"../repo\" }.")

(* [git args], in [dir] when given: its output when it succeeds. A repository
   that asks for a password fails, rather than waiting for one. *)
let git ?dir args =
  check_git ();
  Unix.putenv "GIT_TERMINAL_PROMPT" "0";
  if Sys.getenv_opt "GIT_SSH_COMMAND" = None && Sys.getenv_opt "GIT_SSH" = None then
    Unix.putenv "GIT_SSH_COMMAND" "ssh -oBatchMode=yes";
  let out = Filename.temp_file "soma-git" ".out" in
  let args = (match dir with Some d -> ["-C"; d] | None -> []) @ args in
  Fun.protect ~finally:(fun () -> try Sys.remove out with Sys_error _ -> ()) (fun () ->
      if SomaOpam.run ~log:out ("git" :: args) then read_file out
      else git_failed args out)

let remove_tree d = ignore (Sys.command (Filename.quote_command "rm" ["-rf"; d]))

(* the refs of a [git ls-remote]: name, commit; a tag's own object, and what
   an annotated tag points at, as NAME^{} *)
let refs_of output =
  List.filter_map (fun l -> match String.split_on_char '\t' l with
      | [commit; name] -> Some (name, commit)
      | _ -> None) (String.split_on_char '\n' output)

(* The commit of a tag: refs/tags/NAME, peeled when it is annotated *)
let tag_commit refs name =
  let r = "refs/tags/" ^ name in
  match List.assoc_opt (r ^ "^{}") refs with
  | Some c -> Some c
  | None -> List.assoc_opt r refs

(* the commit of the tag vVERSION or VERSION *)
let lookup_tag (p : dependency_path) version =
  let v = version_to_string version in
  let tags = ["v" ^ v; v] in
  let patterns = List.concat_map (fun t -> ["refs/tags/" ^ t; "refs/tags/" ^ t ^ "^{}"]) tags in
  let refs = refs_of (git (["ls-remote"; p.url] @ patterns)) in
  match List.filter_map (tag_commit refs) tags with
  | [] ->
    error (str p.canonical ++ str " " ++ str v ++ str ": no tag v" ++ str v ++ str " or " ++ str v ++
           str " on " ++ str p.url)
  | [c] -> c
  | a :: b :: _ when a = b -> a
  | a :: b :: _ ->
    error (str p.canonical ++ str " " ++ str v ++ str ": the tags v" ++ str v ++ str " and " ++ str v ++
           str " are two commits, " ++ str a ++ str " and " ++ str b ++ str ".")

let source_root () = Filename.concat (SomaOpam.cache_root ()) "src"

let source_dir ~path ~version ~commit =
  Filename.concat (source_root ())
    (Printf.sprintf "%s@%s-%s" path (version_to_string version) commit)

(* The repository at [commit], in the shared cache, once. It appears whole,
   or not at all: it is checked out beside it, and moved there. *)
let fetch (p : dependency_path) ~version ~commit =
  let dir = source_dir ~path:p.canonical ~version ~commit in
  if not (Sys.file_exists dir) then begin
    Printf.eprintf "Fetching %s %s (%s)\n%!" p.canonical (version_to_string version) (short commit);
    SomaOpam.mkdir_p (Filename.dirname dir);
    let tmp = Printf.sprintf "%s.tmp-%d" dir (Unix.getpid ()) in
    remove_tree tmp;
    Fun.protect ~finally:(fun () -> remove_tree tmp) (fun () ->
        Unix.mkdir tmp 0o755;
        ignore (git ~dir:tmp ["init"; "-q"]);
        (* one commit, when the host gives it by its id; or else all it has,
           as a commit of soma.lock need not be what its tag points at now, and
           a host need not give what it does not advertise *)
        (try ignore (git ~dir:tmp ["fetch"; "-q"; "--depth"; "1"; p.url; commit])
         with e when CErrors.noncritical e ->
           ignore (git ~dir:tmp ["fetch"; "-q"; p.url; "+refs/*:refs/remotes/all/*"]));
        (try ignore (git ~dir:tmp ["checkout"; "-q"; "--detach"; commit])
         with e when CErrors.noncritical e ->
           let v = version_to_string version in
           error (str p.canonical ++ str " " ++ str v ++ str ": the commit " ++ str commit ++
                  str " is no longer on " ++ str p.url ++ str ", and is not in the source cache." ++ spc () ++
                  str "Its tag was moved, and the history rewritten. What the tag is now is another" ++ spc () ++
                  str "program than the one soma.lock pinned: review it, then soma get writes it."));
        let got = String.trim (git ~dir:tmp ["rev-parse"; "HEAD"]) in
        if got <> commit then
          error (str p.canonical ++ str ": fetched " ++ str got ++ str ", which is not the commit " ++ str commit ++ str ".");
        remove_tree (Filename.concat tmp ".git");
        Sys.rename tmp dir)
  end;
  dir

(* The project a dependency fetched is *)
let load_fetched (p : dependency_path) ~version ~commit =
  let dir = CUnix.canonical_path_name (fetch p ~version ~commit) in
  let v = version_to_string version in
  if not (Sys.file_exists (Filename.concat dir file_name)) then
    error (str p.canonical ++ str " " ++ str v ++ str " (" ++ str commit ++ str "): the repository has no " ++
           str file_name ++ str ".");
  let project = load ~display:(p.canonical ^ " " ^ file_name) dir in
  List.iter (fun (d : dependency) -> match d.source with
      | Checkout _ ->
        error (str p.canonical ++ str " " ++ str file_name ++ str ":" ++ int d.line ++ str ": " ++
               str d.written ++ str " is a checkout on disk, which a project fetched by others cannot have.")
      | Version _ -> ()) project.dependencies;
  if compare_version project.version version <> 0 then
    warn "%s: the tag is %s, and its %s says %s." p.canonical v file_name (version_to_string project.version);
  project

(* * soma.lock *)

type entry = { e_path : string; e_version : version; e_commit : string option }

(* A locked commit becomes a folder name (in [fetch] and [cache_of]) and
   reaches git, so it is taken only as a full commit: exactly 40
   hexadecimal digits, lowercase, as git writes them and [write_lock]
   records them. A branch or tag name, an abbreviation, a leading [-],
   or a [/] or [..] in it is refused here, before any of that. *)
let is_commit s =
  let rec hex i =
    i = String.length s ||
    (match s.[i] with '0'..'9' | 'a'..'f' -> hex (i + 1) | _ -> false)
  in
  String.length s = 40 && hex 0

let read_lock root =
  let file = Filename.concat root lock_name in
  if not (Sys.file_exists file) then None else
  let wrong line fmt =
    Printf.ksprintf (fun m -> error (str lock_name ++ str ":" ++ int line ++ str ": " ++ str m ++ spc () ++
                                     str "It is written by soma: soma get writes it again.")) fmt in
  let toml = try SomaToml.parse (read_file file) with SomaToml.Error (line, m) -> wrong line "%s" m in
  List.iter (fun (k, { SomaToml.line; _ }) ->
      if k <> "resolved" then wrong line "%s is not something %s says." k lock_name) toml;
  let tables = match List.assoc_opt "resolved" toml with
    | None -> []
    | Some { SomaToml.value = Array l; _ } -> l
    | Some { SomaToml.line; _ } -> wrong line "resolved is an array of tables, [[resolved]]." in
  Some (List.map (function
      | SomaToml.Table t ->
        List.iter (fun (k, { SomaToml.line; _ }) ->
            if not (List.mem k ["path"; "version"; "commit"]) then
              wrong line "%s is not a key of [[resolved]], which has path, version and commit." k) t;
        let string k = match List.assoc_opt k t with
          | Some { SomaToml.value = String s; _ } -> Some s
          | _ -> None in
        let required k = match string k with
          | Some s -> s
          | None -> wrong 1 "an entry of [[resolved]] has no %s." k in
        let version = match parse_version (required "version") with
          | Ok v -> v
          | Error why -> wrong 1 "%s" why in
        let path = required "path" in
        let commit = match string "commit" with
          | None -> None
          | Some c when is_commit c -> Some c
          | Some c ->
            wrong 1 "%s: commit %S is not a full commit: a commit in %s is exactly 40 hexadecimal digits (0-9, a-f)."
              path c lock_name in
        { e_path = path; e_version = version; e_commit = commit }
      | _ -> wrong 1 "resolved is an array of tables, [[resolved]].") tables)

let write_lock root selected =
  let entry (s : selected) =
    Printf.sprintf "\n[[resolved]]\npath = %S\nversion = %S\n%s" s.path (version_to_string s.version)
      (match s.commit with Some c -> Printf.sprintf "commit = %S\n" c | None -> "") in
  let contents = lock_marker ^ "\n" ^ String.concat "" (List.map entry selected) in
  let file = Filename.concat root lock_name in
  if not (Sys.file_exists file && read_file file = contents) then write_file file contents

(* * The projects a build uses *)

(* A soma.lock that does not have what soma.toml asks *)
exception Stale

(* The checkouts on disk, from this project through those it names: path, folder *)
let checkouts top =
  let found = Hashtbl.create 7 in
  let rec go (p : t) =
    List.iter (fun (d : dependency) -> match d.source with
        | Version _ -> ()
        | Checkout dir ->
          match Hashtbl.find_opt found d.path.canonical with
          | Some other when other = dir -> ()
          | Some other ->
            error (str d.written ++ str " is two checkouts, " ++ str other ++ str " and " ++ str dir ++ str ".")
          | None ->
            Hashtbl.add found d.path.canonical dir;
            go (load dir)) p.dependencies in
  go top;
  found

let direct (top : t) canonical =
  List.find_opt (fun (d : dependency) -> d.path.canonical = canonical) top.dependencies

(* What the build uses: from [top], through the versions of [entries], each
   project once. [Stale] when [entries] do not have what a project asks. *)
let walk (top : t) entries =
  let local = checkouts top in
  let found = Hashtbl.create 17 in
  let rec visit stack (p : t) =
    List.iter (fun (d : dependency) ->
        let c = d.path.canonical in
        if List.mem c stack then begin
          let cycle = List.rev (c :: stack) in
          let rec from = function x :: _ as l when x = c -> l | _ :: r -> from r | [] -> [] in
          error (str "Dependency cycle: " ++ str (String.concat " -> " (from cycle)) ++ str ".")
        end;
        if not (Hashtbl.mem found c) then begin
          let s = match Hashtbl.find_opt local c with
            | Some dir ->
              let project = load dir in
              { path = c; version = project.version; commit = None; project }
            | None ->
              let e = match List.find_opt (fun e -> e.e_path = c) entries with
                | Some e -> e
                | None -> raise Stale in
              let commit = match e.e_commit with Some k -> k | None -> raise Stale in
              { path = c; version = e.e_version; commit = Some commit;
                project = load_fetched d.path ~version:e.e_version ~commit } in
          Hashtbl.add found c s;
          visit (c :: stack) s.project
        end;
        let s = Hashtbl.find found c in
        match d.source with
        | Version v when s.commit <> None ->
          if compare_version v s.version > 0 then raise Stale;
          (* what this project names, it gets *)
          if p == top && compare_version v s.version <> 0 then raise Stale
        | _ -> ()) p.dependencies in
  visit [] top;
  let all = Hashtbl.fold (fun _ s acc -> s :: acc) found [] in
  List.sort (fun (a : selected) (b : selected) -> compare a.path b.path) all

(* What must hold of the projects selected: a name imports one of them, and
   no file or folder of a project that depends on it *)
let check (top : t) selected =
  ignore (List.fold_left (fun seen (s : selected) ->
      (match List.find_opt (fun (o : selected) -> o.project.name = s.project.name) seen with
       | Some o ->
         let message = Printf.sprintf "%S is named %s, and so is %S. A dependency is imported by that name."
             s.path s.project.name o.path in
         (match direct top s.path with
          | Some d -> error_at d.line "%s" message
          | None -> error (str message))
       | None -> ());
      s :: seen) [] selected);
  let check_project shown (p : t) =
    List.iter (fun (d : dependency) ->
        match List.find_opt (fun (s : selected) -> s.path = d.path.canonical) selected with
        | None -> ()
        | Some s ->
          let name = s.project.name in
          let has = List.filter (fun f -> Sys.file_exists (Filename.concat p.root f))
              [name; name ^ ".soma"] in
          match has with
          | [] -> ()
          | f :: _ ->
            error (str shown ++ str ":" ++ int d.line ++ str ": the dependency " ++ str s.path ++
                   str " is named " ++ str name ++ str ", and this project has " ++ str f ++
                   str (if f = name then "/" else "") ++ str ". Import " ++ str name ++
                   str ".X is that, and not the dependency.")) p.dependencies in
  check_project file_name top;
  (* the project being built has no prefix: its util/ is the library util.*,
     which is also what a project named util compiles to, whoever brought it *)
  List.iter (fun (s : selected) ->
      let name = s.project.name in
      if Option.is_empty (direct top s.path) then
        match List.filter (fun f -> Sys.file_exists (Filename.concat top.root f)) [name; name ^ ".soma"] with
        | [] -> ()
        | f :: _ ->
          error (str file_name ++ str ": the dependency " ++ str s.path ++ str ", which a dependency of this project needs, is named " ++
                 str name ++ str ", and this project has " ++ str f ++ str (if f = name then "/" else "") ++
                 str ". Both would be the library " ++ str name ++ str ": rename this project's.")) selected;
  List.iter (fun (s : selected) -> check_project (s.path ^ " " ^ file_name) s.project) selected

(* Every version asked for, from the tags or what [known] has of them, and the
   greatest of each path, whose project may ask for more *)
let resolve (top : t) ~known =
  let local = checkouts top in
  let greatest = Hashtbl.create 17 in
  let commits = Hashtbl.create 17 in
  let visited = Hashtbl.create 17 in
  let commit_of (p : dependency_path) version =
    let key = p.canonical, version_to_string version in
    match Hashtbl.find_opt commits key with
    | Some c -> c
    | None ->
      let c = match List.find_opt (fun e -> e.e_path = p.canonical && compare_version e.e_version version = 0) known with
        | Some { e_commit = Some c; _ } -> c
        | _ -> lookup_tag p version in
      Hashtbl.add commits key c;
      c in
  let rec gather ~from (p : t) =
    List.iter (fun (d : dependency) ->
        let c = d.path.canonical in
        match Hashtbl.find_opt local c, d.source with
        | Some dir, _ ->
          if not (Hashtbl.mem visited (c, dir)) then begin
            Hashtbl.add visited (c, dir) ();
            gather ~from:c (load dir)
          end
        | None, Checkout _ -> assert false
        | None, Version v ->
          let v = match direct top c with
            | Some ({ source = Version named; _ } as line) when p != top ->
              if compare_version v named > 0 then
                error_at line.line "%S is %S here, and %S in %s. %S = %S"
                  line.written (version_to_string named) (version_to_string v) from
                  line.written (version_to_string v);
              named
            | _ -> v in
          (match Hashtbl.find_opt greatest c with
           | Some (_, g) when compare_version g v >= 0 -> ()
           | _ -> Hashtbl.replace greatest c (d.path, v));
          let key = c, version_to_string v in
          if not (Hashtbl.mem visited key) then begin
            Hashtbl.add visited key ();
            let commit = commit_of d.path v in
            gather ~from:c (load_fetched d.path ~version:v ~commit)
          end) p.dependencies in
  gather ~from:"this project" top;
  let entries = Hashtbl.fold (fun c ((p : dependency_path), v) acc ->
      { e_path = c; e_version = v; e_commit = Some (commit_of p v) } :: acc) greatest [] in
  let selected = walk top entries in
  check top selected;
  write_lock top.root selected;
  selected

let empty_lock root =
  let file = Filename.concat root lock_name in
  if Sys.file_exists file && String.starts_with ~prefix:lock_marker (read_file file) then Sys.remove file

let ensure (top : t) =
  if top.dependencies = [] then (empty_lock top.root; [])
  else
    let known = Option.default [] (read_lock top.root) in
    match read_lock top.root with
    | None -> resolve top ~known
    | Some entries ->
      match walk top entries with
      | selected when List.length selected = List.length entries ->
        check top selected;
        (* a checkout's version is its own, which may have moved *)
        write_lock top.root selected;
        selected
      | _ -> resolve top ~known
      | exception Stale -> resolve top ~known

let locked (top : t) =
  if top.dependencies = [] then []
  else
    let entries = Option.default [] (read_lock top.root) in
    try walk top entries
    with Stale -> error (str lock_name ++ str " changed during the build, in " ++ str top.root ++ str ".")

(* .soma-cache/.deps: a . keeps it out of the libraries of the project's own
   cache, as the load path does not read such folders *)
let cache_of ~root (s : selected) =
  let base = List.fold_left Filename.concat root [".soma-cache"; ".deps"] in
  match s.commit with
  | Some commit -> Filename.concat (Filename.concat base s.path) commit
  | None ->
    List.fold_left Filename.concat base
      ["local"; s.path; String.sub (Digest.to_hex (Digest.string s.project.root)) 0 8]

(* * soma get *)

(* the greatest tag of this path's major; a pre-release only when there is
   nothing else *)
let latest (p : dependency_path) =
  let refs = refs_of (git ["ls-remote"; "--tags"; p.url]) in
  let versions = List.filter_map (fun (name, _) ->
      let prefix = "refs/tags/" in
      if not (String.starts_with ~prefix name) || Filename.check_suffix name "^{}" then None else
      let tag = String.sub name (String.length prefix) (String.length name - String.length prefix) in
      let tag = if String.starts_with ~prefix:"v" tag then String.sub tag 1 (String.length tag - 1) else tag in
      match parse_version tag with
      | Ok v when v.build = [] &&
                  (match p.major with Some n -> v.major = n | None -> v.major < 2) -> Some v
      | _ -> None) refs in
  let pick l = List.fold_left (fun best v -> match best with
      | Some b when compare_version b v >= 0 -> best
      | _ -> Some v) None l in
  match pick (List.filter (fun v -> v.pre = []) versions), pick versions with
  | Some v, _ | None, Some v -> v
  | None, None ->
    error (str p.canonical ++ str ": no tag of major " ++
           str (match p.major with Some n -> string_of_int n | None -> "0 or 1") ++
           str " on " ++ str p.url ++ str ".")

let is_table_header l = let l = String.trim l in l <> "" && l.[0] = '['

(* soma.toml, with [line] replacing that of [existing], or added to [dependencies] *)
let with_line text ~existing ~line =
  let lines = String.split_on_char '\n' text in
  match existing with
  | Some (d : dependency) ->
    let current = List.nth lines (d.line - 1) in
    if not (String.starts_with ~prefix:(Printf.sprintf "%S" d.written) (String.trim current)) then
      error (str file_name ++ str ":" ++ int d.line ++ str ": soma get writes one line, " ++ str line ++
             str ", and " ++ str d.written ++ str " is not one line here: change it by hand.");
    String.concat "\n" (List.mapi (fun i l -> if i = d.line - 1 then line else l) lines)
  | None ->
    let is_header l =
      let l = String.trim l in
      String.starts_with ~prefix:"[dependencies]" l in
    if List.exists is_header lines then begin
      (* after the last line of the table that is not blank *)
      let rec go = function
        | [] -> []
        | l :: rest when is_header l ->
          let rec table seen = function
            | x :: r when not (is_table_header x) -> table (x :: seen) r
            | r -> seen, r in
          let body, after = table [] rest in
          let rec strip blank = function
            | x :: r when String.trim x = "" -> strip (x :: blank) r
            | r -> blank, r in
          let blank, body = strip [] body in
          l :: List.rev body @ [line] @ blank @ after
        | l :: rest -> l :: go rest in
      String.concat "\n" (go lines)
    end else
      let text = if text <> "" && text.[String.length text - 1] <> '\n' then text ^ "\n" else text in
      text ^ "\n[dependencies]\n" ^ line ^ "\n"

let get spec =
  let cwd = CUnix.canonical_path_name (Sys.getcwd ()) in
  let root = match find_root cwd with
    | Some r -> r
    | None ->
      error (str "No " ++ str file_name ++ str " in " ++ str cwd ++ str " or above: soma get writes a dependency into one." ++
             spc () ++ str "It begins:" ++ fnl () ++ fnl () ++
             str "[project]" ++ fnl () ++ str "name = \"my_project\"" ++ fnl () ++ str "version = \"0.1.0\"") in
  let file = Filename.concat root file_name in
  let before = read_file file in
  let top = load root in
  let written_new = match spec with
    | None -> false
    | Some spec ->
      let written, version = split_version spec in
      let path = match parse_path written with
        | Ok p -> p
        | Error why -> error (str why) in
      let version = match version with
        | None -> latest path
        | Some v ->
          let v = if String.starts_with ~prefix:"v" v then String.sub v 1 (String.length v - 1) else v in
          match parse_version v with
          | Error why -> error (str (Printf.sprintf "%S is no semantic version (https://semver.org): %s" v why))
          | Ok parsed ->
            (match check_dependency_version ~written path parsed with
             | Ok () -> parsed
             | Error why -> error (str why)) in
      let line = Printf.sprintf "%S = %S" written (version_to_string version) in
      let existing = direct top path.canonical in
      write_file file (with_line before ~existing ~line);
      true in
  try
    let top = if written_new then reload root else top in
    let known = [] in
    let previous = Option.default [] (read_lock root) in
    let selected = resolve top ~known in
    List.iter (fun (s : selected) ->
        (match s.commit, List.find_opt (fun e -> e.e_path = s.path && compare_version e.e_version s.version = 0) previous with
         | Some c, Some { e_commit = Some old; _ } when old <> c ->
           warn "%s %s: its tag has moved, from %s to %s." s.path (version_to_string s.version) old c
         | _ -> ());
        Printf.printf "%s %s (%s)\n" s.path (version_to_string s.version)
          (match s.commit with Some c -> short c | None -> "checkout " ^ s.project.root)) selected;
    if selected = [] then empty_lock root
  with e when CErrors.noncritical e ->
    if written_new then write_file file before;
    raise e

let fetched path version =
  load_fetched path ~version ~commit:(lookup_tag path version)
