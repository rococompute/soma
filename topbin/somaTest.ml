(* Change-aware Soma test entry points. The compiler supplies the import graph;
   Git supplies the comparison, including dirty and untracked working files.
   Receipts also contain source hashes so an older/different cached graph can
   never silently exclude a test. Unknown inputs select the whole suite. *)
module S = Set.Make (String)
module M = Map.Make (String)
exception Error of string
exception Test_failure of int
let error fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

let help = {|Usage: soma test [PATH ...] [--changedSince REF | --full] [--listTests] [--no-image]

Build/check .soma entry points and their paired .exp expectations. With no
paths, discover .soma files recursively under test/ and tests/. Explicit paths
may be files or directories. This does not boot images or run external scripts.

By default, use the first non-empty project diff in this order:
  1. Unstaged changes (including untracked files).
  2. Staged changes.
  3. HEAD compared with the current branch's remote-tracking branch.
  4. HEAD compared with the default branch.
Remote comparisons use local refs without fetching. If there is no usable
comparison, run the full suite. If comparisons exist but are empty, select no
tests except those with missing or uncertain dependency records.

  --changedSince REF   Select tests affected since a Git commit/tag/branch,
                       including staged, unstaged and untracked changes.
                       Overrides automatic diff selection.
  --full               Run every discovered entry point; incompatible with
                       --changedSince.
  --listTests          Print selected paths only, without building or writing.
  --no-image           Check without building Mirage images, as soma build does.

Selection uses dependencies recorded by successful soma test builds. Missing
records, configuration/toolchain changes and uncertain dependencies select all
relevant tests. Symbolic-link fixtures are supported within the project; links
outside it and sources inside Git submodules are not certified for skipping.
--full also works outside a Git checkout. --changed-since and --list-tests are
accepted spellings too.
|}

let read file = In_channel.with_open_bin file In_channel.input_all
let nul s = String.split_on_char '\000' s |> List.filter ((<>) "")
let lines s = String.split_on_char '\n' s |> List.filter ((<>) "")
let absolute p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p
let quoted line = Scanf.sscanf line "%S%!" Fun.id
let under root p = p = root || String.starts_with ~prefix:(root ^ "/") p
let relative root p =
  if not (under root p) || p = root then error "%s is outside %s" p root;
  String.sub p (String.length root + 1) (String.length p - String.length root - 1)

let capture_opt ?(quiet=false) args =
  try
  let argv = Array.of_list ("git" :: args) in
  let input, output = Unix.pipe ~cloexec:true () in
  let stderr = if quiet then Unix.openfile "/dev/null" [Unix.O_WRONLY; Unix.O_CLOEXEC] 0 else Unix.stderr in
  let pid = try Unix.create_process "git" argv Unix.stdin output stderr with exn ->
    Unix.close input; Unix.close output;
    if quiet then Unix.close stderr;
    raise exn in
  Unix.close output;
  if quiet then Unix.close stderr;
  let ic = Unix.in_channel_of_descr input in
  let out = Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () -> In_channel.input_all ic) in
  let rec wait () = try snd (Unix.waitpid [] pid) with Unix.Unix_error (Unix.EINTR, _, _) -> wait () in
  match wait () with
  | Unix.WEXITED 0 -> Some out
  | _ -> None
  with Unix.Unix_error (Unix.ENOENT, _, _) -> None

let capture args = match capture_opt args with
  | Some out -> out
  | None -> error "git %s failed" (String.concat " " args)

let rec mkdir dir =
  if not (Sys.file_exists dir) then begin
    mkdir (Filename.dirname dir);
    try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

let rec project dir =
  if Sys.file_exists (Filename.concat dir "soma.toml") then Some dir
  else let parent = Filename.dirname dir in
    if parent = dir then None else project parent

let generated p = List.exists (fun part ->
    List.mem part [".soma-cache"; "_build"; "node_modules"]) (String.split_on_char '/' p)

let files root =
  capture ["-C"; root; "ls-files"; "--full-name"; "-z"; "--cached";
           "--others"; "--exclude-standard"; "--"; "."] |> nul
  |> List.filter (fun p -> not (generated p))

(* Hash the descriptor we opened, and check that neither it nor the path
   changed during the read. An editor's rename/unlink is retried, never exposed
   as a raw Digest.file failure or certified as the former input. *)
let same_file a b =
  a.Unix.st_dev = b.Unix.st_dev && a.Unix.st_ino = b.Unix.st_ino &&
  a.Unix.st_kind = b.Unix.st_kind && a.Unix.st_size = b.Unix.st_size &&
  a.Unix.st_mtime = b.Unix.st_mtime && a.Unix.st_ctime = b.Unix.st_ctime

exception Changed_input
let regular_hash file expected =
  (* A path replaced by a FIFO must not block before its kind is checked. *)
  let fd = Unix.openfile file [Unix.O_RDONLY; Unix.O_NONBLOCK; Unix.O_CLOEXEC] 0 in
  let ic = Unix.in_channel_of_descr fd in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () ->
      let before = Unix.fstat fd in
      if not (same_file expected before) then raise Changed_input;
      let digest = Digest.to_hex (Digest.channel ic (-1)) in
      if not (same_file before (Unix.fstat fd)) ||
         not (same_file before (Unix.lstat file)) then raise Changed_input;
      digest)

let rec disk_files dir =
  Sys.readdir dir |> Array.to_list |> List.sort String.compare
  |> List.filter (fun name -> not (List.mem name [".git"; ".soma-cache"; "_build"; "node_modules"]))
  |> List.concat_map (fun name ->
      let file = Filename.concat dir name in
      match Unix.lstat file with
      | stat when stat.Unix.st_kind = Unix.S_DIR -> disk_files file
      | _ -> [file]
      | exception Unix.Unix_error (Unix.ENOENT, _, _) -> [])

let snapshot root repo =
  let paths = match repo with
    | Some repo -> files root |> List.map (Filename.concat repo) |> List.filter (under root)
    | None -> disk_files root in
  let one full =
    let rec attempt remaining =
      try
        let stat = Unix.lstat full in
        let digest = match stat.Unix.st_kind with
          | Unix.S_REG -> regular_hash full stat
          | Unix.S_LNK ->
            let target = Unix.readlink full in
            let contents = match Unix.realpath full with
              | path when under root path ->
                let target_stat = Unix.lstat path in
                if target_stat.Unix.st_kind = Unix.S_REG then regular_hash path target_stat else "directory"
              | _ -> "external"
              | exception Unix.Unix_error ((Unix.ENOENT | Unix.ENOTDIR | Unix.ELOOP), _, _) -> "unresolved" in
            if not (same_file stat (Unix.lstat full)) || Unix.readlink full <> target then raise Changed_input;
            Digest.to_hex (Digest.string ("symlink\000" ^ target ^ "\000" ^ contents))
          | Unix.S_DIR ->
            (* Git lists a gitlink as one directory, not as its sources. Keep
               its checkout state as an opaque input. A dependency inside it
               will fail the per-source coverage check below and always rerun. *)
            let initialized = Sys.file_exists (Filename.concat full ".git") in
            let state = match (if initialized then capture_opt ~quiet:true ["-C"; full; "rev-parse"; "HEAD"] else None) with
              | Some head -> head | None -> "uninitialized" in
            let dirty = match (if initialized then capture_opt ~quiet:true ["-C"; full; "status"; "--porcelain=v1"; "-z"; "--untracked-files=all"] else None) with
              | Some dirty -> dirty | None -> "unknown" in
            Digest.to_hex (Digest.string ("gitlink\000" ^ state ^ "\000" ^ dirty))
          | _ -> error "cannot track special input %s" full in
        Some (relative root full, digest)
      with
      | Unix.Unix_error ((Unix.ENOENT | Unix.ENOTDIR), _, _) -> None
      | Changed_input ->
        if remaining > 0 then attempt (remaining - 1)
        else error "input %s changed while taking the test snapshot; retry soma test" full
      | Sys_error reason ->
        if remaining > 0 then attempt (remaining - 1)
        else error "cannot snapshot input %s: %s" full reason
      | Unix.Unix_error (reason, _, _) ->
        error "cannot snapshot input %s: %s" full (Unix.error_message reason) in
    attempt 2 in
  List.filter_map one paths |> List.sort_uniq compare

let discover root path =
  let rec walk ancestors path =
    let resolved = Unix.realpath path in
    if not (under root resolved) then error "test path %s is outside the project" path;
    let stat = Unix.stat resolved in
    match stat.Unix.st_kind with
    | Unix.S_DIR ->
      let inode = stat.Unix.st_dev, stat.Unix.st_ino in
      if List.mem inode ancestors then [] else
      Sys.readdir resolved |> Array.to_list |> List.sort String.compare
      |> List.filter (fun n -> not (List.mem n [".git"; ".soma-cache"; "_build"; "node_modules"]))
      |> List.concat_map (fun name ->
          let child = Filename.concat resolved name in
          match Unix.realpath child with
          | _ -> walk (inode :: ancestors) child
          | exception Unix.Unix_error ((Unix.ENOENT | Unix.ENOTDIR | Unix.ELOOP), _, _) ->
            if Filename.check_suffix child ".soma" then error "cannot resolve test path %s" child else [])
    | Unix.S_REG when Filename.check_suffix resolved ".soma" -> [relative root resolved]
    | Unix.S_REG -> []
    | _ -> error "cannot discover tests in %s" path in
  walk [] path

let external_input root path =
  match Unix.lstat path with
  | _ -> (match Unix.realpath path with
      | resolved -> not (under root resolved)
      | exception Unix.Unix_error _ -> true)
  | exception Unix.Unix_error ((Unix.ENOENT | Unix.ENOTDIR), _, _) -> false

let source_extensions = [".soma"; ".exp"; ".ext"; ".definition"; ".wasm"; ".ml"; ".mli"; ".lean"]
let companions file =
  let stem = Filename.remove_extension file in
  List.map (fun ext -> stem ^ ext) source_extensions
let narrow file = List.exists (Filename.check_suffix file) [".soma"; ".exp"; ".definition"]
let record root test =
  Filename.concat root (".soma-cache/.tests/" ^ Digest.to_hex (Digest.string test))

type receipt = { identity : string; inputs : (string * string) list; dependencies : S.t }
let load file =
  if not (SomaCache.trusted file) then error "no trusted dependency record";
  match lines (read file) with
  | "soma-test 1" :: identity :: body ->
    let inputs = ref [] and dependencies = ref S.empty in
    List.iter (fun line ->
        if String.starts_with ~prefix:"input " line then
          inputs := Scanf.sscanf line "input %S %s%!" (fun p d -> p, d) :: !inputs
        else if String.starts_with ~prefix:"dependency " line then
          dependencies := S.add (Scanf.sscanf line "dependency %S%!" Fun.id) !dependencies
        else error "unknown test receipt field") body;
    if S.is_empty !dependencies then error "empty dependency record";
    { identity; inputs = List.sort_uniq compare !inputs; dependencies = !dependencies }
  | _ -> error "missing dependency record"

let store file receipt =
  mkdir (Filename.dirname file);
  let tmp = Filename.temp_file ~temp_dir:(Filename.dirname file) ".test-" ".tmp" in
  Fun.protect ~finally:(fun () -> if Sys.file_exists tmp then Sys.remove tmp) (fun () ->
      Out_channel.with_open_bin tmp (fun oc ->
          Printf.fprintf oc "soma-test 1\n%s\n" receipt.identity;
          List.iter (fun (p, d) -> Printf.fprintf oc "input %S %s\n" p d) receipt.inputs;
          S.iter (fun p -> Printf.fprintf oc "dependency %S\n" p) receipt.dependencies);
      Sys.rename tmp file;
      SomaCache.record file)

let drift before after =
  let map pairs = List.fold_left (fun m (p, d) -> M.add p d m) M.empty pairs in
  let before_map = map before and after_map = map after in
  List.filter_map (fun (p, d) -> if M.find_opt p after_map = Some d then None else Some p) before @
  List.filter_map (fun (p, d) -> if M.find_opt p before_map = Some d then None else Some p) after
  |> S.of_list

let affected ~identity ~inputs ~changed ~include_drift receipt =
  if receipt.identity <> identity then true else
  let delta = drift receipt.inputs inputs in
  (* An explicit baseline retains the historical snapshot-drift safeguard.
     Automatic mode deliberately focuses on one diff: lower-priority staged
     or committed edits must not silently become part of that diff. *)
  let changed = if include_drift then S.union delta changed else changed in
  (* An added/removed source may shadow an installed module or a folder rule.
     Ordinary edits can use the recorded graph. Unknown file kinds may be
     resources used by readers or native builds, so require the full suite. *)
  S.exists (fun p ->
      not (narrow p) ||
      (S.mem p delta && (not (List.mem_assoc p receipt.inputs) || not (List.mem_assoc p inputs))) ||
      S.mem p receipt.dependencies) changed

type selection = Full of string | Diff of S.t * string * bool

let changed_paths root repo output =
  nul output |> List.filter (fun p -> not (generated p))
  |> List.map (fun p -> relative root (Filename.concat repo p)) |> S.of_list

let diff root args =
  capture (["-C"; root; "diff"; "--no-relative"; "--no-renames"; "--name-only"; "-z"]
           @ args @ ["--"; "."])

let untracked root =
  capture ["-C"; root; "ls-files"; "--full-name"; "--others"; "--exclude-standard"; "-z"; "--"; "."]

let commit root ref_ =
  Option.map String.trim (capture_opt ["-C"; root; "rev-parse"; "--verify"; "--quiet";
                                      "--end-of-options"; ref_ ^ "^{commit}"])

let automatic root repo =
  let paths output = changed_paths root repo output in
  let unstaged = paths (diff root [] ^ untracked root) in
  if not (S.is_empty unstaged) then Diff (unstaged, "unstaged changes", false) else
  let staged = paths (diff root ["--cached"]) in
  if not (S.is_empty staged) then Diff (staged, "staged changes", false) else
  let optional args = match capture_opt (["-C"; root] @ args) with
    | Some out when String.trim out <> "" -> Some (String.trim out) | _ -> None in
  let branch = optional ["symbolic-ref"; "--quiet"; "--short"; "HEAD"] in
  let upstream = Option.bind branch (fun b ->
      optional ["for-each-ref"; "--format=%(upstream)"; "refs/heads/" ^ b]) in
  let remotes = lines (capture ["-C"; root; "remote"]) in
  let configured = Option.bind branch (fun b -> optional ["config"; "--get"; "branch." ^ b ^ ".remote"]) in
  let remote = match configured with
    | Some r when List.mem r remotes -> Some r
    | _ when List.mem "origin" remotes -> Some "origin"
    | _ -> (match remotes with [r] -> Some r | _ -> None) in
  let upstream = match upstream with
    | Some r when String.starts_with ~prefix:"refs/remotes/" r && commit root r <> None -> Some r
    | _ -> Option.bind remote (fun r -> Option.bind branch (fun b ->
        let ref_ = "refs/remotes/" ^ r ^ "/" ^ b in
        if commit root ref_ <> None then Some ref_ else None)) in
  let local_default () =
    match optional ["config"; "--get"; "init.defaultBranch"] with
    | Some b when commit root ("refs/heads/" ^ b) <> None -> Some ("refs/heads/" ^ b)
    | _ -> (match List.filter (fun r -> commit root r <> None) ["refs/heads/main"; "refs/heads/master"] with
        | [r] -> Some r | _ -> None) in
  let default = match remote with
    | Some r -> (match optional ["symbolic-ref"; "--quiet"; "refs/remotes/" ^ r ^ "/HEAD"] with
        | Some ref_ when commit root ref_ <> None -> Some ref_
        | _ -> local_default ())
    | None -> local_default () in
  let rec choose usable = function
    | [] -> if usable then Diff (S.empty, "no changes", false) else Full "no usable comparison"
    | (label, None) :: rest -> choose usable rest
    | (label, Some ref_) :: rest ->
      let changes = paths (diff root [ref_; "HEAD"]) in
      if S.is_empty changes then choose true rest else Diff (changes, label ^ " " ^ ref_, false) in
  choose false ["remote branch", upstream; "default branch", default]

let run ~identity ~build args =
  let since = ref None and full = ref false and list_only = ref false and no_image = ref false in
  let rec options paths = function
    | [] -> List.rev paths
    | ("--changedSince" | "--changed-since") :: ref_ :: rest ->
      if !since <> None then error "--changedSince given twice";
      since := Some ref_; options paths rest
    | "--full" :: rest -> full := true; options paths rest
    | ("--listTests" | "--list-tests") :: rest -> list_only := true; options paths rest
    | "--no-image" :: rest -> no_image := true; options paths rest
    | "--" :: rest -> List.rev paths @ rest
    | arg :: _ when String.starts_with ~prefix:"-" arg -> error "unknown or incomplete option %s" arg
    | path :: rest -> options (path :: paths) rest in
  let paths = options [] args in
  if !full && !since <> None then error "--full and --changedSince cannot be used together";
  let cwd = Unix.realpath (Sys.getcwd ()) in
  let repo = match capture_opt ~quiet:true ["rev-parse"; "--show-toplevel"] with
    | Some path -> Some (Unix.realpath (String.trim path))
    | None when !full -> None
    | None -> error "automatic and --changedSince selection require Git; use --full outside a checkout" in
  let root = match project cwd with Some root -> root | None -> cwd in
  Option.iter (fun repo -> if not (under repo root) then error "project root must be inside the Git repository") repo;
  let selection = match !full, !since with
    | true, _ -> Full "--full"
    | false, None -> automatic root (Option.get repo)
    | false, Some ref_ ->
      let base = match commit root ref_ with Some c -> c | None -> error "invalid Git commit %s" ref_ in
      Diff (changed_paths root (Option.get repo) (diff root [base] ^ untracked root), "since " ^ ref_, true) in
  let paths = if paths <> [] then paths else
      List.filter (fun p -> Sys.file_exists (Filename.concat root p)) ["test"; "tests"]
      |> List.map (Filename.concat root) in
  let tests = List.concat_map (fun p -> discover root (absolute p)) paths |> List.sort_uniq String.compare in
  let inputs = snapshot root repo in
  let identity = if tests = [] then "" else identity !no_image in
  let selected = List.filter (fun test ->
      match selection with
      | Full _ -> true
      | Diff (changed, _, include_drift) ->
        try let receipt = load (record root test) in
          not (S.mem test receipt.dependencies) || affected ~identity ~inputs ~changed ~include_drift receipt
        with Error _ | Sys_error _ | Scanf.Scan_failure _ | End_of_file | Failure _ -> true) tests in
  if !list_only then List.iter print_endline selected else begin
    let reason = match selection with Full reason -> reason | Diff (_, reason, _) -> reason ^ "; missing or uncertain records also run" in
    Printf.eprintf "soma test: %d of %d entry points selected (%s)\n%!" (List.length selected) (List.length tests) reason;
    List.iter (fun test ->
        let receipt_file = record root test in
        if Sys.file_exists receipt_file then Sys.remove receipt_file;
        let before = snapshot root repo in
        let trace = Filename.temp_file "soma-test-" ".deps" in
        Fun.protect ~finally:(fun () -> Sys.remove trace) (fun () ->
            Printf.eprintf "soma test: %s\n%!" test;
            let source = Filename.concat root test in
            let code = build ~source ~trace ~no_image:!no_image in
            if code <> 0 then raise (Test_failure code);
            try
              let sources = match lines (read trace) with
                | "soma-test-dependencies 1" :: paths -> List.map quoted paths
                | _ -> error "compiler could not record complete dependencies" in
              let dependencies = List.concat_map (fun p -> companions (relative root p)) sources |> S.of_list in
              if not (S.mem test dependencies) then error "entry point missing from dependencies";
              if S.exists (fun p -> external_input root (Filename.concat root p)) dependencies then
                error "a dependency resolves outside the project or through an unresolved link";
              if List.exists (fun p -> not (List.mem_assoc p before))
                   (List.map (relative root) sources) then error "dependency is not tracked by Git discovery";
              if snapshot root repo <> before then error "project changed while the test was building";
              store receipt_file { identity; inputs = before; dependencies }
            with Error reason -> Printf.eprintf "soma test: %s: next run will include this test (%s)\n%!" test reason)) selected
  end
