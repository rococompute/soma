(* Change-aware Soma test entry points. The compiler supplies the import graph;
   Git supplies the comparison, including dirty and untracked working files.
   Receipts also contain source hashes so an older/different cached graph can
   never silently exclude a test. Unknown inputs select the whole suite. *)
module S = Set.Make (String)
module M = Map.Make (String)
exception Error of string
exception Test_failure of int
let error fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

let help = {|Usage: soma test [PATH ...] [--changedSince REF] [--listTests] [--no-image]

Build/check .soma entry points and their paired .exp expectations. With no
paths, discover .soma files recursively under test/ and tests/. Explicit paths
may be files or directories. This does not boot images or run external scripts.

  --changedSince REF   Select tests affected since a Git commit/tag/branch,
                       including staged, unstaged and untracked changes.
  --listTests          Print selected paths only, without building or writing.
  --no-image           Check without building Mirage images, as soma build does.

Selection uses dependencies recorded by successful soma test builds. Missing
records, configuration/toolchain changes and uncertain dependencies select all
relevant tests. --changed-since and --list-tests are accepted spellings too.
|}

let read file = In_channel.with_open_bin file In_channel.input_all
let hash file = Digest.to_hex (Digest.file file)
let nul s = String.split_on_char '\000' s |> List.filter ((<>) "")
let lines s = String.split_on_char '\n' s |> List.filter ((<>) "")
let absolute p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p
let quoted line = Scanf.sscanf line "%S%!" Fun.id
let under root p = p = root || String.starts_with ~prefix:(root ^ "/") p
let relative root p =
  if not (under root p) || p = root then error "%s is outside %s" p root;
  String.sub p (String.length root + 1) (String.length p - String.length root - 1)

let capture args =
  let argv = Array.of_list ("git" :: args) in
  let ic = Unix.open_process_args_in "git" argv in
  let out = In_channel.input_all ic in
  match Unix.close_process_in ic with
  | Unix.WEXITED 0 -> out
  | _ -> error "git %s failed" (String.concat " " args)

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

let snapshot root repo =
  files root |> List.filter_map (fun p ->
      let full = Filename.concat repo p in
      if not (under root full) then None else
      match Unix.lstat full with
      | stat when stat.Unix.st_kind = Unix.S_REG -> Some (relative root full, hash full)
      | _ -> error "cannot track non-regular input %s" full
      | exception Unix.Unix_error (Unix.ENOENT, _, _) -> None)
  |> List.sort_uniq compare

let rec discover root path =
  let path = Unix.realpath path in
  if not (under root path) then error "test path %s is outside the project" path;
  match (Unix.lstat path).Unix.st_kind with
  | Unix.S_DIR ->
    Sys.readdir path |> Array.to_list |> List.sort String.compare
    |> List.filter (fun n -> n <> ".git" && n <> ".soma-cache" && n <> "_build" && n <> "node_modules")
    |> List.concat_map (fun n ->
        let child = Filename.concat path n in
        if (Unix.lstat child).Unix.st_kind = Unix.S_LNK then
          error "cannot discover tests through symbolic link %s" child;
        discover root child)
  | Unix.S_REG when Filename.check_suffix path ".soma" -> [relative root path]
  | Unix.S_REG -> []
  | _ -> error "cannot discover tests in %s" path

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

let affected ~identity ~inputs ~changed receipt =
  if receipt.identity <> identity then true else
  let delta = drift receipt.inputs inputs in
  let changed = S.union delta changed in
  (* An added/removed source may shadow an installed module or a folder rule.
     Ordinary edits can use the recorded graph. Unknown file kinds may be
     resources used by readers or native builds, so require the full suite. *)
  S.exists (fun p ->
      not (narrow p) ||
      (S.mem p delta && (not (List.mem_assoc p receipt.inputs) || not (List.mem_assoc p inputs))) ||
      S.mem p receipt.dependencies) changed

let run ~identity ~build args =
  let since = ref None and list_only = ref false and no_image = ref false in
  let rec options paths = function
    | [] -> List.rev paths
    | ("--changedSince" | "--changed-since") :: ref_ :: rest ->
      if !since <> None then error "--changedSince given twice";
      since := Some ref_; options paths rest
    | ("--listTests" | "--list-tests") :: rest -> list_only := true; options paths rest
    | "--no-image" :: rest -> no_image := true; options paths rest
    | "--" :: rest -> List.rev paths @ rest
    | arg :: _ when String.starts_with ~prefix:"-" arg -> error "unknown or incomplete option %s" arg
    | path :: rest -> options (path :: paths) rest in
  let paths = options [] args in
  let cwd = Unix.realpath (Sys.getcwd ()) in
  let repo = String.trim (capture ["rev-parse"; "--show-toplevel"]) |> Unix.realpath in
  let root = match project cwd with Some root -> root | None -> cwd in
  if not (under repo root) then error "project root must be inside the Git repository";
  let changed = match !since with
    | None -> S.empty
    | Some ref_ ->
      let commit = String.trim (capture ["rev-parse"; "--verify"; "--end-of-options"; ref_ ^ "^{commit}"]) in
      let tracked = capture ["-C"; root; "diff"; "--no-relative"; "--no-renames"; "--name-only"; "-z"; commit; "--"; "."] in
      let untracked = capture ["-C"; root; "ls-files"; "--full-name"; "--others"; "--exclude-standard"; "-z"; "--"; "."] in
      nul (tracked ^ untracked) |> List.filter (fun p -> not (generated p))
      |> List.map (fun p -> relative root (Filename.concat repo p)) |> S.of_list in
  let paths = if paths <> [] then paths else
      List.filter (fun p -> Sys.file_exists (Filename.concat root p)) ["test"; "tests"]
      |> List.map (Filename.concat root) in
  let tests = List.concat_map (fun p -> discover root (absolute p)) paths |> List.sort_uniq String.compare in
  let inputs = snapshot root repo in
  let identity = if tests = [] then "" else identity !no_image in
  let selected = List.filter (fun test ->
      !since = None ||
      try let receipt = load (record root test) in
        not (S.mem test receipt.dependencies) || affected ~identity ~inputs ~changed receipt
      with Error _ | Sys_error _ | Scanf.Scan_failure _ | End_of_file | Failure _ -> true) tests in
  if !list_only then List.iter print_endline selected else begin
    Printf.eprintf "soma test: %d of %d entry points selected%s\n%!" (List.length selected) (List.length tests)
      (if !since = None then "" else " (missing or uncertain records also run)");
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
              if List.exists (fun p -> not (List.mem_assoc p before))
                   (List.map (relative root) sources) then error "dependency is not tracked by Git discovery";
              if snapshot root repo <> before then error "project changed while the test was building";
              store receipt_file { identity; inputs = before; dependencies }
            with Error reason -> Printf.eprintf "soma test: %s: next run will include this test (%s)\n%!" test reason)) selected
  end
