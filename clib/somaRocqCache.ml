(* A checkout can supply cache files, but cannot supply a producer receipt.
   A completion binds the selected key, source metadata, theory directories
   and the complete .vo set. No load path is accepted before that binding. *)
type entry = { completion_digest : string; theories : (string * string) list; inputs : (string * string) list; inputs_complete : bool; artifacts : (string * string) list }
let marker = ".soma-complete"
let inputs_name = ".soma-inputs"
let theory_name = "theories"
let under root path = path = root || String.starts_with ~prefix:(root ^ "/") path
let same a b =
  a.Unix.st_dev = b.Unix.st_dev && a.Unix.st_ino = b.Unix.st_ino &&
  a.Unix.st_kind = b.Unix.st_kind && a.Unix.st_size = b.Unix.st_size &&
  a.Unix.st_mtime = b.Unix.st_mtime && a.Unix.st_ctime = b.Unix.st_ctime
let invalid () = failwith "untrusted or changing Rocq cache entry"
let regular path f =
  let before = Unix.lstat path in
  if before.Unix.st_kind <> Unix.S_REG then invalid ();
  let fd = Unix.openfile path [Unix.O_RDONLY; Unix.O_NONBLOCK; Unix.O_CLOEXEC] 0 in
  let ic = Unix.in_channel_of_descr fd in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () ->
      if not (same before (Unix.fstat fd)) then invalid ();
      let result = f ic in
      if not (same before (Unix.fstat fd) && same before (Unix.lstat path)) then invalid ();
      result)
let read path = regular path In_channel.input_all
let hash path = regular path (fun ic -> SomaMerkle.channel ic)
let lines text =
  if text = "" || text.[String.length text - 1] <> '\n' then invalid ();
  let rows = String.split_on_char '\n' text in
  List.rev (List.tl (List.rev rows))
let safe_relative path =
  Filename.is_relative path && path <> "" && not (String.contains path '\000') &&
  List.for_all (fun p -> p <> "" && p <> "." && p <> "..") (String.split_on_char '/' path)
let relative directory path =
  let root = Unix.realpath directory and path = Unix.realpath path in
  if not (under root path) then invalid ();
  if root = path then "." else String.sub path (String.length root + 1) (String.length path - String.length root - 1)
let is_source path = Filename.check_suffix path ".v" ||
  List.mem (Filename.basename path) ["dune"; "_RocqProject"; "_CoqProject"]
let inventory directory =
  let rec walk depth relative_path dir =
    if depth > 128 then invalid ();
    let before = Unix.lstat dir in
    if before.Unix.st_kind <> Unix.S_DIR then invalid ();
    let names () = Array.to_list (Sys.readdir dir) |> List.sort String.compare in
    let entries = names () in
    let files = List.concat_map (fun name ->
        let path = Filename.concat dir name in
        let rel = if relative_path = "" then name else relative_path ^ "/" ^ name in
        match (Unix.lstat path).Unix.st_kind with
        | Unix.S_DIR -> walk (depth + 1) rel path
        | Unix.S_REG ->
          if relative_path = "" && List.mem name [marker; inputs_name; theory_name] then []
          else [rel, hash path]
        | _ -> invalid ()) entries in
    if names () <> entries || not (same before (Unix.lstat dir)) then invalid ();
    files in
  walk 0 "" directory |> List.sort compare
let source_snapshot ~directory = List.filter (fun (path, _) -> is_source path) (inventory directory)
let atomic file contents =
  let tmp = Filename.temp_file ~temp_dir:(Filename.dirname file) ".rocq-" ".tmp" in
  Fun.protect ~finally:(fun () -> if Sys.file_exists tmp then Sys.remove tmp) (fun () ->
      Out_channel.with_open_bin tmp (fun oc -> output_string oc contents);
      Sys.rename tmp file)
let publish ~key ~directory ~sources ~theories =
  let rows = List.map (fun (name, path) ->
      if name = "" || String.contains name '\000' then invalid ();
      Printf.sprintf "theory %S %S\n" name (relative directory path)) theories in
  if rows = [] then invalid ();
  let theory_file = Filename.concat directory theory_name in
  atomic theory_file ("soma-rocq-theories 2\n" ^ String.concat "" rows);
  let input_file = Filename.concat directory inputs_name in
  let inputs = read input_file in
  if not (SomaCache.trusted_metadata input_file ~contents:inputs) then invalid ();
  let outputs = inventory directory in
  if not (List.exists (fun (path, _) -> Filename.check_suffix path ".vo") outputs) ||
     List.filter (fun (path, _) -> is_source path) outputs <> sources then invalid ();
  let contents = "soma-rocq-complete 2\n" ^ Printf.sprintf "key %S\n" key ^
                 "inputs " ^ SomaMerkle.string inputs ^ "\ntheories " ^ hash theory_file ^ "\n" ^
                 String.concat "" (List.map (fun (path, digest) -> Printf.sprintf "artifact %S %s\n" path digest) outputs) in
  let file = Filename.concat directory marker in
  atomic file contents;
  SomaCache.record file
let load ~key ~directory ~resolve_input =
  try
    let file = Filename.concat directory marker in
    let contents = read file in
    if not (SomaCache.trusted_metadata file ~contents) then invalid ();
    let inputs_digest, theories_digest, outputs = match lines contents with
      | "soma-rocq-complete 2" :: key_row :: input_row :: theory_row :: rows ->
        if Scanf.sscanf key_row "key %S%!" Fun.id <> key then invalid ();
        let input = Scanf.sscanf input_row "inputs %s%!" Fun.id in
        let theory = Scanf.sscanf theory_row "theories %s%!" Fun.id in
        if not (SomaMerkle.valid_hash input && SomaMerkle.valid_hash theory) then invalid ();
        let rec parse seen = function
          | [] ->
            if not (List.exists (fun (path, _) -> Filename.check_suffix path ".vo") seen) then invalid ();
            List.sort compare seen
          | row :: rows ->
            let path, digest = Scanf.sscanf row "artifact %S %s%!" (fun p h -> p, h) in
            if not (safe_relative path && SomaMerkle.valid_hash digest) || List.mem_assoc path seen then invalid ();
            parse ((path, digest) :: seen) rows in
        input, theory, parse [] rows
      | _ -> invalid () in
    let input_file = Filename.concat directory inputs_name in
    let inputs = read input_file in
    if SomaMerkle.string inputs <> inputs_digest || not (SomaCache.trusted_metadata input_file ~contents:inputs) then invalid ();
    let inputs_complete, input_rows = match lines inputs with
      | "soma-rocq-inputs 1" :: rows -> true, rows
      | "incomplete" :: rows -> false, rows
      | _ -> invalid () in
    let inputs = List.fold_left (fun seen row ->
        let path, digest = Scanf.sscanf row "input %S %s%!" (fun p h -> p, h) in
        if path = "" || String.contains path '\000' || List.mem_assoc path seen ||
           not (SomaMerkle.valid_hash digest) || hash (Unix.realpath (resolve_input path)) <> digest then invalid ();
        (path, digest) :: seen) [] input_rows |> List.rev in
    let theory_contents = read (Filename.concat directory theory_name) in
    if SomaMerkle.string theory_contents <> theories_digest || inventory directory <> outputs then invalid ();
    let theories = match lines theory_contents with
      | "soma-rocq-theories 2" :: rows when rows <> [] ->
        List.map (fun row ->
            let name, rel = Scanf.sscanf row "theory %S %S%!" (fun n p -> n, p) in
            if name = "" || not (rel = "." || safe_relative rel) then invalid ();
            let path = Filename.concat directory rel in
            if (Unix.lstat path).Unix.st_kind <> Unix.S_DIR || relative directory path <> rel then invalid ();
            name, path) rows
      | _ -> invalid () in
    Some { completion_digest = SomaMerkle.string contents; theories; inputs; inputs_complete; artifacts = outputs }
  with Sys_error _ | Unix.Unix_error _ | Failure _ | Invalid_argument _ | Scanf.Scan_failure _ | End_of_file -> None

(* After one whole-entry validation, verify each actually loaded artifact
   against that manifest. A metadata collection need not reread a large
   library's entire object set for every transitive module it loaded. *)
let artifact_digest entry ~directory ~file =
  try
    let prefix = directory ^ "/" in
    if not (String.starts_with ~prefix file) then None else
    let relative = String.sub file (String.length prefix) (String.length file - String.length prefix) in
    match List.assoc_opt relative entry.artifacts with
    | Some expected when hash file = expected -> Some expected
    | _ -> None
  with Sys_error _ | Unix.Unix_error _ | Failure _ -> None
