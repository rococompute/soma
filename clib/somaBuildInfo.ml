type input = string * string

let manifest variable = match Sys.getenv_opt variable with
  | Some file when file <> "" -> Some file
  | _ -> None

let append variable fields =
  Option.iter (fun file ->
      Out_channel.with_open_gen [Open_wronly; Open_creat; Open_append; Open_binary] 0o600 file (fun oc ->
          List.iter (fun field -> output_string oc field; output_char oc '\000') fields))
    (manifest variable)

let stable a b =
  a.Unix.st_dev = b.Unix.st_dev && a.Unix.st_ino = b.Unix.st_ino &&
  a.Unix.st_kind = b.Unix.st_kind && a.Unix.st_size = b.Unix.st_size &&
  a.Unix.st_mtime = b.Unix.st_mtime && a.Unix.st_ctime = b.Unix.st_ctime &&
  a.Unix.st_perm = b.Unix.st_perm

let signature ?(write=true) path =
  let before = Unix.stat path in
  let kind, digest = match before.Unix.st_kind with
    | Unix.S_REG -> "file", SomaMerkle.file_hash path
    | Unix.S_DIR -> "directory", (SomaMerkle.scan ~write path).SomaMerkle.digest
    | _ -> failwith ("unsupported build input: " ^ path) in
  if not (stable before (Unix.stat path)) then
    failwith ("build input changed while fingerprinting: " ^ path);
  Printf.sprintf "%s:%o:%s" kind before.Unix.st_perm digest

let prepare_inputs paths =
  match manifest "SOMA_BUILD_INPUTS" with
  | None -> None
  | Some _ ->
    try
      let absolute path = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path in
      let paths = List.sort_uniq String.compare (List.map absolute paths) in
      Some (List.map (fun path -> path, signature path) paths)
    with Sys_error _ | Unix.Unix_error _ | Failure _ | Not_found -> None

let publish_inputs inputs =
  Option.iter (fun inputs ->
      append "SOMA_BUILD_INPUTS" (List.concat_map (fun (path, signature) -> [path; signature]) inputs)) inputs

let publish_products paths = append "SOMA_BUILD_PRODUCTS" paths

let publish_command argv =
  Option.iter (fun file ->
      Out_channel.with_open_bin file (fun oc ->
          List.iter (fun arg -> output_string oc arg; output_char oc '\000') argv))
    (manifest "SOMA_MIRAGE_ARGV")
