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
  match Unix.stat path with
  | exception Unix.Unix_error ((Unix.ENOENT | Unix.ENOTDIR), _, _) -> "absent"
  | before ->
  let kind, digest = match before.Unix.st_kind with
    | Unix.S_REG -> "file", SomaMerkle.file_hash path
    | Unix.S_DIR -> "directory", (SomaMerkle.scan ~write path).SomaMerkle.digest
    | _ -> failwith ("unsupported build input: " ^ path) in
  if not (stable before (Unix.stat path)) then
    failwith ("build input changed while fingerprinting: " ^ path);
  Printf.sprintf "%s:%o:%s" kind before.Unix.st_perm digest

let program name =
  let executable path =
    try Unix.access path [Unix.X_OK];
      if (Unix.stat path).Unix.st_kind = Unix.S_REG then Some path else None
    with Unix.Unix_error _ -> None in
  if String.contains name '/' then executable name else
  let separator = if Sys.win32 then ';' else ':' in
  let paths = Option.value ~default:"" (Sys.getenv_opt "PATH") |> String.split_on_char separator in
  List.find_map (fun dir -> executable (Filename.concat (if dir = "" then "." else dir) name)) paths

let program_candidates name =
  if String.contains name '/' then [name] else
  let separator = if Sys.win32 then ';' else ':' in
  let paths = Option.value ~default:"" (Sys.getenv_opt "PATH") |> String.split_on_char separator in
  let rec until_found = function
    | [] -> []
    | dir :: rest ->
      let path = Filename.concat (if dir = "" then "." else dir) name in
      path :: (match program path with Some _ -> [] | None -> until_found rest) in
  until_found paths

let host_inputs () =
  (* Flags can name arbitrary response files/SDK directories. Do not certify
     a foreign build whose extra input set we do not know how to enumerate. *)
  List.iter (fun name -> match Sys.getenv_opt name with
      | Some value when value <> "" -> failwith ("uncertified native flags: " ^ name)
      | _ -> ()) ["CFLAGS"; "CXXFLAGS"; "CPPFLAGS"; "LDFLAGS"];
  let tools = List.concat_map program_candidates
      ["opam"; "sh"; "cc"; "ld"; "pkg-config"; "make"; "mirage"; "ocamlc"; "ocamlopt"; "dune"] in
  let compilers = List.concat_map (fun name -> match Sys.getenv_opt name with
      | Some value when value <> "" ->
        (match program value with Some _ -> program_candidates value | None -> failwith ("unknown compiler: " ^ value))
      | _ -> []) ["CC"; "CXX"; "CPP"] in
  let paths = List.concat_map (fun name -> match Sys.getenv_opt name with
      | Some value when value <> "" -> String.split_on_char (if Sys.win32 then ';' else ':') value
      | _ -> []) ["SDKROOT"; "CPATH"; "LIBRARY_PATH"; "PKG_CONFIG_PATH"; "PKG_CONFIG_LIBDIR"] in
  tools @ compilers @ paths

let prepare_inputs paths =
  match manifest "SOMA_BUILD_INPUTS" with
  | None -> None
  | Some _ ->
    try
      let absolute path = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path in
      let paths = List.sort_uniq String.compare (List.map absolute (host_inputs () @ paths)) in
      Some (List.map (fun path -> path, signature path) paths)
    with Sys_error _ | Unix.Unix_error _ | Failure _ | Not_found -> None

let publish_inputs inputs =
  Option.iter (fun inputs ->
      append "SOMA_BUILD_INPUTS" (List.concat_map (fun (path, signature) -> [path; signature]) inputs)) inputs

let publish_products paths = append "SOMA_BUILD_PRODUCTS" paths

let mark_external () = append "SOMA_BUILD_EXTERNAL" ["external"]

let publish_command argv =
  Option.iter (fun file ->
      Out_channel.with_open_bin file (fun oc ->
          List.iter (fun arg -> output_string oc arg; output_char oc '\000') argv))
    (manifest "SOMA_MIRAGE_ARGV")
