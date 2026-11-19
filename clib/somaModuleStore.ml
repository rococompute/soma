(* Store hints are deliberately weaker than import freshness: the compiler must
   still check the restored source and every currently selected prerequisite.
   Descriptors bind the producer's logical path, so moving a trusted object to
   another filename cannot mint a donor for that other library. *)
let source_hash src =
  let base = Filename.remove_extension src in
  let one f = if Sys.file_exists f then SomaMerkle.file_hash f else "-" in
  let ml = base ^ ".ml" in
  let ml_digest = if Sys.file_exists ml then "rel:" ^ SomaMerkle.file_hash ml else "-" in
  SomaMerkle.string (String.concat " "
    [one src; one (base ^ ".exp"); one (base ^ ".ext"); one (base ^ ".wasm");
     ml_digest; one (base ^ ".lean")])

external rename_absent : string -> string -> bool = "soma_cache_rename_absent"

let exists file = try ignore (Unix.lstat file); true with Unix.Unix_error (Unix.ENOENT, _, _) -> false
let regular file = try (Unix.lstat file).Unix.st_kind = Unix.S_REG with Unix.Unix_error _ -> false
let directory file = try (Unix.lstat file).Unix.st_kind = Unix.S_DIR with Unix.Unix_error _ -> false
let safe f fallback = try f () with Sys_error _ | Unix.Unix_error _ | Failure _ -> fallback
let rec mkdir dir =
  if not (directory dir) then begin
    let parent = Filename.dirname dir in
    if parent <> dir then mkdir parent;
    try Unix.mkdir dir 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) when directory dir -> ()
  end
let rec remove dir =
  if directory dir then begin
    Array.iter (fun n -> remove (Filename.concat dir n)) (Sys.readdir dir);
    Unix.rmdir dir
  end else if exists dir then Sys.remove dir
let private_dir parent =
  mkdir parent;
  let file = Filename.temp_file ~temp_dir:parent ".donor-" "" in
  Sys.remove file;
  Unix.mkdir file 0o700;
  file
let clean_relative path =
  path <> "" && Filename.is_relative path &&
  String.for_all (fun c -> c > ' ' && c <> '\127' && c <> '\\') path &&
  List.for_all (fun p -> p <> "" && p <> "." && p <> "..") (String.split_on_char '/' path)
let plain_path root rel =
  clean_relative rel && directory root &&
  let rec walk dir = function
    | [] -> false
    | [name] -> regular (Filename.concat dir name)
    | name :: rest -> let dir = Filename.concat dir name in directory dir && walk dir rest in
  walk root (String.split_on_char '/' rel)
let relative root file =
  let root = if Filename.is_relative root then Filename.concat (Sys.getcwd ()) root else root in
  let file = if Filename.is_relative file then Filename.concat (Sys.getcwd ()) file else file in
  let prefix = root ^ "/" in
  if String.starts_with ~prefix file then
    let p = String.sub file (String.length prefix) (String.length file - String.length prefix) in
    if clean_relative p then Some p else None
  else None

type descriptor = { unit_name : string; source : string; checked_source : string; object_hash : string; stamp_hash : string }
let encode d = Printf.sprintf "soma-module-donor 2\nunit %S\nprefix %S\nsource %s\nchecked-source %s\nobject %s\nstamp %s\n"
    d.unit_name "" d.source d.checked_source d.object_hash d.stamp_hash
let decode text =
  try
    let unit_name, prefix, source, checked_source, object_hash, stamp_hash =
      Scanf.sscanf text "soma-module-donor 2\nunit %S\nprefix %S\nsource %s\nchecked-source %s\nobject %s\nstamp %s\n%!"
        (fun u p s c o t -> u, p, s, c, o, t) in
    let d = { unit_name; source; checked_source; object_hash; stamp_hash } in
    if prefix = "" && clean_relative unit_name &&
       List.for_all SomaMerkle.valid_hash [source; checked_source; object_hash; stamp_hash] && encode d = text
    then Some d else None
  with Scanf.Scan_failure _ | Failure _ | End_of_file -> None
let read_descriptor file = safe (fun () ->
    if not (regular file) || (Unix.lstat file).Unix.st_size > 16384 then None else
    let text = In_channel.with_open_bin file In_channel.input_all in
    if SomaCache.trusted_metadata file ~contents:text then decode text else None) None
let complete stamp expected =
  let text = In_channel.with_open_bin stamp In_channel.input_all in
  String.starts_with ~prefix:("soma-stamp 4\nsource " ^ expected ^ "\n") text
let matches d vo stamp =
  regular vo && regular stamp && complete stamp d.checked_source && SomaCache.trusted vo && SomaCache.trusted stamp &&
  SomaMerkle.file_hash vo = d.object_hash && SomaMerkle.file_hash stamp = d.stamp_hash
let source_matches d root =
  let source = d.unit_name ^ ".soma" in
  plain_path root source && source_hash (Filename.concat root source) = d.source
let donor_file vo = Filename.chop_suffix vo ".vo" ^ ".donor"

let native_side_files cache =
  (* Native proof side files are not covered by a .vo/.stamp-only descriptor. *)
  exists (Filename.concat cache ".coq-native")
let record ~root ~cache ~prefix ~source ~vo ~stamp ~expected ~candidate =
  safe (fun () ->
      match relative root source, relative cache vo with
      | Some source_rel, Some vo_rel when prefix = "" &&
          Filename.check_suffix source_rel ".soma" &&
          Filename.remove_extension source_rel ^ ".vo" = vo_rel &&
          plain_path root source_rel && plain_path cache vo_rel &&
          plain_path cache (Filename.remove_extension source_rel ^ ".stamp") &&
          stamp = Filename.chop_suffix vo ".vo" ^ ".stamp" &&
          not (native_side_files cache || native_side_files (Filename.dirname vo)) && source_hash source = candidate &&
          complete stamp expected && SomaCache.trusted vo && SomaCache.trusted stamp ->
        let d = { unit_name = Filename.remove_extension source_rel; source = candidate; checked_source = expected;
                  object_hash = SomaMerkle.file_hash vo; stamp_hash = SomaMerkle.file_hash stamp } in
        let file = donor_file vo in
        let tmp = Filename.temp_file ~temp_dir:(Filename.dirname file) ".donor-" ".tmp" in
        Fun.protect ~finally:(fun () -> if exists tmp then Sys.remove tmp) (fun () ->
            Out_channel.with_open_bin tmp (fun oc -> output_string oc (encode d));
            if matches d vo stamp && source_hash source = candidate then begin
              Sys.rename tmp file;
              SomaCache.record file;
              (* Changed objects invalidate the descriptor; no receiver trusts
                 this file without checking the exact pair again. *)
              if not (matches d vo stamp && source_hash source = candidate) then Sys.remove file
            end)
      | _ -> ()) ()
let copy source target =
  In_channel.with_open_bin source (fun ic ->
      Out_channel.with_open_bin target (fun oc ->
          let buf = Bytes.create 65536 in
          let rec loop () = let n = input ic buf 0 (Bytes.length buf) in
            if n > 0 then (output oc buf 0 n; loop ()) in loop ()))
let entry_key d = SomaMerkle.string ("soma-module-source 2\000" ^ SomaCache.identity () ^ "\000" ^ d.unit_name ^ "\000" ^ d.source)
let store_root store context = Filename.concat (Filename.concat store "modules-v2") context
let valid_context context = SomaMerkle.valid_hash context
let artifacts entry = Filename.concat entry "object.vo", Filename.concat entry "object.stamp", Filename.concat entry "descriptor"
let verified_entry entry =
  if not (directory entry) then None else
  let vo, stamp, descriptor = artifacts entry in
  match read_descriptor descriptor with Some d when matches d vo stamp -> Some d | _ -> None
let publish ~store ~context ~root ~cache =
  if valid_context context && directory cache && not (native_side_files cache) then
    safe (fun () ->
        let rec walk rel dir = Array.iter (fun name ->
            let r = if rel = "" then name else rel ^ "/" ^ name in
            let file = Filename.concat dir name in
            if directory file && name <> ".tests" && name <> "rocq" then walk r file
            else if Filename.check_suffix name ".donor" && plain_path cache r then
              match read_descriptor file with
              | Some d when r = d.unit_name ^ ".donor" && source_matches d root ->
                let vo = Filename.concat cache (d.unit_name ^ ".vo") in
                let stamp = Filename.concat cache (d.unit_name ^ ".stamp") in
                if plain_path cache (d.unit_name ^ ".vo") && plain_path cache (d.unit_name ^ ".stamp") && not (native_side_files (Filename.dirname vo)) && matches d vo stamp then begin
                  let parent = Filename.concat (store_root store context) (entry_key d) in
                  let target = Filename.concat parent (SomaMerkle.string (encode d)) in
                  if not (exists target) then begin
                    let tmp = private_dir parent in
                    Fun.protect ~finally:(fun () -> if exists tmp then remove tmp) (fun () ->
                        let out_vo, out_stamp, out_descriptor = artifacts tmp in
                        copy vo out_vo; copy stamp out_stamp; copy file out_descriptor;
                        match verified_entry tmp with
                        | Some copied when copied = d -> ignore (rename_absent tmp target)
                        | _ -> ())
                  end
                end
              | _ -> ()) (Sys.readdir dir) in
        walk "" cache) ()
let restore ~store ~context ~root ~cache =
  if valid_context context && not (exists cache) && directory (store_root store context) then
    safe (fun () ->
        let tmp = private_dir (Filename.dirname cache) in
        Fun.protect ~finally:(fun () -> if exists tmp then remove tmp) (fun () ->
            let count = ref 0 in
            let rec sources rel dir = Array.iter (fun name ->
                let r = if rel = "" then name else rel ^ "/" ^ name in
                let file = Filename.concat dir name in
                if directory file && not (List.mem name [".soma-cache"; ".git"; "_build"]) then sources r file
                else if Filename.check_suffix name ".soma" && plain_path root r then begin
                  let d = { unit_name = Filename.remove_extension r; source = source_hash file;
                            checked_source = ""; object_hash = ""; stamp_hash = "" } in
                  let candidates = Filename.concat (store_root store context) (entry_key d) in
                  if directory candidates then begin
                    (* Newer candidates are hints only. A different dependency
                       selection may force the ordinary compiler to recheck. *)
                    let entries = Array.to_list (Sys.readdir candidates) |> List.filter SomaMerkle.valid_hash |>
                      List.map (fun n -> Filename.concat candidates n) |>
                      List.sort (fun a b ->
                          let by_time = compare (Unix.lstat b).Unix.st_mtime (Unix.lstat a).Unix.st_mtime in
                          if by_time = 0 then String.compare a b else by_time) in
                    match List.find_map (fun entry -> match verified_entry entry with
                        | Some found when found.unit_name = d.unit_name && found.source = d.source -> Some (entry, found)
                        | _ -> None) entries with
                    | None -> ()
                    | Some (entry, found) ->
                      let vo = Filename.concat tmp (found.unit_name ^ ".vo") in
                      let stamp = Filename.concat tmp (found.unit_name ^ ".stamp") in
                      let descriptor = donor_file vo in
                      mkdir (Filename.dirname vo);
                      let from_vo, from_stamp, from_descriptor = artifacts entry in
                      copy from_vo vo; copy from_stamp stamp; copy from_descriptor descriptor;
                      (match read_descriptor descriptor with
                       | Some copied when copied = found && matches copied vo stamp && source_matches copied root -> incr count
                       | _ -> List.iter (fun f -> if exists f then Sys.remove f) [vo; stamp; descriptor])
                  end
                end) (Sys.readdir dir) in
            sources "" root;
            if !count > 0 then ignore (rename_absent tmp cache))) ()

let remove_staging = remove
