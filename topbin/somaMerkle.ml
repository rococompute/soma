module H = Digestif.SHA256
module M = Map.Make (String)

type snapshot = {
  digest : string;
  files : (string * string) list;
  directories : (string * string) list;
  hashed_files : int;
  reused_files : int;
  hashed_bytes : int64;
}

let string s = H.to_hex (H.digest_string s)
let read f = In_channel.with_open_bin f In_channel.input_all
let valid_hash s = String.length s = 64 && String.for_all (function
    | '0'..'9' | 'a'..'f' -> true | _ -> false) s

let default_cache () =
  let base = match Sys.getenv_opt "XDG_CACHE_HOME" with
    | Some p when p <> "" -> p
    | _ -> Filename.concat (Sys.getenv "HOME") ".cache" in
  Filename.concat base "soma-fingerprints/v1"

(* Cache hints belong to this user, outside source checkouts. Never traverse a
   link at a cache destination, and never deserialize OCaml values from disk. *)
let private_path p directory =
  let st = Unix.lstat p in
  st.Unix.st_kind = (if directory then Unix.S_DIR else Unix.S_REG) &&
  st.Unix.st_uid = Unix.getuid () && st.Unix.st_perm land 0o077 = 0

let rec mkdir p =
  if Sys.file_exists p then () else begin
    mkdir (Filename.dirname p);
    try Unix.mkdir p 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

let atomic file contents =
  let dir = Filename.dirname file in
  let tmp = Filename.temp_file ~temp_dir:dir ".fingerprint-" ".tmp" in
  Fun.protect ~finally:(fun () -> if Sys.file_exists tmp then Sys.remove tmp) (fun () ->
      Out_channel.with_open_bin tmp (fun oc -> output_string oc contents);
      Sys.rename tmp file)

let object_path cache digest = Filename.concat (Filename.concat cache "objects") digest
let object_put cache contents =
  let digest = string contents in
  let path = object_path cache digest in
  let intact = try private_path path false && string (read path) = digest
    with Sys_error _ | Unix.Unix_error _ -> false in
  if not intact then atomic path contents;
  digest

let cache_load cache key =
  try
    if not (private_path cache true && private_path (Filename.concat cache "objects") true &&
            private_path (Filename.concat cache "indices") true) then M.empty else
    let index = Filename.concat (Filename.concat cache "indices") key in
    if not (private_path index false) then M.empty else
    let digest = String.trim (read index) in
    if not (valid_hash digest) then M.empty else
    let path = object_path cache digest in
    if not (private_path path false) || (Unix.stat path).Unix.st_size > 64 * 1024 * 1024 then M.empty else
    let contents = read path in
    if string contents <> digest then M.empty else
    match String.split_on_char '\n' contents with
    | "soma-fingerprint 1" :: _root :: rows ->
      List.fold_left (fun acc row -> if row = "" then acc else
          Scanf.sscanf row "file %S %S %s%!" (fun path stamp hash ->
              if not (valid_hash hash) || M.mem path acc then failwith "bad fingerprint";
              M.add path (stamp, hash) acc)) M.empty rows
    | _ -> M.empty
  with Sys_error _ | Unix.Unix_error _ | Failure _ | Scanf.Scan_failure _ | End_of_file -> M.empty

let stamp (s : Unix.LargeFile.stats) =
  Printf.sprintf "%d:%d:%d:%Ld:%.17g:%.17g" s.st_dev s.st_ino s.st_perm s.st_size s.st_mtime s.st_ctime

let file_hash file =
  let buffer = Bytes.create 65536 in
  In_channel.with_open_bin file (fun ic ->
      let rec loop ctx =
        let len = input ic buffer 0 (Bytes.length buffer) in
        if len = 0 then H.to_hex (H.get ctx)
        else loop (H.feed_bytes ctx ~len buffer) in
      loop H.empty)

let scan ?cache ?(write = true) ?(skip = []) root =
  let root = Unix.realpath root in
  let enabled = Sys.getenv_opt "SOMA_FINGERPRINT_CACHE" <> Some "0" in
  let cache = if not enabled then None else match cache with
    | Some p -> Some p
    | None -> (try Some (default_cache ()) with Not_found -> None) in
  let cache = match cache with
    | Some p ->
      (try
         if write then begin
           mkdir p;
           if private_path p true then begin
             mkdir (Filename.concat p "objects"); mkdir (Filename.concat p "indices")
           end
         end;
         if private_path p true && private_path (Filename.concat p "objects") true &&
            private_path (Filename.concat p "indices") true then Some p else None
       with Sys_error _ | Unix.Unix_error _ -> None)
    | None -> None in
  let key = string (root ^ "\000" ^ String.concat "\000" (List.sort_uniq compare skip)) in
  let previous = match cache with Some c -> cache_load c key | None -> M.empty in
  let records = ref M.empty and files = ref [] and directories = ref [] in
  let hashed_files = ref 0 and reused_files = ref 0 and hashed_bytes = ref 0L in
  let started = Unix.gettimeofday () in
  let nodes = ref [] in
  let rec walk ancestors relative dir =
    let before = Unix.LargeFile.stat dir in
    if before.st_kind <> Unix.S_DIR || List.mem (before.st_dev, before.st_ino) ancestors then
      failwith ("directory cycle or unsupported input: " ^ dir);
    let ancestors = (before.st_dev, before.st_ino) :: ancestors in
    if List.length ancestors > 64 then failwith ("directory tree too deep: " ^ dir);
    let names () = Sys.readdir dir |> Array.to_list |> List.sort compare in
    let entries = names () in
    let children = List.filter_map (fun name ->
        if List.mem name skip then None else
        let full = Filename.concat dir name in
        let rel = if relative = "" then name else relative ^ "/" ^ name in
        let st = Unix.LargeFile.stat full in
        let kind, digest = match st.st_kind with
          | Unix.S_DIR -> "directory", walk ancestors rel full
          | Unix.S_REG ->
            let signature = stamp st in
            (* Recent timestamps and coarse clocks can hide rapid same-size
               writes. Read those files again until the timestamp is old. *)
            let stable = st.st_mtime < started -. 2. && st.st_ctime < started -. 2. in
            let digest = match M.find_opt rel previous with
              | Some (old, digest) when stable && old = signature ->
                incr reused_files; digest
              | _ ->
                incr hashed_files; hashed_bytes := Int64.add !hashed_bytes st.st_size;
                file_hash full in
            if stamp (Unix.LargeFile.stat full) <> signature then
              failwith ("file changed while hashing: " ^ full);
            records := M.add rel (signature, digest) !records;
            files := (rel, digest) :: !files;
            "file", digest
          | _ -> failwith ("not a regular file or directory: " ^ full) in
        Some (Printf.sprintf "%s %S %o %s\n" kind name st.st_perm digest)) entries in
    if names () <> entries || stamp (Unix.LargeFile.stat dir) <> stamp before then
      failwith ("directory changed while hashing: " ^ dir);
    let contents = "soma-directory 1\n" ^ String.concat "" children in
    let digest = string contents in
    nodes := contents :: !nodes;
    directories := (relative, digest) :: !directories;
    digest in
  let digest = walk [] "" root in
  (match cache with
   | Some c when write ->
     (try
        List.iter (fun contents -> ignore (object_put c contents)) !nodes;
        let body = "soma-fingerprint 1\n" ^ digest ^ "\n" ^
            String.concat "" (List.map (fun (path, (stamp, hash)) ->
                Printf.sprintf "file %S %S %s\n" path stamp hash) (M.bindings !records)) in
        let object_id = object_put c body in
        let index = Filename.concat (Filename.concat c "indices") key in
        if not (Sys.file_exists index) || String.trim (read index) <> object_id then
          atomic index (object_id ^ "\n")
      with Sys_error _ | Unix.Unix_error _ -> ())
   | _ -> ());
  { digest; files = List.sort compare !files; directories = List.sort compare !directories;
    hashed_files = !hashed_files; reused_files = !reused_files; hashed_bytes = !hashed_bytes }
