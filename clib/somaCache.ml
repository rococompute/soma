(* Receipts live outside the checkout. A stamp is freshness metadata, not
   evidence that the compiler produced the bytes next to it. *)
let identity () = match Sys.getenv_opt "SOMA_CACHE_ID" with
  | Some s when s <> "" -> s
  | _ -> SomaMerkle.file_hash Sys.executable_name

let rec mkdir d =
  if not (Sys.file_exists d) then begin
    mkdir (Filename.dirname d);
    try Unix.mkdir d 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

(* $XDG_CACHE_HOME/soma-receipts, or ~/.cache/soma-receipts *)
let receipts () = match Sys.getenv_opt "XDG_CACHE_HOME" with
  | Some x when x <> "" -> Filename.concat x "soma-receipts"
  | _ -> Filename.concat (Sys.getenv "HOME") ".cache/soma-receipts"

let receipt_for_digest digest =
  let key = SomaMerkle.string ("soma-receipt 2\000" ^ identity () ^ "\000" ^ digest) in
  Filename.concat (receipts ()) key

let receipt file =
  (* Bind the object and its stamp together: separate receipts would allow
     a checkout to mix the stamp of one compilation with another object. *)
  let contents =
    if Filename.check_suffix file ".vo" then
      SomaMerkle.file_hash file ^ SomaMerkle.file_hash (Filename.chop_suffix file ".vo" ^ ".stamp")
    else if Filename.check_suffix file ".stamp" then
      SomaMerkle.file_hash (Filename.chop_suffix file ".stamp" ^ ".vo") ^ SomaMerkle.file_hash file
    else SomaMerkle.file_hash file in
  receipt_for_digest contents

let tracked file =
  let null = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
  Fun.protect ~finally:(fun () -> Unix.close null) (fun () ->
      let pid = Unix.create_process "git"
          [|"git"; "-C"; Filename.dirname file; "ls-files";
            "--error-unmatch"; "--"; Filename.basename file|]
          Unix.stdin null null in
      let rec wait () = try snd (Unix.waitpid [] pid)
        with Unix.Unix_error (Unix.EINTR, _, _) -> wait () in
      wait () = Unix.WEXITED 0)

let trusted file =
  try
    (Unix.lstat file).Unix.st_kind = Unix.S_REG &&
    not (tracked file) && Sys.file_exists (receipt file)
  with Sys_error _ | Unix.Unix_error _ | Not_found -> false

(* Verify the bytes consumed by a metadata parser, not a later read of a
   mutable pathname. Object/stamp pairs deliberately use their stricter API. *)
let trusted_metadata file ~contents =
  try
    not (Filename.check_suffix file ".vo" || Filename.check_suffix file ".stamp") &&
    (Unix.lstat file).Unix.st_kind = Unix.S_REG && not (tracked file) &&
    Sys.file_exists (receipt_for_digest (SomaMerkle.string contents))
  with Sys_error _ | Unix.Unix_error _ | Not_found -> false

let record file =
  try
    if (Unix.lstat file).Unix.st_kind = Unix.S_REG && not (tracked file) then begin
      let r = receipt file in
      mkdir (Filename.dirname r);
      Out_channel.with_open_bin r (fun _ -> ())
    end
  with Sys_error _ | Unix.Unix_error _ | Not_found -> ()
