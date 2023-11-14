(* Receipts live outside the checkout. A stamp is freshness metadata, not
   evidence that the compiler produced the bytes next to it. *)
let identity () = match Sys.getenv_opt "SOMA_CACHE_ID" with
  | Some s when s <> "" -> s
  | _ -> Digest.to_hex (Digest.file Sys.executable_name)

let rec mkdir d =
  if not (Sys.file_exists d) then begin
    mkdir (Filename.dirname d);
    try Unix.mkdir d 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

(* $XDG_CACHE_HOME/soma-receipts, or ~/.cache/soma-receipts *)
let receipts () = match Sys.getenv_opt "XDG_CACHE_HOME" with
  | Some x when x <> "" -> Filename.concat x "soma-receipts"
  | _ -> Filename.concat (Sys.getenv "HOME") ".cache/soma-receipts"

let receipt file =
  (* Bind the object and its stamp together: separate receipts would allow
     a checkout to mix the stamp of one compilation with another object. *)
  let contents =
    if Filename.check_suffix file ".vo" then
      Digest.file file ^ Digest.file (Filename.chop_suffix file ".vo" ^ ".stamp")
    else if Filename.check_suffix file ".stamp" then
      Digest.file (Filename.chop_suffix file ".stamp" ^ ".vo") ^ Digest.file file
    else Digest.file file in
  let key = Digest.to_hex (Digest.string (identity () ^ contents)) in
  Filename.concat (receipts ()) key

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

let record file =
  try
    if (Unix.lstat file).Unix.st_kind = Unix.S_REG && not (tracked file) then begin
      let r = receipt file in
      mkdir (Filename.dirname r);
      Out_channel.with_open_bin r (fun _ -> ())
    end
  with Sys_error _ | Unix.Unix_error _ | Not_found -> ()
