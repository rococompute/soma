(* User configuration paths shared by lightweight command-line tools and the
   compiler. Keep environment fallback and rc selection in one place. *)
let getenv_else name fallback =
  match Util.getenv_opt name with Some value -> value | None -> fallback ()

let ( / ) a b = if Filename.is_relative b then a ^ "/" ^ b else b
let coqify dir = dir / "coq"

let home ~warn =
  getenv_else "HOME" (fun () ->
    try (Sys.getenv "HOMEDRIVE")^(Sys.getenv "HOMEPATH") with Not_found ->
      getenv_else "USERPROFILE" (fun () ->
        warn ("Cannot determine user home directory, using '.' .");
        Filename.current_dir_name))


let xdg_config_home warn =
  coqify
    (getenv_else "XDG_CONFIG_HOME" (fun () -> (home ~warn) / ".config"))


let rc_candidates ~warn =
  let append = Filename.concat in
  [ append (xdg_config_home warn) ("coqrc." ^ Coq_config.version);
    append (xdg_config_home warn) "coqrc";
    append (home ~warn) (".coqrc." ^ Coq_config.version);
    append (home ~warn) ".coqrc" ]
