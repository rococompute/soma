(* User configuration paths shared by lightweight command-line tools and the
   compiler. Keep environment fallback and rc selection in one place. *)
let getenv_else getenv name fallback =
  match getenv name with Some value -> value | None -> fallback ()

let ( / ) a b = if Filename.is_relative b then a ^ "/" ^ b else b
let coqify dir = dir / "coq"

let home_using getenv ~warn =
  getenv_else getenv "HOME" (fun () ->
    try (Sys.getenv "HOMEDRIVE")^(Sys.getenv "HOMEPATH") with Not_found ->
      getenv_else getenv "USERPROFILE" (fun () ->
        warn ("Cannot determine user home directory, using '.' .");
        Filename.current_dir_name))


let xdg_config_home_using getenv warn =
  coqify
    (getenv_else getenv "XDG_CONFIG_HOME" (fun () -> (home_using getenv ~warn) / ".config"))


let rc_candidates_using getenv ~warn =
  let append = Filename.concat in
  [ append (xdg_config_home_using getenv warn) ("coqrc." ^ Coq_config.version);
    append (xdg_config_home_using getenv warn) "coqrc";
    append (home_using getenv ~warn) (".coqrc." ^ Coq_config.version);
    append (home_using getenv ~warn) ".coqrc" ]


let home ~warn = home_using Util.getenv_opt ~warn
let xdg_config_home warn = xdg_config_home_using Util.getenv_opt warn
let rc_candidates ~warn = rc_candidates_using Util.getenv_opt ~warn
let rc_candidates_for_executable executable ~warn =
  rc_candidates_using (Util.getenv_opt_for_executable executable) ~warn
