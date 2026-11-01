(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let getenv_default var default =
  match Sys.getenv_opt var with Some v when v <> "" -> v | _ -> default

let cache_root () =
  let cache = match Sys.getenv_opt "XDG_CACHE_HOME" with
    | Some d when d <> "" -> d
    | _ -> Filename.concat (getenv_default "HOME" ".") ".cache" in
  Filename.concat cache "soma"

let switch () = match Sys.getenv_opt "SOMA_OCAML_SWITCH" with
  | Some s when s <> "" -> s, false
  | _ -> Filename.concat (cache_root ()) "ocaml", true

let rec mkdir_p d =
  if not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

let run ~log args =
  Sys.command (Filename.quote_command (List.hd args) (List.tl args) ~stdout:log ~stderr:log) = 0

let command_exists name =
  Sys.command (Filename.quote_command "sh" ["-c"; "command -v " ^ name] ~stdout:"/dev/null" ~stderr:"/dev/null") = 0

let read_lines f =
  try List.filter (( <> ) "") (String.split_on_char '\n' (In_channel.with_open_bin f In_channel.input_all))
  with Sys_error _ -> []

let tail_of_file ?(lines = 20) f =
  try
    let all = String.split_on_char '\n' (In_channel.with_open_bin f In_channel.input_all) in
    let n = List.length all in
    String.concat "\n" (List.filteri (fun i _ -> i >= n - lines) all)
  with Sys_error _ -> ""

let ensure_switch ~who ~log =
  let switch, managed = switch () in
  if not (command_exists "opam") then
    CErrors.user_err Pp.(str who ++ str ": Soma takes the packages it needs from opam," ++ spc () ++
                         str "which is not installed: see https://opam.ocaml.org/doc/Install.html.");
  if managed && not (Sys.file_exists (Filename.concat switch "_opam")) then begin
    mkdir_p switch;
    Printf.eprintf "%s: making the opam switch %s (once)\n%!" who switch;
    if not (run ~log ["opam"; "switch"; "create"; switch; "--empty"; "--no-switch"; "-y"]) then
      CErrors.user_err Pp.(str who ++ str ": making the opam switch " ++ str switch ++
                           str " failed; the end of " ++ str log ++ str ":" ++ fnl () ++ str (tail_of_file log))
  end;
  switch
