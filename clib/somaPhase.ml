type plan = {
  key : string; source : string; root : string; directory : string;
  switch : string; output : string;
  generated : SomaBuildInfo.input list;
  imports : SomaBuildInfo.input list;
}

let getenv name = Stdlib.Option.value ~default:"" (Sys.getenv_opt name)
let requested () = getenv "SOMA_BUILD_PHASE" <> "" && getenv "SOMA_PHASE_KEY" <> ""
let checking = ref true
let safe = ref true
let refuse () = if !checking && requested () then safe := false
let checked_imports = ref []
let finish_checking ~imports = checked_imports := imports; checking := false
let eligible () = requested () && !safe && not !checking
let within root file = String.starts_with ~prefix:(root ^ "/") file
let canonical file = Unix.realpath file
let regular file = (Unix.lstat file).Unix.st_kind = Unix.S_REG
let imported = Hashtbl.create 97
let with_import file f =
  let before = if requested () then
      (try Some (canonical file, SomaBuildInfo.signature file) with _ -> safe := false; None)
    else None in
  let result = f () in
  (match before with
   | Some (path,expected) ->
     (try
        if SomaBuildInfo.signature file <> expected || canonical file <> path then safe := false
        else Hashtbl.replace imported path expected
      with Sys_error _ | Unix.Unix_error _ | Failure _ -> safe := false)
   | None -> ());
  result
(* Installation trees contain symlinks into the compiler build tree. Match
   the actual file set the installation exposes, not a permissive parent
   directory prefix around their realpaths. *)
let installed_files = lazy (
  let files = Hashtbl.create 4096 in
  List.iter (fun name ->
      let root = getenv name in
      if root <> "" then begin
        let snapshot = SomaMerkle.scan root in
        List.iter (fun (relative,_) ->
            Hashtbl.replace files (canonical (Filename.concat root relative)) ())
          snapshot.SomaMerkle.files
      end) ["SOMA_PHASE_COQLIB"; "SOMA_PHASE_RUNTIMELIB"];
  files)
let installed file = Hashtbl.mem (Lazy.force installed_files) file

let plugin ~package ~files =
  if requested () &&
     (not (String.starts_with ~prefix:"soma-runtime.plugins." package) ||
      files = [] || not (List.for_all (fun file -> try installed (canonical file) with _ -> false) files))
  then safe := false

let rec mkdir dir =
  if not (Sys.file_exists dir) then begin
    mkdir (Filename.dirname dir);
    try Unix.mkdir dir 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

(* Shared by generation and resume: aliases serialize on the same lock. *)
let with_project_lock dir f =
  let dir = if Filename.is_relative dir then Filename.concat (Sys.getcwd ()) dir else dir in
  mkdir (Filename.dirname dir);
  let dir = try canonical dir with Unix.Unix_error (Unix.ENOENT, _, _) ->
      Filename.concat (canonical (Filename.dirname dir)) (Filename.basename dir) in
  let lock = Filename.concat (Filename.dirname dir) ("." ^ Filename.basename dir ^ ".soma-ocaml.lock") in
  let fd = Unix.openfile lock [Unix.O_RDWR; Unix.O_CREAT; Unix.O_CLOEXEC] 0o600 in
  Fun.protect ~finally:(fun () -> Unix.close fd) (fun () ->
      let rec wait () = match Unix.lockf fd Unix.F_LOCK 0 with
        | () -> ()
        | exception Unix.Unix_error (Unix.EINTR, _, _) -> wait () in
      wait (); f dir)

let fields p =
  let rows label values = label :: string_of_int (List.length values) ::
      List.concat_map (fun (a,b) -> [a;b]) values in
  ["soma-native-phase 1"; p.key; p.source; p.root; p.directory; p.switch; p.output] @
  rows "generated" p.generated @ rows "imports" p.imports
let contents p = String.concat "\000" (fields p) ^ "\000"
let atomic_write path contents =
  mkdir (Filename.dirname path);
  let tmp,oc = Filename.open_temp_file ~temp_dir:(Filename.dirname path) ".phase-" ".tmp" in
  Fun.protect ~finally:(fun () -> close_out_noerr oc; try Sys.remove tmp with Sys_error _ -> ()) (fun () ->
      output_string oc contents; close_out oc; Unix.rename tmp path)

let publish ~source ~directory ~switch ~output ~generated =
  if eligible () then
    try
      let source = canonical source and root = canonical (getenv "SOMA_PHASE_ROOT") in
      let imports = List.map (fun path ->
          let path = canonical path in
          if not (installed path || (within root path && SomaCache.trusted path)) then
            failwith "uncertified phase import";
          let expected = Hashtbl.find imported path in
          if SomaBuildInfo.signature path <> expected then failwith "loaded phase import changed";
          path, expected) !checked_imports in
      let plan = {key=getenv "SOMA_PHASE_KEY"; source; root; directory=canonical directory;
                  switch; output=canonical output; generated; imports} in
      let text = contents plan in
      atomic_write (getenv "SOMA_BUILD_PHASE") text;
      (* The compiler producer certifies these exact bytes. The driver may
         relocate them, but must never create a receipt for observed plans. *)
      SomaCache.record (getenv "SOMA_BUILD_PHASE")
    with Sys_error _ | Unix.Unix_error _ | Failure _ | Not_found -> ()

let read path =
  try
    let info=Unix.lstat path in
    if info.Unix.st_kind<>Unix.S_REG || info.Unix.st_size>16*1024*1024 then failwith "oversized phase plan";
    let text = In_channel.with_open_bin path In_channel.input_all in
    if String.length text > 16 * 1024 * 1024 || not (SomaCache.trusted_metadata path ~contents:text) then None else
    let fs = String.split_on_char '\000' text in
    let rec rows n fs acc = match n,fs with
      | 0,_ -> List.rev acc,fs
      | _,a::b::rest when n>0 -> rows (n-1) rest ((a,b)::acc)
      | _ -> failwith "bad phase rows" in
    match fs with
    | "soma-native-phase 1"::key::source::root::directory::switch::output::"generated"::n::rest ->
      let n=int_of_string n in if n<1 || n>65536 then None else
      let generated,rest=rows n rest [] in
      (match rest with
       | "imports"::n::rest ->
         let n=int_of_string n in if n<0 || n>65536 then None else
         let imports,rest=rows n rest [] in
         if rest<>[""] then None else Some {key;source;root;directory;switch;output;generated;imports}
       | _ -> None)
    | _ -> None
  with Sys_error _ | Unix.Unix_error _ | Failure _ -> None

let validate p =
  try
    let same (path,expected) = regular path && SomaBuildInfo.signature path = expected in
    p.key<>"" && p.source=canonical p.source && p.root=canonical p.root &&
    within p.root p.source && p.directory=canonical p.directory &&
    not (within p.root p.directory) &&
    p.output=Filename.remove_extension p.source ^ ".exe" &&
    List.for_all (fun (file,_) -> within p.directory file &&
        Filename.dirname file=p.directory) p.generated &&
    List.for_all (fun ((path,expected) as input) ->
        (* Optional dune-workspace is represented by a certified absence. *)
        (expected="absent" && not (Sys.file_exists path)) || same input) p.generated &&
    List.for_all (fun ((path,_) as input) ->
        same input && (installed path || (within p.root path && SomaCache.trusted path))) p.imports
  with Sys_error _ | Unix.Unix_error _ | Failure _ -> false

let record_path key =
  let cache = match Sys.getenv_opt "XDG_CACHE_HOME" with
    | Some d when d<>"" -> Some d
    | _ -> Option.bind (Sys.getenv_opt "HOME") (fun home ->
        if home="" then None else Some (Filename.concat home ".cache")) in
  Option.map (fun cache -> Filename.concat (Filename.concat cache "soma-native-phases") key) cache

let promote ~draft ~key =
  match read draft,record_path key with
  | Some p,Some destination when p.key=key && validate p ->
    (try
       let text=contents p in
       (* Preserve exact producer-certified bytes and their existing receipt. *)
       atomic_write destination text;
       SomaCache.trusted_metadata destination ~contents:text
     with Sys_error _ | Unix.Unix_error _ -> false)
  | _ -> false

let resume p ~run =
  with_project_lock p.directory (fun directory ->
      if not (validate p) then false else begin
        let log=Filename.concat directory "build.log" in
        if not (run ~directory ~log) then failwith ("native validation failed; see " ^ log);
        (* Dune is always run. Copy from its current validated target, never
           accept the old final executable as proof of native success. *)
        if not (validate p) then failwith "generated inputs changed during native validation";
        let built=Filename.concat directory "_build/default/soma_main.exe" in
        let expected=SomaBuildInfo.signature built in
        if expected="absent" then failwith "native validation produced no executable";
        let text=In_channel.with_open_bin built In_channel.input_all in
        let mode=(Unix.stat built).Unix.st_perm in
        let tmp,oc=Filename.open_temp_file ~temp_dir:(Filename.dirname p.output) ".soma-native-" ".tmp" in
        Fun.protect ~finally:(fun () -> close_out_noerr oc;try Sys.remove tmp with Sys_error _ -> ()) (fun () ->
            output_string oc text;close_out oc;Unix.chmod tmp mode;
            if SomaBuildInfo.signature built<>expected || SomaBuildInfo.signature tmp<>expected then
              failwith "native product changed while copying";
            Unix.rename tmp p.output;SomaCache.record p.output);
        true
      end)
