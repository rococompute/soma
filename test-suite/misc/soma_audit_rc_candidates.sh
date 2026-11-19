#!/usr/bin/env bash
# Run the actual Coqrc loader/candidate function and root guard without a full
# compiler build. Only platform/vernacular/provenance endpoints are adapters.
set -euo pipefail
export SOMA_RC_SOURCE="$(cd "$(dirname "$0")/../.." && pwd -P)"
python3 - <<'PY'
import os,pathlib,subprocess,tempfile
source=pathlib.Path(os.environ['SOMA_RC_SOURCE'])
loader=(source/'toplevel/coqrc.ml').read_text()
cli=(source/'topbin/soma.ml').read_text();start=cli.index('  List.iter (fun path ->\n      match Unix.lstat path with',cli.index('let fresh_inputs '))
end=cli.index('  (match initial_getenv "SOMA_OCAML_EXTRACT"',start);guard=cli[start:end]
prefix=r'''
module CUnix=struct let file_readable_p p=try Unix.access p [Unix.R_OK];not(Sys.is_directory p) with Unix.Unix_error _->false end
module Pp=struct let str s=s end
module Feedback=struct let msg_warning _=() let msg_info _=() end
module Exninfo=struct let capture e=e let iraise e=raise e end
module SomaImport=struct
 let noted=ref []
 let rc_noted=ref []
 let note_loaded_source f=noted:=f :: !noted
 let note_rc_source f=note_loaded_source f;rc_noted:=f :: !rc_noted
end
module Vernac=struct
 let executed=ref []
 let load_vernac ~check:_ ~state file=
  assert(List.hd !SomaImport.noted=file && List.hd !SomaImport.rc_noted=file);
  let text=In_channel.with_open_bin file In_channel.input_all in
  executed:=(file,text)::!executed;
  if text="invalid" then failwith "rc failed";
  state+1
end
module Coqrc=struct
'''
suffix=r'''
end
let can_skip = Cli_guard.can_skip
let write file text=Out_channel.with_open_bin file(fun oc->output_string oc text)
let ()=
 let root=Sys.argv.(1) in
 let home=Filename.concat root "home" and config=Filename.concat root "config" in
 Unix.mkdir home 0o700;Unix.mkdir config 0o700;Unix.mkdir(Filename.concat config "coq")0o700;
 Unix.putenv "HOME" home;Unix.putenv "XDG_CONFIG_HOME" config;
 let candidates=Boot.UserConfig.rc_candidates ~warn:ignore in
 assert(candidates=[Filename.concat config "coq/coqrc.audit-version";Filename.concat config "coq/coqrc";Filename.concat home ".coqrc.audit-version";Filename.concat home ".coqrc"]);
 assert(can_skip() && Coqrc.load_rcfile ~rcfile:None ~state:0=0);
 List.iteri(fun i file->write file(string_of_int i))candidates;
 List.iteri(fun i file->
  assert(not(can_skip()));
  assert(Coqrc.load_rcfile ~rcfile:None ~state:0=1);
  assert(List.hd !SomaImport.noted=file);
  assert(List.hd !Vernac.executed=(file,string_of_int i));
  write file "edited";
  ignore(Coqrc.load_rcfile ~rcfile:None ~state:0);
  assert(List.hd !Vernac.executed=(file,"edited"));
  Sys.remove file)candidates;
 assert(can_skip());
 (* Dangling candidates conservatively block skipping, though not selected. *)
 let dangling=List.hd candidates in Unix.symlink(Filename.concat root "missing")dangling;
 assert(not(can_skip()) && Coqrc.load_rcfile ~rcfile:None ~state:0=0);Sys.remove dangling;
 (* Even a candidate aliasing a known companion must take the RC hook. *)
 let companion=Filename.concat root "main.ext" in write companion "companion";
 Unix.symlink companion dangling;
 ignore(Coqrc.load_rcfile ~rcfile:None ~state:0);
 assert(List.hd !SomaImport.rc_noted=dangling);Sys.remove dangling;
 let explicit=Filename.concat root "explicit.rc" in write explicit "explicit";
 assert(Coqrc.load_rcfile ~rcfile:(Some explicit) ~state:0=1);
 write explicit "invalid";
 assert(try ignore(Coqrc.load_rcfile ~rcfile:(Some explicit) ~state:0);false with Failure _->true);
 assert(List.hd !SomaImport.noted=explicit);
 print_endline "shared rc order, absent/present/edit/remove guard, dangling candidate, explicit/companion-alias loads and preparse RC provenance: passed"
'''
with tempfile.TemporaryDirectory(prefix='soma-rc-candidates-') as tmp:
 root=pathlib.Path(tmp)
 for name in ['util.ml','util.mli','userConfig.ml','userConfig.mli']:
  (root/name).write_bytes((source/'boot'/name).read_bytes())
 (root/'coq_config.ml').write_text('let version="audit-version"\n')
 (root/'boot.ml').write_text('module UserConfig = UserConfig\n')
 (root/'cli_guard.ml').write_text('exception Uncertain of string\nlet uncertain fmt=Printf.ksprintf(fun s->raise(Uncertain s))fmt\nlet can_skip ()=try\n'+guard+'true with Uncertain _->false\n')
 # Compile the actual driver guard BEFORE any Coqrc/compiler endpoint exists.
 # This catches accidentally adding a toplevel-only driver dependency.
 subprocess.run(['ocamlfind','ocamlopt','-package','unix','-c','coq_config.ml','util.mli','util.ml','userConfig.mli','userConfig.ml','boot.ml','cli_guard.ml'],cwd=root,check=True)
 (root/'check.ml').write_text(prefix+loader+suffix)
 subprocess.run(['ocamlfind','ocamlopt','-package','unix','-linkpkg','coq_config.cmx','util.cmx','userConfig.cmx','boot.cmx','cli_guard.cmx','check.ml','-o','check'],cwd=root,check=True)
 subprocess.run([str(root/'check'),tmp],cwd=root,check=True)
PY
