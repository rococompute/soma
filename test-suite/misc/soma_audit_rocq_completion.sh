#!/usr/bin/env bash
# Exercise actual SHA receipts and completed-library validation, not a mock
# trust predicate. A cache marker cannot certify changed/unrecorded objects.
set -euo pipefail
SOURCE="$(cd "$(dirname "$0")/../.." && pwd -P)"
export SOMA_AUDIT_SOURCE="$SOURCE"
python3 - <<'PY'
import os,pathlib,shutil,subprocess,tempfile
source=pathlib.Path(os.environ['SOMA_AUDIT_SOURCE'])
with tempfile.TemporaryDirectory(prefix='soma-rocq-completion-') as tmp:
    root=pathlib.Path(tmp)
    for name in ['somaMerkle.ml','somaCache.ml','somaRocqCache.ml']:
        shutil.copyfile(source/'clib'/name,root/name)
    (root/'check.ml').write_text(r'''
let write p s = Out_channel.with_open_bin p (fun oc -> output_string oc s)
let () =
  let root = Unix.realpath (Sys.getcwd ()) in
  let project = Filename.concat root "project" in
  Unix.mkdir project 0o755;
  let git = Unix.create_process "git" [|"git"; "init"; "-q"; project|] Unix.stdin Unix.stdout Unix.stderr in
  assert (snd (Unix.waitpid [] git) = Unix.WEXITED 0);
  let original = Filename.concat project "original.v" in
  write original "Definition value := 1.\n";
  let entry = Filename.concat project "cache-entry" in
  Unix.mkdir entry 0o755;
  let src = Filename.concat entry "src" in
  Unix.mkdir src 0o755;
  let source = Filename.concat src "A.v" and output = Filename.concat src "A.vo" in
  write source "Definition value := 1.\n";
  write output "compiler output one";
  let inputs = Filename.concat entry ".soma-inputs" in
  write inputs ("soma-rocq-inputs 1\ninput \"original.v\" " ^ SomaMerkle.file_hash original ^ "\n");
  SomaCache.record inputs;
  let key = "library-full-sha-key" in
  let snapshot = SomaRocqCache.source_snapshot ~directory:entry in
  let publish () = SomaRocqCache.publish ~key ~directory:entry ~sources:snapshot ~theories:["mylib",src] in
  let load () = SomaRocqCache.load ~key ~directory:entry ~resolve_input:(Filename.concat project) in
  assert (load () = None);
  publish ();
  assert (load () <> None);
  assert (SomaRocqCache.load ~key:"another-key" ~directory:entry ~resolve_input:(Filename.concat project) = None);
  let complete = Filename.concat entry SomaRocqCache.marker in
  assert (not (SomaCache.trusted_metadata complete ~contents:"forged parser bytes"));
  write output "different compiled object";
  assert (SomaCache.trusted inputs && load () = None);
  write output "compiler output one";
  assert (load () <> None);
  let theory_file = Filename.concat entry "theories" in
  let theory = In_channel.with_open_bin theory_file In_channel.input_all in
  write theory_file "soma-rocq-theories 2\ntheory \"mylib\" \"../outside\"\n";
  assert (load () = None);
  write theory_file theory;
  assert (load () <> None);
  let extra = Filename.concat src "unrecorded.v" in
  write extra "Definition extra := 2.\n";
  assert (load () = None);
  Sys.remove extra;
  write original "Definition value := 2.\n";
  assert (load () = None);
  write original "Definition value := 1.\n";
  assert (load () <> None);
  let backup = complete ^ ".saved" in
  Unix.rename complete backup;
  Unix.symlink backup complete;
  assert (load () = None);
  Sys.remove complete;
  Unix.rename backup complete;
  let saved = Filename.concat entry "saved-src" in
  Unix.rename src saved;
  Unix.symlink saved src;
  assert (load () = None);
  Sys.remove src;
  Unix.rename saved src;
  assert (load () <> None);
  write source "Definition value := 3.\n";
  let rejected = try publish (); false with Failure _ -> true in
  assert rejected;
  assert (load () = None);
  print_endline "Rocq completion provenance binds source metadata, theory paths and all compiled outputs: passed"
''')
    env=dict(os.environ,XDG_CACHE_HOME=str(root/'xdg'),SOMA_CACHE_ID='completion-test')
    subprocess.run(['ocamlfind','ocamlc','-package','digestif.c,unix','-linkpkg',
                    'somaMerkle.ml','somaCache.ml','somaRocqCache.ml','check.ml','-o','check'],cwd=root,env=env,check=True)
    subprocess.run([str(root/'check')],cwd=root,env=env,check=True)
PY
