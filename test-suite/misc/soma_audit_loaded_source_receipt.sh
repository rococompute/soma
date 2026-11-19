#!/usr/bin/env bash
# A producer receipt cannot by itself bind metadata to a fresh child. Test
# the production sidecar reader against real receipts and replayed old bytes.
set -euo pipefail
export SOMA_AUDIT_SOURCE="${SOMA_AUDIT_SOURCE:-$(cd "$(dirname "$0")/../.." && pwd -P)}"
python3 - <<'PY'
import os,pathlib,shutil,subprocess,tempfile
source=pathlib.Path(os.environ['SOMA_AUDIT_SOURCE'])
with tempfile.TemporaryDirectory(prefix='soma-load-receipt-') as tmp:
    root=pathlib.Path(tmp)
    for f in ['somaMerkle.ml','somaCache.ml']:shutil.copyfile(source/'clib'/f,root/f)
    plugin=(source/'plugins/soma_rocq/soma_rocq.ml').read_text()
    function=plugin[plugin.index('let read_loaded_source_inputs '):plugin.index('(* [ts] compiled by Soma')]
    (root/'check.ml').write_text(r'''
let str x = x
let error = failwith
let read_file file = In_channel.with_open_bin file In_channel.input_all
'''+function+r'''
let write file text = Out_channel.with_open_bin file (fun oc -> output_string oc text)
let rejected f = try ignore (f ()); false with Failure _ -> true
let () =
  let source = Filename.concat (Sys.getcwd ()) "outside.v" in
  write source "Definition value := 1.\n";
  let first = SomaMerkle.string "first request" and next = SomaMerkle.string "next request" in
  let body request complete = Printf.sprintf
      "soma-loaded-inputs 2\nrequest %S\nuncertain %b\ninput %S %s\n"
      request (not complete) source (SomaMerkle.file_hash source) in
  let original = body first false in
  write "old.inputs" original; SomaCache.record "old.inputs";
  let inputs, complete = read_loaded_source_inputs ~request:first "old.inputs" in
  assert (List.length inputs = 1 && not complete);
  write "new.inputs" original;
  assert (SomaCache.trusted_metadata "new.inputs" ~contents:original);
  assert (rejected (fun () -> read_loaded_source_inputs ~request:next "new.inputs"));
  let changed_request = body next true in
  write "new.inputs" changed_request;
  assert (rejected (fun () -> read_loaded_source_inputs ~request:next "new.inputs"));
  SomaCache.record "new.inputs";
  assert (snd (read_loaded_source_inputs ~request:next "new.inputs"));
  write source "Definition value := 2.\n";
  assert (rejected (fun () -> read_loaded_source_inputs ~request:next "new.inputs"));
  print_endline "Loaded-source receipts bind fresh child requests and reject replay, altered metadata and changed inputs: passed"
''')
    env=dict(os.environ,XDG_CACHE_HOME=str(root/'xdg'),SOMA_CACHE_ID='source-load-request-test')
    subprocess.run(['ocamlfind','ocamlc','-package','digestif.c,unix','-linkpkg','somaMerkle.ml','somaCache.ml','check.ml','-o','check'],cwd=root,env=env,check=True)
    subprocess.run([str(root/'check')],cwd=root,env=env,check=True)
PY
