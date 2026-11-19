#!/usr/bin/env bash
# Actual driver restore function, with one deterministic filesystem interleaving:
# another compiler creates/populates the cache after the initial absent check.
set -euo pipefail
export SOMA_AUDIT_SOURCE="${SOMA_AUDIT_SOURCE:-$(cd "$(dirname "$0")/../.." && pwd -P)}"
python3 - <<'PY'
import os,pathlib,shutil,subprocess,tempfile
source=pathlib.Path(os.environ['SOMA_AUDIT_SOURCE'])
text=pathlib.Path(os.environ.get('SOMA_AUDIT_DRIVER_SOURCE',source/'topbin/soma.ml')).read_text()
with tempfile.TemporaryDirectory(prefix='soma-cache-restore-race-') as tmp:
    root=pathlib.Path(tmp)
    for name in ['somaMerkle.ml','somaCache.ml','somaModuleStore.ml','soma_cache_fs.c']:
        shutil.copyfile(source/'clib'/name,root/name)
    start=text.index('let rec mkdir_p d =')
    functions=text[start:text.index('(* The source files',start)]
    start=text.index('let restore_shared_cache file =')
    restore=text[start:text.index('let publish_shared_cache file =',start)]
    prelude=r'''
let write f text = Out_channel.with_open_bin f (fun oc -> output_string oc text)
let read f = In_channel.with_open_bin f In_channel.input_all
let triggered = ref false
module Sys = struct
  include Sys
  let file_exists file =
    let existed = Stdlib.Sys.file_exists file in
    if file = "cache" && not !triggered then begin
      triggered := true;
      Unix.mkdir "cache" 0o700;
      write "cache/protected" "live compiler bytes"
    end;
    existed
end
let shared_store_for _ = Some ("store",("root","cache","key"))
let module_store_context _ = SomaMerkle.string "context"
'''
    main=r'''
let () =
  Unix.mkdir "store" 0o700; Unix.mkdir "store/key" 0o700; Unix.mkdir "root" 0o700;
  write "store/key/protected" "old cached bytes";
  SomaCache.record "store/key/protected";
  assert (SomaCache.trusted "store/key/protected");
  restore_shared_cache "main.soma";
  assert !triggered;
  if read "cache/protected" <> "live compiler bytes" then
    failwith "restore overwrote a cache created by another compiler after its absent check";
  print_endline "Actual driver restore preserves concurrently created live cache: passed"
'''
    (root/'check.ml').write_text(prelude+functions+restore+main)
    env=dict(os.environ,XDG_CACHE_HOME=str(root/'xdg'),SOMA_CACHE_ID='restore-race')
    subprocess.run(['ocamlfind','ocamlc','-custom','-package','digestif.c,unix','-linkpkg',
                    'somaMerkle.ml','somaCache.ml','soma_cache_fs.c','somaModuleStore.ml','check.ml','-o','check'],
                   cwd=root,env=env,check=True)
    subprocess.run([str(root/'check')],cwd=root,env=env,check=True)
PY
