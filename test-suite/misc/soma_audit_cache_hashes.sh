#!/usr/bin/env bash
# Hash and stamp checks use the production cache/reader functions without
# rebuilding the compiler. Receipt provenance is never replaced by a stub.
set -euo pipefail
export SOMA_AUDIT_SOURCE="${SOMA_AUDIT_SOURCE:-$(cd "$(dirname "$0")/../.." && pwd -P)}"
python3 - <<'PY'
import os
import pathlib
import shutil
import subprocess
import tempfile

source = pathlib.Path(os.environ['SOMA_AUDIT_SOURCE'])
with tempfile.TemporaryDirectory(prefix='soma-cache-hashes-') as tmp:
    root = pathlib.Path(tmp)
    merkle = source / 'clib/somaMerkle.ml'
    if not merkle.exists():
        merkle = source / 'topbin/somaMerkle.ml'
    shutil.copyfile(merkle, root / 'somaMerkle.ml')
    shutil.copyfile(source / 'clib/somaCache.ml', root / 'somaCache.ml')
    extra = []
    if (source / 'clib/somaModuleStore.ml').exists():
        for name in ['somaModuleStore.ml', 'soma_cache_fs.c', 'somaRuleInputs.ml']:
            shutil.copyfile(source / 'clib' / name, root / name)
        extra = ['soma_cache_fs.c', 'somaModuleStore.ml', 'somaRuleInputs.ml']
    text = (source / 'vernac/somaImport.ml').read_text()
    start = text.index('let source_hash ')
    end = text.index('(* What an importer', start)
    stamp = text.index('let stamp_format =')
    stamp_end = text.index('\nlet rec mkdir_p', stamp)
    (root / 'cache_functions.ml').write_text(r'''
let rules_source_var = "SOMA_IMPORT_RULE_SOURCE"
let env_value = Sys.getenv_opt
let env_root () = None
let absolute p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p
let root_of_dir = Unix.realpath
let root_rules_name = Filename.basename
''' + text[start:end] + text[stamp:stamp_end])
    (root / 'check.ml').write_text(r'''
let write f s = Out_channel.with_open_bin f (fun oc -> output_string oc s)
let () =
  let hash = SomaMerkle.string "abc" in
  assert (hash = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
  write "source.soma" "x : nat := 1.\n";
  assert (String.length (Cache_functions.source_hash "source.soma") = 64);
  let first = Cache_functions.source_hash "source.soma" in
  write "source.soma" "x : nat := 2.\n";
  assert (first <> Cache_functions.source_hash "source.soma");
  write "object.vo" "object bytes";
  write "object.stamp" "stamp bytes";
  SomaCache.record "object.vo";
  assert (String.length (Filename.basename (SomaCache.receipt "object.vo")) = 64);
  assert (SomaCache.trusted "object.vo");
  write "object.stamp" "different stamp bytes";
  assert (not (SomaCache.trusted "object.vo"));
  let header = Cache_functions.stamp_format ^ "\n" in
  let valid = header ^ "source " ^ hash ^ "\n" in
  let parse contents = write "read.stamp" contents; Cache_functions.read_stamp "read.stamp" in
  assert (parse valid <> None);
  List.iter (fun text -> assert (parse text = None))
    [ ""; header; header ^ "source " ^ hash;
      valid ^ "unknown ignored-before\n";
      valid ^ "source " ^ hash ^ "\n";
      header ^ "source not-a-sha256\n";
      valid ^ "import leaf " ^ hash ^ "\nimport leaf " ^ hash ^ "\n";
      valid ^ "library A.B " ^ hash ^ "\nlibrary A.B " ^ hash ^ "\n";
      valid ^ "input \"path with spaces.v\" " ^ hash ^ "\ninput \"path with spaces.v\" " ^ hash ^ "\n";
      valid ^ "input bad-unquoted " ^ hash ^ "\n" ];
  assert (parse (valid ^ "import leaf " ^ hash ^ "\nlibrary A.B " ^ hash ^
                  "\ninput \"path with spaces.v\" " ^ hash ^ "\n") <> None);
  print_endline "SHA-256 source/paired receipts and strict stamp parsing: passed"
''')
    env = dict(os.environ, XDG_CACHE_HOME=str(root / 'xdg'), SOMA_CACHE_ID='hash-regression')
    subprocess.run(['ocamlfind', 'ocamlc', '-custom', '-package', 'digestif.c,unix', '-linkpkg',
                    'somaMerkle.ml', 'somaCache.ml', *extra, 'cache_functions.ml', 'check.ml', '-o', 'check'],
                   cwd=root, env=env, check=True)
    subprocess.run([str(root / 'check')], cwd=root, env=env, check=True)
PY
