#!/usr/bin/env bash
# Exercise the exact shared policy and full import fingerprint, without
# replacing source hashing or rule selection with a duplicate parser.
set -euo pipefail
export SOMA_AUDIT_SOURCE="${SOMA_AUDIT_SOURCE:-$(cd "$(dirname "$0")/../.." && pwd -P)}"
python3 - <<'PY'
import os,pathlib,shutil,subprocess,tempfile
source=pathlib.Path(os.environ['SOMA_AUDIT_SOURCE'])
with tempfile.TemporaryDirectory(prefix='soma-rule-inputs-') as tmp:
    root=pathlib.Path(tmp)
    for f in ['somaMerkle.ml','somaCache.ml','somaModuleStore.ml','soma_cache_fs.c','somaToml.ml','somaRuleInputs.ml']:shutil.copyfile(source/'clib'/f,root/f)
    text=(source/'vernac/somaImport.ml').read_text();function=text[text.index('let source_hash '):text.index('\nlet digest ',text.index('let source_hash '))]
    (root/'check.ml').write_text(r'''
let env_value = Sys.getenv_opt
let env_root () = None
let rules_source_var = "SOMA_IMPORT_RULE_SOURCE"
let absolute p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p
let root_of_dir = Unix.realpath
let root_rules_name _ = "project"
'''+function+r'''
let write f body = Out_channel.with_open_bin f (fun oc -> output_string oc body)
let () =
  let root = Sys.getcwd () in
  Unix.mkdir "lib" 0o755;
  write "lib/item.soma" "flag : bool := true.\n";
  let item = Filename.concat root "lib/item.soma" in
  let select () = SomaRuleInputs.select ~root ~root_name:"project" ~source:item in
  let initial = SomaRuleInputs.fingerprint (select ()) in
  let hash0 = source_hash ~root item in
  write "lib/lib.ext" "Notation \"'true'\" := false.\n";
  let selected = SomaRuleInputs.fingerprint (select ()) in
  assert (selected <> initial && source_hash ~root item <> hash0);
  let selected_hash = source_hash ~root item in
  write "lib/lib.ext" "(* body edit, selection unchanged *)\nNotation \"'true'\" := false.\n";
  assert (SomaRuleInputs.fingerprint (select ()) = selected);
  assert (source_hash ~root item = selected_hash);
  write "lib/lib.soma" "unused : nat := 0.\n";
  let suppressed = SomaRuleInputs.fingerprint (select ()) in
  assert (suppressed <> selected);
  let suppressed_hash = source_hash ~root item in
  write "lib/lib.soma" "unused : nat := 123.\n";
  write "unrelated.soma" "unrelated : nat := 456.\n";
  assert (SomaRuleInputs.fingerprint (select ()) = suppressed);
  assert (source_hash ~root item = suppressed_hash);
  Sys.remove "lib/lib.soma";
  assert (SomaRuleInputs.fingerprint (select ()) = selected);
  Sys.remove "lib/lib.ext";
  write "lib/lib.exp" "orphan proof";
  assert (SomaRuleInputs.fingerprint (select ()) <> initial);
  Sys.remove "lib/lib.exp";
  assert (SomaRuleInputs.fingerprint (select ()) = initial);
  write "lib/lib.lang" "legacy names are checked even if suppressed/self";
  assert (SomaRuleInputs.fingerprint (select ()) <> initial);
  Sys.remove "lib/lib.lang";
  let body = "Definition flag : bool := true.\n" in
  write "lib/lib.ext" body; write "lib/lib.soma" body;
  let ext = Filename.concat root "lib/lib.ext" and soma = Filename.concat root "lib/lib.soma" in
  assert (SomaModuleStore.source_hash ext = SomaModuleStore.source_hash soma);
  assert (source_hash ~root ext <> source_hash ~root soma);
  let before = SomaRuleInputs.fingerprint (select ()) in
  Unix.mkdir "clone" 0o755; Unix.mkdir "clone/lib" 0o755;
  write "clone/lib/item.soma" "flag : bool := true.\n";
  write "clone/lib/lib.ext" body; write "clone/lib/lib.soma" body;
  let clone = Filename.concat root "clone" in
  assert (SomaRuleInputs.fingerprint (SomaRuleInputs.select ~root:clone ~root_name:"project"
      ~source:(Filename.concat clone "lib/item.soma")) = before);
  assert (source_hash ~root:clone (Filename.concat clone "lib/item.soma") = source_hash ~root item);
  assert (SomaRuleInputs.fingerprint (SomaRuleInputs.select ~root ~root_name:"renamed" ~source:item) <> before);
  print_endline "Exact rule membership, suppressors, orphan/legacy inputs, kind and location-independent import identity: passed"
''')
    env=dict(os.environ,XDG_CACHE_HOME=str(root/'xdg'),SOMA_CACHE_ID='rule-input-harness')
    subprocess.run(['ocamlfind','ocamlc','-custom','-package','digestif.c,unix','-linkpkg','somaMerkle.ml','somaCache.ml','soma_cache_fs.c','somaModuleStore.ml','somaToml.ml','somaRuleInputs.ml','check.ml','-o','check'],cwd=root,env=env,check=True)
    subprocess.run([str(root/'check')],cwd=root,env=env,check=True)
PY
