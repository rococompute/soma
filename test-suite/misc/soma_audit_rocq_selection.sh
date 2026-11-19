#!/usr/bin/env bash
# Execute the production ensure cache-hit path against actual completion
# receipts. Only fetch/compiler/platform integration is stubbed: a warm hit
# must apply CURRENT selection policy without rewriting shared metadata.
set -euo pipefail
export SOMA_AUDIT_SOURCE="${SOMA_AUDIT_SOURCE:-$(cd "$(dirname "$0")/../.." && pwd -P)}"
python3 - <<'PY'
import os,pathlib,shutil,subprocess,tempfile
source=pathlib.Path(os.environ['SOMA_AUDIT_SOURCE'])
with tempfile.TemporaryDirectory(prefix='soma-rocq-selection-') as tmp:
    root=pathlib.Path(tmp)
    for name in ['somaMerkle.ml','somaCache.ml','somaRocqCache.ml']:
        shutil.copyfile(source/'clib'/name,root/name)
    plugin=pathlib.Path(os.environ.get('SOMA_AUDIT_ROCQ_SOURCE',source/'plugins/soma_rocq/soma_rocq.ml')).read_text()
    start=plugin.index('let compiled_theories ')
    end=plugin.index('\n(* [Rocq Library',start)
    ensure=plugin[start:end]
    imports=(source/'vernac/somaImport.ml').read_text()
    start=imports.index('let rocq_selection_uncertified =')
    end=imports.index('\nlet rocq_inputs_name',start)
    policy=imports[start:end]
    prelude=r'''
let project = Filename.concat (Unix.realpath (Sys.getcwd ())) "project"
let cache_root = Filename.concat project "cache"
let str x = x
let qstring x = Printf.sprintf "%S" x
let ( ++ ) = ( ^ )
let spc () = " "
let fnl () = "\n"
let error x = failwith x
module CString = struct let is_prefix prefix value = String.starts_with ~prefix value end
module SomaImport = struct
let built_root () = project
'''+policy+r'''
let resolve_project_file file = if Filename.is_relative file then Filename.concat project file else file
let record_rocq_inputs ~directory:_ ~complete:_ _ : unit = failwith "unexpected cache miss"
end
module SomaOpam = struct
let mkdir_p p = if not (Sys.file_exists p) then Unix.mkdir p 0o755
let ensure_switch ~who:_ ~log:_ = "unused-opam-switch"
let run ~log:_ _ = failwith "fetch must not run on a warm hit"
let tail_of_file _ = ""
let read_lines file = try In_channel.with_open_bin file In_channel.input_all |> String.split_on_char '\n' |> List.filter ((<>) "") with Sys_error _ -> []
end
type source = Opam of string option | Local of string
type theory = { dir:string; logical:string; subdirs:bool }
let cache () = cache_root
let require_component _ _ = ()
let soma_key () = "test-toolchain"
let source_key _ = "test-source-snapshot"
let source_files _ = []
let copy_tree _ _ = failwith "unexpected fetch"
let ensure_repository ~switch:_ ~log:_ = ()
let latest ~switch:_ ~log:_ _ = "1.0"
let lock_file root name = Filename.concat root (name ^ ".lock")
let with_lock _ f = f ()
let theories ~package:_ _ : theory list = failwith "unexpected compile"
let compile ~prerequisites:_ ~name:_ ~log:_ _ : unit = failwith "unexpected compile"
'''
    (root/'harness.ml').write_text(prelude+ensure+r'''
let write p s = Out_channel.with_open_bin p (fun oc -> output_string oc s)
let prepare name =
  let directory = Filename.concat cache_root name in
  Unix.mkdir directory 0o755;
  let src = Filename.concat directory "src" in
  Unix.mkdir src 0o755;
  write (Filename.concat src "A.v") "Definition value := 1.\n";
  write (Filename.concat src "A.vo") "compiler output";
  let inputs = Filename.concat directory ".soma-inputs" in
  write inputs ("soma-rocq-inputs 1\ninput \"original.v\" " ^ SomaMerkle.file_hash (Filename.concat project "original.v") ^ "\n");
  SomaCache.record inputs;
  let sources = SomaRocqCache.source_snapshot ~directory in
  SomaRocqCache.publish ~key:name ~directory ~sources ~theories:["mylib",src];
  inputs
let () =
  Unix.mkdir project 0o755; Unix.mkdir cache_root 0o755;
  write (Filename.concat project "original.v") "Definition value := 1.\n";
  let opam_name = "pkg.1.0-test-toolchain" in
  let inputs = prepare opam_name in
  let before = SomaMerkle.file_hash inputs in
  ignore (ensure ~package:"pkg" (Opam (Some "1.0")));
  assert (not !(SomaImport.rocq_selection_uncertified));
  ignore (ensure ~package:"pkg" (Opam None));
  if not !(SomaImport.rocq_selection_uncertified) then failwith "floating warm cache hit was incorrectly certified";
  assert (SomaMerkle.file_hash inputs = before);
  SomaImport.rocq_selection_uncertified := false;
  let external_dir = Filename.concat (Unix.realpath (Sys.getcwd ())) "external" in
  Unix.mkdir external_dir 0o755;
  let local_name = "pkg-local-" ^ SomaMerkle.string ("test-source-snapshot\000test-toolchain") in
  ignore (prepare local_name);
  ignore (ensure ~package:"pkg" (Local external_dir));
  if not !(SomaImport.rocq_selection_uncertified) then failwith "external warm cache hit was incorrectly certified";
  selected_libraries := [];
  let alpha1 = "alpha.1.0-test-toolchain" in
  ignore (prepare alpha1);
  ignore (ensure ~package:"alpha" (Opam (Some "1.0")));
  let prereq1 = prerequisite_key "test-toolchain" !selected_libraries in
  let beta1 = "beta.1.0-" ^ prereq1 in
  ignore (prepare beta1);
  ignore (ensure ~package:"beta" (Opam (Some "1.0")));
  let paths = prerequisite_paths (List.filter (fun (name,_) -> name <> "beta") !selected_libraries) in
  assert (paths = ["mylib", Filename.concat (Filename.concat cache_root alpha1) "src"]);
  ignore (ensure ~package:"beta" (Opam (Some "1.0")));
  assert (List.length !selected_libraries = 2);
  selected_libraries := [];
  ignore (prepare "alpha.2.0-test-toolchain");
  ignore (ensure ~package:"alpha" (Opam (Some "2.0")));
  let prereq2 = prerequisite_key "test-toolchain" !selected_libraries in
  assert (prereq1 <> prereq2);
  ignore (prepare ("beta.1.0-" ^ prereq2));
  ignore (ensure ~package:"beta" (Opam (Some "1.0")));
  write (Filename.concat project "original.v") "Definition changed := 2.\n";
  let rejected = try ignore (ensure ~package:"beta" (Opam (Some "1.0"))); false with Failure _ -> true in
  assert rejected;
  write (Filename.concat project "original.v") "Definition value := 1.\n";
  selected_libraries := [];
  let pinned_dir = Filename.concat cache_root opam_name in
  List.iter (fun name ->
      let path = Filename.concat pinned_dir name in
      Sys.remove path; Unix.symlink "missing-marker-target" path) ["theories"; SomaRocqCache.marker];
  let refused = try ignore (ensure ~package:"pkg" (Opam (Some "1.0"))); false with Failure _ -> true in
  assert refused;
  assert (Sys.file_exists (Filename.concat pinned_dir "src/A.vo"));
  print_endline "Warm pinned-to-floating and local-to-external requests remain uncertified without mutating cache metadata: passed"
''')
    env=dict(os.environ,XDG_CACHE_HOME=str(root/'xdg'),SOMA_CACHE_ID='selection-test')
    subprocess.run(['ocamlfind','ocamlc','-package','digestif.c,unix','-linkpkg',
                    'somaMerkle.ml','somaCache.ml','somaRocqCache.ml','harness.ml','-o','check'],cwd=root,env=env,check=True)
    subprocess.run([str(root/'check')],cwd=root,env=env,check=True)
PY
