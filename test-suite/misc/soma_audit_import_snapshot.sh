#!/usr/bin/env bash
# Real import output/stamp/receipt functions; only kernel compilation is a
# controlled worker that captures old bytes before a deterministic edit.
set -euo pipefail
export SOMA_AUDIT_SOURCE="${SOMA_AUDIT_SOURCE:-$(cd "$(dirname "$0")/../.." && pwd -P)}"
python3 - <<'PY'
import os,pathlib,shutil,subprocess,tempfile
source=pathlib.Path(os.environ['SOMA_AUDIT_SOURCE'])
text=pathlib.Path(os.environ.get('SOMA_AUDIT_IMPORT_SOURCE', source/'vernac/somaImport.ml')).read_text()
def section(a,b): return text[text.index(a):text.index(b,text.index(a))]
with tempfile.TemporaryDirectory(prefix='soma-import-snapshot-') as tmp:
    root=pathlib.Path(tmp)
    for f in ['somaMerkle.ml','somaCache.ml']: shutil.copyfile(source/'clib'/f,root/f)
    extra=[]
    if (source/'clib/somaModuleStore.ml').exists():
        for f in ['somaModuleStore.ml','soma_cache_fs.c','somaToml.ml','somaRuleInputs.ml']: shutil.copyfile(source/'clib'/f,root/f)
        extra=['soma_cache_fs.c','somaModuleStore.ml','somaToml.ml','somaRuleInputs.ml']
    prelude=r'''
module Pp = struct let str x = x let ( ++ ) = ( ^ ) end
module CErrors = struct let user_err x = failwith x end
module CString = struct let is_prefix prefix s = String.starts_with ~prefix s end
module DirPath = struct let to_string x = x end
module Library = struct let loaded_library_files () = [] end
module ObjFile = struct
let same_values _ _ _ = assert false
let splice ~base:_ ~from:_ _ ~out:_ = assert false
end
let env_value = Sys.getenv_opt
let env_root () = None
let cache p = Filename.concat p ".soma-cache"
let absolute x = x
let rocq_selection_uncertified = ref false
let rocq_entry _ = None
let rocq_inputs _ _ = None
let file_digest = SomaMerkle.file_hash
let interface_digest = file_digest
let imported = ref []
let proof_job () = None
let job_status _ = ()
let stamp_var = "SOMA_IMPORT_STAMP"
let source_var = "SOMA_IMPORT_SOURCE"
let expected_source_var = "SOMA_IMPORT_EXPECTED_SOURCE"
let expected_candidate_var = "SOMA_IMPORT_EXPECTED_CANDIDATE"
let rules_source_var = "SOMA_IMPORT_RULE_SOURCE"
let root_of_dir = Unix.realpath
let root_rules_name = Filename.basename
let build_var = "SOMA_BUILD_ROOT"
let interface_digest_var = "SOMA_INTERFACE_DIGEST"
let loaded_source_inputs_var = "SOMA_LOADED_SOURCE_INPUTS"
let loaded_source_request_var = "SOMA_LOADED_SOURCE_REQUEST"
let root_var = "SOMA_PROJECT_ROOT"
let cache_var = "SOMA_PROJECT_CACHE"
let prefix_var = "SOMA_PROJECT_PREFIX"
let stack_var = "SOMA_IMPORT_STACK"
let proof_job_var = "SOMA_PROOF_JOB"
let interface_var = "SOMA_IMPORT_INTERFACE"
type project = { root : string; cache_dir : string; prefix : string }
let mkdir_p = SomaCache.mkdir
let vo_of p path = Filename.concat p.cache_dir (path ^ ".vo")
let stamp_of p path = Filename.concat p.cache_dir (path ^ ".stamp")
let build_root ?loc:_ () = Sys.getcwd ()
let stack ?loc:_ () = []
let qualified _ path = path
module Boot = struct module Env = struct let self = "controlled-worker" end end
'''
    functions=section('let source_hash ','(* What an importer')
    if 'let import_outputs :' in text:
        functions+=section('let import_outputs :','(* The digests of the files')
    functions+=section('let rule_source_of ' if 'let rule_source_of ' in text else 'let compile_command ','\n(* Starts a compilation')
    # Exercise the real caller's pre-spawn environment, not a reconstructed
    # expected hash. The old production function returned a triple.
    if 'prog, argv, env, expected_source' in functions:
        functions+='\nlet captured_environment p path src = let _,_,env,_ = compile_command ~interface:false p path src in env\n'
        functions+='let deferred_environment p path src expected = let _,_,env,_ = compile_command ~interface:false ~expected_source:expected p path src in env\n'
    else:
        functions+='\nlet captured_environment p path src = let _,_,env = compile_command ~interface:false p path src in env\n'
        functions+='let deferred_environment p path src _ = captured_environment p path src\n'
    functions+=section('let stamp_format =','\nlet rec mkdir_p')
    functions+=section('let write_stamp () =','\n(* Observational metadata')
    functions+=text[text.index('let checked_output vo ='):]
    # checked_output/install_checked are the final production functions.
    (root/'check.ml').write_text(prelude+functions+r'''
let write f s = Out_channel.with_open_bin f (fun oc -> output_string oc s)
let read f = In_channel.with_open_bin f In_channel.input_all
let signal fd = ignore (Unix.write fd (Bytes.of_string "x") 0 1)
let await fd = let b = Bytes.create 1 in assert (Unix.read fd b 0 1 = 1)
let run suffix ~late ~other =
  let dir = Filename.concat (Sys.getcwd ()) ("case-" ^ suffix ^ string_of_bool late ^ string_of_bool other) in
  Unix.mkdir dir 0o755;
  let src = Filename.concat dir "item.soma" in
  let rule = Filename.concat dir (Filename.basename dir) in
  let companion = match suffix with
    | "source" -> src
    | "rule" -> rule ^ ".ext"
    | "suppressor" -> rule ^ ".soma"
    | _ -> Filename.remove_extension src ^ "." ^ suffix in
  let vo = Filename.concat dir "item.vo" in
  let stamp = Filename.concat dir "item.stamp" in
  write src "old-source";
  if suffix = "suppressor" then write (rule ^ ".ext") "old-rule";
  if companion <> src && suffix <> "rule" then write companion "old-companion";
  let environment = captured_environment {root=dir;cache_dir=dir;prefix=""} "item" src in
  let ready_r,ready_w = Unix.pipe () in
  let resume_r,resume_w = Unix.pipe () in
  match Unix.fork () with
  | 0 ->
    Unix.close ready_r; Unix.close resume_w;
    Array.iter (fun binding ->
        let split = String.index binding '=' in
        Unix.putenv (String.sub binding 0 split)
          (String.sub binding (split+1) (String.length binding-split-1))) environment;
    let parsed = read src in
    let result = try
      if late then begin
        write (checked_output vo) parsed; install_checked ~vo;
        signal ready_w; await resume_r;
        write_stamp ()
      end else begin
        signal ready_w; await resume_r;
        write (checked_output vo) parsed; install_checked ~vo; write_stamp ()
      end;
      0
    with Failure msg ->
      if not (String.contains msg ':') then raise (Failure msg);
      23 in
    exit result
  | pid ->
    Unix.close ready_w; Unix.close resume_r;
    await ready_r;
    if suffix = "suppressor" then Sys.remove companion else write companion "new-bytes";
    if other then write vo "other-writer-output";
    signal resume_w;
    let status = snd (Unix.waitpid [] pid) in
    List.iter Unix.close [ready_r;resume_w];
    (match status with
     | Unix.WEXITED 23 -> ()
     | Unix.WEXITED 0 ->
       let poisoned = match read_stamp stamp with
         | Some (hash,_,_,_) -> hash = source_hash src && SomaCache.trusted vo && read vo = "old-source"
         | None -> false in
       if poisoned then failwith "old object certified with post-compilation source bytes";
       failwith "source edit did not refuse import publication"
     | _ -> failwith "unexpected worker failure");
    if other then assert (read vo = "other-writer-output")
    else assert (not (Sys.file_exists vo));
    assert (not (Sys.file_exists stamp));
    assert (Array.to_list (Sys.readdir dir) |> List.for_all (fun n -> not (String.starts_with ~prefix:".soma-" n)))
let () =
  List.iter (fun suffix -> run suffix ~late:false ~other:false)
    ["source";"exp";"ext";"wasm";"ml";"lean";"rule";"suppressor"];
  run "source" ~late:false ~other:true;
  run "source" ~late:true ~other:false;
  run "rule" ~late:true ~other:false;
  run "suppressor" ~late:true ~other:false;
  run "source" ~late:true ~other:true;
  assert (checked_output "root.vo" = "root.vo");
  write "deferred.soma" "old-interface";
  let expected = source_hash "deferred.soma" in
  write "deferred.soma" "new-source";
  let rejected = try ignore (deferred_environment
      {root=Sys.getcwd ();cache_dir=Sys.getcwd ();prefix=""} "deferred" "deferred.soma" expected); false
    with Failure _ -> true in
  if not rejected then failwith "deferred proof adopted changed source snapshot";
  print_endline "Import snapshot changes reject old objects/new stamps; owned-output cleanup and unrelated writer preservation: passed"
''')
    env=dict(os.environ,XDG_CACHE_HOME=str(root/'xdg'),SOMA_CACHE_ID='snapshot-regression')
    subprocess.run(['ocamlfind','ocamlc','-custom','-package','digestif.c,unix','-linkpkg','somaMerkle.ml','somaCache.ml',*extra,'check.ml','-o','check'],cwd=root,env=env,check=True)
    subprocess.run([str(root/'check')],cwd=root,env=env,check=True)
PY
