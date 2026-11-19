#!/usr/bin/env bash
# Compile the production receipt/parser/resume helper directly; no compiler
# rebuild and no substitute cache model. Native integration is tested separately.
set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd -P)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
for name in somaMerkle somaCache somaBuildInfo somaPhase; do
  cp "$root/clib/$name.ml" "$root/clib/$name.mli" "$work/"
done
cat > "$work/check.ml" <<'ML'
let write path text = Out_channel.with_open_bin path (fun oc -> output_string oc text)
let text path = In_channel.with_open_bin path In_channel.input_all
let path = Filename.concat
let () =
  let base=Unix.realpath Sys.argv.(1) and mode=Sys.argv.(2) in
  if mode="nohome" then begin
    assert(Sys.getenv_opt "HOME"=None && Sys.getenv_opt "XDG_CACHE_HOME"=None);
    assert(SomaPhase.record_path "fixture-key"=None);
    print_endline "unset cache home declines optional reuse: passed";exit 0
  end;
  let root=path base "project" and dir=path base "generated" and install=path base "install" in
  List.iter (fun d -> Unix.mkdir d 0o700) [root;dir;install];
  Unix.putenv "XDG_CACHE_HOME" (path base "cache"); Unix.putenv "SOMA_CACHE_ID" "phase-unit-compiler";
  Unix.putenv "SOMA_BUILD_PHASE" (path base "draft"); Unix.putenv "SOMA_PHASE_KEY" "fixture-key";
  Unix.putenv "SOMA_PHASE_ROOT" root;Unix.putenv "SOMA_PHASE_COQLIB" install;
  Unix.putenv "SOMA_PHASE_RUNTIMELIB" install;
  let source=path root "main.soma" and output=path root "main.exe" in
  write source "main := 1.";write output "initial native product";
  let library=path install "dependency.vo" in write library "fixture loaded object bytes";
  ignore (SomaPhase.with_import library (fun () ->
      if mode="drift" then write library "replacement object bytes"; text library));
  (* Code-free umbrellas execute nothing; every implementing dependency still
     reaches its own nonempty-file guard independently. *)
  SomaPhase.plugin ~package:"digestif" ~files:[];
  SomaPhase.plugin ~package:"fixture.umbrella" ~files:[];
  if mode="plugin" then SomaPhase.plugin ~package:"unknown.plugin" ~files:[library];
  SomaPhase.finish_checking ~imports:[library];
  let generated=path dir "prog.ml" and ownership=path dir ".soma-ocaml-files" in
  write generated "let main = 1";write ownership "producer-owned";
  let generated=[generated,SomaBuildInfo.signature generated;ownership,SomaBuildInfo.signature ownership;
                 path dir "dune-workspace","absent"] in
  SomaPhase.publish ~source ~directory:dir ~switch:"fixture-switch" ~output ~generated;
  let draft=path base "draft" in
  if mode<>"normal" then begin
    assert (SomaPhase.read draft=None);
    Printf.printf "%s phase cannot certify: passed\n" mode
  end else begin
    let plan=Option.get (SomaPhase.read draft) in
    assert (SomaPhase.validate plan);
    assert (not (SomaPhase.validate {plan with source=path root "other.soma"}));
    assert (not (SomaPhase.promote ~draft ~key:"different-key"));
    assert (SomaPhase.promote ~draft ~key:"fixture-key");
    assert (SomaPhase.read (Option.get (SomaPhase.record_path "fixture-key"))=Some plan);
    let original=text draft in
    write draft (original ^ "forged\000");assert (SomaPhase.read draft=None);
    write draft "soma-native-phase 2\000";SomaCache.record draft;assert (SomaPhase.read draft=None);
    write draft "soma-native-phase 1\000truncated";SomaCache.record draft;assert (SomaPhase.read draft=None);
    List.iter (fun count ->
        let fields=String.split_on_char '\000' original in
        let fields=List.mapi (fun i value -> if i=8 then count else value) fields in
        write draft (String.concat "\000" fields);SomaCache.record draft;
        assert (SomaPhase.read draft=None)) ["-1";"65537";"not-a-count"];
    write draft original;assert (SomaPhase.read draft=Some plan);
    let rd,wr=Unix.pipe () in
    let child=ref 0 in
    SomaPhase.with_project_lock dir (fun _ ->
        match Unix.fork () with
        | 0 ->
          Unix.close rd;ignore(Unix.write_substring wr "s" 0 1);
          SomaPhase.with_project_lock dir (fun _ -> ignore(Unix.write_substring wr "a" 0 1));
          Unix._exit 0
        | pid ->
          child:=pid;Unix.close wr;
          let buf=Bytes.create 1 in assert(Unix.read rd buf 0 1=1 && Bytes.to_string buf="s");
          let ready,_,_=Unix.select [rd] [] [] 0.05 in assert(ready=[]));
    let buf=Bytes.create 1 in assert(Unix.read rd buf 0 1=1 && Bytes.to_string buf="a");
    Unix.close rd;assert(snd(Unix.waitpid [] !child)=Unix.WEXITED 0);
    let calls=ref 0 in
    (match SomaPhase.resume plan ~run:(fun ~directory:_ ~log:_ -> incr calls;false) with
     | _ -> failwith "failed native validation was treated as a fallback/success"
     | exception Failure _ -> ());
    assert (!calls=1 && text output="initial native product");
    Unix.mkdir (path dir "_build") 0o700;Unix.mkdir (path dir "_build/default") 0o700;
    let run ~directory ~log:_ =
      incr calls;let built=path directory "_build/default/soma_main.exe" in
      write built "fresh validated native product";Unix.chmod built 0o751;true in
    assert (SomaPhase.resume plan ~run);assert (!calls=2);
    assert (text output="fresh validated native product");
    assert ((Unix.stat output).Unix.st_perm=0o751 && SomaCache.trusted output);
    write (path dir "prog.ml") "tampered";
    assert (not (SomaPhase.resume plan ~run));assert (!calls=2);
    write (path dir "prog.ml") "let main = 1";
    let mutate ~directory ~log:_ = write (path directory "prog.ml") "race";true in
    (match SomaPhase.resume plan ~run:mutate with
     | _ -> failwith "generated mutation during validation was accepted"
     | exception Failure _ -> ());
    assert (text output="fresh validated native product");
    Unix.putenv "HOME" "";Unix.putenv "XDG_CACHE_HOME" "";
    assert(SomaPhase.record_path "fixture-key"=None);
    assert(not(SomaPhase.promote ~draft ~key:"fixture-key"));
    print_endline "production phase parser, receipts, identity, native failure and producer copy: passed"
  end
ML
(cd "$work" && ocamlfind ocamlc -package unix,digestif.c -linkpkg -o check \
  somaMerkle.mli somaMerkle.ml somaCache.mli somaCache.ml somaBuildInfo.mli somaBuildInfo.ml \
  somaPhase.mli somaPhase.ml check.ml)
for mode in normal drift plugin; do
  mkdir "$work/$mode"
  "$work/check" "$work/$mode" "$mode"
done

env -u HOME -u XDG_CACHE_HOME "$work/check" "$work" nohome
