#!/usr/bin/env bash
# Check replacement identity and receipt refusal against the real SomaTest
# module. Only receipt signing is stubbed; no compiler build is needed here.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cp "$ROOT/topbin/somaTest.ml" "$ROOT/clib/somaMerkle.ml" "$TMP/"
cd "$TMP"
printf 'let trusted _ = true\nlet record _ = ()\n' > somaCache.ml
cat > check.ml <<'ML'
let write file text = Out_channel.with_open_bin file (fun oc -> output_string oc text)
let () =
  let outer = Unix.realpath (Sys.getcwd ()) in
  let root = Filename.concat outer "project" in
  Unix.mkdir root 0o755;
  let file = Filename.concat root "input.soma" in
  write file "value : nat := 1.\n";
  let before = Unix.lstat file in
  Unix.rename file (file ^ ".old");
  write file "value : nat := 1.\n";
  (try ignore (SomaTest.regular_hash file before); failwith "replacement input was certified"
   with SomaTest.Changed_input -> ());
  Sys.remove (file ^ ".old");
  let before_fifo = Unix.lstat file in
  Sys.remove file;
  Unix.mkfifo file 0o600;
  ignore (Unix.alarm 3);
  (try ignore (SomaTest.regular_hash file before_fifo); failwith "FIFO replacement was certified"
   with SomaTest.Changed_input -> ());
  ignore (Unix.alarm 0);
  Sys.remove file;
  write file "value : nat := 1.\n";
  let snapshot = SomaTest.snapshot root None in
  assert (List.assoc "input.soma" snapshot = SomaMerkle.file_hash file);
  let external_file = Filename.concat outer "external.v" in
  write external_file "Definition input := 1.\n";
  let receipt = { SomaTest.identity = "unit"; inputs = snapshot;
                  dependencies = SomaTest.S.singleton "input.soma";
                  external_inputs = [external_file, SomaMerkle.file_hash external_file] } in
  assert (not (SomaTest.affected ~identity:"unit" ~inputs:snapshot
                 ~changed:SomaTest.S.empty ~include_drift:false receipt));
  write external_file "Definition input := 2.\n";
  assert (SomaTest.affected ~identity:"unit" ~inputs:snapshot
            ~changed:SomaTest.S.empty ~include_drift:false receipt);
  Sys.remove external_file;
  assert (SomaTest.affected ~identity:"unit" ~inputs:snapshot
            ~changed:SomaTest.S.empty ~include_drift:false receipt);
  (* Internal aliases hash the target bytes, including an ignored/unlisted
     target; external symlinks are not opened (this target is a FIFO). *)
  let alias = Filename.concat root "alias.soma" in
  Unix.symlink "input.soma" alias;
  let first = List.assoc "alias.soma" (SomaTest.snapshot root None) in
  write file "value : nat := 2.\n";
  assert (first <> List.assoc "alias.soma" (SomaTest.snapshot root None));
  let fifo = Filename.concat outer "outside-fifo" in
  Unix.mkfifo fifo 0o600;
  Unix.symlink fifo (Filename.concat root "external-fixture");
  ignore (SomaTest.snapshot root None);
  (* A change observed across the build is never stored as a passing receipt. *)
  Sys.chdir root;
  let build ~source ~trace ~no_image:_ =
    write trace (Printf.sprintf "soma-test-dependencies 1\n%S\n" source);
    write source "value : nat := 3.\n";
    0 in
  SomaTest.run ~identity:(fun _ -> "unit") ~build ["--full"; "input.soma"];
  assert (not (Sys.file_exists (SomaTest.record root "input.soma")));
  print_endline "soma test replacement identity, confined links and changed-input receipt refusal: passed"
ML
ocamlfind ocamlc -package digestif.c,unix -linkpkg somaMerkle.ml somaCache.ml somaTest.ml check.ml -o check
./check
