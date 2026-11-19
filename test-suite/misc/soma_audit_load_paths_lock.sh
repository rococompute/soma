#!/usr/bin/env bash

# Exercise the production load-path functions and receipt implementation.
# Pause writer A after it decided that the old file was untrusted. Without
# the sibling lock, B publishes its line and A then removes it. This precise
# schedule avoids depending on a probabilistic parallel compiler race.
set -euo pipefail
export SOMA_AUDIT_SOURCE="${SOMA_AUDIT_SOURCE:-$(cd "$(dirname "$0")/../.." && pwd -P)}"

python3 - <<'PY'
import fcntl
import os
import pathlib
import shutil
import subprocess
import tempfile
import time

source = pathlib.Path(os.environ["SOMA_AUDIT_SOURCE"])
compiler = shutil.which("ocamlfind")
assert compiler, "ocamlfind is required (run within the Soma build environment)"
with tempfile.TemporaryDirectory(prefix="soma-load-paths-") as tmp:
    root = pathlib.Path(tmp).resolve()
    text = (source / "vernac" / "somaImport.ml").read_text()
    # Extract the exact production transaction, including the lock when
    # present; the same regression also runs against the pre-fix revision.
    start = text.index("let load_paths_file () =")
    end = text.index("\n(* A Rocq library records", start) if "\n(* A Rocq library records" in text[start:] else text.index("\nlet add_load_path unix_path", start)
    transaction = text[start:end]
    if "let read_load_paths () =" in transaction:
        read_operation = "read_load_paths ()"
    else:
        # The old reader expression, used only for the baseline reproducer.
        read_start = text.index("(if SomaCache.trusted (load_paths_file ())")
        read_operation = text[read_start:text.index("\n", read_start)]
    opam = (source / "vernac" / "somaOpam.ml").read_text()
    lines_start = opam.index("let read_lines f =")
    lines_end = opam.index("\nlet tail_of_file", lines_start)
    (root / "somaMerkle.ml").write_text((source / "clib" / "somaMerkle.ml").read_text())
    (root / "receipt_cache.ml").write_text((source / "clib" / "somaCache.ml").read_text())
    harness = r'''
let root = Sys.argv.(2)
let role = Sys.argv.(1)
let marker name = Filename.concat root name
let touch file = Out_channel.with_open_bin file (fun _ -> ())
let rec wait file =
  if not (Sys.file_exists file) then (Unix.sleepf 0.01; wait file)
module SomaCache = struct
  include Receipt_cache
  let first = ref true
  let trusted file =
    let result = Receipt_cache.trusted file in
    if role = "a" && !first then begin
      first := false;
      touch (marker "a-checked");
      wait (marker "release-a")
    end;
    result
  let record file =
    if role = "c" then begin
      touch (marker "c-written");
      wait (marker "release-c")
    end;
    Receipt_cache.record file
end
module SomaOpam = struct
'''+opam[lines_start:lines_end]+r'''
end
module CString = struct let is_prefix prefix s = String.starts_with ~prefix s end
module DirPath = struct let to_string x = x end
module Loadpath = struct
let paths = ref []
let get_load_paths () = !paths
let physical (x,_) = x
let logical (_,x) = x
let remove_load_path physical = paths := List.filter (fun (p,_) -> p <> physical) !paths
end
let project_cache () = Filename.concat root "cache"
let mkdir_p = Receipt_cache.mkdir
let remove_if_present file = try Sys.remove file with Sys_error _ -> ()
'''+transaction+'\nlet read_paths_for_test () = '+read_operation+r'''
let () =
  match role with
  | "a" -> record_load_path "Alpha" "/alpha"; touch (marker "a-done")
  | "b" -> record_load_path "Beta" "/beta"; touch (marker "b-done")
  | "c" -> record_load_path "Gamma" "/gamma"
  | "selection" ->
    Loadpath.paths := ["/old", "Root"; "/old/Sub", "Root.Sub";
                       "/old/Independent", "Root.Nested"; "/else", "Else"];
    record_load_path "Root" "/old";
    record_load_path "Root.Nested" "/old/Independent";
    record_load_path "Root" "/new";
    assert (!(Loadpath.paths) = ["/old/Independent", "Root.Nested"; "/else", "Else"]);
    let lines = read_load_paths () in
    assert (List.mem "Root /new" lines && not (List.mem "Root /old" lines));
    assert (List.mem "Root.Nested /old/Independent" lines)
  | "read" ->
    let lines = read_paths_for_test () in
    Out_channel.with_open_bin (marker "read-result") (fun oc ->
        List.iter (fun line -> output_string oc (line ^ "\n")) lines)
  | _ -> failwith "unknown role"
'''
    (root / "transaction.ml").write_text(harness)
    subprocess.run([compiler, "ocamlc", "-package", "digestif.c,unix", "-linkpkg", "-o", "transaction",
                    "somaMerkle.ml", "receipt_cache.ml", "transaction.ml"], cwd=root, check=True)
    env = dict(os.environ, XDG_CACHE_HOME=str(root / "xdg"), SOMA_CACHE_ID="audit-load-paths")
    cache = root / "cache"
    cache.mkdir()
    # No receipt: this file is intentionally untrusted.
    (cache / "load-paths").write_text("Discard /untrusted\n")
    c = reader = None
    a = subprocess.Popen([str(root / "transaction"), "a", str(root)], env=env)
    b = None
    try:
        deadline = time.monotonic() + 10
        while not (root / "a-checked").exists():
            assert a.poll() is None, "writer A exited before checking trust"
            assert time.monotonic() < deadline, "writer A did not reach the barrier"
            time.sleep(0.01)
        b = subprocess.Popen([str(root / "transaction"), "b", str(root)], env=env)
        # If A really holds the sibling lock, B cannot pass it. Otherwise
        # wait for B to finish, so the baseline schedule is deterministic.
        held = False
        lock_file = cache / "load-paths.lock"
        if lock_file.exists():
            with lock_file.open("a") as lock:
                try:
                    fcntl.lockf(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    held = True
        if not held:
            assert b.wait(timeout=10) == 0
        (root / "release-a").touch()
        assert a.wait(timeout=10) == 0
        assert b.wait(timeout=10) == 0
        actual = (cache / "load-paths").read_text().splitlines()
        assert sorted(actual) == ["Alpha /alpha", "Beta /beta"], actual
        # A reader must not treat an in-flight append as untrusted and
        # silently omit the whole load path list before its new receipt.
        c = subprocess.Popen([str(root / "transaction"), "c", str(root)], env=env)
        deadline = time.monotonic() + 10
        while not (root / "c-written").exists():
            assert c.poll() is None, "writer C exited before publishing"
            assert time.monotonic() < deadline, "writer C did not reach the barrier"
            time.sleep(0.01)
        reader = subprocess.Popen([str(root / "transaction"), "read", str(root)], env=env)
        deadline = time.monotonic() + 1
        while reader.poll() is None and time.monotonic() < deadline:
            time.sleep(0.01)
        (root / "release-c").touch()
        assert c.wait(timeout=10) == 0
        assert reader.wait(timeout=10) == 0
        actual = (root / "read-result").read_text().splitlines()
        assert sorted(actual) == ["Alpha /alpha", "Beta /beta", "Gamma /gamma"], actual
    finally:
        (root / "release-a").touch()
        (root / "release-c").touch()
        for child in (a, b, c, reader):
            if child is not None and child.poll() is None:
                child.kill()
                child.wait()
    subprocess.run([str(root / "transaction"), "selection", str(root)], env=env, check=True)
print("soma audit: load-path trust/selection/receipt transaction: passed")
PY
