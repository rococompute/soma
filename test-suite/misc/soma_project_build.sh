#!/usr/bin/env bash
# Real checker -> declarative graph -> native/bytecode compilation, without Python.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat >exports.definition <<'SOMA'
From Soma Require Import Native.
OCaml Native Reexport Type public_flag As "flag" := bool.
OCaml Native Module Alias L := "Stdlib.List".
OCaml Native External Value identity : forall A:Type,A -> A := "Stdlib.Fun.id".
OCaml Native Reexport Value id := identity.
SOMA
cat >main.soma <<'SOMA'
Import exports.
Definition main := (public_flag,L,id).
Verification Properties "public_identity_checked" Invariants "" Trust "".
SOMA
cat >main.exp <<'SOMA'
Theorem public_identity_checked : id=tt.
Proof. reflexivity. Qed.
SOMA
cat >soma.toml <<'TOML'
[project]
name="graph_test"
version="0.1.0"
[build]
directory="products"
targets=["native"]
[build.extract.source]
file="main.soma"
verify=true
options=["-no-soma-prelude"]
[build.unit.prefix]
output="prefix.ml"
parts=[{extract="source",kind="source-types",namespace="exports"}]
[build.unit.public]
output="public.ml"
parts=[{unit="prefix"},{extract="source",kind="aliases",namespace="exports"},{extract="source",kind="values",namespace="exports"}]
[build.dune.native]
directory="."
targets=["check.exe","check.bc"]
needs=["public"]
TOML
cat >dune-project <<'DUNE'
(lang dune 3.13)
DUNE
cat >dune <<'DUNE'
(rule (target public.ml) (deps products/public.ml) (action (copy %{deps} %{target})))
(executable (name check) (modules check public) (modes exe byte))
DUNE
cat >check.ml <<'ML'
let () =
  let flag : Public.flag = true in assert flag;
  assert (Public.L.length [1;2] = 2);
  let bytes=Bytes.of_string "same object" in assert (Public.id bytes == bytes);
  assert (Public.id 7 = 7 && Public.id "generic" = "generic");
  print_endline "PASS: native project graph preserves types, aliases, generic values and identity"
ML
soma project plan >plan.log
printf 'source: \nprefix: source\npublic: prefix source\nnative: public\n' >expected-plan
cmp plan.log expected-plan
soma project build >build.log 2>&1
_build/default/check.exe
_build/default/check.bc
cp products/public.ml previous.ml
cp products/.receipts/public.toml previous-receipt.toml
cp -p products/.extract/source/prog.ml previous-prog.ml
soma project build >repeat.log 2>&1
grep -q 'unchanged .*public.ml' repeat.log
cmp products/public.ml previous.ml
cmp products/.receipts/public.toml previous-receipt.toml
test ! products/.extract/source/prog.ml -nt previous-prog.ml
# Same unit through two graph edges must not duplicate runtime initialization.
cp soma.toml previous-config
cat >>soma.toml <<'TOML'
[build.unit.duplicate]
output="public-again.ml"
parts=[{unit="public"},{unit="prefix"}]
TOML
if soma project build --target duplicate >duplicate.log 2>&1; then exit 1; fi
grep -q 'duplicate whole artifact' duplicate.log
test ! -e products/public-again.ml
cmp products/public.ml previous.ml
mv previous-config soma.toml
# Removing the complete declaration cannot turn a verified graph into a
# successful unverified extraction, or replace its previous checked products.
cp main.soma previous-source
sed '/^Verification /d' previous-source >main.soma
if soma project build >missing-policy.log 2>&1; then exit 1; fi
grep -q 'no source-owned Verification policy' missing-policy.log
cmp products/public.ml previous.ml
cmp products/.extract/source/prog.ml previous-prog.ml
mv previous-source main.soma
# A failed proof recheck cannot publish a changed unit or extraction.
cp products/.extract/source/prog.ml previous-prog.ml
printf '\nTheorem impossible : False. Proof. exact I. Qed.\n' >>main.exp
if soma project build >failed.log 2>&1; then exit 1; fi
cmp products/public.ml previous.ml
cmp products/.extract/source/prog.ml previous-prog.ml
test -z "$(find products/.extract -name '*.stage*' -print)"
echo 'PASS: unchanged publication, duplicate initialization rejection, failed proof rollback/cleanup'
