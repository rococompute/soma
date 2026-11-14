#!/usr/bin/env bash
# Soma.Wire outside an image: a program built for the machine imports it
# (lines and frames, which Sandbox exports) and is built into an
# executable, not a unikernel, and its frames split as an image's would: a
# short frame, a 200 000-byte one (taken by offset, so in one copy rather
# than a character at a time, in well under a second, as main requires
# ExtrOcamlNatInt), an empty one, and a partial one kept. The
# framing's theorems are checked by Wire.v when Soma is built.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
cd "$WORK"

# a project with one OCaml binding, so main is extracted and built into
# main.exe (a program with none is evaluated, not built)
cat > soma.toml <<'TOML'
[project]
name = "wire_check"
version = "0.1.0"
TOML
printf 'same : string -> string.\n' > same.definition
printf 'let same (s : string) : string = s\n' > same.ml
cat > main.soma <<'SOMA'
Require Import Soma.Wire.
From Stdlib Require ExtrOcamlNatInt.
From Stdlib Require Import List NArith.BinNat.
Import same.

big : string := String.concat "" (List.repeat "abcd" 50000).

received : string :=
  String.concat "" [frame "hi", frame big, frame "", "xy"].

main : string :=
  let r := split_frames max_frame (same received) in
  String.concat " " (map (fun f => to_string (String.length f)) (fst r) ++ ["kept", snd r]).
SOMA

soma build main.soma > build.log 2>&1
[ -x main.exe ] || { echo "FAIL: no main.exe"; exit 1; }
[ ! -e main.hvt ] || { echo "FAIL: a program that imports Soma.Wire was built as an image"; exit 1; }
[ ! -d "$SOMA_MIRAGE_DIR" ] || { echo "FAIL: a Mirage project was made for it"; exit 1; }
start=$SECONDS
out=$(./main.exe)
[ "$out" = "2 200000 0 kept xy" ] || { echo "FAIL: split_frames gave: $out"; exit 1; }
# a millisecond's work: a minute means String's length, get and substring
# weren't OCaml's (somaOcaml.ml's extracts_nat_as_int)
[ $((SECONDS - start)) -lt 10 ] || { echo "FAIL: splitting took $((SECONDS - start)) s"; exit 1; }
echo "ok Soma.Wire splits frames in a program built for the machine"
