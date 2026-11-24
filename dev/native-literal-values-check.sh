#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 50 "$WORK"/*.log 2>/dev/null || true; fi; rm -rf "$WORK"' EXIT

host_ocaml() {
  opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"
}

cp -r "$HERE/examples/example_projects/native_literal_values" "$WORK/app"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
assumptions=$(sed -n 's/^.* assumes //p' "$WORK/hash" | sort -u)
[[ "$assumptions" == 'Corelib.Numbers.Cyclic.Int63.PrimInt63.int' ]]
grep -q 'external-literal-value' "$WORK/native/native_abi.manifest"
if grep -q 'Obj\.' "$WORK/native/soma_bindings.ml"; then
  echo 'Unsafe cast in the generated literal binding' >&2
  exit 1
fi

cat > "$WORK/native/fixture.ml" <<'ML'
let key : int Lwt.key = Lwt.new_key ()
let stages = ref []
let latest : (string -> string) option ref = ref None
let prefix : string option ref = ref None
let specialize text =
  stages := ("prefix", Lwt.get key) :: !stages;
  prefix := Some text;
  let finish tail =
    stages := ("tail", Lwt.get key) :: !stages;
    tail
  in
  latest := Some finish;
  finish
ML
cat > "$WORK/native/probe.ml" <<'ML'
let require message passed = if not passed then failwith message

let () =
  let format_time = Prog.raw_time () in
  List.iter (fun time ->
    require "raw float formatting"
      (format_time time = Printf.sprintf "%.10f" time))
    [0.; -0.; 1.23456789; -1234567890.000001; max_float; min_float; nan; infinity; neg_infinity];
  let padded = Prog.padded () in
  List.iter (fun n ->
    require "raw integer formatting" (padded n = Printf.sprintf "%02d" n))
    [min_int; -10; -1; 0; 1; 9; 10; max_int];
  require "getter delayed until called" (!(Fixture.stages) = []);
  let partial = Lwt.with_value Fixture.key (Some 31) (fun () -> Prog.specialize ()) in
  require "native stage runs at binding call" (!(Fixture.stages) = ["prefix", Some 31]);
  require "literal is quoted as data"
    (!(Fixture.prefix) = Some "a\"; failwith \"literal\"; (* \\payload");
  require "returns the original partially applied value"
    (partial == Option.get !(Fixture.latest));
  let borrowed = Bytes.to_string (Bytes.create 103) in
  require "native returned callable, input identity and call context"
    (Lwt.with_value Fixture.key (Some 42) (fun () -> partial borrowed) == borrowed
     && !(Fixture.stages) = ["tail", Some 42; "prefix", Some 31]);
  print_endline "PASS: exact typed Printf output, escaped literal and partial function identity/stages"
ML
python3 - "$WORK/native" <<'PY'
from pathlib import Path
import sys
folder = Path(sys.argv[1])
modules = sorted(file.stem for file in folder.glob('*.ml') if file.stem != 'soma_main')
(folder / 'dune').write_text(
    '(executable (name probe) (modes exe byte) (modules '
    + ' '.join(modules) + ') (libraries lwt) (flags (:standard -w -a)))\n')
PY
host_ocaml dune build --root "$WORK/native" --profile release -j2 probe.exe probe.bc > "$WORK/build.log" 2>&1
host_ocaml "$WORK/native/_build/default/probe.exe"
host_ocaml ocamlrun "$WORK/native/_build/default/probe.bc"

negative() {
  local name=$1 path=$2 literal=$3 phase=$4 diagnostic=$5
  mkdir "$WORK/$name"
  cat > "$WORK/$name/functions.definition" <<SOMA
From Soma Require Native.
OCaml Native External Type timestamp := "Float.t".
OCaml Native External Value bad : timestamp -> string := "$path" With "$literal".
SOMA
  printf 'From Soma Require Native.\nImport functions.\nDefinition main := functions.bad.\n' > "$WORK/$name/main.soma"
  if [ "$phase" = check ]; then
    if "$SOMA" check "$WORK/$name/main.soma" > "$WORK/$name.log" 2>&1; then
      echo "Accepted invalid native path $name" >&2
      exit 1
    fi
  else
    "$SOMA" extract "$WORK/$name/main.soma" -o "$WORK/$name/native" > "$WORK/$name-extract.log" 2>&1
    if host_ocaml dune build --root "$WORK/$name/native" --profile release -j2 > "$WORK/$name.log" 2>&1; then
      echo "Accepted invalid native format $name" >&2
      exit 1
    fi
  fi
  grep -Eq "$diagnostic" "$WORK/$name.log"
}
negative path 'Printf.sprintf ()' '%.10f' check 'an external operator needs a qualified OCaml operator path'
negative malformed 'Printf.sprintf' '%q' ocaml 'invalid format|invalid conversion|bad conversion'
negative mismatch 'Printf.sprintf' '%d' ocaml 'not compatible|expected'
echo 'PASS: checked paths, malformed format and type mismatch rejection'
