#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 50 "$WORK"/*.log 2>/dev/null || true; fi; rm -rf "$WORK"' EXIT

host_ocaml() {
  opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"
}

cp -r "$HERE/examples/example_projects/native_callable_wrap" "$WORK/app"
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
assumptions=$(sed -n 's/^.* assumes //p' "$WORK/hash" | sort -u)
if [[ "$assumptions" != 'Corelib.Numbers.Cyclic.Int63.PrimInt63.int' ]]; then
  printf 'Unexpected assumptions in callable wrappers: %s\n' "$assumptions" >&2
  exit 1
fi
if grep -q 'Obj\.' "$WORK/native/soma_bindings.ml"; then
  echo 'Unsafe cast in generated callable wrapper' >&2
  exit 1
fi
grep -q 'wrap native-callable-type' "$WORK/native/native_abi.manifest"

cat > "$WORK/native/probe.ml" <<'ML'
let require name passed = if not passed then failwith name

let () =
  let key = Lwt.new_key () in
  let events = ref [] in
  let note event = events := (event, Lwt.get key) :: !events in
  let borrowed_tag = Bytes.to_string (Bytes.make 103 't') in
  let borrowed_input = Bytes.to_string (Bytes.make 113 'i') in
  let result = Bytes.create 117 in
  let tail input =
    require "borrowed argument" (input == borrowed_input);
    note "tail";
    result
  in
  let target flag =
    note (if flag = Some false then "supplied" else "omitted");
    fun tag ->
      require "borrowed label" (tag == borrowed_tag);
      note "label";
      tail
  in
  let wrapped = Prog.wrap target in
  require "construction does not apply callback" (!events = []);
  let labelled = Lwt.with_value key (Some 1) (fun () -> wrapped ?flag:(Some false)) in
  require "optional stage" (!events = ["supplied", Some 1]);
  let final = Lwt.with_value key (Some 2) (fun () -> labelled ~tag:borrowed_tag) in
  require "labelled stage and raw positional tail" (final == tail && !events = ["label", Some 2; "supplied", Some 1]);
  require "borrowed return" (final borrowed_input == result);
  require "omitted flag" (wrapped ~tag:borrowed_tag borrowed_input == result
                          && !events = ["tail", None; "label", None; "omitted", None; "tail", None; "label", Some 2; "supplied", Some 1]);

  let reason = Failure "partial application" in
  let wrapped = Prog.wrap (fun _ -> raise reason) in
  require "throw at partial stage" (try ignore (Sys.opaque_identity (wrapped ?flag:None)); false with e -> e == reason);

  let returned _ = true in
  let stage _ _ = Fun.const returned in
  require "returned function identity" (Prog.wrap_function stage ~tag:borrowed_tag true == returned);

  let plain _ = true in
  require "all-positional callable keeps original identity" (Prog.wrap_plain plain == plain);
  print_endline "PASS: borrowed values, exact partial stages, optional labels, throw identity and saved native contexts"
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

reject() {
  local name=$1 declaration=$2 expected=$3
  mkdir "$WORK/$name"
  cp "$WORK/app/functions.definition" "$WORK/$name/"
  printf 'From Soma Require Native.\nImport functions.\n%s\n' "$declaration" > "$WORK/$name/bad.definition"
  printf 'From Soma Require Native.\nImport bad.\nDefinition main := bad.bad.\n' > "$WORK/$name/main.soma"
  if "$SOMA" extract "$WORK/$name/main.soma" -o "$WORK/$name/native" > "$WORK/$name.log" 2>&1; then
    echo "Accepted invalid callable wrapper $name" >&2
    exit 1
  fi
  grep -q "$expected" "$WORK/$name.log"
}
reject wrong_argument 'OCaml Native Wrap bad : Native.callback bool bool -> positional.' 'positional callback chain'
reject wrong_result 'OCaml Native Wrap bad : Native.callback string string -> positional.' 'positional callback chain'
reject not_callable 'OCaml Native Wrap bad : Native.callback string bool -> bool.' 'declared native callable as its result'
echo 'PASS: callable wrapper signatures reject incorrect input chains and results'
