#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$HERE/_build/install/default/bin/soma}
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 45 "$WORK"/*.log 2>/dev/null || true; fi; rm -rf "$WORK"' EXIT

host_ocaml() {
  opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"
}

mkdir "$WORK/app"
cat > "$WORK/app/exceptions.definition" <<'SOMA'
From Soma Require Native.
OCaml Native External Exception qualified := "Stdlib.Division_by_zero".
OCaml Native External Exception unqualified := "Division_by_zero".
OCaml Native External Exception custom := "Fixture.Custom".
SOMA
cat > "$WORK/app/main.soma" <<'SOMA'
From Soma Require Native.
Import exceptions.

Definition get_qualified (_ : unit) :=
  Native.Export (Native.Call_callback qualified tt).
Definition get_unqualified (_ : unit) :=
  Native.Export (Native.Call_callback unqualified tt).
Definition get_custom (_ : unit) :=
  Native.Export (Native.Call_callback custom tt).
Definition raise_early (pending : unit -> promise unit) :=
  Native.Export (Native.Promise_bind_entry
    (fun _ => Native.Export (Native.Bind (Native.Call_callback qualified tt) (@Native.Throw (promise unit))))
    (fun _ => Native.Export (Native.Invoke pending Native.Return))).
Definition raise_on_continue (pending : unit -> promise unit) :=
  Native.Export (Native.Promise_bind pending
    (fun _ => Native.Export (Native.Bind (Native.Call_callback custom tt) Native.Throw))).
Definition failed (_ : unit) :=
  Native.Export (Native.Bind (Native.Call_callback custom tt) (@Native.Promise_fail unit)).
Definition main := (get_qualified,get_unqualified,get_custom,raise_early,raise_on_continue,failed).
SOMA
"$SOMA" extract "$WORK/app/main.soma" -o "$WORK/native" > "$WORK/extract.log" 2>&1
"$SOMA" hash "$WORK/app/main.soma" > "$WORK/hash"
assumptions=$(sed -n 's/^.* assumes //p' "$WORK/hash" | sort -u)
[[ "$assumptions" == 'Corelib.Numbers.Cyclic.Int63.PrimInt63.int' ]]
grep -q 'external-exception' "$WORK/native/native_abi.manifest"
grep -q 'Soma_handles.exception_value) =' "$WORK/native/soma_bindings.ml"
if grep -q 'Obj\.' "$WORK/native/soma_bindings.ml"; then
  echo 'Unsafe cast in the generated exception binding' >&2
  exit 1
fi

cat > "$WORK/native/fixture.ml" <<'ML'
exception Custom
ML
cat > "$WORK/native/probe.ml" <<'ML'
let require message passed = if not passed then failwith message

let catch expected call =
  try ignore (call ()); false with raised -> raised == expected

let rejects expected promise =
  match Lwt.state promise with
  | Lwt.Fail raised -> raised == expected
  | _ -> false

let observe expected call =
  try if rejects expected (call ()) then `Rejected else `Unexpected
  with raised -> if raised == expected then `Thrown else `Unexpected

let () =
  require "qualified built-in getter preserves the exception object"
    (Prog.get_qualified () == Division_by_zero);
  require "unqualified built-in getter preserves the exception object"
    (Prog.get_unqualified () == Division_by_zero);
  require "custom getter preserves the exception object"
    (Prog.get_custom () == Fixture.Custom);
  let calls = ref 0 in
  let settled () = incr calls; Lwt.return_unit in
  require "throw before bind keeps the original exception and bypasses the continuation"
    (catch Division_by_zero (fun () -> Prog.raise_early settled) && !calls = 0);
  let ready = observe Fixture.Custom (fun () -> Prog.raise_on_continue settled) in
  let raw_ready = observe Fixture.Custom
    (fun () -> Lwt.bind Lwt.return_unit (fun () -> raise Fixture.Custom)) in
  require "throw from ready continuation matches raw Lwt bind"
    (ready <> `Unexpected && ready = raw_ready);
  require "ready provider runs once" (!calls = 1);
  let pending, resolver = Lwt.task () in
  let delayed = Prog.raise_on_continue (fun () -> pending) in
  require "delayed continuation stays pending" (Lwt.state delayed = Lwt.Sleep);
  Lwt.wakeup resolver ();
  require "delayed continuation rejects with the same exception" (rejects Fixture.Custom delayed);
  require "explicit rejection carries the same exception" (rejects Fixture.Custom (Prog.failed ()));
  print_endline "PASS: exact native exception identity, direct throw and ready/pending Lwt stages"
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
  local name=$1 path=$2 phase=$3 diagnostic=$4
  mkdir "$WORK/$name"
  cat > "$WORK/$name/exceptions.definition" <<SOMA
From Soma Require Native.
OCaml Native External Exception bad := "$path".
SOMA
  printf 'From Soma Require Native.\nImport exceptions.\nDefinition main := exceptions.bad.\n' > "$WORK/$name/main.soma"
  if [ "$phase" = check ]; then
    if "$SOMA" check "$WORK/$name/main.soma" > "$WORK/$name.log" 2>&1; then
      echo "Accepted invalid exception path $name" >&2
      exit 1
    fi
  else
    "$SOMA" extract "$WORK/$name/main.soma" -o "$WORK/$name/native" > "$WORK/$name-extract.log" 2>&1
    if host_ocaml dune build --root "$WORK/$name/native" --profile release -j2 > "$WORK/$name.log" 2>&1; then
      echo "Accepted invalid exception constructor $name" >&2
      exit 1
    fi
  fi
  grep -qF "$diagnostic" "$WORK/$name.log"
}

negative lowercase-module 'stdlib.Division_by_zero' check 'a constructor path needs uppercase'
negative lowercase-value 'Stdlib.ignore' check 'a constructor path needs uppercase'
negative open-expression 'Stdlib.(Failure)' check 'a constructor path needs uppercase'
negative empty-segment 'Stdlib..Division_by_zero' check 'a constructor path needs uppercase'
negative payload 'Stdlib.Failure' build 'expects 1 argument'
negative wrong-type 'None' build 'There is no constructor None within type'
echo 'PASS: invalid paths, payload-bearing constructors and non-exception constructors rejected'
