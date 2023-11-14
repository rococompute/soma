#!/usr/bin/env bash
# Exercise the actual generated interface, including its private open row.
set -euo pipefail
export PATH="$BIN:$PATH"
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2; fi; rm -rf "$WORK"' EXIT
export SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE SOMA_MIRAGE_SWITCH
cd "$WORK"
cp "$ROOT/examples/example_files/mirage_link_client/mirage_link_client.soma" .
soma build --no-image mirage_link_client.soma > build.log 2>&1
grep -q '(no image)' build.log
CHECKS="$SOMA_MIRAGE_DIR/net/no-image"
test -f "$CHECKS/standins.cmi"
test -f "$CHECKS/prog.cmo"
test -f "$CHECKS/soma_rt.cmo"
test -f "$CHECKS/unikernel.cmo"
cat > good.ml <<'OCAML'
module Check (S : Standins.Tcpip.Stack.V4V6) = struct
  let classify (e : S.TCP.write_error) = match e with
    | `Closed -> "closed"
    | `Refused -> "refused"
    | `Timeout -> "timeout"
    | _ -> "implementation-specific"
end
OCAML
ocamlc -I "$CHECKS" -c good.ml > good.log 2>&1
# Only the documented constructors are available to callers; the private
# row does not let them invent an implementation-specific error.
cat > bad.ml <<'OCAML'
module Check (S : Standins.Tcpip.Stack.V4V6) = struct
  let fabricated : S.TCP.write_error = `Invented
end
OCAML
if ocamlc -I "$CHECKS" -c bad.ml > bad.log 2>&1; then
    echo 'TCP write_error incorrectly permits callers to invent errors' >&2
    exit 1
fi
grep -q 'Error:' bad.log
grep -q 'S.TCP.write_error' bad.log
# Even the documented cases do not exhaust an implementation's open row.
cat > exhaustive.ml <<'OCAML'
module Check (S : Standins.Tcpip.Stack.V4V6) = struct
  let classify (e : S.TCP.write_error) = match e with
    | `Closed -> ()
    | `Refused -> ()
    | `Timeout -> ()
end
OCAML
if ocamlc -I "$CHECKS" -w +8 -warn-error +8 -c exhaustive.ml > exhaustive.log 2>&1; then
    echo 'TCP write_error incorrectly treats its documented cases as exhaustive' >&2
    exit 1
fi
grep -q 'partial-match' exhaustive.log
