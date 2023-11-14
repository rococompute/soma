#!/usr/bin/env bash
# The stand-ins keep the real Mirage signatures' optional arguments, open
# rows and record fields: what types against the real libraries this way
# types against them, and what the real ones refuse they refuse.
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
[ ! -f mirage_link_client.hvt ]

# accepted by the real signatures, so by the stand-ins
cat > good.ml <<'OCAML'
open Standins
let info_without_doc = Cmdliner.Arg.info [ "x" ]
let info_with_docv = Cmdliner.Arg.info ~docv:"V" ~doc:"d" [ "y" ]
let with_vopt = Cmdliner.Arg.(value & opt_all ~vopt:"v" string [] info_without_doc)
let bytes = Mirage_crypto_rng.generate 8
let date_utc t = Ptime.to_date_time ~tz_offset_s:0 t
let first c = Cstruct.to_string ~off:0 ~len:1 c
let part s = Cstruct.of_string ~off:1 s
let address s = match Ipaddr.of_string s with
  | Ok _ -> "ok" | Error (`Msg m) -> m
let stack_kb () = (Solo5_os.Memory.stat ()).Solo5_os.Memory.stack_words
module Check (S : Tcpip.Stack.V4V6) = struct
  let classify (e : S.TCP.error) = match e with
    | `Refused -> "refused" | `Timeout -> "timeout" | _ -> "other"
end
OCAML
ocamlc -I "$CHECKS" -c good.ml > good.log 2>&1

# refused by the real signatures, so by the stand-ins
reject() {
    printf 'open Standins\n%s\n' "$2" > "bad_$1.ml"
    if ocamlc -I "$CHECKS" -c "bad_$1.ml" > "bad_$1.log" 2>&1; then
        echo "the stand-ins accept $1, which Mirage refuses" >&2
        exit 1
    fi
    grep -q 'Error:' "bad_$1.log"
}
reject vopt_list 'let a = Cmdliner.Arg.(opt_all ~vopt:["v"] string [] (info ["x"]))'
reject memory_fields 'let m : Solo5_os.Memory.stat = { heap_words = 0; live_words = 0; free_words = 0 }'
reject async_value 'let () = Lwt.async (fun () -> Lwt.return 1)'
reject tcp_error 'module Check (S : Tcpip.Stack.V4V6) = struct let e : S.TCP.error = `Invented end'

# an implementation's TCP errors are more than the documented ones
cat > exhaustive.ml <<'OCAML'
module Check (S : Standins.Tcpip.Stack.V4V6) = struct
  let classify (e : S.TCP.error) = match e with `Refused -> () | `Timeout -> ()
end
OCAML
if ocamlc -I "$CHECKS" -w +8 -warn-error +8 -c exhaustive.ml > exhaustive.log 2>&1; then
    echo 'TCP error incorrectly treats its documented cases as exhaustive' >&2
    exit 1
fi
grep -q 'partial-match' exhaustive.log
