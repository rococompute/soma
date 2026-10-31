#!/usr/bin/env bash

# What a value of type Any may be (GradualTyping.casts_that_may_fail): an
# Any made from a string, used as an N, is reported when the program is
# checked [gradual-may-fail], with where it was made an Any; one whose
# origin is not known (an argument) or that only fits is not.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

cat > prog.soma <<'EOT'
start_of (given : option string) : Any :=
  match given with
  | Some v => v
  | None => 0%N
  end.

page (n : N) : string := to_string n.

(* an Any that may be a string, used as an N *)
served (given : option string) : string := page (start_of given).

(* an Any whose origin is not known: an argument *)
from_argument (x : Any) : string := page x.

(* an Any that may only be an N *)
only_numbers (b : bool) : Any := if b then 1%N else 2%N.
fits (b : bool) : string := page (only_numbers b).
EOT
rocq c prog.soma > out.log 2>&1
grep -q 'served: start_of given is an Any that may be' out.log
grep -q 'a string (made an Any in start_of)' out.log
grep -q 'A string is never' out.log
grep -q '"expected an N,' out.log
grep -q 'It may also be an N (made an Any in start_of), which is' out.log
[ "$(grep -c 'gradual-may-fail' out.log)" = 1 ]

# when it is run, it says the same
cat > run.soma <<'EOT'
start_of (given : option string) : Any := match given with Some v => v | None => 0%N end.
page (n : N) : string := to_string n.
page (start_of (Some "41")).
EOT
rocq c run.soma > out.log 2>&1 || true
grep -q 'expected an N, but got "41" : string' out.log
