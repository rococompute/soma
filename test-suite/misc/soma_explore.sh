#!/usr/bin/env bash

# Explore model. (theories/Soma/Explore.v, plugins/soma_explore): from each
# input, each sequence of actions up to the depth; a state or a property
# that is false or a run-time error is a violation, reported with the
# input and the behaviour up to it, and fails the command.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

cat > prog.soma <<'EOT'
Import Explore.

Inductive action := Up | Twice.
next (a : action) (n : nat) : nat := match a with Up => n + 1 | Twice => n * 2 end.

grows : Explore.model nat nat action := {|
  Explore.inputs := [0, 1, 5];
  Explore.initial := fun n => n;
  Explore.actions := [Up, Twice];
  Explore.transition := next;
  Explore.depth := 3;
  Explore.invariants := [("below 100", fun n => n <? 100)];
  Explore.steps := [("each action increases", fun before after => before <? after)]
|}.
Explore grows.
EOT
if rocq c prog.soma > out.log 2>&1; then echo "a violated model was not reported"; exit 1; fi
# Twice does not increase 0: found from 0 at once
grep -q 'Violation 1, from input 0:' out.log
grep -q '"each action increases" does not hold' out.log
grep -q '1: Twice  0' out.log
grep -q 'No violation from: 1, 5.' out.log

# a state that is a run-time error, as an Any that is not a nat
cat > prog.soma <<'EOT'
Import Explore.
Inductive action := Up.
grows : Explore.model Any nat action := {|
  Explore.inputs := [(1 : Any), ("one" : Any)];
  Explore.initial := fun x => (x : nat);
  Explore.actions := [Up];
  Explore.transition := fun _ n => n + 1;
  Explore.depth := 2;
  Explore.invariants := [];
  Explore.steps := [("increases", fun before after => before <? after)]
|}.
Explore grows.
EOT
if rocq c prog.soma > out.log 2>&1; then echo "a run-time error was not reported"; exit 1; fi
grep -q 'the initial state is a run-time error: expected a nat, but got "one" : string' out.log
grep -q '1 violation, from 1 of the 2 inputs.' out.log

# without violation, what was explored
sed -i.bak 's/("one" : Any)/(2 : Any)/' prog.soma
rocq c prog.soma > out.log 2>&1
grep -q 'Explored 2 inputs, 1 action, up to 2 in a row: .* No violation.' out.log

# soma explore FILE: a review of FILE and the project files it imports
mkdir -p proj/lib
cat > proj/lib/start.soma <<'EOT'
start_of (given : option string) : Any := match given with Some v => v | None => 0%N end.
EOT
cat > proj/main.soma <<'EOT'
Import Explore.
Import lib.start.
page (n : N) : string := to_string n.
served (given : option string) : string := page (start_of given).
Inductive action := Up.
grows : Explore.model (option string) N action := {|
  Explore.inputs := [None, Some "41"];
  Explore.initial := fun g => (start_of g : N);
  Explore.actions := [Up];
  Explore.transition := fun _ n => N.succ n;
  Explore.depth := 2;
  Explore.invariants := [];
  Explore.steps := [("increases", fun before after => (before <? after)%N)]
|}.
(* its own Explore does not stop the review, which explores it too *)
Explore grows.
EOT
cat > proj/main.proof <<'EOT'
Theorem assumed : forall n : N, (n <= n + 1)%N.
Proof.
Admitted.
Theorem rests : (0 <= 1)%N.
Proof.
  By assumed, we conclude that (0 <= 1)%N.
Qed.
EOT
if soma explore proj/main.soma > out.log 2>&1; then echo "a review with issues did not fail"; exit 1; fi
grep -q '^Review of main and the 1 project file it imports' out.log
grep -q 'Violation 1, from input (Some "41"):' out.log
grep -q 'lib.start.start_of' out.log
grep -q 'makes an Any from a string, an N' out.log
grep -q 'main.served: start_of given is an Any that may be a string, used as' out.log
grep -q 'main.assumed: is assumed' out.log
grep -q 'main.rests: rests on what is assumed: main.assumed.' out.log
grep -q '1 model with a violation, 4 issues.' out.log
# nothing is left behind but the cache
[ ! -e proj/main.vo ]

# a program without any: no issue, and soma explore succeeds
cat > clean.soma <<'EOT'
double (n : nat) : nat := n + n.
EOT
soma explore clean.soma > out.log 2>&1
grep -q 'No issue, and no violation.' out.log

# soma compile FILE: soma build, then the review, in one check; it keeps
# what soma build keeps, and fails when the review finds something
soma compile clean.soma > out.log 2>&1
grep -q 'No issue, and no violation.' out.log
[ ! -e clean.vo ]
if soma compile proj/main.soma > out.log 2>&1; then echo "soma compile passed a review with issues"; exit 1; fi
grep -q '1 model with a violation, 4 issues.' out.log
[ ! -e proj/main.vo ]
