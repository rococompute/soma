#!/usr/bin/env bash
# Soma.Host: a program with no OCaml of its own, built for the machine over
# Soma's host primitives (theories/Soma/Host.v, carried out by
# toplevel/somaHost.ml), reads its arguments, writes and reads a file, runs
# a process and reads its output, and sends bytes over a TCP connection to
# itself. soma explore lists the Soma.Host primitives main reaches, and a
# number in it runs as OCaml's int with no ExtrOcamlNatInt of its own.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
cd "$WORK"

cat > soma.toml <<'TOML'
[project]
name = "host_check"
version = "0.1.0"
TOML
cat > main.soma <<'SOMA'
Require Soma.Host.
From Soma Require Import OCaml.

data (a : bool * (float * list string)) : list string := snd (snd a).
first (a : bool * (float * list string)) : string :=
  match data a with x :: _ => x | [] => "" end.

check (label : string) (ok : bool) : string := append (if ok then "ok " else "FAIL ") label.

files (dir : string) : list string :=
  let f := append dir "/note" in
  match Host.file_put f "written" "true" with
  | (true, _) =>
      [check "a file written and read" (String.eqb (first (Host.read_text f)) "written"),
       check "a file there" (fst (Host.file_exists f)),
       check "a file not there" (negb (fst (Host.file_exists (append dir "/none"))))]
  | _ => [check "a file written" false]
  end.

process (u : unit) : list string :=
  match data (Host.spawn "/bin/echo" "" "" [] ["from a process"]) with
  | [pid, pipe] =>
      let out := data (Host.sock_read pipe) in
      let ended := data (Host.wait_pid pid) in
      [check "a process's output" (match out with ["bytes", s] => String.eqb s "from a process
" | _ => false end),
       check "a process's end" (match ended with ["exit", "0"] => true | _ => false end)]
  | _ => [check "a process started" false]
  end.

network (port : string) : list string :=
  match data (Host.sock_listen "127.0.0.1" port "4") with
  | [l] =>
      match data (Host.sock_dial "127.0.0.1" port) with
      | d :: _ =>
          match Host.sock_select "1000" [] [d] with
          | (true, (_, [_])) =>
              match data (Host.sock_accept l "false") with
              | c :: _ =>
                  match data (Host.sock_write d "ping") with
                  | ["wrote", "4"] =>
                      [check "a socket's bytes" (match data (Host.sock_read c) with ["bytes", "ping"] => true | _ => false end)]
                  | _ => [check "a socket written" false]
                  end
              | _ => [check "a connection accepted" false]
              end
          | _ => [check "a dial connected" false]
          end
      | _ => [check "a dial" false]
      end
  | _ => [check "a listener" false]
  end.

main : unit :=
  match Host.argv tt with
  | [word, port] =>
      Host.print_lines
        (check "its arguments" (String.eqb word "given")
         :: check "a nat as OCaml's int" (Nat.eqb (Nat.div (Nat.pow 2 40) (Nat.pow 2 39)) 2)
         :: app (files (first (Host.temp_dir "soma-host"))) (app (process tt) (network port)))
  | _ => Host.print_lines ["FAIL its arguments"]
  end.
SOMA

soma build main.soma > build.log 2>&1
[ -x main.exe ] || { echo "FAIL: no main.exe"; exit 1; }
[ ! -e main.hvt ] || { echo "FAIL: a program over Soma.Host was built as an image"; exit 1; }
soma explore main.soma > explore.log 2>&1 || true
grep -q "What main asks of the machine (Soma.Host's primitives" explore.log || { echo "FAIL: soma explore doesn't name Soma.Host's primitives"; exit 1; }
for p in argv print_lines file_put read_text spawn wait_pid sock_listen sock_write; do
  grep -A1 "What main asks of the machine" explore.log | grep -qw "$p" || { echo "FAIL: soma explore doesn't list $p"; cat explore.log; exit 1; }
done
port=$((40000 + RANDOM % 20000))
out=$(./main.exe given "$port")
echo "$out"
if echo "$out" | grep -q FAIL; then exit 1; fi
[ "$(echo "$out" | grep -c '^ok ')" = 8 ] || { echo "FAIL: expected 8 checks"; exit 1; }
echo "ok Soma.Host carries out a program's arguments, files, processes and sockets"
