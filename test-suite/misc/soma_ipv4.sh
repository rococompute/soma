#!/usr/bin/env bash
# Actual Source IPv4 parser/geometry against the installed Ipaddr implementation.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat >main.soma <<'SOMA'
From Soma Require Import Native.
From Soma Require IPv4.
Definition parse := IPv4.of_string.
Definition parse_prefix := IPv4.prefix_of_string.
Definition octets := IPv4.address_bytes.
Definition membership := IPv4.contains.
Definition build_prefix := IPv4.make_prefix.
Definition prefix_width := IPv4.bits.
Definition prefix_address := IPv4.network.
Definition main := (parse, parse_prefix, octets, membership, build_prefix, prefix_width, prefix_address).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,prog.ml,prog.mli} .
cat >check.ml <<'ML'
let checked=ref 0
let failure = function
 | Prog.Need_more -> "not enough data"
 | Prog.Bad_character(c,i) -> Printf.sprintf "invalid character '%c' at %d" c i
 | Prog.Octal_notation -> "octal notation disallowed"
 | Prog.Octet_bounds ordinal -> (List.nth ["first";"second";"third";"fourth"] (ordinal-1))^" octet out of bounds"
 | Prog.Invalid_prefix_size -> "invalid prefix size"
let native_parse f text = try Ok(f text) with Ipaddr.Parse_error(message,input)->assert(input=text);Error message
let bytes ip = let raw=Ipaddr.V4.to_octets ip in List.init 4(fun i->Char.code raw.[i])
let source_address text = match Prog.parse text with
 | Prog.Ready(ip,position)->assert(position=String.length text);Ok(Prog.octets ip)
 | Prog.Failed reason ->Error(failure reason)
let source_prefix text = match Prog.parse_prefix text with
 | Prog.Ready(prefix,position)->assert(position=String.length text);Ok(Prog.octets(Prog.prefix_address prefix),Prog.prefix_width prefix)
 | Prog.Failed reason ->Error(failure reason)
let check_address text =
 let expected=Result.map bytes(native_parse Ipaddr.V4.of_string_exn text) in
 let observed=source_address text in
 if expected<>observed then failwith("IPv4 address mismatch: "^String.escaped text);
 incr checked
let check_prefix text =
 let expected=Result.map(fun p->bytes(Ipaddr.V4.Prefix.address p),Ipaddr.V4.Prefix.bits p)
   (native_parse Ipaddr.V4.Prefix.of_string_exn text) in
 let observed=source_prefix text in
 if expected<>observed then failwith("IPv4 prefix mismatch: "^String.escaped text);
 incr checked
let source_ip text = match Prog.parse text with Prog.Ready(ip,_)->ip|_->failwith "test address"
let state=Random.State.make[|0x495034;2026;71|]
let random_ip () = List.init 4(fun _->Random.State.int state 256)
let text octets = String.concat "." (List.map string_of_int octets)
let () =
 List.iter(fun value->check_address value;check_prefix value)
 ["";".";"1.2.3.4";"1.2.3.4/0";"255.255.255.255";"0.0.0.0/32";
  "001.2.3.4";"999.000.0.0";"999.0.0.0junk";"1.2.3.4/999junk";
  "1.2.3.4/00";"1.2.3.4/-1";"1.2.3.4/+1";"1.2.3.4/33";
  " 1.2.3.4";"1.2.3.4 ";"1.2.3.4\000";"::1";"1.2.3.4:80";
  "9223372036854775808.0.0.1";"18446744073709551617.2.3.4";
  "4611686018427387904.2.3.4";"9223372036854775809.0.0.1/9223372036854775840";
  String.make 2000 '9'^".0.0.1";"1.2.3.4/"^String.make 2000 '0'];
 for n=0 to 65535 do
  let octet=string_of_int n in check_address(octet^".2.3.4");
  if n<512 then check_prefix("1.2.3.4/"^octet)
 done;
 for _=1 to 4000 do
  let network=text(random_ip()) and candidate=text(random_ip()) in
  check_address network;
  let source_net=source_ip network and source_candidate=source_ip candidate in
  for width=0 to 32 do
   let prefix=network^"/"^string_of_int width in check_prefix prefix;
   let parsed=match Prog.parse_prefix prefix with Prog.Ready(p,_)->p|_->failwith "test prefix" in
   let native=Ipaddr.V4.Prefix.of_string_exn prefix in
   let query=Ipaddr.V4.of_string_exn candidate in
   assert(Prog.membership parsed source_candidate=Ipaddr.V4.Prefix.mem query native);
   let built=Option.get(Prog.build_prefix source_net width) in
   assert(Prog.membership built source_candidate=Ipaddr.V4.Prefix.mem query native);
   assert(Prog.membership parsed source_net);
   incr checked
  done
 done;
 for _=1 to 5000 do
  let raw=String.init(Random.State.int state 50)(fun _->Char.chr(Random.State.int state 256)) in
  check_address raw;check_prefix raw
 done;
 Printf.printf "PASS: %d IPv4 parse/error/CIDR comparisons, every prefix width and legacy 63-bit wrapped spellings\n" !checked
ML
for backend in ocamlopt ocamlc; do
 ocamlfind "$backend" -w -a -package lwt,ipaddr -linkpkg soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml prog.mli prog.ml check.ml -o "check-$backend" >"$backend.log" 2>&1
 "./check-$backend"
done
