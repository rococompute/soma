#!/usr/bin/env bash
# Actual Source checked arithmetic/page geometry, with independent Int64 math.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat >main.soma <<'SOMA'
From Soma Require Import Native.
From Soma Require CheckedArithmetic PageGeometry.
From Stdlib Require Import ZArith List.
Definition view range := (CheckedArithmetic.beginning range,
  (CheckedArithmetic.ending range, CheckedArithmetic.length range)).
Definition test_span start count := option_map view (CheckedArithmetic.checked_span start count).
Definition test_scaled start count stride := option_map view (CheckedArithmetic.checked_scale_end start count stride).
Definition test_arithmetic a b := (CheckedArithmetic.add a b, (CheckedArithmetic.sub a b, CheckedArithmetic.mul a b)).
Definition test_page address := (PageGeometry.page_base address,
  (PageGeometry.page_offset address, PageGeometry.page_end address)).
Definition test_geometry lo hi cowlo cowhi base address stop :=
  let layout := PageGeometry.Layout lo hi cowlo cowhi base in
  (PageGeometry.paged layout address, (PageGeometry.run_end layout address, PageGeometry.piece_end layout stop address)).
Definition test_pieces lo hi cowlo cowhi base start count :=
  match CheckedArithmetic.checked_span start count with
  | None => None
  | Some range => Some (PageGeometry.partition (PageGeometry.Layout lo hi cowlo cowhi base) range)
  end.
Definition main := (test_span, test_scaled, test_arithmetic, test_page, test_geometry, test_pieces).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,prog.ml,prog.mli} .
cat >check.ml <<'ML'
let checked=ref 0
let maximum=Int64.pred(Int64.shift_left 1L 62) and minimum=Int64.neg(Int64.shift_left 1L 62)
let rec positive bits = if bits=1L then Prog.XH else
 let rest=positive(Int64.shift_right_logical bits 1) in
 if Int64.logand bits 1L=0L then Prog.XO rest else Prog.XI rest
let source number=if number=0L then Prog.Z0 else if number>0L then Prog.Zpos(positive number)
 else Prog.Zneg(positive(Int64.neg number))
let rec bits=function Prog.XH->1L|Prog.XO rest->Int64.shift_left(bits rest)1
 |Prog.XI rest->Int64.logor(Int64.shift_left(bits rest)1)1L
let integer=function Prog.Z0->0L|Prog.Zpos value->bits value|Prog.Zneg value->Int64.neg(bits value)
let mapped=Option.map integer
let fits number=minimum<=number && number<=maximum
let checked_number number=if fits number then Some number else None
let span start count = if start<0L || count<0L || start>maximum || count>maximum || count>Int64.sub maximum start then None
 else Some(start,(Int64.add start count,count))
let source_span start count=Option.map(fun(a,(b,c))->integer a,(integer b,integer c))(Prog.test_span(source start)(source count))
let scaled start count stride =
 if start<0L || start>maximum || count<0L || stride<0L then None else
 if count=0L then span start 0L else
 if stride>Int64.div(Int64.sub maximum start)count then None else span start(Int64.mul count stride)
let multiply a b =
 if a=0L || b=0L then Some 0L else
 let limit=if (a<0L)<>(b<0L) then Int64.neg minimum else maximum in
 if Int64.abs a>Int64.div limit(Int64.abs b) then None else Some(Int64.mul a b)
let check_arithmetic a b =
 let plus,(minus,product)=Prog.test_arithmetic(source a)(source b) in
 assert(mapped plus=checked_number(Int64.add a b));
 assert(mapped minus=checked_number(Int64.sub a b));
 assert(mapped product=multiply a b);checked:= !checked+3
let check_span start count stride =
 assert(source_span start count=span start count);
 let actual=Option.map(fun(a,(b,c))->integer a,(integer b,integer c))
   (Prog.test_scaled(source start)(source count)(source stride)) in
 assert(actual=scaled start count stride);checked:= !checked+2
let page_base a=Int64.logand a(Int64.lognot 4095L)
let page_end a=Int64.add(page_base a)4096L
let paged (_,_,cowlo,cowhi,base) a=base<=a || (cowlo<=a && a<cowhi)
let run_end ((lo,hi,cowlo,cowhi,base)as layout) a=
 if paged layout a then page_end a else
 List.fold_left(fun before candidate->if a<candidate && candidate<before then candidate else before)base[lo;hi;cowlo;cowhi]
let source_geometry (lo,hi,cowlo,cowhi,base) a stop=
 let p,(r,e)=Prog.test_geometry(source lo)(source hi)(source cowlo)(source cowhi)(source base)(source a)(source stop)in p,integer r,integer e
let check_geometry layout a stop =
 let low,(offset,high)=Prog.test_page(source a)in
 assert((integer low,integer offset,integer high)=(page_base a,Int64.sub a(page_base a),page_end a));
 let finish=run_end layout a in
 assert(source_geometry layout a stop=(paged layout a,finish,Int64.min stop finish));
 assert(a<finish);checked:= !checked+2
let check_partition ((lo,hi,cowlo,cowhi,base)as layout) start count =
 let actual=Option.map(List.map(fun(a,b)->integer a,integer b))
   (Prog.test_pieces(source lo)(source hi)(source cowlo)(source cowhi)(source base)(source start)(source count)) in
 let expected=match span start count with None->None|Some(_, (stop,_))->
  let rec loop cursor after=if cursor=stop then List.rev after else
   let ending=Int64.min stop(run_end layout cursor)in
   assert(cursor<ending && ending<=stop);
   if paged layout cursor then assert(ending<=page_end cursor);
   loop ending((cursor,ending)::after)
  in Some(loop start[])in
 assert(actual=expected);
 (match actual with None->()|Some pieces->
  assert(List.fold_left(fun total(a,b)->Int64.add total(Int64.sub b a))0L pieces=count));
 incr checked
let random=Random.State.make[|0x5350414e;2026;71|]
let word()=let magnitude=Int64.logor(Int64.of_int(Random.State.bits random))
 (Int64.shift_left(Int64.of_int(Random.State.bits random))30)in
 if Random.State.bool random then magnitude else Int64.neg magnitude
let edges=[minimum;Int64.succ minimum;-8193L;-4096L;-1L;0L;1L;4095L;4096L;8191L;8192L;
 8589934591L;8589934592L;Int64.sub maximum 4095L;maximum]
let layouts=[0L,8192L,0L,0L,8589934592L;4096L,8192L,8192L,16384L,8589934592L;
 minimum,maximum,4096L,8192L,8589934592L;maximum,minimum,maximum,minimum,8589934592L]
let () =
 List.iter(fun a->List.iter(fun b->check_arithmetic a b;check_span a b 4096L)edges)edges;
 for _=1 to 5000 do let a=word()and b=word()in check_arithmetic a b;check_span a b(word())done;
 List.iter(fun layout->List.iter(fun address->List.iter(fun stop->check_geometry layout address stop)edges)edges)layouts;
 let starts=[0L;1L;4095L;4096L;8191L;16383L;8589934591L;8589934592L;Int64.sub maximum 4095L;maximum]in
 List.iter(fun layout->List.iter(fun start->List.iter(fun count->check_partition layout start count)
  [-1L;0L;1L;2L;4095L;4096L;8193L])starts)layouts;
 let start=Int64.sub maximum 4095L in
 let legacy=((Int64.to_int start)lor 4095)+1 in
 assert(legacy=min_int);
 assert(Prog.test_pieces(source 0L)(source 0L)(source 0L)(source 0L)(source 8589934592L)(source start)(source 1L)=
  Some[source start,source(Int64.succ start)]);
 assert(source_span maximum 1L=None);
 Printf.printf "PASS: %d checked arithmetic/span/page/partition comparisons; exact extrema, negative counts, scaled endpoints, coverage and legacy page-end wrap counterexample\n" !checked
ML
for backend in ocamlopt ocamlc; do
 ocamlfind "$backend" -w -a -package lwt -linkpkg soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml prog.mli prog.ml check.ml -o "check-$backend" >"$backend.log" 2>&1
 "./check-$backend"
done
