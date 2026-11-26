#!/usr/bin/env bash
# Positional default adaptation preserves already-compatible function objects.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat > target.ml <<'ML'
type g = { name : string }
let current=ref {name="first"}
let trace=ref []
let response=ref (Lwt.return "ready")
let context:string Lwt.key=Lwt.new_key()
let observe=ref(fun (_:string)->())
let default()=trace:="default" :: !trace;!current
let generate ?(g=default()) text=trace:=g.name :: !trace;(!observe)text;!response
let raw text=(!observe)text;!response
ML
cat > target.definition <<'SOMA'
From Soma Require Import Native Handles.
From Stdlib Require Import Strings.String.
OCaml Native External Type g := "Target.g".
OCaml Native Callable generator Optional g := forall(g:option g), string -> promise string.
OCaml Native External Defaulted Function adapted : string -> promise string := "Target.generate" Using generator.
OCaml Native External Defaulted Function borrowed : string -> promise string := "Target.raw" Using generator.
SOMA
cat > main.soma <<'SOMA'
From Soma Require Import Native.
Import target.
Definition body := Native.Export (Native.Return (adapted,borrowed)).
Definition main := body.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
(cd native && dune build --profile release -j2)>build.log 2>&1
cp native/{prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml,target.ml} .
cp native/soma_callable_*.ml .
cat > check.ml <<'ML'
let require name value=if not value then failwith name
let original()=(fun (f:string->string Lwt.t)->f)Target.generate
let ()=
 let make,borrow=Prog.body in
 let adapted=make()in
 require "already-positional target borrowed"(borrow()==Target.raw);
 Target.trace:=[];let later=make()in require "preparation does not apply optional default"(!Target.trace=[]);
 let text=String.make 1048576 'x'and fault=Failure "provider fault"in
 Target.observe:=(fun actual->require "borrowed argument"(actual==text);require "caller context"(Lwt.get Target.context=Some "caller"));
 let pending,wake=Lwt.task()in let canceled=ref 0 in Lwt.on_cancel pending(fun()->incr canceled);
 List.iter(fun response->Target.response:=response;
  List.iter(fun name->Target.current:={Target.name};
   let run f=Target.trace:=[];let value=Lwt.with_value Target.context(Some "caller")(fun()->f text)in
    require "exact returned promise"(value==response);List.rev !Target.trace in
   require "default lookup occurs on every invocation"(run(original())=run later)) ["first";"second"])
  [Lwt.return text;pending;Lwt.fail fault];
 Target.response:=pending;Lwt.cancel(Lwt.with_value Target.context(Some "caller")(fun()->adapted text));require "cancellation reaches original promise"(!canceled=1);ignore(Sys.opaque_identity wake);
 Target.observe:=(fun _->raise fault);
 require "exact synchronous exception"(try ignore(adapted text);false with error->error==fault);
 Target.observe:=(fun _->());Target.response:=Lwt.return text;
 let collect()=Gc.full_major();Gc.full_major()in
 let measure f=collect();let before=Gc.allocated_bytes()in for _=1 to 10000 do ignore(Sys.opaque_identity(f()))done;Gc.allocated_bytes()-.before in
 require "closed getter sharing"((make()==make())=(original()==original()));
 require "getter allocation matches native coercion"(measure make=measure original);
 let before=original()in
 require "call allocation matches native coercion"(measure(fun()->before text)=measure(fun()->adapted text));
 print_endline "PASS: positional coercion borrows compatible functions, applies optional defaults at invocation, and preserves promises, context, faults, cancellation, sharing and exact allocation."
ML
for compiler in ocamlopt ocamlc;do
 ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
  soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml target.ml soma_callable_*.ml soma_bindings.ml prog.mli prog.ml check.ml
 "./check-$compiler"
done
