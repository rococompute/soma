# bonsai_counter

A counter in the browser. Its state, actions and view are Soma's, written
in JSX. Bonsai, Jane Street's OCaml library for web apps, runs it. Soma
code calls Bonsai's own functions, and the project has no OCaml code of
its own.

```
soma run main.soma        serves it at http://localhost:8080 (Ctrl-C stops)
soma build main.soma      writes main.html and main.js, a page that runs as it is
soma extract main.soma    writes main-ocaml/, the program as an OCaml project
```

```
main.soma               the counter: its actions, step, view; main runs it
main.proof              the count stays at most 10, and main runs the counter
render.soma             JSX elements as Bonsai's virtual DOM, and JSX apps run by Bonsai
bonsai.definition       what Soma takes Bonsai's module Bonsai to be
bonsai_web.definition   ... and Bonsai_web, its library for the web
js_of_ocaml.definition  ... and the types of js_of_ocaml that a click has
```

## What it needs

Only `soma`, and opam. The first build of a program that uses OCaml makes
an opam switch for Soma, in `~/.cache/soma/ocaml`. It then installs the
libraries that the definitions name into it, here `bonsai`: about 150
packages, which takes a while, once. Soma says so as it starts
(`OCaml: installing ...`), and logs it in `~/.cache/soma/ocaml/setup.log`.
`SOMA_OCAML_SWITCH` names a switch to use instead.

What can stop the setup is a library of the system that a package needs.
Bonsai's opam package pulls in `async_ssl`, whose C code does not build
against OpenSSL 4. If the setup fails there, point pkg-config at OpenSSL 3
and build again:

```
PKG_CONFIG_PATH=$(brew --prefix openssl@3)/lib/pkgconfig soma build main.soma
```

## A library's modules, declared

`bonsai.definition` is next to no `bonsai.ml`, so it declares the module of
a library: `Bonsai`, named after the file. Its Soma modules are Bonsai's
submodules, and each declaration is the value or type of its name there:

```
OCaml Library "bonsai".

Module Var.
  t : Type -> Type.
  create : forall {A}, A -> t A.
  value : forall {A}, t A -> Value.t A.
  update : forall {A}, t A -> forall (f : A -> A), unit.
End Var.
```

`Var.update` in Soma is `Bonsai.Var.update` in OCaml. A named argument is
OCaml's labeled one: `forall (f : A -> A)` is `~f`, and in
`bonsai_web.definition`, `Vdom.Node.create`'s `forall (attrs : list
Attr.t)` is its optional `?attrs`. In Soma, all of them are given by
position. Optional arguments that are not declared are left out.

A declared type of `Type` (or `Type -> Type`) is one of the library's
types: `Var.t` is `'a Bonsai.Var.t`. The type of a value is made of
`string`, `bool`, `unit`, `list`, `option`, products, `float`, functions,
these types, and type variables. A type that OCaml does not share with
Soma, such as `nat` or `Any`, is refused when the definition is compiled.

## Building it

Soma never computes Bonsai. To the kernel and to the evaluation of a term,
its values are parameters, so no proof holds by running OCaml code.
`render (view ...)` at the end of `main.soma` is computed by Soma, as
HTML, and not by Bonsai.

Building `main.soma` extracts `main` to OCaml. Next to it goes
`soma_bindings.ml`, which has each declared value at its declared type:

```
let bonsai__Var__update : 'a. 'a Bonsai.Var.t -> ('a -> 'a) -> unit =
  fun a0 a1 -> Bonsai.Var.update a0 ~f:a1
```

OCaml then checks each declaration against Bonsai, as dune builds the
program with `bonsai.web`. `soma extract main.soma` writes this project into
`main-ocaml/`. It builds with or without Soma (`opam install . --deps-only &&
dune build --profile release`, then open `index.html`). Its type variables are rigid, so a declaration
more general than the library's value is an error too. Bonsai depends on
js_of_ocaml, so the program is made for the browser: it is built into
`main.js`, with `main.html`, the page that runs it in `<div id="app">`.
The projects are kept in `~/.cache/soma/ocaml/build/`.

## The app

`render.soma` runs an app of `Soma.JSX` with Bonsai. Its state is one of
Bonsai's variables (`Var.create (init a)`), and a click sets it to the
app's `update` of it (`Var.update state (update a action)`). The page is
the app's `view` of it, as Bonsai's virtual DOM:

```
run {S A} (a : app S A) : unit :=
  let state := Var.create (init a) in
  let send := fun action => Var.update state (update a action) in
  Start.start (read (Value.map (Var.value state) (fun s => page send (view a s)))).
```

Bonsai's own state machines, `state` and `state_machine0`, take the state's
type as an OCaml module of the `Model` signature, which Soma has no way to
write: so the state is a variable, and its machine is Soma's `step`.

## What is proved

`main.proof` proves, as `reason_counter.proof` does, that whatever the
clicks, the count stays at most `limit`, and that `main` runs this counter:
`run (make_app 0 step view)`. That Bonsai then shows `view` of the state
after each click is Bonsai's to keep.

`soma explore main.soma` lists the library's values as escape hatches,
with their OCaml types.

## Not yet

- Numbers between Soma and OCaml (`nat`, `N`, `Z` and `int`).
- OCaml's modules as values (`(module Model with type t = 'a)`), and
  labeled arguments of a function given to OCaml.
- A value whose OCaml name is a keyword of Soma's (`return`).
