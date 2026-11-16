# async_tasks

Three tasks, run at once by Async, Jane Street's OCaml library for
concurrent programs, called from Soma. The project has no OCaml code of
its own: `async.definition` and `core.definition` declare the values of the
libraries' modules that the program uses, named as in OCaml.

```
soma run main.soma        runs it
soma build main.soma      writes main.exe
soma extract main.soma    writes main-ocaml/, the program as an OCaml project
```

```
fast is done
medium is done
slow is done
all done
```

```
soma.toml          the project: its name, version and description
main.soma          the tasks, run at once, and the order they finish in
main.exp         ordering the tasks keeps every one
async.definition   what Soma takes Async to be
core.definition    ... and Core, for lengths of time and printing
```

## The libraries, declared

A `.definition` next to no module declares the module of a library, named
after the file: `async.definition` declares `Async`. Its Soma modules are
Async's submodules:

```rocq
OCaml Library "async".
Import core.

Module Deferred.
  t : Type -> Type.
  map : forall {A B}, t A -> (A -> B) -> t B.
  all : forall {A}, list (t A) -> t (list A).
End Deferred.

Module Clock_ns.
  after : Time_ns.Span.t -> Deferred.t unit.
End Clock_ns.
```

`Deferred.map` in Soma is `Async.Deferred.map` in OCaml, whose function is
labeled, `~f`. A label can be left undeclared, as here, and then the
argument is given in its place. It can also be declared by naming the
argument: `forall (f : A -> B)`. `Time_ns.Span.t` is
`core.definition`'s, Core's `Core.Time_ns.Span.t`, as Async has it.

## The program

```rocq
run_task (t : task) : Deferred.t unit :=
  Deferred.map (Clock_ns.after (Time_ns.Span.of_sec (snd t)))
    (fun _ => print_endline (fst t ++ " is done")).

run_all (ts : list task) : Deferred.t unit :=
  Deferred.map (Deferred.all (map run_task ts)) (fun _ => print_endline "all done").

main := Thread_safe.block_on_async_exn (fun _ => run_all tasks).
```

The tasks take 0.5, 0.125 and 0.25 seconds, and all of them take 0.5
seconds, as Async runs them at once. Soma computes the order they finish in,
without Async (`map fst (by_seconds tasks)`: `["fast", "medium", "slow"]`).
Running `main` prints them in this order. `main.exp` proves that
`by_seconds` keeps every task.

Soma never computes Async: to the kernel and to the evaluation of a term,
its values are parameters. Building the program extracts `main` to
OCaml, with `soma_bindings.ml`, which has each declared value at its
declared type, so that OCaml checks the declarations against the
libraries. Async does not depend on js_of_ocaml, so the program is an
executable, `main.exe`.

The first build installs `async` and `core` into Soma's opam switch,
`~/.cache/soma/ocaml`, once (see `bonsai_counter/README.md`).

## The program in OCaml

`soma extract main.soma` checks the program, and writes into `main-ocaml/`
the OCaml project that `soma build` builds. `prog.ml` is the program,
`soma_bindings.ml` holds the declarations, and the dune files and
`main.opam` list `async` and `core`. It builds with or without Soma:

```sh
cd main-ocaml
opam install . --deps-only
dune build --profile release
./_build/default/soma_main.exe
```

## Not yet

- Numbers between Soma and OCaml: a time is given as a `float` of seconds.
- A value whose OCaml name is a keyword of Soma's, such as `return`.
