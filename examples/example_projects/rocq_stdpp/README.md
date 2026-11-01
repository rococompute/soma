# rocq_stdpp

A shop's stock, kept in a finite map of
[stdpp](https://gitlab.mpi-sws.org/iris/stdpp), a Rocq library of finite
maps, sets and lists. stdpp is Rocq, which Soma takes as it is: no
definition, nothing translated, nothing taken on trust. Soma computes with
its functions, and proves with its lemmas and tactics.

```
soma build -v main.soma     the stock, computed; main.proof checked
soma explore main.soma      no escape hatch: stdpp is checked by Soma's kernel
```

```
main.soma     the stock, restock and sell, on stdpp's gmap
main.proof    restocking adds, selling one item changes no other, selling never sells what is not there
```

## A Rocq library

```
Rocq Library "rocq-stdpp".
From stdpp Require Import gmap strings.

stock : gmap string nat := <["apples" := 3]> (<["pears" := 5]> ∅).

sell (item : string) (n : nat) (s : gmap string nat) : option (gmap string nat) :=
  match s !! item with
  | Some k => if n <=? k then Some (<[item := k - n]> s) else None
  | None => None
  end.
```

`Rocq Library "rocq-stdpp".` names stdpp by its opam package. After it,
stdpp is in the load path, and `From stdpp Require Import gmap.` is Rocq's
own `Require`. Soma evaluates stdpp's functions as its own:

```
map_to_list (restock "plums" 4 stock).
     = [("apples", 3); ("pears", 5); ("plums", 4)]
option_map map_to_list (sell "apples" 2 stock).
     = Some [("apples", 1); ("pears", 5)]
sell "apples" 5 stock.
     = None
```

`main.proof` uses stdpp's lemma `lookup_insert_ne` and its tactic
`simplify_map_eq`, as any Rocq proof would:

```
Theorem sell_other : forall item other n s s',
  other <> item -> sell item n s = Some s' -> s' !! other = s !! other.
```

stdpp keeps the empty map opaque (`Global Opaque gmap_empty`) for its
proofs, and computes maps with `vm_compute`. The program makes it
transparent, `Transparent gmap_empty.`, so that Soma's evaluation computes
them.

## How Soma gets it

Soma cannot load the compiled stdpp that opam would install. Soma's kernel
is gradual, not that Rocq's, so its compiled files do not load. So Soma
compiles stdpp from its source, itself, the first time the program is
built:

1. It fetches the source with `opam source rocq-stdpp.1.13.0`, from
   Rocq's opam repository, which Soma adds to its own switch
   (`~/.cache/soma/ocaml`).
2. It finds the theories the package declares in its dune files,
   `(rocq.theory (name stdpp) (package rocq-stdpp))`.
3. It compiles them with Soma's `rocq c`, as Rocq: without Soma's
   prelude, whose names (`R`, the reals) and gradual typing stdpp does
   not expect. stdpp's own scripts and Makefiles do not run.

It goes into this project's `.soma-cache/rocq/`, once:

```
Rocq: fetching rocq-stdpp 1.13.0 (opam source)
Rocq: compiling rocq-stdpp.1.13.0-95f89058: 1/55 stdpp/options.v
...
Rocq: compiling rocq-stdpp.1.13.0-95f89058: 55/55 stdpp/binders.v
```

This takes about 50 seconds; later builds take a fraction of a second. The
directory is named after Soma's own compiled libraries, whose change makes
what was compiled with them inconsistent: a new Soma compiles it again,
and removes the old one.

`Rocq Library "rocq-stdpp" "1.13.0".` asks for a version, and
`Rocq Library "mylib" in "vendor/mylib".` takes a library from a
directory of the project instead. A library that loads an OCaml plugin is
refused, as a plugin is built against the Rocq it extends.

## Not yet

- A library's own dependencies are not found from its opam file: each is
  named by a `Rocq Library` before it (stdpp needs only Rocq's Stdlib,
  which Soma has).
- Libraries with OCaml plugins (Equations, Elpi, mathcomp's Hierarchy
  Builder).
