(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * OCaml modules, [Soma.OCaml]

    An OCaml module [FILE.ml] is used from Soma through [FILE.definition],
    next to it, which says what Soma takes its values and types to be, and
    which libraries it uses:

        OCaml Library "bonsai.web".
        html : Type -> Type.
        text : forall {A}, string -> html A.

    [Import FILE.] compiles the definition into a library of the project
    (plugins/soma_ocaml), where each declared name is FILE.ml's value or
    type of that name, in the submodule of its Soma module: [Module
    Deferred. bind : ... End Deferred.] declares [File.Deferred.bind].

    Next to no module, FILE.definition declares a module of the libraries
    it names: async.definition declares [Async], its values and types
    named as in OCaml, with their labels left out ([Deferred.bind]'s [~f]
    is its second argument) and their optional arguments too:

        OCaml Library "async".
        Module Deferred.
          t : Type -> Type.
          bind : forall {A B}, t A -> (A -> t B) -> t B.
        End Deferred.

    A declared type of [Type] (or [Type -> Type], ...)
    is an OCaml type ([html] is ['a File.html]); the type of a value is
    made of [string], [bool], [unit], [list], [option], products, [float],
    functions, these types, and type variables ([forall A]).

    Soma never computes them: they are parameters to the kernel and when
    Soma evaluates a term, so that no proof holds by running OCaml. A
    program whose [main] uses them is built with FILE.ml and the
    libraries, by OCaml, which checks each declaration against what it
    declares (toplevel/somaOcaml.ml).

    The same declarations work in a [Sandbox] program. Its local OCaml
    modules and typed bindings are compiled into the MirageOS image,
    with declared libraries (including C-backed libraries) built for the
    Solo5 target. Those libraries must support that target; host-only
    facilities such as [Soma.Host] and [unix] are not available. Exact
    [soma.toml] [opam] versions constrain the image's dependency solver.
    [soma build --no-image] checks the bindings too, using the declared
    libraries installed for its OCaml compiler; it does not link or run
    their C stubs. Native declarations stay opaque to the proof kernel.
    See examples/example_projects/native_crypto and
    dev/ocaml-mirage-check.sh. *)

From Stdlib Require Strings.String.
From Corelib Require PrimFloat.

(** [float], OCaml's, and its literals ([0.5]), without PrimFloat's names
    ([add], [mul], ...), which a module may have *)
Module Export Floats.
  Export PrimFloat.PrimFloatNotations.
  Abbreviation float := PrimFloat.float.
  Number Notation PrimFloat.float PrimFloat.parser PrimFloat.printer : float_scope.
End Floats.

Declare ML Module "soma-runtime.plugins.soma_ocaml".
