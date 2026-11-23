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
    [int] ([Uint63.t], OCaml's int), [nat], [word64] (Soma.Word64's
    unsigned 64-bit words, OCaml's [int64]; C's [uint64_t]), [buffer]
    (Sandbox's, OCaml's [bytes]; C's [soma_bytes], an argument it may
    write in place), [promise A] (Sandbox's, OCaml's ['a Lwt.t], which a
    program waits for with [await_promise]; an image's only), [deferred A]
    (Sandbox's cached computation), [reference A] (a mutable location),
    [exception_value] (the native exception object),
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

(** ** Assumption-free native ABI declarations

    A [.definition] may instead import [Soma.Native] and declare executable
    descriptors. These commands define symbolic, namespaced values; they add
    no Parameter or Axiom and never evaluate the external library in Soma:

        From Soma Require Native.
        OCaml Native Type item := "item".
        OCaml Native Get value : item -> string := "value".
        OCaml Native Set put_value : item -> string -> unit := "value".
        OCaml Native Build make : string -> bool -> item := "value" "flag".
        OCaml Native Copy with_value : item -> string -> item := "value".
        OCaml Native Callback join : forall (left : string), string -> string := "join".

    Paths are relative to the OCaml module declared by the file, including
    its submodules. A native type is an opaque handle indexed by the full
    logical declaration name. A callback is [Native.Named_callback namespace
    name], where the compiler supplies the logical module and declaration
    names. Two same-typed imports in different modules have distinct symbolic
    identities. Native wrapper names encode both components injectively, so
    nested module paths cannot collide with names containing underscores.
    Placeholder constructors fail if executed; inspection is rejected during
    extraction. Neither can create or inspect real native values.

    Execute a descriptor with [Native.Call_callback]. Its arguments are one
    value, or a right-nested product for multiple arguments: [join (left,
    right)], [make (value, flag)]. The generated wrapper unpacks that product
    and applies the native function fully, using named binders as OCaml
    labels. No wrapper catches exceptions, maps promises, or stores providers.

    Get and Set keep native record identity. Get may return a function value
    without allocating a replacement. Set requires a mutable native field.
    Build supplies every field; Copy allocates a record using native copy
    syntax and preserves all unspecified components. Record arguments are
    positional. OCaml checks field existence, field types, mutability and
    construction completeness against the actual module. Field access and
    mutation are callback effects, with no mutable pure projection laws.

    Extraction emits [native_abi.manifest], containing canonical descriptor
    names, signatures, operations and source digests. The same metadata is
    included in definition hashes: changing a target or record operation
    invalidates dependents even if the symbolic placeholder stays unchanged.
    Binding discovery follows opaque exported main bodies as well as ordinary
    definitions. An unavailable opaque dependency is an explicit error.

    The first stage supports monomorphic opaque types and callback signatures.
    Explicitly supplied optional arguments, polymorphic descriptors, native
    variant views, exception declarations and emission of owned native record
    types are not yet supported. Existing
    parameter-based [.definition] declarations remain available separately.
    See [examples/example_projects/native_abi] and [dev/native-abi-check.sh]. *)

From Stdlib Require Strings.String.
From Corelib Require PrimFloat.

(** [float], OCaml's, and its literals ([0.5]), without PrimFloat's names
    ([add], [mul], ...), which a module may have *)
Module Export Floats.
  Export PrimFloat.PrimFloatNotations.
  Abbreviation float := PrimFloat.float.
  Number Notation PrimFloat.float PrimFloat.parser PrimFloat.printer : float_scope.
End Floats.

From Corelib Require PrimInt63.

(** [int], Rocq's primitive 63-bit integer (OCaml's [int] once extracted:
    [Uint63.t] in an OCaml module, [int64_t] in a C one), and its literals
    ([42]), without PrimInt63's names ([add], [lsl], ...), which a module
    may have *)
Module Export Ints.
  Export PrimInt63.PrimInt63Notations.
  Abbreviation int := PrimInt63.int.
  Number Notation PrimInt63.int PrimInt63.parser PrimInt63.printer : uint63_scope.
End Ints.

(** [word64], Soma.Word64's unsigned 64-bit words, and Sandbox's
    [buffer], [promise], [deferred], [reference] and [exception_value] *)
From Soma Require Word64 Handles.
Module Export Words.
  Abbreviation word64 := Soma.Word64.word64.
  Abbreviation buffer := Soma.Handles.buffer.
  Abbreviation promise := Soma.Handles.promise.
  Abbreviation deferred := Soma.Handles.deferred.
  Abbreviation reference := Soma.Handles.reference.
  Abbreviation exception_value := Soma.Handles.exception_value.
End Words.

Declare ML Module "soma-runtime.plugins.soma_ocaml".
