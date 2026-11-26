# Optional arguments on external native callbacks

An external callback can forward selected native options directly:

```soma
OCaml Native External Callback info_with_doc Optional doc :
  list string -> forall (doc : option string), info := "Cmdliner.Arg.info".
```

The optional names identify value binders in the checked signature. Each must
occur exactly once and have the standard logical/native option representation.
Missing names, duplicate declarations/binders, non-option domains and type
parameters listed as options fail checking. Multiple optional arguments,
ordinary positional/required-labelled arguments, generic type parameters,
functions and promises retain their existing callback types.

The backend forwards the same option with `?doc:argument`. It does not turn it
into a required label, unwrap it, build a replacement `Some`, choose a default,
or introduce another native adapter. Actual OCaml compilation checks the
external owner's optional payload types as well as its result. Native defaults
and exceptions remain the external function's behavior.

This uses the existing native callback descriptor and label field. No metadata
case/layout or assumption is added; optional labels participate in the existing
ABI and semantic identity. Old declarations without `Optional` keep their
previous fingerprints and artifacts. The callback's existing logical product
input and extraction calling convention are unchanged.

`test-suite/misc/soma_native_optional_callback.sh` checks native and bytecode
option-box/content/owner/payload identity, multiple optional arguments in
signature order, generic bytes/functions, quiet partial applications, exact
promises, caller context, fault/cancellation phases and natural Weak ownership.
Its allocation oracle is the previous checked callback through an independent
positional-to-optional wrapper: 100,000 calls allocate exactly 13,600,096 bytes
in native and 13,600,144 in bytecode on both paths. Those are existing callback
costs, not a claim of allocation-free native calls. Generic forwarding also
retains exact allocation. Invalid declarations and an incorrect actual OCaml
optional payload signature fail; optional/required label changes alter both
ABI and semantic hashes. The previous raw-callable fixture remains unchanged.
