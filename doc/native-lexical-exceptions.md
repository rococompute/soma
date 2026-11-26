# Fresh public exceptions around lexical implementations

A monomorphic lexical assembly can declare public exceptions in its enclosing
scope while keeping its implementation in a sealed local module:

```soma
OCaml Native Static Assembly main As "Checked" With
 [Exception "Bad" := native_bad;Project "(read, parse)" := public_api].
OCaml Native Lexical Scope main.
OCaml Native Lexical Environment main
 Prefix [Modules layout.marker;Exception native_bad;Types types.marker;
         Values publication.last]
 Modules [] Local [].
```

`Exception` selects one of that same assembly's already checked exception
constructors. The ordinary static checks still require matching unqualified
constructor names, exception-value results, concrete payloads, main dependencies
and unique public names. Wrong constructors, cases, unrelated declarations and
duplicates fail. An explicit environment must place every declared exception
exactly once. Without an environment, public exceptions precede the lexical
binding. The enclosing scope, including any prefix, precedes the optional public
functor; exceptions are not silently moved into a functor application.

The emitted declaration creates the original public exception slot at its
selected position, rather than a new helper-owned slot or constructor wrapper.
The local binding module rebases `Soma_handles` constructors/cases to that public
exception. Type/module escapes and polymorphic lexical value generalization
remain rejected. Existing typed prefix order, dependency and scope checks apply.
The exception marker and constructor descriptor participate in environment
identity, in addition to the assembly's existing full exception metadata.

These newly supported exception-bearing lexical frames also avoid allocating
unused native binding fields solely because a publication schema is imported.
After normal extraction optimization, Soma records the actual `MLglob` references
from the compiler's intermediate representation. Within captured prefix scopes, only those callbacks need runtime wrappers;
other native bindings retain their original layout. Callbacks used by executable
Source remain present even
when their namespace also supplies a prefix. Already captured prefix module
scopes need no duplicate internal alias module. This uses compiler references,
not a parser or string scan over generated OCaml. The selected callback metadata
and proof/assumption validation remain intact. Other pre-existing assembly modes
retain their previous output and binding behavior.

The assembly manifest continues to authenticate Source, program, interface,
bindings, complete output and layout. No manifest or existing descriptor format
changes. A consumer copies the complete assembly and removes its original
products only through the existing whole-product assembly path.

`soma_native_lexical_exceptions.sh` checks complete APIs, original root slot names,
constructor and case rebasing, nullary and multiple payloads, borrowed payload
objects and natural Weak ownership, exact native/bytecode constructor allocation
against the previous ordinary static frame, ordered and default exception
placement, used prefix callback retention and unused callback removal. Invalid
prefixes and generic payloads fail; assumptions, hashes, byte provenance and
obsolete-output cleanup are checked. Existing lexical-scope, environment and
ordinary static-exception fixtures remain compatibility tests.
