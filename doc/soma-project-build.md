# Native project build graphs

`soma project plan` validates and prints the dependency order in `soma.toml`.
`soma project build` executes it. Both accept `--config FILE` and repeated
`--target NAME`. An explicit config may contain just `[build]`, which is useful
when integrating an existing project without changing its import root.

```toml
[project]
name = "example"
version = "0.1.0"

[build]
directory = ".soma-build"
targets = ["executable"]
source-only = true

[build.extract.source]
file = "main.soma"
source-root = "."
bindings = "Soma_bindings"
verify = true

[build.unit.public]
output = "public.ml"
parts = [
  { extract = "source", kind = "source-types", namespace = "exports" },
  { extract = "source", kind = "modules", namespace = "exports" },
  { extract = "source", kind = "values", namespace = "exports" },
]

[build.publish.implementation]
extract = "source"
file = "prog.ml"
output = "implementation.ml"

[build.module-list.modules]
output = "modules.sexp"
units = ["public", "implementation"]

[build.dune.executable]
directory = "."
targets = ["main.exe"]
needs = ["public"]
```

The project's Dune rules must consume `.soma-build/public.ml` and any required
support modules from `.soma-build/.extract/source`. The graph delegates native
compilation, linking, C dependencies and their incremental scheduling to Dune;
it does not synthesize or rewrite Dune files. Dune also type-checks the resulting
OCaml unit. There is no new handwritten application OCaml involved in assembly.

## Nodes and order

An artifact selector may declare an ordered export contract. `names` lists the
public names introduced by one compiler declaration (including the field order
of a record or tuple projection); `target` identifies its declared source or
native target. The native publisher compares these rows with the authenticated
compiler manifests before publishing that unit:

```toml
[build.unit.flags]
output = "flags.ml"
parts = [
  { extract = "source", kind = "source-types", namespace = "exports", expect = [{ names = ["flag"], target = "" }] },
]
```

Contracts apply to complete namespaces. A changed name, target, projection order
or row inventory fails the build; the contract cannot select only matching
members from an artifact. For `bindings`, values and projections are compared
in their common compiler order. For `initializers`, the same binding inventory
is checked without inserting a second copy of the published values. The build
configuration hash binds the contract into product receipts, and fresh audit
enforces it too. These are structural publication checks; they provide no proof
of a target's behavior or of cross-module runtime type compatibility.
An empty target explicitly matches a local type declaration, whose compiler
manifest has no external target name.

An extraction may also bind the complete native ABI of selected logical owners:

```toml
[build.extract.source]
file = "main.soma"
verify = true
abi = [{ symbol = "main.main", sha256 = "<64 lowercase hexadecimal digits>" }]
```

`soma project abi --directory .soma-build/.extract/source` reports the available
fingerprints as TOML. It authenticates the ABI manifest against the completed
compiler product inventory; it is an inspection command, not evidence of fresh
source verification. Review the native declarations and API before recording a
fingerprint. Build and audit check it against a **fresh extraction**, before that
extraction or any dependent product is published. A missing owner, changed tuple
projection, record/module layout, type equation, publication frame, native
target or other identity attached to that owner fails the contract. Every
identity for a contracted symbol participates, including when the compiler
records several kinds of identity for the same owner. Uncontracted owners are
unconstrained by this additional API check.

Fingerprint format 1 hashes `soma-project-abi-v1` followed by a newline and the
sorted `(namespace, identity)` pairs from `native_abi.manifest`, each string
encoded as its decimal byte length, a colon and its bytes. Duplicate identities
are invalid. Source byte hashes are excluded from this API fingerprint so that
comments and implementation edits with the same declared ABI remain possible;
the native verification receipt still binds the full source/proof inputs.
The build configuration hash binds expected ABI fingerprints into publication
receipts. This is an explicit structural compatibility contract, not a type
checker for foreign links, a semantic specification, or a verified compiler.

All node names share one namespace. `needs` adds dependencies to any node.
`[build.publish.NAME]` publishes one complete file from a fresh checked
extraction, optionally under a different filename. It can publish a complete
implementation, signature, native assembly, support file or verification receipt.
It cannot read arbitrary project files or slice or modify compiler output.
Its extraction is an implicit dependency. Published `.ml`/`.mli` outputs may
also be referenced by `{ unit = "NAME" }`; metadata files cannot be inserted
into OCaml compositions through unit references.

`[build.module-list.NAME]` emits a closed Dune module list from named checked
unit outputs, without globbing a directory that could contain stale or unowned
OCaml. Implementation/signature pairs become one module name. Every unit's
published bytes are rechecked, and the inventory receipt binds the contributing
unit receipt hashes. Dune can consume it as `(modules (:include modules.sexp))`.
Metadata nodes and extractions cannot be passed as units.
The list must live in a different directory from the consuming Dune stanza,
for example `build-info/modules.sexp`, to avoid Dune's module-discovery dependency
cycle. See Dune's [module field documentation](https://dune.readthedocs.io/en/stable/reference/dune/library.html).

`[build.source-map.NAME]` emits a TOML source map for a checked OCaml `unit`,
at its configured `output` path (ending in `.toml`). It records the complete
unit hash, configuration and producer receipt hashes, plus the ordered whole
compiler artifacts with byte sizes and hashes and the exact ASCII spacing.
Nested unit compositions are flattened without slicing artifacts. Tools can
recover source spans without implementing assembly themselves; the source map
does not grant permission to publish partial artifacts. A fresh project audit
checks maps as well as products and receipts.

```toml
[build.source-map.public_spans]
unit = "public"
output = "public.ml.soma-parts.toml"
```

`[build] source-only = true` requires `verify = true` on every extraction and
refuses copied foreign OCaml source modules before extraction publishes files.
Soma-generated bindings/runtime modules, linked library modules and C sources
remain available. This distinguishes generated OCaml from an extractor merely
copying a handwritten foreign `.ml` file. It does not verify linked libraries,
C, extraction or the compiler; those remain part of the TCB.
Artifact parts implicitly depend on their extraction; `{ unit = "prefix" }`
depends on another composed unit and consumes its complete contents. Targets
are extracted once per invocation, even if several units depend on them.
`{ whitespace = "\n" }` can preserve ASCII spacing between complete products;
only spaces, tabs and line endings are accepted, never source text.
Unknown references, cycles, wrong reference kinds, unknown keys, wrong TOML
types and conflicting output paths are rejected before executing any node.

Parts are ordered, never sorted: declarations and initialization may depend on
earlier parts. Supported artifact kinds are `source-types`, `modules`, `values`,
`bindings`, `aliases`, and `initializers`. `bindings` validates the combined
value/projection inventory while copying its complete compiler artifact;
it never synthesizes or reorders declarations. A selector names a whole compiler-owned namespace
artifact. It cannot supply OCaml text, select individual declarations, slice an
artifact or insert a wrapper. Duplicate artifacts in one composed unit are
rejected, including through nested unit dependencies and extraction aliases.
Source namespaces remain responsible for which definitions are exported.

Every selected manifest must have its known version/schema and contiguous
declaration order. The manager verifies SHA-256 hashes of the referenced Source
files and the complete artifact bytes. A selection cannot silently include a
different namespace or span several files. Relative paths cannot escape the
config/source/output roots or traverse symlinks. Reserved output paths cannot
overwrite extraction directories, receipts or the build lock.

## Freshness and publication

The implementation is statically typed OCaml in Soma, using Soma's existing
typed TOML parser. It invokes tools with argv, never interpolated shell commands.
Extraction options are deliberately restricted to `-no-soma-prelude` and
`--no-module-cache`; locations and bindings have their own typed fields.
`verify = true` requires a source-owned `Verification` policy for every Soma
library in that extraction's project dependency closure, including cached
imports. Foreign `.definition` libraries are checked through their users.
Missing policies or failed obligations stop extraction before the previous
completed products are replaced. See [native verification](soma-verification.md)
for the declaration, static-fragment restriction and receipt format.

Each build runs the ordinary Soma checker/extractor, which owns dependency and
proof validation. There is deliberately no new extraction-skip cache based on
mtime, a Python receipt, a main-file hash, or an unverified external directory.
Existing Soma import caching remains in use. Native compilation is incremental
through Dune. Whole unit output is compared by bytes and left untouched when
unchanged, so downstream native builds are not invalidated by publication.
An identical completed extraction also retains its files and Dune cache.
Existing `[dependencies]`/`soma.lock` resolution continues to belong to Soma;
this graph does not introduce a second package resolver.

`soma project audit` freshly checks and extracts the selected source closure,
reconstructs the whole products and module inventories, and compares both their
bytes and receipt contents to the completed publication. It does not trust an
old Python inventory, an existing extracted program or a receipt's claims as
evidence of current source checking. Missing/changed products, stale proof
inputs and modified receipts fail the audit. Temporary extractions are cleaned;
completed extraction directories, published products and receipts are not
replaced. Source/import caches and private checking scratch may be refreshed.
External Dune compilation nodes are skipped: the audit covers graph-owned
source products and evidence, not a linked executable or final image's TCB.

A per-project lock serializes builders. Extraction runs into a fresh directory;
a failed compiler invocation leaves the previous completed extraction in place.
Each unit is validated completely before atomic replacement. A failed later
node may leave earlier successful nodes updated, as in ordinary build systems;
publication is per node, not a transaction over the entire graph.
`.receipts/NAME.toml` records the config hash, ordered whole-artifact hashes,
output hash and the contributing extractions' native verification receipt
hashes, where declared. Receipts describe successful publication; they are not trusted as
proofs or used to skip checking. Temporary failed extraction directories are
removed. Completed extraction directories remain available to Dune.

This first version executes graph nodes serially. It is not yet a replacement
for Ninja's parallel execution engine, distributed builds or toolchain lock
resolution. Preserving compiler-checked type identities, generics, initialization
and ownership semantics remains necessary: a typed build manager and byte hashes
do not themselves prove runtime behavior or the compiler correct.

## Publish products from an existing checking pipeline

`soma project assemble --config units.toml --inventory checked-inputs.toml`
supports projects whose existing build already checks proofs and authenticates
compiler products. `--unit NAME` selects a unit; `--check` compares without
publishing. This is an artifact linking step, not a second proof checker or an
extraction-skip cache. The producer must supply its complete checked input closure.

```toml
format = 1
[units.public]
output = "generated/public.ml"
parts = [
  { owner = "types", product = "public_types" },
  { whitespace = "\n" },
  { owner = "runtime", product = "public_values" },
]
```

The inventory is data from the producer's proof/origin gate. Its schema is
`format = 1`, `config-sha256`, a `[sources]` table of project-relative input
paths to SHA-256 strings, and `[products.NAME]` tables containing `owner`,
`path`, and `sha256`. Inputs include Source, proof receipts and supporting
products. The assembler rechecks every input, binds the inventory to the exact
config hash, and permits only complete products and ASCII whitespace. Input
map order never determines output order. Missing products, changed owners,
paths/symlinks escaping the root, duplicate/aliased products, unknown schema
fields, conflicting outputs and overwriting checked inputs fail before output
publication. All selected units are prepared before any output is replaced.

Invocations sharing an inventory directory serialize on its private lock file.
The producer should use immutable unique inventory filenames in that shared
directory. Publication is atomic per file and leaves unchanged bytes/mtimes alone.
An ordered `NAME.composition.toml` receipt beside the inventory records the
config/inventory/output hashes and each whole input's owner, size and digest.
The same data is published as `OUTPUT.soma-parts.toml` for consumers that need
authenticated source spans without putting delimiters into the OCaml itself.
That lets the existing provenance auditor retain original dependency edges
without asking a dynamically typed orchestration script to reconstruct ordering
or concatenate source text. Like other build receipts, it is metadata and does
not add logical assumptions or establish a proof of the compiler.
