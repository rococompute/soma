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

All node names share one namespace. `needs` adds dependencies to any node.
Artifact parts implicitly depend on their extraction; `{ unit = "prefix" }`
depends on another composed unit and consumes its complete contents. Targets
are extracted once per invocation, even if several units depend on them.
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

A per-project lock serializes builders. Extraction runs into a fresh directory;
a failed compiler invocation leaves the previous completed extraction in place.
Each unit is validated completely before atomic replacement. A failed later
node may leave earlier successful nodes updated, as in ordinary build systems;
publication is per node, not a transaction over the entire graph.
`.receipts/NAME.toml` records the config hash, ordered whole-artifact hashes and
output hash. Receipts describe successful publication; they are not trusted as
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
