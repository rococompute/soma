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
`aliases`, and `initializers`. A selector names a whole compiler-owned namespace
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
