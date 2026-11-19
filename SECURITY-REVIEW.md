# Security review: Soma's findings

From an independent review of Soma and Pantheon before open sourcing (Nov 8
2026), scoped to what Soma changed since forking Rocq at d77b754ffa. The full
report, Pantheon's findings included, is Pantheon's docs/SECURITY-REVIEW-2.md.
Paths here are relative to this repository. .plan lists what's next.

## S-1. Soma: the build cache and shared cache are trusted without rechecking

**Severity: High (Soma); Medium for Pantheon.** `somaImport.ensure`
(`somaImport.ml:445-456`) considers a cached `.vo` fresh when the `.stamp`
(`:288-306`) says its source hash and import digests match. The `.stamp`,
`load-paths` (`:350-378`) and the `.vo` are all in the project's
`.soma-cache`, which a hostile project can carry. The shared cache
(`soma.ml:299-340`) is keyed only by project source files (MD5 via OCaml's
`Digest`), ignores the Soma/toolchain, and publishes whatever is in
`.soma-cache` first-writer-wins. The freshness record
(`soma.ml:1080-1113`) is likewise a plain file the project can forge.

**Scenario.** A project (or a checkout with a committed `.soma-cache`)
supplies a `.vo` and a matching `.stamp`; `soma build` loads the `.vo`
without the kernel rechecking it, so a false theorem or different definitions
pass. For Pantheon, a bid can add `.stamp`/`load-paths` text (they are text)
and rely on a tracked `.vo`; a person or a binary worker can commit the
`.vo` (a normal text bid skips binary files in `edits_of_checkout`). The
shared cache can be poisoned by any local build with the same source key,
and a later clean checkout restores the attacker's definitions. The earlier
review reproduced both.

**Fix.** Do not trust a `.soma-cache` that git tracks or that this machine
did not write; include the Soma and toolchain digests in the shared-cache
key; publish only what this build wrote, atomically; make the shared cache
opt-in for untrusted checkouts; recheck a `.vo` with `rocqchk` (or load it
with a provenance digest) when it comes from the project.

## S-2. Soma: `Rocq Library` uses an unvalidated package/version as a path component

**Severity: High (Soma); Medium for Pantheon.** `plugins/soma_rocq/soma_rocq.ml:275-323`
computes the cache directory as

```ocaml
Filename.concat root (package ^ "." ^ version ^ "-" ^ key)
```

where `package` and `version` come from `Rocq Library "PKG" "VER" in "DIR".`
in an untrusted `.soma`; `ensure` then does `remove_tree dir`, `mkdir_p dir`,
`copy_tree`, and compiles there. There is no validation of `package` or
`version` (unlike `SomaProject.parse_path`), and `package` is also passed to
`opam show/source`.

**Scenario.** A bid contains
`Rocq Library "../../../../tmp/x" in "."`. `dir` escapes
`$XDG_CACHE_HOME/rocq`; `remove_tree`/`mkdir_p`/`copy_tree` write or
delete at the traversed path as the builder. A target directory has to end
in `.<version>-<key>` to be removed, but the attacker controls `package` and
`version` and can create such a directory (for example under `/tmp`), and
`mkdir_p`/`copy_tree` write outside the cache. On `host.sh` or `pantheon up`
the builder is the node's user. A `package` beginning with `-` is also
passed to opam as an option.

**Fix.** Require a safe single component for `package` and `version`
(letters, digits, `.`, `_`, `-`, no `/`, no `..`, no leading `-`), then
canonicalize the result under the cache and reject anything that escapes.

## S-3. Soma: `soma.lock`'s commit is not validated

**Severity: Medium.** `somaDeps.read_lock` (`:174-202`) accepts any string for
`commit`; `source_dir`/`fetch` (`:116-151`) put it in a directory name and
`cache_of` (`:400-406`) uses it as a path component. A leading `-` also
reaches `git checkout`/`fetch` as an option.

**Scenario.** A hostile `soma.lock` sets `commit = "../../../../tmp/x"`.
`fetch` builds `dir` with `..`, calls `remove_tree tmp` and `mkdir_p` before
the fetch can fail; `cache_of` can write compiled files outside
`.soma-cache/.deps`. A commit that resolves must avoid `..`, but the
traversal/deletion happens before checkout, and the cache path is used even
when it later fails. The earlier review's Medium.

**Fix.** Require 40 hexadecimal digits (or a validated full ref) and reject
anything else; canonicalize the cache path under the project.

## S-5. Soma: building an untrusted project can run code and write outside the project

**Severity: High for Soma standalone; Medium for Pantheon.** The build path
runs code from the project:

- `toplevel/somaOcaml.ml:168-203` runs `opam install` (package build
  scripts), and `:494-496` runs `dune build` (ppx and project `.ml`/dune
  rules).
- `toplevel/somaMirage.ml:664-675` runs `mirage configure`, `make depends`
  and `make build`.
- `plugins/soma_rocq/soma_rocq.ml:288-298` runs `opam source`; a Rocq
  library's `.v` can
  `Redirect`/`Extraction` because `soma_rocq.clean_env` removes the
  `SOMA_PROJECT_PREFIX` that `refuse_in_dependency` checks.
- `plugins/extraction/extract_env.ml:746` and `vernac/synterp.ml:386` refuse
  writes only in a dependency; the project being built can
  `Extraction "/abs/path"` or `Redirect`.
- `plugins/soma_lean` runs Lean, which evaluates `#eval` and may fetch a
  `lean-toolchain`.

`GRADUAL.md:440-444` says "This is not a sandbox", but it understates the
`[opam]`/dune/Mirage/Lean paths. In `pantheon up`/`host.sh` the model's own
`soma build` runs as the node's user; in CI the Docker/`ci-sandbox` limits
it, but the model's local build is not sandboxed.

**Scenario.** A bid's `soma.toml` has `[opam]` with a package whose build
script does something, or a `.ml`/dune rule that runs a command; the build
executes it as the builder and can read the builder's files (keys when it is
the node's user) or write outside the checkout. A `.soma` can
`Extraction "/home/pantheon/...` or `Redirect`; a `Rocq Library` can write.

**Fix.** Run untrusted builds as a user without keys and without network
(or in a container), confine `Extraction`/`Redirect` output to the project,
and document the trust boundary. At minimum, use `BIDDER_USER` for every
model that runs `soma build`.

## Known limits

| Item | Where | Why it is a limit |
|---|---|---|
| Soma is not a sandbox | `GRADUAL.md:440-444` | Understates opam/dune/Mirage/Lean (S-5). |
| Lean theorems are axioms to Soma | `theories/Soma/Lean.v` | Trusted as Lean's kernel; `soma explore` lists them. |
| Native plugins require an explicit trust boundary | `vernac/somaImport.ml`, `plugins/soma_rocq/soma_rocq.ml` | Rocq-library compilation refuses parsed `Declare ML Module` commands, including whitespace/comment variants. General Soma source may load already installed plugins; installed native code is trusted and a build is not a sandbox. |
| Foreign bindings can read named files; building is not filesystem isolation | `plugins/soma_ocaml/soma_ocaml.ml`, `topbin/soma.ml` (`project_cache_sources`, `copy_tree`) | Use an isolated build user for untrusted sources. The cache copier uses `lstat` and does not recurse through symlinked directories. Source discovery detects ancestor inode cycles and records unusable links without recursing indefinitely; this does not make foreign bindings a sandbox. |

## Smaller items

- The historical `soma diff` folder-path quoting issue is fixed:
  `SomaDiff.toml_string` emits escaped TOML basic strings. Its source walk
  also detects directory cycles, and incomplete comparisons fail explicitly.
  `SomaToml` bounds nested values and dotted paths at 128 levels, reporting
  a TOML error rather than exhausting the native parser stack.
- `somaOcaml.ocaml_type` uses `List.hd` on `list`/`option`/`prod` arguments
  without checking arity (`plugins/soma_ocaml/soma_ocaml.ml:159-165`); a
  `.definition` such as `x : list.` can raise `Failure` and fail the build.
- `soma_wasm` runs the reference interpreter (`Wasm.Eval.invoke`, with its
  `Exhaustion` budget; `plugins/soma_wasm/soma_wasm.ml:401-422`); a hostile
  `.wasm` can still be expensive enough to use a CI slot. Check the fuel and
  add a wall-clock bound for untrusted modules.
- `soma`'s `soma build --check-fresh` reads paths out of a record with
  `Scanf.unescaped` (`topbin/soma.ml:1106-1112`); a forged record can make it
  read outside the cache (same trust issue as S-1).
- `[opam]` versions are installed into the shared switch
  (`toplevel/somaOcaml.ml:168-203`); a project can downgrade a package the
  node's later builds use, and package build scripts/ppx run at build time.
  Pin a switch per project or make version changes explicit.
- Soma reuses an OCaml build directory per source path without cleaning it
  (`toplevel/somaOcaml.ml:485-496`); a stale `_build` can affect a later
  build. `soma get` writes `soma.toml`/`soma.lock` non-atomically
  (`somaDeps.ml:204-210,499-502`).
