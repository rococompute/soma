# Dependencies in `soma.toml`

A Soma project depends on another Soma project by a path and a version in
`soma.toml`. The path is where it is fetched from. The version is a semantic
version, the same one `[project]` already uses. In a Soma file, `Import`
names the dependency by the `name` in that project's own `soma.toml`.

```toml
[project]
name = "shop"
version = "0.1.0"
description = "A shop's stock"

[dependencies]
"owner/repo" = "1.2.3"
"gitlab.com/iris/maps" = "1.13.0"
```

`Import maps.gmap.` is `gmap.soma` of the project fetched from
`gitlab.com/iris/maps`, whose `[project] name` is `maps`.

This is the Go module idea fitted to the manifest Soma already has. Go
writes `require github.com/owner/repo v1.2.3` and imports that path. Soma
writes the path in `[dependencies]` and imports a Rocq qualid, because
`Import` is a qualid (`vernac/somaImport.ml`) and a qualid has no `/` and
no `.` inside a component.

## The line as proposed does not parse

```toml
[dependencies]
owner/repo = "1.2.3"
```

`vernac/somaToml.ml` reads a bare key as letters, digits, `_` and `-`
(`is_bare`). `/` ends the key. The parser reports:

```
soma.toml:5: expected = after the key owner, found '/'
```

A quoted key is already a key (`"a b"`, and a header `[dependencies."a/b"]`).
The path is quoted:

```toml
"owner/repo" = "1.2.3"
```

`owner.repo = "1.2.3"` is a different value: a dotted key, the table
`owner` with the key `repo`. That is rejected below, with the quoted line
in the message.

## What the two sides are

`[project]` stays the project's own identity (`vernac/somaProject.ml`):
`name`, `version`, `description`. `name` is what other projects import it
by: lowercase letters, digits and `_`, beginning with a letter, 64 at most.
`version` is `MAJOR.MINOR.PATCH`, then `-PRERELEASE` and `+BUILD`
(`parse_version`, https://semver.org).

`[dependencies]` is what this project is built with. Each key is a fetch
path. Each value is the version fetched for that path. A project with no
dependencies has no `[dependencies]` table. An empty `[dependencies]` is
the same as none.

The fetch path and the import name are different strings, on purpose.

- The path is an address: `owner/repo`, `gitlab.com/group/repo`. It can
  contain `-`, `.` and capitals, which a Rocq name cannot.
- The import name is the dependency's own `[project] name`, checked with
  the same `valid_name` as this project's name, when the repo is fetched.
  A bad name is that file's existing error, prefixed with the path:
  `github.com/owner/repo soma.toml:2: "My-shop" is no project name: ...`.

Go can use one string for both because an import there is a string. Here
the address goes in the manifest and the Rocq name stays the name the
dependency already declares for Rocq, OCaml and opam.

## Paths

A key is one quoted string of segments separated by `/`.

- `owner/repo` (two segments, the first with no `.`) is
  `https://github.com/owner/repo.git`.
- A first segment with a `.` is the host:
  `gitlab.com/iris/maps` is `https://gitlab.com/iris/maps.git`.
- Major 2 and above is a suffix segment, as in Go: `owner/repo/v2`,
  `gitlab.com/iris/maps/v2`. The number is the version's major. Major 0
  and 1 have no suffix. `v0` and `v1` are rejected. A suffix that is not
  `v` and a major number is a further path segment of the repo, and the
  repo must contain the Soma project at its root (`soma.toml` at the root
  of the tag). Subdirectories of a repo are a later key.

Rejected, with the line to write:

```
soma.toml:5: "https://github.com/owner/repo" is a URL. A dependency is a path: "owner/repo" = "1.2.3"
soma.toml:5: "owner/repo/" is no path. A path is segments separated by /: "owner/repo" = "1.2.3"
soma.toml:5: "owner//repo" is no path. A path is segments separated by /: "owner/repo" = "1.2.3"
soma.toml:5: "../repo" is no path. A path is segments separated by /: "owner/repo" = "1.2.3"
soma.toml:5: owner is no path. A dependency path is in quotes: "owner/repo" = "1.2.3"
```

A segment is the characters GitHub allows in a repository name: letters,
digits, `.`, `_` and `-`, not empty, not `.` or `..`. Anything else is
`soma.toml:LINE: "bad seg" is no path segment.`

## Versions

The value is a string that `parse_version` already accepts. The errors are
the ones `[project]` gives (`"1.0" is no semantic version...`), and the
repair is the dependency line.

Build metadata (`1.2.3+build.5`) is rejected on a dependency. It is not
part of semver precedence and it is not a git tag:

```
soma.toml:5: "1.2.3+build.5" has build metadata. A dependency version is a tag: "owner/repo" = "1.2.3"
```

A pre-release is allowed: `"1.2.3-rc.1"` is the tag `v1.2.3-rc.1`.

The version's major agrees with the path:

```
soma.toml:5: "owner/repo/v2" is major 2, and "1.4.0" is major 1. The version's major is the /vN of the path.
soma.toml:5: "owner/repo" is major 0 or 1, and "2.0.0" is major 2. Major 2 and above is "owner/repo/v2" = "2.0.0".
```

So a build never treats `2.0.0` as a later `1.9.0`. They are different
paths, as `github.com/owner/repo/v2` is a different Go module.

Tags are looked up in order: `v` followed by the version string, then the
version string alone. Both point at the same commit, or only one exists.
Pointing at two commits is an error that prints both. A missing tag is:

```
owner/repo 1.2.3: no tag v1.2.3 or 1.2.3 on https://github.com/owner/repo.git
```

## Fetch and the two caches

Resolution runs once, when the project is loaded, before any file is
compiled. `Import` does not fetch on its own. The graph is known before
the first `.vo` is built, so a later dependency cannot ask for a version
this build has already compiled.

For each path, Soma asks git for the tag (`git ls-remote URL refs/tags/v1.2.3`)
and clones that commit into the shared source cache:

```
~/.cache/soma/src/github.com/owner/repo@1.2.3-<commit>/
```

(`$XDG_CACHE_HOME/soma` when that is set, the same root as
`vernac/somaOpam.ml`). The directory is the repo at that commit, and it
is not written to again. A second project using the same commit uses the
same directory.

The compiled files go in the consuming project's cache, next to the Rocq
libraries it already compiles for itself (`.soma-cache/rocq`,
`plugins/soma_rocq`):

```
.soma-cache/deps/github.com/owner/repo/<commit>/<soma key>/
```

The Soma key is the one `soma_rocq` already computes from Soma's Corelib:
a new Soma compiles the dependency again. The source cache is shared; the
`.vo` files are not, for that reason.

Today the project root is both where `Import` finds files and the parent
of `.soma-cache` (`vernac/somaImport.ml`, `cache`). A dependency splits
those: files and folder rules come from the source-cache checkout, and
the cache is the consumer's `.soma-cache/deps/...`. The checkout stays
immutable. `SOMA_PROJECT_ROOT` for a dependency compilation is the
checkout; the cache path is set beside it.

Nothing in the repo runs except Soma compiling the files that are
imported, the way a Rocq library's Makefiles do not run. A dependency is
Soma, so it is compiled with the prelude, its folder rules and its
proofs. A Rocq library named inside it is still compiled without the
prelude, by the `Rocq Library` sentence that names it.

git missing, or the clone failing, is reported like a failed `opam
source`: the command, and the end of its output.

A dependency that has no `soma.toml` at its root:

```
owner/repo 1.2.3 (<commit>): the repository has no soma.toml
```

## Selection

A version written in this project's `[dependencies]` is the version the
build uses. It is not raised quietly.

A fetched project's own `[dependencies]` are requirements of the same
kind. For one path, the candidates are those requirements. The selected
version is the greatest of them (semver precedence: major, minor, patch,
then pre-release; a release is greater than its pre-release). This is
Go's minimal version selection, with one Soma rule added: if this
project names the path, the version it names is the one used, and it
must be greater than or equal to every version a dependency asks for.
Otherwise the manifest is wrong, and the message says the line to write:

```
soma.toml:5: "owner/repo" is "1.2.0" here, and "1.4.0" in gitlab.com/iris/maps. "owner/repo" = "1.4.0"
```

A path that only dependencies ask for is selected at the greatest
version they name and recorded in the lock, not copied back into this
`soma.toml`.

A cycle in paths:

```
Dependency cycle: owner/a -> owner/b -> owner/a.
```

the same shape as `Import cycle: a -> b -> a.`

Two selected projects whose `[project] name` is the same word:

```
soma.toml:6: "gitlab.com/other/shop" is named shop, and so is "owner/shop". A dependency is imported by that name.
```

The repair, when it is needed, is the table form below. Until that form
is read, the build stops.

## The lock

`soma.lock` sits next to `soma.toml`. It is TOML, read by the same
parser, and it is generated. A build with a lock that matches the
manifest (the same direct paths and versions) uses the locked commits
and does not use the network. A missing lock, or a manifest that has
moved past it, resolves the tags, then writes the lock. Tags move;
commits do not. The lock is what a later build compiles.

```toml
# written by soma
[[resolved]]
path = "github.com/owner/repo"
version = "1.2.3"
commit = "95f89058abcdef0123456789abcdef0123456789"
```

`[[resolved]]` is an array of tables, which `somaToml.ml` already reads.
The commit is the full id from `git ls-remote`. The source-cache
directory is named with it. A lock entry whose checkout is absent is
cloned at that commit. A checkout whose commit is not the locked one is
deleted and cloned again.

The lock is part of the project, as `go.sum` is: it is committed. It is
not a table of `soma.toml`. Putting the commits in the manifest would
make a generated file fail the "every key is known" check on every
edit, and would mix the version a person asked for with the commit a
tool resolved.

A hand edit that adds a key `soma.lock` does not know is an error at
that key's line. The known keys of `[[resolved]]` are `path`, `version`,
`commit`.

## Import

`Import` keeps its order (`vernac/somaImport.ml`):

1. A module already in scope.
2. A file of this project: `Import X.Y` is `ROOT/X/Y.soma` (or `.lang`,
   `.definition`, `.wasm`) when that file exists.
3. A dependency, when the first component is a selected project's
   `name` and this project has no file or folder of that name.
   `Import maps.gmap` is `gmap.soma` at the root of the `maps` checkout.
   `Import maps.a.b` is `a/b.soma` there. The file is compiled as a
   project of its own: its root, its folder rules, its `.proof`, its
   `.lang`, its dependencies. The result is loaded and opened, as a
   project file is today.
4. A library already in the load path (`Import Sandbox`).

`Import maps` on its own is the file `maps.soma` in that checkout when
it has one. With no such file:

```
maps is gitlab.com/iris/maps, which has no maps.soma. Import maps.gmap.
```

and the message names the `.soma` files at that root.

A folder of this project with the dependency's name:

```
soma.toml:5: the dependency gitlab.com/iris/maps is named maps, and this project has maps/. Import maps.gmap is that folder.
```

Inside the dependency, `Import` is resolved at its root. Its own files
win over its dependencies, by the same rule. Folder rules of the
dependency apply to its files and not to the importer's.

The stamp of an importer that imported a dependency file records it as
an import whose digest is that compiled file's digest, as a project
import is recorded today (`soma-stamp`). A change in the dependency
recompiles what imported it only when the `.vo` changed.

One command loads each dependency file once. Two builds of one project
at once are already unhandled for a project's own files; the same limit
covers dependencies.

## A checkout on disk

A value that is an inline table is a checkout, for a project being
edited, the way `Rocq Library "mylib" in "vendor/mylib".` is a directory
and the way Go's `replace` is a local module:

```toml
[dependencies]
"owner/wip" = { path = "../wip" }
```

`path` is the only key. It is relative to the `soma.toml` it is written
in, and the directory has a `soma.toml`. There is no version key: the
checkout's own `[project] version` is the version. No tag is fetched.
The lock records `path` and omits `commit`. A change in the checkout is
picked up by the stamps, as a change in this project's files is.

```
soma.toml:6: "owner/wip" has path and version. A checkout is "owner/wip" = { path = "../wip" }.
soma.toml:6: "owner/wip" has no path. A checkout is "owner/wip" = { path = "../wip" }.
soma.toml:6: "../wip" has no soma.toml.
```

Any other key in the table is an unknown key, rejected the way an
unknown key of `[project]` is. That is the room for a local import name
later (`name = "other_shop"` when two dependencies are both `shop`),
and it stays unknown until the code reads it.

A string value and a `path` table are the two values `[dependencies]`
accepts. Anything else:

```
soma.toml:5: "owner/repo" is a table. A dependency is a version, "owner/repo" = "1.2.3", or a checkout, "owner/repo" = { path = "../wip" }.
soma.toml:5: "owner/repo" is an integer. A dependency is a version: "owner/repo" = "1.2.3"
```

## What `soma.toml` checks

`load` in `vernac/somaProject.ml` currently says soma.toml has one
table, `[project]`. It grows by one table. A table other than `project`
and `dependencies` keeps today's error, and the sentence of what the
file has lists both:

```
soma.toml:4: ocaml is not something soma.toml says (yet). soma.toml has [project] (name, version, description) and [dependencies] ("owner/repo" = "1.2.3").
```

`[dependencies]` is optional. Its keys are checked with the path and
version rules above. The type `SomaProject.t` gains the direct
requirements: path, version or local path, and the line, so a later
error can point at it. Resolving the graph is separate from parsing the
file, as parsing does not use the network. `soma build`, `run`,
`explore`, `compile` and `extract` resolve, the same commands that
check the manifest today. A command that only needs the name and the
version can still parse without resolving; a command that compiles
resolves first.

`test-suite/misc/soma_project.sh` keeps its unknown-table case. New
cases are the quoted path, the `/` parse error, a bad version, a major
that disagrees with `/vN`, a `path` checkout, and an unknown key inside
the checkout table.

## Rocq libraries and OCaml libraries

They stay where they are.

- `Rocq Library "rocq-stdpp" "1.13.0".` fetches an opam package from
  `coq-released` and compiles it as Rocq (`plugins/soma_rocq`).
- `OCaml Library "async".` is a findlib library installed into Soma's
  opam switch (`toplevel/somaOcaml.ml`).

Those are not git paths and they are not imported by a `[project]`
name. A `[dependencies]` key is a Soma project. A Soma project that
itself contains a `Rocq Library` sentence compiles that library when it
is compiled, so a dependency can bring stdpp along without the importer
repeating the sentence.

The open gap in `examples/example_projects/rocq_stdpp` (a Rocq
library's opam dependencies are each named by their own `Rocq Library`)
is unchanged. It is an opam graph. It is a different mechanism from
this table.

`soma extract` names the opam package from `[project]`. It does not
turn `[dependencies]` into opam `depends`. A git dependency is not an
opam package. The opam file continues to carry the OCaml libraries the
program's `OCaml Library` sentences name.

## Commands

`soma get owner/repo@1.2.3` writes or replaces that one line in
`[dependencies]` and resolves, which rewrites `soma.lock`. Without
`@`, it uses the greatest tag that is a semantic version of the path's
major (no suffix: majors 0 and 1, greatest of those; `/v2`: the
greatest `2.*.*`). `soma get` with no argument resolves what is already
written and refreshes the lock. This is the whole writer. The file
stays hand-editable; `soma get` is how a version is looked up.

## Left for later

These fit the same table and are not part of the first reading of it.
Each is an unknown key until then, so a file that uses it fails with
the line to write today.

- A local import name, when two dependencies share a `[project] name`.
- A dependency in a subdirectory of a repository.
- Private repositories and hosts other than `https` git.
- Content hashes beyond the git commit (the commit id is the pin for a
  fetch straight from the host). A hash of the tree, in the Unison
  direction `vision.md` mentions, can sit in `[[resolved]]` as another
  known key when it exists.
- IPFS, or any fetch that is not git.
- opam solving for Rocq and OCaml dependencies.

## Where the work goes

| Piece | File |
|---|---|
| Quoted paths already parse | `vernac/somaToml.ml` |
| `[dependencies]`, path and version checks, the new error text | `vernac/somaProject.ml` |
| Source root and cache root as two paths; `Import` step 3 | `vernac/somaImport.ml` |
| Shared source cache under the existing Soma cache | `vernac/somaOpam.ml` (`cache_root`) |
| Resolve, lock, `soma get` | a new `vernac/somaDeps.ml`, called where the manifest is loaded for a build |
| The manifest tests | `test-suite/misc/soma_project.sh` |
| One example project depending on another | `examples/example_projects/` |
