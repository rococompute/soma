# Highlights

The dependency work holds together. `soma.toml` parsing, minimal version
selection with a direct pin, `soma.lock`, fetch without hooks, import by
the dependency's `[project] name`, separate libraries for two projects'
`util.soma`, proofs, folder rules, checkouts, a Rocq library brought
along, and the refusal of commands that write a file are what
`test-suite/misc/soma_deps.sh` and `examples/example_projects/scores`
exercise. Two holes are open. The suite stays green because it never
hits them.

## A transitive library can be imported once it is loaded

`locate` in `vernac/somaImport.ml` is the only place that rejects a
dependency of a dependency (`is_direct`). It runs from `prepare`, and
`prepare` runs only for an `Import` whose name is not already a module
(`vernac/synterp.ml`, `VernacImport`).

Compiling a direct dependency loads what that dependency imports.
`add_cache_to_loadpath` then puts every selected dependency whose cache
exists on the load path, which is what lets the direct dependency's own
imports resolve. After `Import a.a`, `Nametab.locate_module` finds
`c.c`. `names_another_library` is false for it, because the top project
has no `c/c.soma`. `in_scope` is true, `prepare` is skipped, and
`Import c.c` is an ordinary Rocq import.

`Require` and `From c Require` never call `prepare`. They go straight
to `synterp_require`.

The test that covers this (`test-suite/misc/soma_deps.sh`) is only

```
echo 'Import c.c.' > main.soma
refused 'c is github.com/owner/c, a dependency of a dependency'
```

Nothing has loaded `c` yet, so `locate` runs and the refusal fires.
The sequence that happens in a program is the other one: import the
direct dependency, then name what it brought in.

The same refusal belongs on every way a Soma file names a library it
did not list:

- `Import c.c` when `c.c` is already loaded.
- `Require c.c` and `From c Require Import c`.

Inside the dependency's own compilation the check stays as it is: `c`
is direct for that project, and its files must import it.

## A transitive name is not checked against this project's files

`check` in `vernac/somaDeps.ml` walks the dependencies each project
lists and rejects a name that is also a file or folder there. The
project being built is checked only against the lines in its own
`soma.toml`.

A project named `util` that arrives through another dependency is
still compiled as the library `util.*` (`-Q` of its cache, prefix
`util`) and placed on the same load path as this project's `util/` or
`util.soma`. Those are one logical name. Direct dependencies already
error in that case. A transitive one should too, at the project being
built, with the same message: the dependency is named `util`, and this
project has `util/`.

## The lock's cold fetch is not what the test runs

The moved-tag test builds, force-moves `v1.0.0`, and builds again. The
source is still in the cache, so the second build does not fetch. The
promise of `soma.lock` is the other build: the cache directory for that
commit is gone, and the program is still the old one.

`fetch` asks git for the commit by id (`git fetch --depth 1 URL COMMIT`).
That succeeded here for a commit the tag no longer pointed at. If it
fails, the fallback is `git fetch --tags`, which follows the tag and
does not have the old commit. Checkout then asks for the locked id. A
test that deletes the source directory after the tag moves, and still
sees `= 1`, is what locks that in.
