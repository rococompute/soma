# folder_rules

A folder's rules: definitions, macros and theorems that apply to every
file under the folder, without importing them.

```
soma.toml                                                 the project: its name, version and description
main.soma                    Import lists.scores.total.   the program
lists/
  lists.ext                 the rules of lists/: zip_with, and the pipe macro
  lists.exp                what is proved about zip_with
  scores/
    total.soma               uses zip_with and pipe, imports nothing
    total.exp              proves totals_length with lists.exp's zip_with_length
```

`soma run main.soma` prints `[12, 26]`, the doubled totals that reach 5,
and `soma build -v main.soma` prints `[4, 6, 13]` too.

## The rules of a folder

`X/X.ext` is the rules of the folder `X/`. Every Soma file under `X/`,
in subfolders too, starts as if it had `Import X.X`: what `X.ext`
defines, its macros included, is in scope there. `X/X.exp` has the
proofs about the rules. They are checked once, when the rules are
compiled, and its theorems can be used in the proofs of every file under
`X/`.

The rules are compiled once into the project's `.soma-cache`, like any
imported file. So `zip_with` is one definition, the same in every file
under `lists/`, and `lists.exp`'s theorems are about it wherever they
are used. A change to the rules compiles them again, then the files they
apply to.

Rules nest: `lists/scores/scores.ext` would apply under `lists/scores/`,
after those of `lists/`, and would see what they define.

## What they do not reach

- **Files outside the folder.** `main.soma` is not under `lists/`:
  `zip_with` is not in scope there (its `Fail` line checks this), even
  though it imports `total.soma`. What a file is given by its folder, it
  does not pass on, as with `Import`.
- **A folder with its own program.** If `X/X.soma` exists, `X/X.ext` and
  `X/X.exp` are that program's, as for any `FILE.soma`, not the
  folder's.
- **A file built by itself.** The project is the folder of the program
  being built, so `soma build lists/scores/total.soma` makes
  `lists/scores/` the project, and the rules of `lists/` do not apply.
  Soma warns about this. Build `main.soma`, or set the project's folder:
  `SOMA_PROJECT_ROOT=. soma build lists/scores/total.soma`.
