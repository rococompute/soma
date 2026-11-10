# scores

A program that depends on another project, `../tally`, and uses its function
and its theorem.

```
soma build -v main.soma     3 of the 5 scores pass; main.proof checked
soma explore main.soma      reviews this project and tally
```

```
soma.toml     the project, and what it depends on
soma.lock     the version of each dependency, written by soma
main.soma     counts the scores that pass, with tally's count_if
main.proof    passing scores <= length scores, by tally's theorem
```

## A dependency

```toml
[dependencies]
"example/tally" = { path = "../tally" }
```

The key is where the project is fetched from, and `path` says it is a folder
on disk for now, so that this example needs nothing but `soma`. A published
one is a version instead, of a tag on GitHub or another host:

```toml
[dependencies]
"owner/tally" = "1.0.0"
"gitlab.com/group/tally/v2" = "2.1.0"
```

`soma get owner/tally@1.0.0` writes that line, and `soma get owner/tally`
looks up the greatest tag.

In a file, a dependency is its own `[project] name`, not its path:

```rocq
Import tally.counts.
```

is `counts.soma` of `tally`. It is compiled with its own proofs, into this
project's `.soma-cache`, and its source is not touched.

See "Dependencies" in `GRADUAL.md`.
