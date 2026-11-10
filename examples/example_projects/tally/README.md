# tally

A library: `count_if` counts the items of a list that pass a test, and its
proof says a count is never more than there are items. It has no `main`.
`../scores` depends on it.

```
soma.toml      the project: its name, version and description
counts.soma    count_if
counts.proof   count_if test items <= length items
```

Another project imports it by the `name` in this `soma.toml`:
`Import tally.counts.`

## Publishing it

A repository is published by its tags, as a Go module is. With this folder
as the root of a repository `owner/tally`:

```sh
git tag v1.0.0
git push origin v1.0.0
```

and in another project:

```sh
soma get owner/tally@1.0.0
```

The tag is the `version` of this `soma.toml`. Version 2 and above is another
path, `owner/tally/v2`, on tags `v2.x.y`.
