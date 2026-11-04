# Example projects

Programs made of several files, each in a folder of its own. The
single-file examples are in `../example_files/`.

| Project | What it is |
| --- | --- |
| `async_tasks` | calls Jane Street's Async; the project has no OCaml code of its own |
| `bonsai_counter` | a JSX counter run by Bonsai in the browser |
| `cached_compilation` | `Import` compiles the project's files into `.soma-cache` |
| `counter_server` | the `sexp_html` counter served over HTTP by a unikernel |
| `folder_rules` | a folder's `X.lang` and `X.proof` apply to every file under it |
| `rocq_stdpp` | a shop's stock in std++, a Rocq library compiled by Soma |
| `scores` | depends on `../tally` and uses its function and its theorem |
| `sexp_html` | HTML as s-expressions, a language for a folder, with proofs about the counter's state |
| `tally` | a library (`count_if`) with no `main`; `scores` depends on it |
| `unchecked_counter` | `counter_server` without the parser: the request start is an `Any` |
| `upgrade_check` | `soma diff` of a dependency that claims not to have changed |
| `wasm_add` | functions compiled from Rust to WebAssembly, including a call from a unikernel |

# TODO

- A project whose proofs are checked by Lean. The plugin remains, and
  `test-suite/misc/soma_lean.sh` checks it when Lean is installed (the
  script skips otherwise). The example project `lean_facts` was removed
  in `36007e62a6`: bridging Lean and Rocq was left as a larger question
  than one example.
