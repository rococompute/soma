# cached_compilation

A program of several files, where `Import` compiles what it imports.

```
main.soma          Import tasks. Import text.   the program
tasks.soma         Import models.task.          adding, finishing, counting tasks
tasks.proof                                     what is proved about tasks.soma
text.soma          Import models.task.          tasks as text
models/task.soma                                the task record
```

`soma run main.soma` prints `1` (the tasks that remain), and `soma build
-v main.soma` the values of its bare terms too.

## What Import does

In a Soma file, `Import tasks` is the file `tasks.soma` of the project
(the folder of the program being built), and `Import models.task` is
`models/task.soma`. Before it is loaded, it is compiled into the
project's `.soma-cache`, unless the cache already has it up to date:

```
$ soma build main.soma
Compiling tasks.soma (into .soma-cache)
Compiling models/task.soma (into .soma-cache)
Compiling text.soma (into .soma-cache)
$ soma build main.soma          # nothing changed: nothing is compiled
```

Each file is compiled once per build, here `models/task.soma` once for
both `tasks.soma` and `text.soma`. Compiling `tasks.soma` checks
`tasks.proof`, so its theorems are checked when it changes, not on every
build.

A compiled file stays in use while its stamp in `.soma-cache` holds. A
stamp has the hash of the source, with its `.proof` and `.lang`, and what
the file imported, as compiled. Try:

- Edit `text.soma`: only it is compiled again.
- Add a comment at the end of `models/task.soma`: it is compiled again,
  to what it was, so `tasks.soma` and `text.soma` are not. (A compiled file
  keeps the locations of what it defines, so a comment that moves its
  lines changes it.)
- Add a definition to `models/task.soma`: it is compiled again, and so are
  `tasks.soma` and `text.soma`, which import it.
- Make a theorem of `tasks.proof` false: compiling `tasks.soma` fails,
  and so does the build, with the proof's error and then
  `Cannot import tasks: tasks.soma does not compile`.

`Import` of a name that is not a file of the project is a library, as
before (`Import Sandbox`). `.soma-cache` can be deleted at any time.
