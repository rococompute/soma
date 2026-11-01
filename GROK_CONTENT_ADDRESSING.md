# Content-addressed definitions

Unison's content addressing fits Soma at the definition layer, on the
kernel terms Soma already checks. It does not require the unikernel to
become an interpreter, and Unison being run as bytecode is not what
makes the hashing work.

What Unison hashes is a typechecked tree, with names removed and each
dependency replaced by its hash (https://www.unison-lang.org/docs/the-big-idea/).
The hash is a SHA3-512 of that tree. A name is a pointer to a hash,
stored beside it. A scratch file is how a person edits; `ucm` hashes
the result into the codebase. The same tree is what the runtime later
runs, as bytecode, so a hash can be sent to another machine and run
there. The interpreter is that last step. The hash exists before it.

Soma already has the tree. A checked definition is a kernel term,
`Constr.t`: binders are de Bruijn indices (`Rel`), there are no source
locations in the term, and elaboration (implicits, gradual casts) has
already happened. That is the tree worth hashing. The file text stays
the scratch file, as it is today.

## What is hashed today

A stamp (`vernac/somaImport.ml`, `soma-stamp 2`) records the MD5 of the
source bytes, the `.proof`, the `.lang`, and the `.wasm`, `.ml` or
`.lean` beside them, then the digest of each imported `.vo` and of each
library. The cache is valid while those bytes hold.

Those hashes name files, not definitions. A line move changes the
source hash, and the `.vo` keeps locations, so what imports the file is
recompiled too (`GRADUAL.md`). Two definitions with the same elaborated
body in two files have two identities. A proof edited under an opaque
lemma changes the `.vo` digest of the whole file, so every importer
rebuilds, though the kernel did not let them see the proof.

Unison's hash is the other cut: the identity of one definition is the
identity of its elaborated body, and of the identities of the
definitions it mentions.

## The hash

After a file has checked, for each definition, bottom up:

1. Take its kernel type and its kernel body.
2. Replace each constant it mentions by that constant's hash.
3. Hash the result, together with whether the body is transparent.

A mutual block (a `Fixpoint` group, an inductive family) is one
component. Hash the members as a set, ordered by the hashes they would
have with the block tied off, and address a member as that hash plus
its index. That is Unison's cycle, `#hash.n`, and it is how a recursive
definition gets a hash that includes itself.

Binder names do not enter. Locations do not enter. The file path does
not enter. Universe names are canonicalized by the order they appear in
the term, then dropped; the constraints travel with the hash. The Soma
corelib digest already used for `.soma-cache/rocq` is a prefix of the
domain, so a hash from one Soma is not a hash in another. Unison gets
the same effect by versioning the serialization. The `.vo` magic
(`tools/configure/configure.ml`) is part of that prefix: it is the
format of the term.

An opaque proof contributes its type to the hash other definitions see,
and its body to a second hash, the witness. Importers depend on the
first. Replacing a proof with a different proof of the same statement
changes the witness and leaves the importers' hashes alone. That is the
"hash the result of a proof contract" in `vision.md`: the contract is
the statement hash, the proof is one witness hash. Checking a witness
is the kernel checking that body against that type. The unikernel is
not on that path.

`Any`, `unk`, `raise` and `cast` are kernel terms, so a gradual
elaboration is inside the hash. A different elaboration is a different
definition.

Builtins and foreign code are leaves, the way `##Nat` is a builtin hash
in Unison:

- A Soma or Rocq primitive is its kernel name plus the corelib prefix.
- A WASM export is the declared type plus the digest of the `.wasm`
  bytes. The stamp already hashes those bytes as part of the source.
- An OCaml value is the declared type plus the findlib package and
  version.
- A Lean theorem is the statement hash plus the fact that Lean checked
  it. To the kernel it is an axiom (`GRADUAL.md`); the hash says so.

A definition that mentions a leaf mentions that leaf's hash, so a
change of wasm bytes or of the trusted Lean statement changes every
hash above it.

## Names stay a map

`Import maps.gmap` remains a name. The project's files, and the
`[project] name` of a dependency (`GROK_DEPENDENCY_MANAGEMENT.md`), are
the namespace: a map from qualids to hashes, which is what a Unison
branch is. The kernel keeps `KerName` internally. The hash is the
identity outside one build: the cache key, the lock, the thing a
dependency is pinned to.

Collapsing two equal hashes into one `KerName` during typechecking
would be a kernel change, and it is not needed for the cache, the lock,
or for checking a witness. Two files that elaborate the same way have
the same hash and distinct kernel names. That is enough.

The git commit in `soma.lock` answers which snapshot was fetched. The
definition hashes answer which code that snapshot contains. A comment
or a line move changes the commit's tree and leaves the hashes. The
`digest` field left open on `[[resolved]]` is these hashes, one per
exported definition, not a second hash of the git tree.

The stamp grows a line per definition, `def NAME HASH WITNESS`, and the
import line records the dependency's definition hashes rather than the
`.vo` file digest. A cached `.vo` is reused when those hashes hold.
The source-byte hash can stay as a fast check that the scratch file
has not moved; the definition hash decides whether importers rebuild.

## Running a hash

Pure code already runs as the kernel term. `Compute`, `soma explore`
and `soma run` of a program that is not a Sandbox program reduce
`Constr.t` with the Rocq VM. A store of serialized terms keyed by hash
is enough to evaluate a hash: load the term, run the VM. That store is
the codebase. No image is built.

`io` is data. `Inductive io` in `theories/Soma/Sandbox.v` describes
printing, sleeping, serving; building a value of that type does
nothing. The program's `main : io unit` is extracted to OCaml and
linked into a MirageOS image (`toplevel/somaMirage.ml`), and the
generated runtime turns those constructors into console, clock and TCP
calls. The pure parts of the program are compiled OCaml inside the
image. The image also contains the OCaml runtime, Mirage and solo5,
from the switch in `~/.cache/soma/mirage`. Its bytes are a function of
that toolchain as much as of `main`.

So there are two different things a person can mean by running a hash:

- Run the pure term, or check a proof. The kernel and the VM do this.
  The unikernel is not involved.
- Boot an `io` program. Unison does the analogous thing by shipping
  bytecode to a shared runtime. Soma's shared runtime would be the
  `plain` or `net` image, built once per Soma version (those projects
  are already kept between builds), loading a program blob whose hash
  is the hash of `main`. The blob is the extracted program, or the
  serialized `io` term. WASM is already split this way: the image holds
  an interpreter and the module bytes. Doing the same for `main` is a
  change to how `somaMirage.ml` links the program into the image. It is
  how "send this hash and run it" gets across the `io` boundary. It is
  optional for content-addressed source, and it is not a change to the
  kernel.

Until that split exists, an image is a deploy artifact of a pair
`(hash of main, hash of the runtime)`. The runtime hash is the corelib
digest plus the digest of the Mirage project Soma generates. Rebuilding
the image when either changes is the cache Soma has today. Reproducible
image bytes are a property of dune, Mirage and solo5, and they are not
required for the definition hashes to be stable.

## What this is for

- A dependency pin that means the code, not the bytes of a file.
- A proof witness that can be fetched and checked by its hash, which is
  the kernel rechecking it. That is the "validate external code" line
  in `vision.md`, done by checking rather than by running.
- A cache that survives formatting and line moves, and that survives a
  new proof of an unchanged statement.
- A program blob a fixed image can load later, if the link step is split.

The scratch files, `soma.toml`, `Import`, folder rules and the kernel's
names stay. The hash is computed at the end of a successful check
(`write_stamp` in `vernac/somaImport.ml`) and stored beside the `.vo`.
