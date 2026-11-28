# Source-owned verification policies

A Soma program can declare the proofs that must exist before it is published:

```soma
Definition identity (n : nat) := n.
Definition main := identity.
Verification Properties "identity_trace"
  Invariants "identity_preserves_input" Trust "".
```

Its companion `.exp` supplies checked proofs, including forward references from
the policy:

```soma
Theorem identity_trace : forall n, identity n = n.
Proof. reflexivity. Qed.
Theorem identity_preserves_input : forall n, identity n = n.
Proof. reflexivity. Qed.
```

Each quoted field is a semicolon-separated list of kernel names, never code.
Property and invariant names are relative to the source library; trusted laws
use fully qualified names. Duplicate names and overlapping classifications are
rejected. One declaration is allowed per library, in the source rather than
its expectation file. Requirements are metadata and do not alter extraction.

`soma build` and `soma extract` enforce declared policies after joining proof
workers and before saving or publishing the checked library or native products.
`soma verify FILE` additionally requires the root file to declare a policy.
Project extraction nodes with `verify = true` require policies throughout the
project's Soma dependency closure, including reused imports. An unclassified
older cached library must be rebuilt before it can enter that verified graph.

Every required entry must be a definition with an accessible checked proof and
a proposition type. Invariants must quantify over inputs; transparent aliases
of quantified proposition types are accepted. The compiler collects the union
of assumptions for **all** checked project definitions and inductives, including
unused helpers and imported project libraries, not just the required proofs.
Only explicitly trusted kernel objects are allowed. Gradual evidence is rejected
even if its primitives were mistakenly listed as trusted. The audit uses
elaborated kernel terms and checking flags, not lexical source scans.

The classification is a reviewed claim by the author. Quantification alone
does not establish that an invariant is substantive, complete, or relevant to a
security specification; a quantified trace remains a trace. Neither the gate
nor an empty policy certifies a program's correctness. Projects must review
their specifications, chosen requirements and trusted laws.

Successful full checking writes `FILE.vo.verification.toml` beside the checked
library; native extraction also exports `verification.toml` in its destination.
The receipt records SHA-256 hashes of source and companion inputs (including
absent companions), separate property/invariant inventories, kernel contract and
proof-witness hashes, each proof's assumptions, and the complete used/allowed
assumption sets. An unsuccessful check cannot publish new native products.
`project-imports` records the checked input fingerprint of each transitive
project import, including `.definition` files. These use the import cache's
identity over source, proof/extension companions, foreign-file inputs and
implicit folder-rule selection. Stale or uncertified project import stamps are
rejected. Consequently even an imported-source edit that leaves runtime bytes
unchanged invalidates existing project publication evidence. Dependencies in
other selected Soma projects are included; external installed libraries and the
full runtime TCB still require their own inventory.
Successful extraction without a policy removes any stale exported verification
receipt. Receipts record an audit; they are not proofs of the compiler,
extraction, external implementations or the rest of the runtime's TCB.
