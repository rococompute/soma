(lang dune 3.21)
(name rocq-prover)

; We use directory targets in documentation
(using directory-targets 0.1)

; We need this for when we use the dune.disabled files instead of our rule_gen
(using rocq 0.11)

(formatting
 (enabled_for ocaml))

(generate_opam_files true)

(license LGPL-2.1-only)
(maintainers "The Rocq development team <rocq+rocq-development@discoursemail.com>")
(authors "The Rocq development team, INRIA, CNRS, and contributors")
; This generates bug-reports and dev-repo
(source (github rocq-prover/rocq))
(homepage https://rocq-prover.org/)
(documentation "https://rocq-prover.org/docs/")
(version dev)
(maintenance_intent "(any)")

; Note that we use soma-runtime.opam.template to have dune add the correct opam
; prefix for configure
(package
 (name soma-runtime)
 (depends
  (ocaml (>= 4.14.0))
  (ocamlfind (and (>= 1.9.1) (or (>= 1.9.8) (<> :os-family "windows"))))
  (zarith (>= 1.11))
  (wasm (>= 2.0.2))
  (conf-linux-libc-dev (= :os "linux")))
 ; soma-runtime and soma-core install Rocq's binaries (rocq, rocqchk) and
 ; Corelib under the same names as Rocq does
 (conflicts rocq-runtime rocq-core coq-core coq)
 (depopts rocq-native (memprof-limits (>= 0.3.0)) memtrace)
 (synopsis "The Rocq Prover -- Core Binaries and Tools")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes the Rocq Prover core binaries, plugins, and tools, but
not the vernacular standard library.

Note that in this setup, Rocq needs to be started with the -boot and
-noinit options, as will otherwise fail to find the regular Rocq
prelude, now living in the soma-core package."))

(package
 (name soma-core)
 (depends
  (soma-runtime (= :version)))
 (synopsis "The Rocq Prover with its prelude")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes the Rocq prelude, that is loaded automatically
by Rocq in every .v file, as well as other modules bound to the
Corelib.* and Ltac2.* namespaces."))

(package
 (name soma-test-suite)
 (allow_empty)
 (depends
  (soma-core (= :version))
  ounit2
  conf-python-3
  conf-time)
 (synopsis "The Rocq Prover test suite")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package runs the test suite."))
