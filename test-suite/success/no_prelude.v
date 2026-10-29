(* -*- coq-prog-args: ("-no-prelude") -*- *)
(* -no-prelude loads neither Corelib.Init.Prelude nor Soma.Soma *)
Fail Check nat.
From Corelib Require Import Init.Prelude.
Check 0.
Fail Check unknown.
