(* Test-only native client: alias the compiler's record, without depending on
   Prog or Soma_bindings. All fields and their representation remain owned. *)
type pipe = Soma_owned_45de90f229ea74f128628256fd6705519ea9f7a67189bb91fc0f1815df1cf5b8.t
let same (value : pipe) = value
