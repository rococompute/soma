(* Primitive integers of the extracted code (gradual_prog.v), as OCaml
   integers: enough for literals. *)
type t = int
let of_int (x : int) : t = x
