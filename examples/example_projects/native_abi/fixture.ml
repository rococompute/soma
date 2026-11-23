(* Test fixture: real native storage, callbacks and labeled functions. *)
type item = { mutable value : string; label : string; root : unit -> unit }
let join ~left right = left ^ right
let same first second = first == second
let visit (_ : item) callback = callback ()
let say = print_endline
let pending (_ : item) callback = callback ()
let join_other ~left right = right ^ left
let inspect (_ : item) callback = callback ()
let left text = "left:" ^ text
let right text = "right:" ^ text
