(* Independent native fixture; owned record types are generated elsewhere. *)
type node = { mutable label : string }
let node label = {label}
let bytes = Bytes.of_string
