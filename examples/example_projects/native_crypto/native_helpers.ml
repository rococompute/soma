type 'a box = Box of 'a
let wrap x = Box x
let unwrap (Box x) = x
let twice f x = f (f x)
let next (n : Soma_nat.nat) : Soma_nat.nat = n + 1
let label ~prefix s = prefix ^ s
let settled n = match Lwt.state (Lwt.return n) with Lwt.Return n -> n | _ -> 0
