(* Promises an image awaits (await_promise), and a buffer read in place *)

(* [v], once the scheduler has run the others *)
let later v = Lwt.map (fun () -> v) (Lwt.pause ())

(* a promise that fails, with [why] *)
let broken why = Lwt.fail_with why

(* the sum of the buffer's bytes *)
let checksum b =
  let s = ref 0 in
  Bytes.iter (fun c -> s := !s + Char.code c) b;
  !s
