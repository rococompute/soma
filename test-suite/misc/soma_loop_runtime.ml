(* Use the emitted loop/catch/finalize interpreter, with real Lwt. *)
let ret value = Prog.Ret value
let await (p : 'a Lwt.t) : 'a Prog.io = Obj.magic (Prog.Await_promise p)
let throw (e : exn) : 'a Prog.io = Obj.magic (Prog.Throw_exception e)
let loop (step : 's -> ('s, 'a) Prog.loop_step Prog.io) (initial : 's) : 'a Prog.io =
  Obj.magic (Prog.Loop ((fun state -> Obj.magic (step (Obj.obj state))), Obj.repr initial))
let run body = Runtime.run () body
let returned p = match Lwt.state p with Lwt.Return v -> v | _ -> failwith "expected result"
let failed p = match Lwt.state p with Lwt.Fail e -> e | _ -> failwith "expected failure"
let () =
  let steps = ref 0 in
  let payload = Bytes.of_string "original result" in
  let step index = incr steps;
    ret (if index = 0 then Prog.Finish payload else Prog.Continue (index-1)) in
  assert (returned (run (loop step 1000000)) == payload);
  assert (!steps = 1000001);
  steps := 0;
  let step () = incr steps; ret (Prog.Finish payload) in
  assert (returned (run (loop step ())) == payload && !steps = 1);
  let trace = ref [] and pending, wake = Lwt.task () in
  let step index = trace := index :: !trace;
    if index = 0 then await pending else ret (Prog.Finish index) in
  let waiting = run (loop step 0) in
  assert (Lwt.state waiting = Lwt.Sleep && !trace = [0]);
  Lwt.wakeup wake (Prog.Continue 1);
  assert (returned waiting = 1 && !trace = [1;0]);
  let reason = Failure "stop here" in
  let steps = ref 0 in
  let step index = incr steps;
    if index = 5 then throw reason else ret (Prog.Continue (index+1)) in
  assert (failed (run (loop step 0)) == reason && !steps = 6);
  let step _ = raise reason in
  let escaped = try ignore (run (loop step ())); None with e -> Some e in
  assert (Option.get escaped == reason);
  let pending, _ = Lwt.task () in
  let entries = ref 0 in
  let waiting = run (loop (fun () -> incr entries; await pending) ()) in
  Lwt.cancel waiting;
  assert (failed waiting = Lwt.Canceled && failed pending = Lwt.Canceled && !entries = 1);
  let key = Lwt.new_key () in
  let pending, wake = Lwt.task () in
  let seen = ref [] in
  let step index = seen := Lwt.get key :: !seen;
    if index = 0 then await pending else ret (Prog.Finish index) in
  let scoped = Lwt.with_value key (Some 7) (fun () -> run (loop step 0)) in
  Lwt.with_value key (Some 9) (fun () -> Lwt.wakeup wake (Prog.Continue 1));
  assert (returned scoped = 1 && !seen = [Some 7;Some 7] && Lwt.get key = None);
  print_endline "loop runtime: one million steps, result identity, early return, pending work, failure, cancellation and context ok"

let weak x = let w = Weak.create 1 in Weak.set w 0 (Some x); w
let collect () = Gc.full_major (); Gc.full_major ()
let[@inline never] suspended () =
  let state = Bytes.make 1024 'x' in
  let promise, wake = Lwt.task () in
  let result = run (loop (fun _ -> await promise) state) in
  result, wake, weak state
let[@inline never] finished () =
  let capture = Bytes.make 1024 'x' in
  let result = run (loop (fun () -> ignore (Sys.opaque_identity capture);
    ret (Prog.Finish 42)) ()) in
  result, weak capture
let () =
  let waiting, wake, state = suspended () in
  collect ();
  assert (not (Weak.check state 0) && Lwt.state waiting = Lwt.Sleep);
  Lwt.wakeup wake (Prog.Finish ());
  assert (returned waiting = ());
  let result, capture = finished () in
  collect ();
  assert (not (Weak.check capture 0) && returned result = 42);
  print_endline "loop runtime: consumed state released while pending; completed step closure collected"
