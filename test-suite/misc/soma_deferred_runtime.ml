(* [Runtime.run] contains the deferred/await branches from the generated
   soma_rt.ml. Use real Lwt promises, including cancellation and dynamic keys. *)
let create (f : unit -> 'a Lwt.t) : 'a Soma_handles.deferred =
  let p : 'a Soma_handles.deferred Lwt.t = Obj.magic
    (Runtime.run () (Prog.New_deferred (fun () ->
      Prog.Await_promise (Obj.magic (f ()))))) in
  match Lwt.state p with
  | Lwt.Return d -> d
  | _ -> failwith "creating a deferred computation blocked"

let force (d : 'a Soma_handles.deferred) : 'a Lwt.t =
  Runtime.run () (Prog.Force_deferred d)

let returned p = match Lwt.state p with
  | Lwt.Return value -> value
  | _ -> failwith "expected resolved promise"

let failed p = match Lwt.state p with
  | Lwt.Fail e -> e
  | _ -> failwith "expected failed promise"

let thrown f = match f () with
  | _ -> failwith "expected synchronous exception"
  | exception e -> e

let () =
  let count = ref 0 in
  let pending, wake = Lwt.task () in
  let d = create (fun () -> incr count; pending) in
  assert (!count = 0);
  let a = force d and b = force d in
  assert (!count = 1 && a == b && a == pending);
  let payload = ref 42 in
  Lwt.wakeup wake payload;
  assert (returned a == payload && returned b == payload);
  payload := 43;
  assert (returned (force d) == payload && !(returned (force d)) = 43);
  assert (!count = 1);
  let reason = Failure "same exception object" in
  let calls = ref 0 in
  let sync = create (fun () -> incr calls; raise reason) in
  assert (thrown (fun () -> force sync) == reason);
  assert (thrown (fun () -> force sync) == reason && !calls = 1);
  let p, w = Lwt.wait () in
  let async = create (fun () -> incr calls; p) in
  ignore (force async);
  Lwt.wakeup_exn w reason;
  assert (failed (force async) == reason && failed (force async) == reason);
  assert (!calls = 2);
  let holder = ref None and entries = ref 0 in
  let recursive = create (fun () -> incr entries; force (Option.get !holder)) in
  holder := Some recursive;
  let recursive_error = thrown (fun () -> force recursive) in
  assert (recursive_error = Lazy.Undefined && !entries = 1);
  assert (thrown (fun () -> force recursive) == recursive_error && !entries = 1);
  let key = Lwt.new_key () in
  let contextual = Lwt.with_value key (Some 1)
    (fun () -> create (fun () -> Lwt.return (Lwt.get key))) in
  assert (Lwt.with_value key (Some 2) (fun () -> returned (force contextual)) = Some 2);
  assert (Lwt.with_value key (Some 3) (fun () -> returned (force contextual)) = Some 2);
  assert (Lwt.get key = None);
  let p, _ = Lwt.task () in
  let starts = ref 0 in
  let cancellable = create (fun () -> incr starts; p) in
  let a = force cancellable and b = force cancellable in
  Lwt.cancel a;
  assert (failed b = Lwt.Canceled && failed (force cancellable) = Lwt.Canceled);
  assert (!starts = 1);
  let p, w = Lwt.wait () in
  let uncancellable = create (fun () -> p) in
  Lwt.cancel (force uncancellable);
  assert (Lwt.state p = Lwt.Sleep);
  Lwt.wakeup w 7;
  assert (returned (force uncancellable) = 7)

let weak x = let w = Weak.create 1 in Weak.set w 0 (Some x); w
let collect () = Gc.full_major (); Gc.full_major ()

let[@inline never] unused () =
  let capture = Bytes.make 1024 'x' in
  let d = create (fun () -> Lwt.return capture) in
  weak d, weak capture

let[@inline never] forced () =
  let capture = Bytes.make 1024 'x' in
  let d = create (fun () -> ignore (Sys.opaque_identity capture); Lwt.return 42) in
  ignore (force d);
  d, weak capture

let[@inline never] cached () =
  let payload = Bytes.make 1024 'x' in
  let d = create (fun () -> Lwt.return payload) in
  ignore (force d);
  weak d, weak payload

let () =
  let d, capture = unused () in
  collect ();
  assert (not (Weak.check d 0) && not (Weak.check capture 0));
  let live, capture = forced () in
  collect ();
  assert (not (Weak.check capture 0));
  assert (returned (force (Sys.opaque_identity live)) = 42);
  let d, payload = cached () in
  collect ();
  assert (not (Weak.check d 0) && not (Weak.check payload 0));
  print_endline "deferred runtime: sharing, identity, failures, reentry, context, cancellation and collection ok"
