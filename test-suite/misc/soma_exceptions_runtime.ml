(* Typed construction of extracted effects. Runtime.run is taken from the
   emitted backend, including catch/throw/finalize rather than a test copy. *)
let ret x = Prog.Ret x
let call (f : unit -> 'a) : 'a Prog.io =
  Obj.magic (Prog.Call (fun () -> Obj.repr (f ())))
let await (p : 'a Lwt.t) : 'a Prog.io = Obj.magic (Prog.Await_promise p)
let throw (e : exn) : 'a Prog.io = Obj.magic (Prog.Throw_exception e)
let catch (body : 'a Prog.io) (recover : exn -> 'a Prog.io) : 'a Prog.io =
  Obj.magic (Prog.Catch (Obj.magic body, fun e -> Obj.magic (recover e)))
let finally (body : 'a Prog.io) (cleanup : unit Prog.io) : 'a Prog.io =
  Obj.magic (Prog.Finally (Obj.magic body, cleanup))
let run body = Runtime.run () body
let returned p = match Lwt.state p with Lwt.Return v -> v | _ -> failwith "expected value"
let failed p = match Lwt.state p with Lwt.Fail e -> e | _ -> failwith "expected failure"
exception Returned of int ref

let () =
  let payload = ref 42 in
  let original = Returned payload in
  let handled = ref 0 in
  let recover e = incr handled; assert (e == original); ret e in
  assert (returned (run (catch (call (fun () -> raise original)) recover)) == original);
  let pending, wake = Lwt.task () in
  let caught = run (catch (await pending) recover) in
  assert (Lwt.state caught = Lwt.Sleep && !handled = 1);
  Lwt.wakeup_exn wake original;
  assert (returned caught == original && !handled = 2);
  let success = Lwt.return payload in
  let no_recovery _ = failwith "recovered successful action" in
  assert (run (catch (await success) no_recovery) == success);
  let replacement = Failure "replacement" in
  let one = ref 0 in
  assert (failed (run (catch (throw original) (fun _ -> incr one; throw replacement))) == replacement);
  assert (!one = 1);
  let observed f = try `Promise (Lwt.state (f ())) with e -> `Synchronous e in
  let direct = observed (fun () -> Lwt.catch (fun () -> Lwt.fail original)
    (fun _ -> raise replacement)) in
  let generated = observed (fun () -> run (catch (throw original)
    (fun _ -> raise replacement))) in
  (match direct, generated with
   | `Synchronous a, `Synchronous b | `Promise (Lwt.Fail a), `Promise (Lwt.Fail b) ->
       assert (a == replacement && b == replacement)
   | _ -> failwith "handler exception crossed a different native Lwt boundary");
  let key = Lwt.new_key () in
  let pending, wake = Lwt.task () in
  let scoped = Lwt.with_value key (Some 7) (fun () ->
    run (catch (await pending) (fun e -> assert (e == original); ret (Lwt.get key)))) in
  Lwt.with_value key (Some 9) (fun () -> Lwt.wakeup_exn wake original);
  assert (returned scoped = Some 7 && Lwt.get key = None);
  let restored = ref false in
  let scoped = finally (throw original) (call (fun () -> restored := true)) in
  let caught = run (catch scoped (fun e -> assert (!restored && e == original); ret e)) in
  assert (returned caught == original);
  assert (failed (run (finally (throw original) (throw replacement))) == replacement);
  let pending, _ = Lwt.task () in
  let cleaned = ref false and canceled = ref None in
  let waiting = run (catch (finally (await pending) (call (fun () -> cleaned := true)))
    (fun error -> assert !cleaned; canceled := Some error; throw error)) in
  Lwt.cancel waiting;
  assert (failed waiting == Option.get !canceled);
  assert (failed waiting = Lwt.Canceled && failed pending = Lwt.Canceled);
  let handled_exit = ref false in
  let escaping = Runtime.Exit_with 7 in
  assert (failed (run (catch (throw escaping) (fun _ -> handled_exit := true; ret ()))) == escaping);
  assert (not !handled_exit);
  let a : exn = returned (run (Obj.magic (Prog.New_failure "same"))) in
  let b : exn = returned (run (Obj.magic (Prog.New_failure "same"))) in
  assert (a != b);
  assert (returned (run (Obj.magic (Prog.Same_exception (original,original)))));
  assert (not (returned (run (Obj.magic (Prog.Same_exception (a,b))))));
  let description : string = returned (run (Obj.magic (Prog.Exception_message original))) in
  assert (description = Printexc.to_string original)

let weak x = let w = Weak.create 1 in Weak.set w 0 (Some x); w
let collect () = Gc.full_major (); Gc.full_major ()
let[@inline never] discarded () =
  let data = ref 42 in
  let error = Returned data in
  let caught = returned (run (catch (throw error) ret)) in
  weak caught, weak data
let[@inline never] consumed_handler () =
  let capture = Bytes.make 1024 'x' in
  let pending, wake = Lwt.task () in
  let result = run (catch (await pending) (fun e ->
    ignore (Sys.opaque_identity capture); ret e)) in
  let error = Failure "delayed" in
  Lwt.wakeup_exn wake error;
  result, weak capture
let () =
  let error, data = discarded () in
  collect ();
  assert (not (Weak.check error 0) && not (Weak.check data 0));
  let result, capture = consumed_handler () in
  collect ();
  assert (not (Weak.check capture 0));
  ignore (returned (Sys.opaque_identity result));
  print_endline "exception runtime: native identity, scopes, handlers, cleanup, cancellation, exit and collection ok"
