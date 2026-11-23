(* Runtime.run uses the actual reference cases emitted by soma build. *)
let returned p = match Lwt.state p with
  | Lwt.Return value -> value
  | _ -> failwith "reference operation did not resolve immediately"

let make value : 'a Soma_handles.reference =
  Obj.magic (returned (Runtime.run () (Prog.New_reference (Obj.repr value))))
let read (r : 'a Soma_handles.reference) : 'a =
  Obj.magic (returned (Runtime.run () (Prog.Read_reference (Obj.magic r))))
let write (r : 'a Soma_handles.reference) (value : 'a) =
  returned (Runtime.run () (Prog.Write_reference (Obj.magic r, Obj.repr value)))
let modify (r : 'a Soma_handles.reference) (f : 'a -> 'a) : 'a =
  Obj.magic (returned (Runtime.run () (Prog.Modify_reference
    (Obj.magic r, fun v -> Obj.repr (f (Obj.obj v))))))

let () =
  let r = make 1 in
  let alias = r in
  write alias 2;
  assert (read r = 2);
  assert (modify r succ = 3 && read alias = 3);
  (* Native .definition bindings use the same ref, with no copy or table. *)
  incr r;
  assert (read alias = 4);
  write r 5;
  assert (!r = 5);
  let reason = Failure "update failed" in
  let failed = try ignore (modify r (fun _ -> raise reason)); false
    with e -> assert (e == reason); true in
  assert (failed && read r = 5);
  let payload = Bytes.of_string "abc" in
  let buffer = make payload in
  assert (read buffer == payload);
  Bytes.set (read buffer) 0 'z';
  assert (Bytes.to_string payload = "zbc");
  let nested = make r in
  write (read nested) 6;
  assert (read r = 6)

let weak x = let w = Weak.create 1 in Weak.set w 0 (Some x); w
let collect () = Gc.full_major (); Gc.full_major ()
type node = Node of node option Soma_handles.reference

let[@inline never] cycle () =
  let r = make None in
  let n = Node r in
  write r (Some n);
  weak r, weak n

let[@inline never] overwritten () =
  let payload = Bytes.make 1024 'x' in
  let r = make payload in
  let old = weak payload in
  write r (Bytes.of_string "new");
  r, old

let[@inline never] held () =
  let payload = Bytes.make 1024 'x' in
  make payload, weak payload

let[@inline never] unused () =
  let payload = Bytes.make 1024 'x' in
  let r = make payload in
  weak r, weak payload

let () =
  let location, node = cycle () in
  collect ();
  assert (not (Weak.check location 0) && not (Weak.check node 0));
  let r, old = overwritten () in
  collect ();
  assert (not (Weak.check old 0));
  assert (Bytes.to_string (read (Sys.opaque_identity r)) = "new");
  let r, payload = held () in
  collect ();
  assert (Weak.check payload 0);
  assert (read (Sys.opaque_identity r) == Option.get (Weak.get payload 0));
  let location, payload = unused () in
  collect ();
  assert (not (Weak.check location 0) && not (Weak.check payload 0));
  print_endline "reference runtime: aliases, native identity, failed updates and cyclic collection ok"
