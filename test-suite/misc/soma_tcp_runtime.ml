(* Run the generated adapter verbatim, with real Lwt and controlled flows. *)
open Links
let ready p = match Lwt.state p with
  | Lwt.Return x -> x | Lwt.Fail e -> raise e | Lwt.Sleep -> failwith "unexpected pending operation"
let flow reads =
  let q = Queue.create () in
  List.iter (fun r -> Queue.add r q) reads;
  S.TCP.{reads=q;closed=0;writes_fail=false;read_count=0}
let data s = Lwt.return (Ok (`Data s))
let eof () = Lwt.return (Ok `Eof)
let reset () = Lwt.return (Error `Reset)
let recv rt id = rt.receive id None
let () =
  let rt = make () in
  let f = flow [data "first"; reset ()] in
  let id = rt.register f in
  assert (ready (recv rt id) = Soma_rt.Got_bytes "first");
  assert (ready (recv rt id) = Soma_rt.Raw_failed "connection reset");
  assert (f.closed = 1 && f.read_count = 2);
  assert (ready (recv rt id) = Soma_rt.Raw_closed);
  assert (ready (rt.send id "late") = Soma_rt.Write_closed);
  ignore (ready (rt.close id)); assert (f.closed = 1);
  let f = flow [eof ()] in
  let id = rt.register f in
  assert (ready (recv rt id) = Soma_rt.Raw_closed);
  assert (f.closed = 1);
  let f = flow [] in
  let id = rt.register f in
  assert (ready (rt.send id "ok") = Soma_rt.Write_ok);
  f.writes_fail <- true;
  assert (ready (rt.send id "bad") = Soma_rt.Write_failed "write closed");
  assert (ready (rt.send id "again") = Soma_rt.Write_closed);
  assert (ready (recv rt id) = Soma_rt.Raw_closed && f.closed = 1);
  (* Line and frame readers preserve their existing closure results. *)
  let f = flow [data "first\r";data "\nsecond\npartial";reset ()] in
  let id = rt.register f in
  assert (ready (rt.receive_line id) = Some "first");
  assert (ready (rt.receive_line id) = Some "second");
  assert (ready (rt.receive_line id) = None && f.closed = 1);
  let f = flow [data "\000\000\000\003abc\000";reset ()] in
  let id = rt.register f in
  assert (ready (rt.receive_frame id 0 100) = Soma_rt.Got_frame "abc");
  assert (ready (rt.receive_frame id 0 100) = Soma_rt.Frame_closed && f.closed = 1);
  (* A checked raw read sees the remainder kept by a line reader first. *)
  let f = flow [data "line\nrest";reset ()] in
  let id = rt.register f in
  assert (ready (rt.receive_line id) = Some "line");
  assert (ready (recv rt id) = Soma_rt.Got_bytes "rest");
  assert (ready (recv rt id) = Soma_rt.Raw_failed "connection reset");
  (* Legacy watched streams still finish with one LinkClosed event. *)
  Queue.clear Soma_rt.incoming;
  let f = flow [data "a";reset ()] in
  let id = rt.register f in
  rt.watch id;
  let events = List.of_seq (Queue.to_seq Soma_rt.incoming) in
  assert (events = [Soma_rt.In_mail (Soma_rt.Mail_bytes (id,"a"));Soma_rt.In_mail (Soma_rt.Mail_closed id)]);
  assert (f.closed = 1);
  print_endline "PASS TCP: data, EOF, read/write errors, legacy framing, and watched cleanup"
