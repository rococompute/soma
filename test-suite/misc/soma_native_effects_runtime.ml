(* Call the actual extracted public entry points, not a second interpreter. *)
exception Fault of string
let reason = Fault "original"
let returned p = match Lwt.state p with Lwt.Return v -> v | _ -> failwith "expected result"
let failed p = match Lwt.state p with Lwt.Fail e -> e | _ -> failwith "expected failure"
let observed f = try `Promise (Lwt.state (f ())) with e -> `Throw e
let same_outcome a b = match a,b with
 | `Throw a,`Throw b | `Promise (Lwt.Fail a),`Promise (Lwt.Fail b) -> assert (a==b)
 | `Promise (Lwt.Return a),`Promise (Lwt.Return b) -> assert (a=b)
 | `Promise Lwt.Sleep,`Promise Lwt.Sleep -> ()
 | _ -> failwith "native boundary changed"
let () =
 let events=ref [] and value=ref 41 in
 let get ()=events:="get"::!events;!value in
 let put n=events:="put"::!events;value:=n in
 assert (Prog.update get put=41 && !value=42 && List.rev !events=["get";"put"]);
 events:=[];
 assert(Prog.sequenced get put=42&&List.rev !events=["get";"put"]);
 let raised=try ignore(Prog.update get(fun _->raise reason));false with e->assert(e==reason);true in
 assert raised;
 let payload=Bytes.to_string(Bytes.of_string "borrowed")in
 assert(returned(Prog.promised payload)==payload);
 let result=Ok payload in assert(Prog.result_alias result==result&&Prog.result_length result=String.length payload);
 let result=Error payload in assert(Prog.result_alias result==result&&Prog.result_length result=0);
 assert(Prog.count 1000000 payload==payload);
 let read ()=raise reason in
 let recover e=assert(e==reason);73 in
 assert(Prog.protected read recover=73);
 let escape=try ignore(Prog.rethrow reason);false with e->assert(e==reason);true in assert escape;
 (* Map and bind must keep synchronous provider throws outside their scopes. *)
 same_outcome (observed(fun()->Lwt.map String.length(read())))
   (observed(fun()->Prog.mapped read String.length));
 let render _=raise reason in
 same_outcome (observed(fun()->Lwt.map render(Lwt.return payload)))
   (observed(fun()->Prog.mapped(fun()->Lwt.return payload)render));
 let pending,wake=Lwt.task()in
 let mapped=Prog.mapped(fun()->pending)String.length in
 assert(Lwt.state mapped=Lwt.Sleep);
 Lwt.wakeup wake payload;assert(returned mapped=String.length payload);
 let pending,_=Lwt.task()in
 let mapped=Prog.mapped(fun()->pending)String.length in Lwt.cancel mapped;
 assert(failed mapped=Lwt.Canceled&&failed pending=Lwt.Canceled);
 let next text=assert(text==payload);Lwt.return 7 in
 assert(returned(Prog.bound(fun()->Lwt.return payload)next)=7);
 same_outcome (observed(fun()->Lwt.bind(read())next))
   (observed(fun()->Prog.bound read next));
 let next _=raise reason in
 same_outcome (observed(fun()->Lwt.bind(Lwt.return payload)next))
   (observed(fun()->Prog.bound(fun()->Lwt.return payload)next));
 let calls=ref 0 in
 let recover e=incr calls;assert(e==reason);Lwt.return 9 in
 assert(returned(Prog.caught read recover)=9&& !calls=1);
 let pending,wake=Lwt.task()in
 let caught=Prog.caught(fun()->pending)recover in
 assert(!calls=1);Lwt.wakeup_exn wake reason;assert(returned caught=9&& !calls=2);
 let replacement=Fault"handler"in
 let recover _=raise replacement in
 same_outcome(observed(fun()->Lwt.catch read recover))
   (observed(fun()->Prog.caught read recover));
 let trace=ref[]in
 let body()=trace:="body"::!trace;Lwt.fail reason in
 let cleanup()=trace:="cleanup"::!trace;Lwt.return_unit in
 assert(failed(Prog.finalized body cleanup)==reason&&List.rev !trace=["body";"cleanup"]);
 assert(failed(Prog.finalized body(fun()->Lwt.fail replacement))==replacement);
 let pending,_=Lwt.task()in
 let cleaned=ref false in
 let result=Prog.finalized(fun()->pending)(fun()->cleaned:=true;Lwt.return_unit)in
 Lwt.cancel result;assert(!cleaned&&failed result=Lwt.Canceled);
 let values=["a";"bb";"ccc"]in
 let record=ref[]in
 let step total word=record:=word::!record;Lwt.return(total+String.length word)in
 assert(returned(Prog.folded step 0 values)=6&&List.rev !record=values);
 let key=Lwt.new_key()in
 let pending,wake=Lwt.task()in
 let scoped=Lwt.with_value key(Some 7)(fun()->Prog.bound(fun()->pending)(fun _->Lwt.return(Option.get(Lwt.get key))))in
 Lwt.with_value key(Some 9)(fun()->Lwt.wakeup wake payload);
 assert(returned scoped=7&&Lwt.get key=None);
 print_endline "native library effects: sequencing, million-step loop, identity, sync/async exceptions, map/bind/fold/finalize, cancellation and context passed"

let weak value=let w=Weak.create 1 in Weak.set w 0(Some value);w
let collect()=Gc.full_major();Gc.full_major()
let[@inline never] pending_state()=
 let data=Bytes.to_string(Bytes.make 1024 'x')in
 let promise,wake=Lwt.task()in
 let result=Prog.mapped(fun()->ignore(Sys.opaque_identity data);promise)String.length in
 result,wake,weak data
let ()=
 let result,wake,data=pending_state()in collect();
 assert(not(Weak.check data 0));
 Lwt.wakeup wake "finished";assert(returned result=8);
 print_endline "native library effects: consumed provider payload released while promise is pending"
