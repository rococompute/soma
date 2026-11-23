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

(* An executing provider must be released before it tailcalls another native
   callback. Keeping the thunk's environment for the later continuation would
   pin the consumed provider even though its own frame has gone away. *)
let lifetime_handle=ref(Weak.create 0)
let lifetime_seen=ref []
let[@inline never] observe_provider ()=
 collect();lifetime_seen:=Weak.check !lifetime_handle 0::!lifetime_seen;
 Lwt.return "value"
let[@inline never] provide marker ()=
 ignore(Sys.opaque_identity marker);observe_provider()
let[@inline never] provider_lifetime original bind=
 let marker=Bytes.make 2048 'p' in lifetime_handle:=weak marker;
 let read=provide marker in
 if bind then
  if original then Lwt.bind(read())(fun text->Lwt.return(String.length text))
  else Prog.bound read(fun text->Lwt.return(String.length text))
 else if original then Lwt.map String.length(read())
 else Prog.mapped read String.length
let ()=
 List.iter(fun bind->
  lifetime_seen:=[];assert(returned(provider_lifetime true bind)=5);
  let before= !lifetime_seen in
  lifetime_seen:=[];assert(returned(provider_lifetime false bind)=5);
  if before<> !lifetime_seen then failwith(Printf.sprintf "provider lifetime changed for bind=%b raw=%b generated=%b" bind(List.hd before)(List.hd !lifetime_seen));
  if Sys.backend_type=Sys.Native then assert(before=[false])
 )[false;true];
 print_endline "native library effects: executing map/bind providers release consumed closure environments"

let[@inline never] observe_value ()=
 collect();lifetime_seen:=Weak.check !lifetime_handle 0::!lifetime_seen;41
let[@inline never] provide_value marker ()=
 ignore(Sys.opaque_identity marker);observe_value()
let[@inline never] primitive_lifetime original=
 let marker=Bytes.make 2048 'i' in lifetime_handle:=weak marker;
 let read=provide_value marker in
 if original then let old=read()in ignore(old+1);old
 else Prog.update read(fun _->())
let ()=
 lifetime_seen:=[];assert(primitive_lifetime true=41);let before= !lifetime_seen in
 lifetime_seen:=[];assert(primitive_lifetime false=41);
 assert(before= !lifetime_seen);
 if Sys.backend_type=Sys.Native then assert(before=[false]);
 print_endline "native library effects: executing synchronous primitives release consumed closure environments"

let ()=
 let seen=ref [] in
 let pending,wake=Lwt.task()in
 let step word=seen:=word::!seen;if word="first"then pending else Lwt.return(String.length word)in
 let result=Prog.mapped_list step["first";"second"]in
 assert(!seen=["first"]&&Lwt.state result=Lwt.Sleep);
 Lwt.wakeup wake 3;assert(returned result=[3;6]&&List.rev !seen=["first";"second"]);
 let read _=raise reason in
 same_outcome(observed(fun()->Lwt_list.map_s read["first"]))
  (observed(fun()->Prog.mapped_list read["first"]));
 let pending,_=Lwt.task()in
 let result=Prog.mapped_list(fun _->pending)["first";"second"]in
 Lwt.cancel result;assert(failed result=Lwt.Canceled&&failed pending=Lwt.Canceled);
 assert(failed(Prog.failed reason)==reason);
 let location=Prog.make_reference 40 in
 assert(Prog.change_reference location((+)2)=40&& !location=42);
 let same=location in same:=7;
 assert(Prog.change_reference location((+)1)=7&& !same=8);
 let raised=try ignore(Prog.change_reference location(fun _->raise reason));false with e->e==reason in
 assert(raised&& !location=8);
 let caught=try ignore(Prog.asserted "native-client" 23 9);false with Assert_failure(file,line,column)->file="native-client"&&line=23&&column=9 in
 assert caught;
 assert(Prog.ordinary_entry(fun()->73)=73);
 let escaped=try ignore(Prog.ordinary_entry(fun()->raise reason));false with e->e==reason in assert escaped;
 print_endline "native library effects: sequential map order, cancellation, failed promise identity, native reference aliases and assertion provenance passed"

let filter_handle=ref(Weak.create 0)
let[@inline never] filter_lifetime original=
 let marker=Bytes.to_string(Bytes.make(1024*1024)'d')in filter_handle:=weak marker;
 let calls=ref 0 in
 let predicate text=incr calls;
  if !calls=16 then begin collect();lifetime_seen:=Weak.check !filter_handle 0::!lifetime_seen end;
  text="keep"in
 let items=marker::List.init 100000(fun _->"keep")in
 if original then List.filter predicate items else Prog.filtered predicate items
let ()=
 lifetime_seen:=[];assert(List.length(filter_lifetime true)=100000);let before= !lifetime_seen in
 lifetime_seen:=[];assert(List.length(filter_lifetime false)=100000);
 assert(before=[false]&&before= !lifetime_seen);
 let raised=try ignore(Prog.filtered(fun _->raise reason)["value"]);false with e->e==reason in assert raised;
 print_endline "native library effects: native filter releases discarded input spine and preserves predicate exception identity"

let callback_handle=ref(Weak.create 0)
let callback_payload=ref(Weak.create 0)
let[@inline never] construct_owned_callback ()=
 let marker=Bytes.create 2048 in callback_payload:=weak marker;
 let pending,wake=Lwt.task()in
 let source=Prog.owned_callback(fun()->ignore(Sys.opaque_identity marker);pending)in
 callback_handle:=weak source;
 source(),wake
let ()=
 List.iter(fun finish->
  let result,wake=construct_owned_callback()in collect();
  assert(Weak.check !callback_handle 0&&Weak.check !callback_payload 0);
  if finish then begin Lwt.wakeup wake 9;assert(returned result=9)end else Lwt.cancel result;
  collect();assert(not(Weak.check !callback_handle 0)&&not(Weak.check !callback_payload 0));
  ignore(Sys.opaque_identity result);ignore(Sys.opaque_identity wake)
 )[false;true];
 print_endline "native library effects: returned entry callbacks retain self while pending and collect cyclic ownership after completion/cancel"

let ()=
 assert(Prog.called_callback(fun value->value+1)41=42);
 let raised=try ignore(Prog.called_callback(fun _->raise reason)0);false with e->e==reason in assert raised;
 print_endline "native library effects: typed callback invocation preserves native arguments and exception identity"

let sync_outcome f=try `Value(f())with e->`Error(Printexc.to_string e)
let ()=
 let first=Bytes.to_string(Bytes.of_string "first")and second=Bytes.to_string(Bytes.of_string "second")in
 let items=Prog.make_vector[first;second]in
 assert(Array.length items=2&&Prog.vector_size items=2&&items.(0)==first);
 let copied=Prog.vector_snapshot items in assert(List.hd copied==first&&List.nth copied 1==second);
 List.iter(fun index->assert(sync_outcome(fun()->Array.get items index)=sync_outcome(fun()->Prog.get_vector items index)))
  [-1;0;1;2;max_int;min_int];
 Prog.set_vector items 0 second;assert(items.(0)==second&&Prog.get_vector items 0==second&&List.hd copied==first);
 List.iter(fun index->assert(sync_outcome(fun()->Array.set items index first)=sync_outcome(fun()->Prog.set_vector items index first)))[-1;2;max_int;min_int];
 List.iter(fun capacity->
  let old=Buffer.create capacity and fresh=Prog.make_builder capacity in
  List.iter(fun text->Buffer.add_string old text;Prog.append_builder fresh text)[first;String.make(1024*1024)'x';second];
  Buffer.add_char old '\000';Prog.char_builder fresh '\000';
  assert(Buffer.contents old=Prog.contents_builder fresh)
 )[-1;0;1;256];
 let table=Prog.make_table 1 in
 assert(Prog.lookup_table table "missing"=None&&not(Prog.has_table table "missing"));
 assert(sync_outcome(fun()->Hashtbl.find table "missing")=sync_outcome(fun()->Prog.find_table table "missing"));
 Prog.put_table table "key" first;assert(Hashtbl.find table "key"==first&&Prog.find_table table "key"==first);
 Hashtbl.replace table "key" second;assert(Option.get(Prog.lookup_table table "key")==second);
 Prog.remove_table table "key";assert(not(Hashtbl.mem table "key"));
 List.iter(fun index->
  let expected=sync_outcome(fun()->String.get first index)in
  assert(expected=sync_outcome(fun()->Prog.get_byte first index));
  assert(expected=sync_outcome(fun()->Prog.get_byte_nat first index))
 )[-1;0;4;5;max_int;min_int];
 assert(Prog.mapped_text Char.uppercase_ascii first=String.map Char.uppercase_ascii first);
 let raised=try ignore(Prog.mapped_text(fun _->raise reason)first);false with e->e==reason in assert raised;
 List.iter(fun value->assert(Prog.format_word value=string_of_int value&&Prog.format_nat value=string_of_int value))[-1;0;1;max_int;min_int];
 List.iter(fun path->assert(Prog.basename path=Filename.basename path&&Prog.dirname path=Filename.dirname path))["";"/";"//";"a/b/";"../x";"relative"];
 List.iter(fun(a,b)->assert(Prog.concat_path a b=Filename.concat a b))["","";"/a","/b";"a/","b";".",".."];
 same_outcome(observed(fun()->Lwt.apply(fun()->raise reason)()))(observed(fun()->Prog.applied(fun()->raise reason)));
 let pending,_=Lwt.task()in let result=Prog.applied(fun()->pending)in Lwt.cancel result;
 assert(failed result=Lwt.Canceled&&failed pending=Lwt.Canceled);
 print_endline "native storage: borrowed elements/snapshots, signed bounds, native buffer/table aliases, byte mapping, decimal/path ABI and Lwt.apply passed"
let storage_roots=ref []
let[@inline never] storage_ownership ()=
 let payload=Bytes.to_string(Bytes.make(1024*1024)'p')in
 let vector=Prog.make_vector[payload]and table=Prog.make_table 1 and buffer=Prog.make_builder 8 in
 Prog.put_table table "payload" payload;Prog.append_builder buffer payload;
 storage_roots:=[Obj.repr(weak vector);Obj.repr(weak table);Obj.repr(weak buffer);Obj.repr(weak payload)]
let ()=
 storage_ownership();collect();
 assert(List.for_all(fun value->not(Weak.check(Obj.obj value)0))!storage_roots);
 storage_roots:=[];print_endline "native storage: owner-managed arrays/tables/buffers collect without registry roots"

let ()=
 let read()=raise reason in
 same_outcome(observed(fun()->Lwt.map String.length(read())))
  (observed(fun()->Prog.mapped_callback read String.length));
 same_outcome(observed(fun()->Lwt.bind(read())(fun _->Lwt.return 1)))
  (observed(fun()->Prog.bound_callback read(fun _->Lwt.return 1)));
 let render _=raise reason in
 same_outcome(observed(fun()->Lwt.map render(Lwt.return "value")))
  (observed(fun()->Prog.mapped_callback(fun()->Lwt.return "value")render));
 same_outcome(observed(fun()->Lwt.bind(Lwt.return "value")render))
  (observed(fun()->Prog.bound_callback(fun()->Lwt.return "value")render));
 let pending,wake=Lwt.task()in let result=Prog.mapped_callback(fun()->pending)String.length in
 Lwt.wakeup wake "value";assert(returned result=5);
 let pending,_=Lwt.task()in let result=Prog.bound_callback(fun()->pending)(fun _->Lwt.return 7)in
 Lwt.cancel result;assert(failed result=Lwt.Canceled&&failed pending=Lwt.Canceled);
 print_endline "native library effects: entry map/bind preserve sync provider throws, callback rejections, delayed results and cancellation"

let ()=
 let calls=ref 0 in let pending,wake=Lwt.task()in
 let deferred=Prog.deferred_read(fun()->incr calls;pending)in
 assert(!calls=0);
 let first=Prog.deferred_force deferred in
 assert(!calls=1&&first==pending&&Prog.deferred_force deferred==first);
 Lwt.wakeup wake "done";assert(returned(Prog.deferred_force deferred)="done"&& !calls=1);
 let calls=ref 0 in let deferred=Prog.deferred_read(fun()->incr calls;raise reason)in
 List.iter(fun()->let caught=try ignore(Prog.deferred_force deferred);false with e->e==reason in assert caught)[();()];
 assert(!calls=1);
 let calls=ref 0 in let deferred=Prog.deferred_read(fun()->incr calls;Lwt.fail reason)in
 let first=Prog.deferred_force deferred in
 assert(failed first==reason&&Prog.deferred_force deferred==first&& !calls=1);
 let pending,_=Lwt.task()in let deferred=Prog.deferred_read(fun()->pending)in
 let first=Prog.deferred_force deferred in Lwt.cancel first;
 assert(Prog.deferred_force deferred==first&&failed first=Lwt.Canceled);
 let text="a\000bc"in
 assert(Prog.text_size text=String.length text);
 List.iter(fun(offset,count)->assert(sync_outcome(fun()->String.sub text offset count)=sync_outcome(fun()->Prog.substring text offset count)))
 [0,0;0,4;1,2;4,0;(-1),1;0,(-1);max_int,1;min_int,0;3,max_int];
 let caught=try ignore(Prog.missing_value());false with Not_found->true in assert caught;
 print_endline "native deferred: lazy/delayed invocation, cached pending/failure/cancel/exn identity and signed substring ABI passed"
let deferred_payload=ref(Weak.create 0)
let[@inline never] deferred_owner ()=
 let marker=Bytes.create 2048 in deferred_payload:=weak marker;
 let promise,_=Lwt.task()in Prog.deferred_read(fun()->ignore(Sys.opaque_identity marker);promise)
let ()=
 let body=deferred_owner()in collect();assert(Weak.check !deferred_payload 0);
 let result=Prog.deferred_force body in collect();assert(not(Weak.check !deferred_payload 0));
 ignore(Sys.opaque_identity body);ignore(Sys.opaque_identity result);
 print_endline "native deferred: force releases provider closure while cached promise remains pending"

(* Compare actual extracted entry points with Array.map, including the points
   at which callbacks can observe mutation, exception identity and live roots. *)
let ()=
 let pool=Array.init 8(fun n->Bytes.to_string(Bytes.of_string(string_of_int n)))in
 let probe invoke size fault=
  let input=Array.init size(fun n->pool.(n mod Array.length pool))in
  let seen=ref[]and step=ref 0 in
  let mapper value=
   let i= !step in incr step;seen:=(i,value)::!seen;
   if i+1<size then input.(i+1)<-pool.((i+3)mod Array.length pool);
   if i=fault then raise reason;
   value in
  let outcome=try let output=invoke mapper input in
    assert(Array.length output=size);
    Array.iteri(fun i value->assert(value==snd(List.nth(List.rev !seen)i)))output;
    `Done(Array.to_list output,output==input)
   with error->assert(error==reason);`Error in
  outcome,List.rev !seen,Array.to_list input in
 List.iter(fun size->List.iter(fun fault->
  assert(probe Array.map size fault=probe Prog.mapped_vector size fault)
 )[-1;0;1;7;31])[0;1;2;8;32];
 let source=[|pool.(1);pool.(2)|]in
 let output=Prog.owned_mapped_vector Fun.id source in
 assert(output!=source&&output.(0)==source.(0)&&output.(1)==source.(1));
 let caught=try ignore(Prog.owned_mapped_vector(fun _->raise reason)source);false with error->error==reason in
 assert caught;
 let key=Lwt.new_key()in
 Lwt.with_value key(Some 73)(fun()->
  ignore(Prog.mapped_vector(fun value->assert(Lwt.get key=Some 73);value)source));
 let floating=[|0.;Float.nan;Float.infinity;(-0.);(-1.25)|]in
 let old=Array.map Fun.id floating and fresh=Prog.mapped_vector Fun.id floating in
 assert(Obj.tag(Obj.repr old)=Obj.tag(Obj.repr fresh));
 Array.iteri(fun i value->assert(Int64.bits_of_float value=Int64.bits_of_float fresh.(i)))old;
 let old=Array.map String.length source and fresh=Prog.mapped_vector String.length source in assert(old=fresh);
 let old=Array.map float_of_string source and fresh=Prog.mapped_vector float_of_string source in
 assert(old=fresh&&Obj.tag(Obj.repr old)=Obj.tag(Obj.repr fresh));
 let old=Array.map string_of_float floating and fresh=Prog.mapped_vector string_of_float floating in assert(old=fresh);
 print_endline "native vector map: mutation order, borrowed aliases, exact exceptions, owned callbacks, Lwt context and polymorphic float-array layouts match Array.map"

let vector_map_roots=ref(fun()->[||])
let vector_map_seen=ref[]
let vector_map_sample()=collect();(!vector_map_roots)()
let[@inline never] vector_map_owner invoke=
 let marker=Bytes.create 4096 in
 let payload=Bytes.to_string(Bytes.make 1024 'p')in
 let input=[|payload;payload;payload|]in
 let mapper text=
  vector_map_seen:=vector_map_sample()::!vector_map_seen;
  ignore(Sys.opaque_identity marker);String.length text in
 let a=weak input and b=weak mapper and c=weak marker and d=weak payload in
 vector_map_roots:=(fun()->[|Weak.check a 0;Weak.check b 0;Weak.check c 0;Weak.check d 0|]);
 invoke mapper input
let vector_map_observe invoke=
 vector_map_seen:=[];
 let output=vector_map_owner invoke in
 let after=vector_map_sample()in
 ignore(Sys.opaque_identity output);List.rev !vector_map_seen,after
let ()=
 let expected=vector_map_observe Array.map and actual=vector_map_observe Prog.mapped_vector in
 assert(expected=actual);
 let during,after=actual in
 assert(List.length during=3&&List.for_all(fun roots->roots.(2))during);
 assert(Array.for_all not after);
 print_endline "native vector map: input/mapper/payload Weak roots match raw Array.map during callbacks and release after return"
