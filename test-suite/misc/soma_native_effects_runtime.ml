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

let consumed_list_roots=ref(fun()->[||])
let consumed_list_seen=ref[]
let consumed_list_sample()=collect();(!consumed_list_roots)()
let rec raw_consumed_list observe items=
 observe items;match items with []->()|_::tail->raw_consumed_list observe tail
let[@inline never] consumed_list_owner invoke=
 let items=List.init 5(fun n->string_of_int n)in
 let a=weak items and b=weak(List.tl items)and c=weak(List.tl(List.tl items))in
 consumed_list_roots:=(fun()->[|Weak.check a 0;Weak.check b 0;Weak.check c 0|]);
 invoke(fun _->consumed_list_seen:=consumed_list_sample()::!consumed_list_seen)items
let consumed_list_observe invoke=
 consumed_list_seen:=[];consumed_list_owner invoke;
 List.rev !consumed_list_seen,consumed_list_sample()
let ()=
 let expected=consumed_list_observe raw_consumed_list and actual=consumed_list_observe Prog.consumed_list in
 if expected<>actual then begin
  let show(seen,after)=String.concat ";"(List.map(fun a->String.concat "/"(Array.to_list(Array.map string_of_bool a)))(seen@[after]))in
  Printf.eprintf "loop consumed input: raw=%s Source=%s\n%!"(show expected)(show actual);
  failwith "native loop retained the consumed initial input"
 end;
 let seen,after=actual in
 assert((List.hd seen).(0)&&not(List.nth seen 1).(0));
 assert(Array.for_all not after);
 print_endline "native loop: consumed initial list cells release in the same callback phases as raw tail recursion"

let rec raw_consumed_list_after observe after items=
 observe items;match items with []->after()|_::tail->raw_consumed_list_after observe after tail
let ()=
 let expected=consumed_list_observe(fun observe items->raw_consumed_list_after observe Fun.id items)
 and actual=consumed_list_observe(fun observe items->Prog.consumed_list_after observe Fun.id items)in
 if expected<>actual then begin
  let show(seen,after)=String.concat ";"(List.map(fun a->String.concat "/"(Array.to_list(Array.map string_of_bool a)))(seen@[after]))in
  Printf.eprintf "fused loop consumed input: raw=%s Source=%s\n%!"(show expected)(show actual);
  failwith "native tail-terminal loop retained the consumed initial input"
 end;
 print_endline "native tail-terminal loop: consumed input releases in the original recursive callback phases"

let ()=
 let borrowed=Bytes.to_string(Bytes.make 4096 'p')in
 let events=ref[]in
 let step n=events:=n::!events;if n=0 then Soma_effect.Finish borrowed else Soma_effect.Continue(n-1)in
 let next value=assert(value==borrowed);events:=(-1)::!events;value in
 assert(Prog.finished_loop step 100 next==borrowed);
 assert(List.rev !events=List.init 102(fun i->100-i));
 let pending,_=Lwt.task()in
 assert(Prog.finished_loop(fun()->Soma_effect.Finish borrowed)()(fun _->pending)==pending);
 let final_called=ref false in
 let caught=try ignore(Prog.finished_loop(fun()->raise reason)()(fun _->final_called:=true));false with error->error==reason in
 assert(caught&&not !final_called);
 let caught=try ignore(Prog.finished_loop(fun()->Soma_effect.Finish borrowed)()(fun _->raise reason));false with error->error==reason in
 assert caught;
 let key=Lwt.new_key()in
 Lwt.with_value key(Some 17)(fun()->ignore(Prog.finished_loop
  (fun()->assert(Lwt.get key=Some 17);Soma_effect.Finish borrowed)()
  (fun value->assert(Lwt.get key=Some 17);value)));
 print_endline "native tail-terminal loop: step/final order, borrowed result/promise identities, exact throws and Lwt context passed"

let both_state show promise=match Lwt.state promise with
 |Lwt.Sleep->`Pending|Lwt.Return value->`Return(show value)|Lwt.Fail error->`Fail(error==reason,error==Lwt.Canceled,Printexc.to_string error)
let both_observe combine left_mode right_mode cancel resolve_right_first=
 let left,left_wake=Lwt.task()and right,right_wake=Lwt.task()in
 let events=ref[]in
 Lwt.on_cancel left(fun()->events:="left-cancel"::!events);Lwt.on_cancel right(fun()->events:="right-cancel"::!events);
 let prepare promise wake mode value=match mode with 0->Lwt.wakeup wake value|1->()|2->Lwt.wakeup_exn wake reason|_->Lwt.cancel promise in
 prepare left left_wake left_mode"left";prepare right right_wake right_mode"right";
 let combined=combine left right in
 let snapshot()=both_state Fun.id left,both_state Fun.id right,both_state Fun.id combined,List.rev !events in
 let before=snapshot()in if cancel then Lwt.cancel combined;
 let settle promise wake value=match Lwt.state promise with Lwt.Sleep->Lwt.wakeup wake value|_->()in
 if resolve_right_first then settle right right_wake"right"else settle left left_wake"left";
 let middle=snapshot()in
 if resolve_right_first then settle left left_wake"left"else settle right right_wake"right";
 before,middle,snapshot()
let ()=
 for left=0 to 3 do for right=0 to 3 do List.iter(fun cancel->List.iter(fun reverse->
  let expected=both_observe Lwt.both left right cancel reverse and actual=both_observe Prog.paired_promises left right cancel reverse in
  assert(expected=actual)
 )[false;true])[false;true]done done;
 let borrowed_left=ref"left"and borrowed_right=Bytes.make 4096 'r'in
 let combined=Prog.paired_promises(Lwt.return borrowed_left)(Lwt.return borrowed_right)in
 (match Lwt.state combined with Lwt.Return(a,b)->assert(a==borrowed_left&&b==borrowed_right)|_->assert false);
 let same=ref"same"in
 (match Lwt.state(Prog.paired_promises(Lwt.return same)(Lwt.return same))with Lwt.Return(a,b)->assert(a==same&&b==same)|_->assert false);
 let key=Lwt.new_key()and seen=ref[]in
 let a,wa=Lwt.task()and b,wb=Lwt.task()in
 let mapped=Lwt.with_value key(Some 17)(fun()->Lwt.map(fun pair->seen:=Lwt.get key::!seen;pair)(Prog.paired_promises a b))in
 Lwt.with_value key(Some 21)(fun()->Lwt.wakeup wa 1);Lwt.with_value key(Some 29)(fun()->Lwt.wakeup wb 2);
 assert(!seen=[Some 17]);(match Lwt.state mapped with Lwt.Return(1,2)->()|_->assert false);
 print_endline"native both: 64 raw comparisons preserve ready/pending/rejected/cancelled states, cancellation order, borrowed results and Lwt context"

let started_both_observe invoke fault=
 let events=ref[]in
 let start label value()=events:=label::!events;if Some label=fault then raise reason else Lwt.return value in
 let result=try let promise=invoke(start"left""L")(start"middle""M")(start"right""R")in
  match Lwt.state promise with Lwt.Return pair->`Return pair|_->assert false
 with error->assert(error==reason);`Thrown in
 result,List.rev !events
let ()=
 List.iter(fun fault->
  let expected=started_both_observe(fun left middle right->Lwt.both(Lwt.both(left())(middle()))(right()))fault
  and actual=started_both_observe Prog.started_nested_pair fault in assert(expected=actual)
 )[None;Some"left";Some"middle";Some"right"];
 let pair_order invoke=let events=ref[]in
  let left()=events:="left"::!events;Lwt.return 1 and right()=events:="right"::!events;Lwt.return 2 in
  let promise=invoke left right in ignore(Sys.opaque_identity promise);List.rev !events in
 assert(pair_order(fun left right->Lwt.both(left())(right()))=pair_order Prog.started_pair);
 assert(pair_order Prog.started_pair=["right";"left"]);
 print_endline"native both: Source consumers retain right-to-left pair/nested initialization and exact synchronous provider throws"

let failure_capture invoke message=try ignore(invoke message);assert false with Failure actual as error->error,actual
let ()=
 let mutable_facts invoke=
  let bytes=Bytes.of_string"borrowed failure payload"in let message=Bytes.unsafe_to_string bytes in
  let first,payload=failure_capture invoke message in
  Bytes.set bytes 0 'B';let second,again=failure_capture invoke message in
  first==second,payload==message,again==message,payload==again,payload.[0] in
 let raw=mutable_facts(fun message->failwith message)and actual=mutable_facts Prog.failure_value in
 assert(raw=actual);let _,a,b,c,byte=actual in assert(a&&b&&c&&byte='B');
 let literal_facts invoke=let first,a=failure_capture invoke()and second,b=failure_capture invoke()in
  first==second,a==b,a,b in
 assert(literal_facts(fun()->failwith"tl")=literal_facts Prog.literal_failure_value);
 let message=Bytes.to_string(Bytes.make 4096 'f')in
 let immediate=Prog.mapped(fun()->Lwt.return "source")(fun _->Prog.failure_value message)in
 (match Lwt.state immediate with Lwt.Fail(Failure actual)->assert(actual==message)|_->assert false);
 let pending,wake=Lwt.task()in let mapped=Prog.mapped(fun()->pending)(fun _->Prog.failure_value message)in
 Lwt.wakeup wake "source";(match Lwt.state mapped with Lwt.Fail(Failure actual)->assert(actual==message)|_->assert false);
 print_endline"native failure: raw-matched mutable/literal message and exception allocation, plus mapped immediate/deferred failure phases passed"

let ()=
 let borrowed=Bytes.to_string(Bytes.make 4096 'x')in
 let action=Prog.Family_text(Prog.Family_count(Prog.Family_unit(Prog.Family_value(),fun()->7),string_of_int),fun value->value,borrowed)in
 (match Lwt.state(Prog.family_run action)with Lwt.Return("7",same)->assert(same==borrowed)|_->assert false);
 let pending,wake=Lwt.task()in
 let action=Prog.Family_unit(Prog.Family_text(Prog.Family_source(fun()->pending),fun value->assert(value==borrowed)),fun()->29)in
 let result=Prog.family_run action in assert(Lwt.state result=Lwt.Sleep);Lwt.wakeup wake borrowed;
 (match Lwt.state result with Lwt.Return 29->()|_->assert false);
 let action=Prog.Family_text(Prog.Family_source(fun()->raise reason),fun _->0)in
 let same=try ignore(Prog.family_run action);false with error->error==reason in assert same;
 print_endline"native indexed structural compiler: heterogeneous text/unit/count bodies preserve typed results, pending phases and provider throw identity"

let both_roots=ref(fun()->[||])
let[@inline never] both_owner combine=
 let value=ref"borrowed-left"in let left=Lwt.return value and right,wake=Lwt.task()in
 let a=weak value and b=weak left and c=weak right in
 both_roots:=(fun()->[|Weak.check a 0;Weak.check b 0;Weak.check c 0|]);
 combine left right,wake
let both_weak_observe combine finish=
 let combined,wake=both_owner combine in collect();let pending=(!both_roots)()in
 if finish then Lwt.wakeup wake(ref"borrowed-right")else Lwt.cancel combined;
 collect();let terminal=(!both_roots)()in
 ignore(Sys.opaque_identity(combined,wake));pending,terminal
let ()=
 List.iter(fun finish->
  let expected=both_weak_observe Lwt.both finish and actual=both_weak_observe Prog.paired_promises finish in
  assert(expected=actual);let pending,terminal=actual in assert(pending.(0)&&terminal.(0)=finish)
 )[false;true];
 print_endline"native both: raw-matched promise/input Weak lifetimes through pending, completion and cancellation"

let raw_literal_assertion()=assert false
let raw_dynamic_assertion file line column()=raise(Assert_failure(file,line,column))
let assertion_capture invoke=try invoke();failwith"returned assertion"with Assert_failure diagnostic as error->error,diagnostic
let assertion_allocation invoke=
 let first,a=assertion_capture invoke and second,b=assertion_capture invoke in first==second,a==b
let assertion_mutation invoke=
 let _,((file,line,column)as diagnostic)=assertion_capture invoke in
 let previous=file.[0]in let bytes=Bytes.unsafe_of_string file in
 Bytes.set bytes 0 '#';
 let _,((again,after_line,after_column)as after)=assertion_capture invoke in
 let visible=diagnostic==after&&file==again&&again.[0]='#'&&line=after_line&&column=after_column in
 Bytes.set bytes 0 previous;visible
let ()=
 assert(assertion_allocation raw_literal_assertion=assertion_allocation Prog.literal_asserted);
 assert(assertion_mutation raw_literal_assertion&&assertion_mutation Prog.literal_asserted);
 let literal,tuple=assertion_capture Prog.literal_asserted in
 ignore(Sys.opaque_identity literal);assert(tuple=("native_assertion_site",7,9));
 let bytes=Bytes.of_string"borrowed_dynamic_assertion"in let file=Bytes.unsafe_to_string bytes in
 let raw()=raw_dynamic_assertion file 71 23()and actual()=Prog.asserted file 71 23 in
 assert(assertion_allocation raw=assertion_allocation actual);
 let _,(raw_file,_,_)=assertion_capture raw and _,(actual_file,_,_)=assertion_capture actual in
 assert(raw_file==file&&actual_file==file);Bytes.set bytes 0 'B';assert(raw_file.[0]='B'&&actual_file.[0]='B');
 print_endline"native assertions: raw-matched literal/dynamic exception allocation and borrowed shared diagnostic tuples preserve unsafe filename mutation visibility"

let ()=
 let a=ref 1 and b=Bytes.make 4096 'b' and c=ref "last"in
 let value=Prog.triple_value a b c in
 let x,y,z=value in assert(x==a&&y==b&&z==c);
 let x,(y,z)=Prog.triple_parts value in assert(x==a&&y==b&&z==c);
 let replacement=ref 99 in Obj.set_field(Obj.repr value)0(Obj.repr replacement);
 let x,(y,z)=Prog.triple_parts value in assert(x==replacement&&y==b&&z==c);
 print_endline"native triples: flat tuple ABI, borrowed fields, pattern matching and mutation aliases passed"

let curried_returned pending=match Lwt.state pending with Lwt.Return value->value|_->failwith "expected an immediate curried result"
(* Full and partial application must execute the body only at saturation;
   callback handles cross the boundary as ordinary curried OCaml functions. *)
let ()=
 let scope=Lwt.new_key()in let calls=ref[]in
 let a=ref 1 and b=Bytes.of_string "borrowed"in
 let f=Prog.owned_callback2(fun x y->calls:=(x==a,y==b,Lwt.get scope)::!calls;Lwt.return(x,y))in
 let partial=f a in assert(!calls=[]);
 let x,y=Lwt.with_value scope(Some 17)(fun()->curried_returned(partial b))in
 assert(x==a&&y==b&& !calls=[true,true,Some 17]);
 let x,y=curried_returned(f a b)in assert(x==a&&y==b);
 let calls=ref 0 in
 let f=Prog.owned_callback6(fun a b c d e f->incr calls;Lwt.return(a,b,c,d,e,f,Lwt.get scope))in
 let one=f a in let three=one b "third"in let five=three false 19 in assert(!calls=0);
 let x,y,c,d,e,last,context=Lwt.with_value scope(Some 23)(fun()->curried_returned(five a))in
 assert(x==a&&y==b&&c="third"&&not d&&e=19&&last==a&&context=Some 23&& !calls=1);
 ignore(curried_returned(f a b "third" false 19 a));assert(!calls=2);
 let reason=Failure "curried callback"in
 let f=Prog.owned_callback2(fun _ _->raise reason)in
 let partial=f()in
 assert(try ignore(partial());false with e->e==reason);
 let f=Prog.owned_callback6(fun _ _ _ _ _ _->raise reason)in
 let partial=f()()()()()in
 assert(try ignore(partial());false with e->e==reason);
 let pending,wake=Lwt.task()in let f=Prog.owned_callback2(fun _ _->pending)in
 let result=f a b in assert(Lwt.state result=Lwt.Sleep);Lwt.wakeup wake a;
 assert(match Lwt.state result with Lwt.Return x->x==a|_->false);
 let pending,_=Lwt.task()in let f=Prog.owned_callback6(fun _ _ _ _ _ _->pending)in
 let result=f()()()()()()in Lwt.cancel result;assert(Lwt.state pending=Lwt.Fail Lwt.Canceled);
 print_endline"native curried callbacks: two/six arguments, full/partial/stored calls, borrowed aliases, dynamic scope, throw timing, pending results and cancellation passed"

let curried_handle=ref(Weak.create 0)
let curried_payload=ref(Weak.create 0)
let[@inline never] make_curried_pending arity=
 let marker=Bytes.create 2048 in curried_payload:=weak marker;
 let pending,wake=Lwt.task()in
 let result=if arity=2 then begin
  let f=Prog.owned_callback2(fun _ _->ignore(Sys.opaque_identity marker);pending)in
  curried_handle:=weak(Obj.repr f);f()()
 end else begin
  let f=Prog.owned_callback6(fun _ _ _ _ _ _->ignore(Sys.opaque_identity marker);pending)in
  curried_handle:=weak(Obj.repr f);f()()()()()()
 end in result,wake
let ()=
 List.iter(fun arity->List.iter(fun cancel->
  let result,wake=make_curried_pending arity in collect();
  assert(Weak.check !curried_handle 0&&Weak.check !curried_payload 0);
  if cancel then Lwt.cancel result else Lwt.wakeup wake();
  collect();assert(not(Weak.check !curried_handle 0)&&not(Weak.check !curried_payload 0));
  ignore(Sys.opaque_identity result)
 )[false;true])[2;6];
 print_endline"native curried callbacks: pending self/provider ownership releases after completion and cancellation"

let ()=
 let pending,wake=Lwt.task()in
 assert(not(Prog.promise_ready pending));Lwt.wakeup wake();assert(Prog.promise_ready pending);
 let reason=Failure"promise-state"in assert(Prog.promise_ready(Lwt.fail reason));
 assert(Prog.native_unit()==Lwt.return_unit);
 assert(Prog.native_none()==Lwt.return_none);
 List.iter(fun value->assert(Prog.signed_timer value=Int64.of_int value))
  [min_int;max_int;-200000000;-1;0;1;200000000];
 let a=Prog.literal_timer()and b=Prog.literal_timer()in assert(a=200000000L&&a==b);
 print_endline"native promise queries/constants and signed timer conversion: settled/failed/pending states, shared promise identities, signed bounds and shared boxed timer passed"

let ()=
 let key=Lwt.new_key()in let reason=Failure"native race"in
 let run race mode=
  let events=ref[]in
  let a,wa=Lwt.task()and b,wb=Lwt.task()in
  let record label=Lwt.on_cancel a(fun()->events:=(label,Lwt.get key)::!events)in
  record"cancel-a";Lwt.on_cancel b(fun()->events:=("cancel-b",Lwt.get key)::!events);
  let pending=match mode with 0->[a;b]|1->[Lwt.return 17;b]|2->[Lwt.fail reason;b]|3->[]|_->[a;b]in
  let started=try `Promise(Lwt.with_value key(Some 31)(fun()->race pending))with e->`Throw(Printexc.to_string e)in
  let observe()=match started with `Throw e->`Throw e|`Promise p->
   match Lwt.state p with Lwt.Sleep->`Sleep|Lwt.Return value->`Return value|Lwt.Fail e->`Fail(Printexc.to_string e,e==reason)in
  let before=observe()in
  Lwt.with_value key(Some 47)(fun()->match started,mode with
   |`Promise p,4->Lwt.cancel p
   |_,0->Lwt.wakeup wb 19
   |_,5->Lwt.wakeup wa 23
   |_->());
  before,observe(),List.rev !events in
 List.iter(fun mode->assert(run Lwt.pick mode=run Prog.promise_race mode))[0;1;2;3;4;5];
 print_endline"native promise race: empty/settled/failed/pending races preserve raw Lwt.pick results, exception identity, winner/loser cancellation and dynamic scope"

let ()=
 let message=Bytes.to_string(Bytes.of_string "native invalid argument")in
 let catch f=try ignore(f message);failwith "expected invalid argument"with Invalid_argument text->text in
 assert(catch invalid_arg==message&&catch Prog.invalid_value==message);
 let source1=(try Prog.invalid_value message with e->e)in
 let source2=(try Prog.invalid_value message with e->e)in
 assert(source1!=source2);
 let bytes=Bytes.unsafe_of_string message in Bytes.set bytes 0 'N';
 assert(catch Prog.invalid_value==message);
 List.iter(fun make->
  let result=Lwt.map(fun()->Prog.invalid_value message)(make())in
  assert(match Lwt.state result with Lwt.Fail(Invalid_argument text)->text==message|_->false)
 )[fun()->Lwt.return_unit];
 print_endline "native invalid_argument: borrowed mutable message, fresh exception identity and mapped failure phase passed"

let ()=
 let[@inline never] raw _owner body next=let pending=body()in Lwt.bind pending next in
 let trial bind mode=
  let weak=Weak.create 1 and stages=ref[]and events=ref[]in
  let key=Lwt.new_key()and error=Fault(Bytes.to_string(Bytes.of_string "borrowed bind"))in
  let pending,wake=Lwt.task()in let payload=Bytes.to_string(Bytes.of_string "borrowed payload")in
  let sample label=Gc.full_major();Gc.full_major();stages:=(label,Weak.check weak 0)::!stages in
  Lwt.on_cancel pending(fun()->events:=("cancel",Lwt.get key)::!events);
  let provider()=sample "provider";events:=("provider",Lwt.get key)::!events;
   match mode with 0->Lwt.return payload|1->Lwt.fail error|2|3|4->pending|_->raise error in
  let next value=sample "next";assert(value==payload);events:=("next",Lwt.get key)::!events;Lwt.return value in
  let[@inline never] start()=let owner=Bytes.to_string(Bytes.make 1001 'o')in Weak.set weak 0(Some owner);bind owner provider next in
  let answer=try `Promise(Lwt.with_value key(Some 17)start)with e->`Throw(e==error)in
  let state()=match answer with `Throw same->`Throw same|`Promise p->match Lwt.state p with
   |Lwt.Sleep->`Sleep|Lwt.Return value->`Return(value==payload)|Lwt.Fail e->`Fail(e==error,Printexc.to_string e)in
  sample "before-wake";let before=state()in
  Lwt.with_value key(Some 99)(fun()->match mode,answer with
   |2,_->Lwt.wakeup wake payload|3,_->Lwt.wakeup_exn wake error|4,`Promise p->Lwt.cancel p|_->());
  sample "returned";before,state(),List.rev !events,List.rev !stages in
 List.iter(fun mode->assert(trial raw mode=trial Prog.borrowed_bind mode))[0;1;2;3;4;5];
 print_endline "native borrowed bind: direct-call owner Weak phases, payload/exception identity, synchronous throw, cancellation and context passed"

let ()=
 let[@inline never] raw ops argument=ops.Prog.tail_function argument in
 let trial invoke mode=
  let weak=Weak.create 3 and stages=ref[]in
  let sample phase=Gc.full_major();Gc.full_major();stages:=(phase,List.init 3(fun i->Weak.check weak i))::!stages in
  let error=Fault "tail invoke"and pending,_=Lwt.task()in
  let function_ _=sample "provider";if mode=1 then raise error else pending in
  let[@inline never] start ()=
   let marker=Bytes.to_string(Bytes.make 1001 'm')and argument=Bytes.to_string(Bytes.make 1009 'a')in
   let ops={Prog.tail_function=function_;tail_marker=marker}in
   Weak.set weak 0(Some(Obj.repr marker));Weak.set weak 1(Some(Obj.repr argument));Weak.set weak 2(Some(Obj.repr ops));
   invoke ops argument in
  let outcome=try let p=start()in assert(p==pending);`Promise with e->assert(e==error);`Throw in
  sample "returned";outcome,List.rev !stages in
 List.iter(fun mode->assert(trial raw mode=trial Prog.tail_record mode))[0;1];
 let key=Lwt.new_key()and reason=Fault "tail context"in
 let pending,_=Lwt.task()in
 let provider()=assert(Lwt.get key=Some 17);pending in
 assert(Lwt.with_value key(Some 17)(fun()->Prog.tail_called provider)==pending);
 assert(try ignore(Prog.tail_called(fun()->raise reason));false with e->e==reason);
 Lwt.cancel(Prog.tail_called(fun()->pending));assert(match Lwt.state pending with Lwt.Fail Lwt.Canceled->true|_->false);
 print_endline "native tail invoke: raw tailcall frames, record/argument Weak phases, exact promise/exception identity, context and cancellation passed"

let ()=
 List.iter(fun size->let text=String.init size(fun i->Char.chr(i land 255))in assert(Prog.word_size text=String.length text))[0;1;2;255;256;4096;1000000];
 print_endline "native word length: exact byte count, embedded NUL/high bytes, empty and large strings passed"
