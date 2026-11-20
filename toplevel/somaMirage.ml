(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: a program that requires [Soma.Sandbox] is a MirageOS
   unikernel. After [rocq c prog.soma] has checked it, its
   [main : io unit] is extracted to OCaml into a MirageOS project, which is
   built for solo5's hvt target into [prog.hvt], next to [prog.vo].

   A program that uses [serve], [fetch], [listen] or [connect] gets a
   network stack, and runs
   under [solo5-vmnet]; the others do not need a network device. Each kind
   has its own project, kept between builds in [$SOMA_MIRAGE_DIR] or
   else [~/.cache/soma/mirage] ([plain/], [net/]), so that
   [mirage configure] and fetching the dependencies ([make depends]) only
   happen once. The MirageOS tools come
   from the opam switch [$SOMA_MIRAGE_SWITCH] (a
   switch with the hvf-mac repository, see solo5-mac). The image runs in
   [$SOMA_MIRAGE_MEM] MB of memory, 256 by default (the command to run it
   says so). Setting [SOMA_MIRAGE_BUILD=0] skips the image.
   [soma build --no-image], and a build with [$SOMA_MIRAGE_SWITCH] unset
   or empty, still extracts the project, parses [config.ml], and
   type-checks [prog.ml] and [soma_rt.ml] with plain OCaml against
   stand-in Mirage signatures ([no-image/standins.mli]). That stops
   before the image. *)

open Names

let mirage_library = DirPath.make (List.rev_map Id.of_string ["Soma"; "Sandbox"])

(* [Library.library_is_loaded] is always true ([find_library] returns an
   option, it does not raise), so the list of loaded libraries is used *)
let requires_mirage () =
  List.exists (DirPath.equal mirage_library) (Library.loaded_libraries ())

let getenv_default var default =
  match Sys.getenv_opt var with Some v when v <> "" -> v | _ -> default

let cache_dir () =
  match Sys.getenv_opt "SOMA_MIRAGE_DIR" with
  | Some d when d <> "" -> d
  | _ ->
    let cache = match Sys.getenv_opt "XDG_CACHE_HOME" with
      | Some d when d <> "" -> d
      | _ -> Filename.concat (getenv_default "HOME" ".") ".cache"
    in
    List.fold_left Filename.concat cache ["soma"; "mirage"]

let rec mkdir_p d =
  if not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

let read_file f =
  let ic = open_in_bin f in
  Fun.protect ~finally:(fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let write_file f s =
  let oc = open_out_bin f in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () -> output_string oc s)

(* [s] as a Soma (Rocq) string literal: a double quote is written twice,
   and every other byte, a backslash included, stands for itself. OCaml's
   [%S] escapes quotes and backslashes as OCaml reads them, which Rocq
   does not: a directory with a quote would end the literal early, and a
   backslash would name another directory. *)
let quote_soma_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (fun c ->
      if c = '"' then Buffer.add_string b "\"\""
      else Buffer.add_char b c) s;
  Buffer.add_char b '"';
  Buffer.contents b

(* Writes [f] only when its contents change, so that dune does not rebuild
   for nothing. Returns whether it changed. *)
let update_file f s =
  if Sys.file_exists f && String.equal (read_file f) s then false
  else (write_file f s; true)

let error msg = CErrors.user_err Pp.(str "Mirage: " ++ msg)

(* [main] exists and has type [io unit] *)
let check_main () =
  let main = Libnames.qualid_of_ident (Id.of_string "main") in
  let gr = try Nametab.locate main with Not_found ->
    error Pp.(str "a program that requires Sandbox defines" ++ spc () ++
              str "main : io unit, what the unikernel does.")
  in
  let env = Global.env () in
  let ty, _ = Typeops.type_of_global_in_context env gr in
  let io = Nametab.global (Libnames.qualid_of_string "Soma.Sandbox.io") in
  let unit = Rocqlib.lib_ref "core.unit.type" in
  let is r c = match Constr.kind c with
    | Constr.Ind (i, _) -> GlobRef.CanOrd.equal r (GlobRef.IndRef i)
    | _ -> false
  in
  let ok = match Constr.kind (Reduction.whd_all env ty) with
    | Constr.App (f, [| a |]) -> is io f && is unit (Reduction.whd_all env a)
    | _ -> false
  in
  if not ok then
    let sigma = Evd.from_env env in
    error Pp.(str "main has type" ++ spc () ++
              Printer.pr_lconstr_env env sigma ty ++ spc () ++
              str "but the unikernel runs an io unit.")

(* The generated files of the MirageOS project. [soma_rt.ml] runs an
   [io]; [unikernel.ml] starts it, with a network stack or without. *)

let header = "(* Generated by Soma (toplevel/somaMirage.ml). *)\n"

(* Findlib sublibraries belong to their root opam package. Name the exact
   library, not the package's default library (digestif.c is one example). *)
let config_ml_base ?(c = false) ~network ~wasm ~libraries () =
  let wasm_package = if wasm then "; package \"wasm\"" else "" in
  let builtins, packages = List.partition (fun l ->
      List.mem (SomaOcamlBindings.package_of l) SomaOcamlBindings.with_compiler) libraries in
  (* the program's C modules: the library soma_c, built for Solo5 *)
  let builtins = builtins @ (if c then ["soma_c"] else []) in
  let native_packages = String.concat "" (List.map (fun l ->
      Printf.sprintf "; package %S ~libs:[%S]" (SomaOcamlBindings.package_of l) l) packages) in
  let locals = if builtins = [] then "" else
    Printf.sprintf " ~local_libs:[%s]" (String.concat "; " (List.map (Printf.sprintf "%S") builtins)) in
  header ^
  if network then {soma|open Mirage

let main =
  main "Unikernel.Main" (stackv4v6 @-> job)
|soma} ^ locals ^ {soma|
    ~packages:[ package "duration"; package "mirage-mtime"; package "ptime"; package "mirage-crypto-rng"|soma} ^ wasm_package ^ native_packages ^ {soma| ]

let stack = generic_stackv4v6 default_network
let () = register "soma" [ main $ stack ]
|soma}
  else {soma|open Mirage

let main =
  main "Unikernel" job
|soma} ^ locals ^ {soma|
    ~packages:[ package "duration"; package "mirage-mtime"; package "ptime"; package "mirage-crypto-rng"|soma} ^ wasm_package ^ native_packages ^ {soma| ]

let () = register "soma" [ main ]
|soma}

let replace_text text old replacement =
  let n = String.length old in
  let out = Buffer.create (String.length text) in
  let rec loop i =
    if i >= String.length text then Buffer.contents out
    else if i+n <= String.length text && String.sub text i n = old then
      (Buffer.add_string out replacement; loop (i+n))
    else (Buffer.add_char out text.[i]; loop (i+1)) in
  loop 0

(* a web image: [resolve] and [https] need MirageOS's dns-client device on
   the stack (with happy-eyeballs, which it asks for), and TLS with the NSS
   certificate authorities *)
let web_config text =
  let text = replace_text text "(stackv4v6 @-> " "(stackv4v6 @-> dns_client @-> " in
  let text = replace_text text "package \"duration\"" "package \"domain-name\"; package \"tls-mirage\"; package \"ca-certs-nss\"; package \"x509\"; package \"duration\"" in
  let text = replace_text text "let () = register" "let happy_eyeballs = generic_happy_eyeballs stack\nlet dns = generic_dns_client stack happy_eyeballs\nlet () = register" in
  replace_text text "main $ stack" "main $ stack $ dns"

let storage_config text =
  let text = replace_text text "(stackv4v6 @-> job)" "(stackv4v6 @-> block @-> job)" in
  let text = replace_text text "main \"Unikernel\" job" "main \"Unikernel.Main\" (block @-> job)" in
  let text = replace_text text "package \"duration\"" "package \"mirage-block\"; package \"cstruct\"; package \"lwt\"; package \"duration\"" in
  let text = replace_text text "let () = register" "let storage = block_of_file \"storage\"\nlet () = register" in
  replace_text (replace_text text "main $ stack" "main $ stack $ storage") "[ main ]" "[ main $ storage ]"

let config_ml ?c ~network ~wasm ~storage ~web ~libraries () =
  let text = config_ml_base ?c ~network ~wasm ~libraries () in
  let text = if storage then storage_config text else text in
  if web then web_config text else text

let runtime_ml = header ^ {soma|(* Runs a Soma program's [main : io unit], extracted to prog.ml: each
   [io] action becomes the unikernel's console, clock, random numbers,
   timers, loops and TCP connections. *)
open Lwt.Infix

(* The image's strings are OCaml's and its [nat] OCaml's [int]
   (ExtrOcamlNativeString, ExtrOcamlNatInt): these name the crossings *)
let string_of_chars (s : string) = s
let chars_of_string (s : string) = s

let int_of_nat (n : int) = n

let nat_of_int (k : int) = max 0 k

(* [unk] and [raise] are values of gradual programs: running one is an
   error, reported as such *)
exception Stuck of string
exception Exit_with of int

let check v =
  if Gradual.is_unknown v then raise (Stuck "unk")
  else if Gradual.is_error v then raise (Stuck "raise")
  else v

(* Events: what happens to the unikernel, one JSON object a line after
   "soma-event ", for whoever runs it (soma run, an orchestrator) to read
   rather than parse the console. Running out of memory has none: the
   unikernel aborts before it can say anything. *)
type field = S of string | I of int | B of bool

let json_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (fun c -> match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | c when Char.code c < 32 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"';
  Buffer.contents b

(* --soma-quiet: no event lines, for a program whose console is a stream
   of its own (a terminal's bytes); the exit code still says how it ended *)
let quiet =
  let doc = Cmdliner.Arg.info ~doc:"Print no soma-event lines on the console." [ "soma-quiet" ] in
  Mirage_runtime.register_arg Cmdliner.Arg.(value & flag doc)

let event name fields =
  let value = function S s -> json_string s | I i -> string_of_int i | B b -> string_of_bool b in
  if not (quiet ()) then
  Printf.printf "soma-event {\"event\":%s%s}\n%!" (json_string name)
    (String.concat "" (List.map (fun (k, v) -> "," ^ json_string k ^ ":" ^ value v) fields))

(* A failure, as fields: a failed cast says what was expected and what
   was there (its message is "expected X, but got Y") *)
let failure_fields = function
  | Stuck what -> ["kind", S (if what = "unk" then "unknown" else "raise")]
  | Gradual.Cast_error msg | Soma_wasm.Failed msg ->
    let sep = ", but got " in
    let rec find i =
      if i + String.length sep > String.length msg then None
      else if String.sub msg i (String.length sep) = sep then Some i else find (i + 1) in
    let parts = match find 0 with
      | Some i when String.length msg > 9 && String.sub msg 0 9 = "expected " ->
        let after = i + String.length sep in
        ["expected", S (String.sub msg 9 (i - 9));
         "actual", S (String.sub msg after (String.length msg - after))]
      | _ -> [] in
    ("kind", S "cast") :: ("message", S msg) :: parts
  | Stack_overflow -> ["kind", S "stack_overflow"]
  | Out_of_memory -> ["kind", S "out_of_memory"]
  | e -> ["kind", S "exception"; "message", S (Printexc.to_string e)]

(* [during] is "main", or "request" for an error answering a request, which
   the server goes on after *)
let report ?(during = "main") e =
  (match e with
   | Stuck what -> Printf.printf "Run-time error: the program reached %s.\n%!" what
   | Gradual.Cast_error msg | Soma_wasm.Failed msg -> Printf.printf "Run-time error: %s.\n%!" msg
   | e -> Printf.printf "Run-time error: %s.\n%!" (Printexc.to_string e));
  event "failure" (("during", S during) :: failure_fields e)

(* What [fetch] gets (Sandbox.fetched): extracted, it has the
   representation of [fetched_value], with the image's string (OCaml's)
   for the reply *)
type fetched = Got of string | Net_refused | Net_timed_out | Net_bad_address
type fetched_value = Reply of string | Refused | TimedOut | BadAddress

(* What [resolve] and [https] get (Sandbox.resolved, answered), as
   extracted *)
type resolved_value = Resolved of string | Unresolved of string
type answered_value = Answer of int * (string * string) list * string | Unanswered of string

(* HTTP/1.1 for [https], over whatever carries it (TLS, in the image):
   the request's bytes, and the answer read from all the bytes the server
   sent before it closed. No network here: these are pure. *)
let has_line_break s = String.contains s '\r' || String.contains s '\n'

let http_request verb host port path headers body =
  let lower = String.lowercase_ascii in
  let set_by_us = ["host"; "connection"; "content-length"] in
  if List.exists has_line_break (verb :: host :: path :: List.concat_map (fun (k, v) -> [k; v]) headers)
     || String.contains verb ' ' || String.contains path ' ' then
    Error "a request's verb, path or header has a space or a line break where it can't"
  else if verb = "" then Error "a request needs a verb, as GET"
  else
    let path = if path = "" then "/" else path in
    let host_header = if port = 443 then host else host ^ ":" ^ string_of_int port in
    let b = Buffer.create (256 + String.length body) in
    Buffer.add_string b (verb ^ " " ^ path ^ " HTTP/1.1\r\nHost: " ^ host_header ^ "\r\nConnection: close\r\n");
    if body <> "" || List.mem verb ["POST"; "PUT"; "PATCH"] then
      Buffer.add_string b ("Content-Length: " ^ string_of_int (String.length body) ^ "\r\n");
    List.iter (fun (k, v) ->
        if not (List.mem (lower k) set_by_us) then Buffer.add_string b (k ^ ": " ^ v ^ "\r\n")) headers;
    if not (List.exists (fun (k, _) -> lower k = "user-agent") headers) then
      Buffer.add_string b "User-Agent: soma\r\n";
    Buffer.add_string b "\r\n";
    Buffer.add_string b body;
    Ok (Buffer.contents b)

let find_from s sub from =
  let n = String.length s and k = String.length sub in
  let rec go i = if i + k > n then None else if String.sub s i k = sub then Some i else go (i + 1) in
  go from

(* a chunked body's chunks, joined *)
let dechunk s =
  let b = Buffer.create (String.length s) in
  let rec go i =
    match find_from s "\r\n" i with
    | None -> Error "a chunked body ends inside a chunk's size"
    | Some j ->
      let size = String.sub s i (j - i) in
      let size = match String.index_opt size ';' with Some k -> String.sub size 0 k | None -> size in
      match int_of_string_opt ("0x" ^ String.trim size) with
      | None -> Error ("a chunk's size isn't hexadecimal: " ^ size)
      | Some 0 -> Ok (Buffer.contents b)
      | Some n when n < 0 || j + 2 + n > String.length s -> Error "a chunked body ends inside a chunk"
      | Some n -> Buffer.add_string b (String.sub s (j + 2) n); go (j + 2 + n + 2)
  in
  go 0

let http_answer raw =
  match find_from raw "\r\n\r\n" 0 with
  | None -> Error (if raw = "" then "the server closed without answering" else "the answer has no end to its headers")
  | Some i ->
    let head = String.sub raw 0 i and rest = String.sub raw (i + 4) (String.length raw - i - 4) in
    let trim_cr l = if l <> "" && l.[String.length l - 1] = '\r' then String.sub l 0 (String.length l - 1) else l in
    match List.map trim_cr (String.split_on_char '\n' head) with
    | [] -> Error "an empty answer"
    | status_line :: lines ->
      match String.split_on_char ' ' status_line with
      | version :: code :: _ when String.length version >= 5 && String.sub version 0 5 = "HTTP/" ->
        (match int_of_string_opt code with
         | None -> Error ("not an HTTP status: " ^ status_line)
         | Some status ->
           let headers = List.filter_map (fun l -> match String.index_opt l ':' with
               | Some j -> Some (String.lowercase_ascii (String.trim (String.sub l 0 j)),
                                 String.trim (String.sub l (j + 1) (String.length l - j - 1)))
               | None -> None) lines in
           let value k = List.assoc_opt k headers in
           let chunked = match value "transfer-encoding" with
             | Some te -> find_from (String.lowercase_ascii te) "chunked" 0 <> None | None -> false in
           let body =
             if chunked then dechunk rest
             else match Option.bind (value "content-length") (fun n -> int_of_string_opt (String.trim n)) with
               | Some n when n >= 0 && n <= String.length rest -> Ok (String.sub rest 0 n)
               | Some _ -> Error "the body is shorter than its Content-Length"
               | None -> Ok rest in
           Result.map (fun body -> (status, headers, body)) body)
      | _ -> Error ("not an HTTP answer: " ^ String.sub status_line 0 (min 80 (String.length status_line)))

(* Links (Sandbox.connection, connected, received, sent): the image knows
   a connection by its number. Extracted, [connected], [received] and
   [sent] have the representations of the [_value] types. *)
type link = Link of int | Link_refused | Link_timed_out | Link_bad_address
type connected_value = Connected of Obj.t | ConnectRefused | ConnectTimedOut | ConnectBadAddress
type received_value = Line of string | Closed
type sent_value = Sent | SendClosed
(* What [receive_frame] gets (Sandbox.framed), and its representation *)
type frame = Got_frame of string | Frame_closed | Frame_timed_out | Frame_too_large
type framed_value = Frame of string | FrameClosed | FrameTimedOut | FrameTooLarge
(* What a mailbox connection did (Sandbox.link_event), by its number, and
   the representation of link_event *)
type mail = Mail_opened of int * string | Mail_bytes of int * string | Mail_closed of int
type link_event_value = LinkOpened of Obj.t * string | LinkBytes of Obj.t * string | LinkClosed of Obj.t
(* What came in, for [select] and [mailbox] (Sandbox.event), and the
   representation of event *)
type incoming = In_mail of mail | In_datagram of int * string * int * string | In_timer of int
type event_value = Linked of Obj.t | Datagram of int * string * int * string | Timer of int
(* What [receive] gets, and the representation of Sandbox.chunk *)
type raw = Got_bytes of string | Raw_closed | Raw_timed_out
type chunk_value = Chunk of string | ChunkClosed | ChunkTimedOut

(* Framing, as Soma.Wire's take_line and take_frame (Sandbox exports it): the first message of
   what a connection has received, and the rest, which is kept for the
   next receive. No network: these are pure. *)
(* The decoder is extracted from Soma.Wire with the program, rather than
   reimplemented here. Standard options avoid relying on extracted names
   for the frame_step constructors. *)
let take_line = Prog.soma_wire_take_line
let take_frame s =
  match Prog.soma_wire_take_frame s with
  | None -> `Need_more
  | Some None -> `Oversized
  | Some (Some (data, rest)) -> `Whole (data, rest)

(* What the network provides; without a network stack, [serve], [fetch],
   [listen] and [connect] are not reached (a program that uses them gets
   one) *)
type net = {
  serve : int -> (string -> string Lwt.t) -> unit;
  fetch : string -> int -> string -> fetched Lwt.t;
  listen : int -> (int -> unit Lwt.t) -> unit;
  connect : string -> int -> link Lwt.t;
  (* connect, giving up when the promise the function gives resolves *)
  connect_within : string -> int -> (unit -> unit Lwt.t) -> link Lwt.t;
  send : int -> string -> bool Lwt.t;
  receive_line : int -> string option Lwt.t;
  (* the connection, and the seconds to wait at most (0: no limit) *)
  receive_frame : int -> int -> frame Lwt.t;
  (* the connection, and when to give up: [None], never *)
  receive : int -> (unit -> unit Lwt.t) option -> raw Lwt.t;
  (* the unikernel's IPv4 address, if it has one *)
  local_address : unit -> string option;
  close : int -> unit Lwt.t;
  (* accept on a port, what the connections do posted as incoming *)
  listen_mailbox : int -> unit;
  (* a connection's bytes and end posted as incoming *)
  watch : int -> unit;
  (* datagrams to a port posted as incoming; one sent: address, port,
     source port (0: any), data *)
  udp_listen : int -> unit;
  udp_send : string -> int -> int -> string -> bool Lwt.t;
  (* a host name's IPv4 address, or why there is none *)
  resolve : string -> (string, string) result Lwt.t;
  (* an HTTPS request: verb, host, port, path, headers, body; the status,
     headers and body, or why there are none *)
  https : string -> string -> int -> string -> (string * string) list -> string ->
    (int * (string * string) list * string, string) result Lwt.t;
}

let no_network =
  let fail () = failwith "this unikernel has no network" in
  { serve = (fun _ _ -> fail ()); fetch = (fun _ _ _ -> fail ());
    listen = (fun _ _ -> fail ()); connect = (fun _ _ -> fail ()); connect_within = (fun _ _ _ -> fail ());
    send = (fun _ _ -> fail ()); receive_line = (fun _ -> fail ());
    receive_frame = (fun _ _ -> fail ());
    receive = (fun _ _ -> fail ()); local_address = (fun _ -> fail ());
    close = (fun _ -> fail ());
    listen_mailbox = (fun _ -> fail ()); watch = (fun _ -> fail ());
    udp_listen = (fun _ -> fail ()); udp_send = (fun _ _ _ _ -> fail ());
    resolve = (fun _ -> fail ()); https = (fun _ _ _ _ _ _ -> fail ()) }

(* What came in, oldest first, for [select] (all of it) and [mailbox]
   (connections' only), and a condition to wait on for more *)
let incoming : incoming Queue.t = Queue.create ()
let came : unit Lwt_condition.t = Lwt_condition.create ()
let post_incoming x = Queue.push x incoming; Lwt_condition.broadcast came ()

(* what [keep] takes, oldest first; the rest stays, in order *)
let take_incoming keep =
  let taken, left = List.partition keep (List.of_seq (Queue.to_seq incoming)) in
  Queue.clear incoming;
  List.iter (fun x -> Queue.push x incoming) left;
  taken

(* what [keep] takes, waiting for some until [give_up] resolves at most:
   its time runs from the call, whatever else comes in meanwhile *)
let wait_incoming keep give_up =
  let has () = Queue.fold (fun found x -> found || keep x) false incoming in
  if has () then Lwt.return (take_incoming keep)
  else begin
    let deadline = give_up () >|= fun () -> `Up in
    let rec loop () =
      Lwt.choose [ (Lwt_condition.wait came >|= fun () -> `Came); deadline ] >>= function
      | `Came -> if has () then Lwt.return_unit else loop ()
      | `Up -> Lwt.return_unit in
    loop () >|= fun () -> Lwt.cancel deadline; take_incoming keep
  end

(* a connection's number, and the connection of a number *)
let link_id (c : Prog.connection) = int_of_nat (check c)
let connection_of (id : int) : Prog.connection = nat_of_int id

(* --arg=..., any number of times, in order *)
let args =
  let doc = Cmdliner.Arg.info ~doc:"An argument for the program, in order." [ "arg" ] in
  Mirage_runtime.register_arg Cmdliner.Arg.(value & opt_all string [] doc)

(* --soma-stats: every 2 seconds, what the unikernel holds, for whoever
   runs it to watch *)
let stats =
  let doc = Cmdliner.Arg.info ~doc:"Print what the unikernel holds every 2 seconds." [ "soma-stats" ] in
  Mirage_runtime.register_arg Cmdliner.Arg.(value & flag doc)

let served = ref 0
let open_connections = ref 0

let kb words = words * (Sys.word_size / 8) / 1024

(* memory is the unikernel's whole heap, network buffers included (they
   are outside OCaml's); ocaml_heap is OCaml's part of it *)
let print_stats () =
  let g = Gc.quick_stat () in
  let m = Solo5_os.Memory.stat () in
  Printf.printf "soma-stats: requests=%d open=%d memory=%dKB live=%dKB free=%dKB ocaml_heap=%dKB major_collections=%d\n%!"
    !served !open_connections (kb m.Solo5_os.Memory.heap_words) (kb m.Solo5_os.Memory.live_words)
    (kb m.Solo5_os.Memory.free_words) (kb g.Gc.heap_words) g.Gc.major_collections

let random bound =
  if bound <= 0 then 0
  else
    let bytes = Mirage_crypto_rng.generate 8 in
    (Int64.to_int (String.get_int64_le bytes 0) land max_int) mod bound

(* [wall_clock]: Ptime's span since the epoch, days and picoseconds into
   the day, as seconds and the nanoseconds past them *)
let seconds_and_ns (days, ps) =
  (days * 86_400 + Int64.to_int (Int64.div ps 1_000_000_000_000L),
   Int64.to_int (Int64.div (Int64.rem ps 1_000_000_000_000L) 1_000L))

(* [monotonic_ns]: Mirage_mtime's unsigned nanoseconds, in OCaml's int
   (which Rocq's primitive int is in the image), the top bit dropped *)
let ns_of_elapsed (ns : int64) = Int64.to_int ns land max_int

(* Binary numbers crossing the runtime boundary, without unary nats. *)
let rec positive_of_int64 n =
  if n = 1L then Prog.XH
  else
    let half = positive_of_int64 (Int64.shift_right_logical n 1) in
    if Int64.logand n 1L = 0L then Prog.XO half else Prog.XI half

let n_of_int64 n = if n = 0L then Prog.N0 else Prog.Npos (positive_of_int64 n)

let milliseconds_of_ns ns = Int64.unsigned_div ns 1_000_000L

(* Only convert a duration when multiplying by 1,000,000 fits in int64.
   Larger binary durations are split in half, slept twice, with one extra
   millisecond for an odd value. No duration is truncated or wrapped. *)
let rec small_positive_ms p =
  match check p with
  | Prog.XH -> Some 1L
  | Prog.XO q | Prog.XI q ->
      match small_positive_ms q with
      | Some n when n <= 4_611_686_018_426L ->
          Some (Int64.add (Int64.mul 2L n)
                  (match p with Prog.XI _ -> 1L | _ -> 0L))
      | _ -> None

let rec sleep_positive_ms p =
  match small_positive_ms p with
  | Some ms -> Mirage_sleep.ns (Int64.mul ms 1_000_000L)
  | None ->
      match check p with
      | Prog.XO q -> sleep_positive_ms q >>= fun () -> sleep_positive_ms q
      | Prog.XI q ->
          sleep_positive_ms q >>= fun () -> sleep_positive_ms q >>= fun () ->
          Mirage_sleep.ns 1_000_000L
      | Prog.XH -> assert false

let sleep_milliseconds n =
  match check n with
  | Prog.N0 -> Mirage_sleep.ns 0L
  | Prog.Npos p -> sleep_positive_ms p

(* The extracted [io] is an OCaml variant whose indices are erased: the
   value an action returns is built with [Obj.repr], at the type the
   program gives the action. [option] and pairs have OCaml's
   representation. *)
type storage = { read : string -> string option Lwt.t;
                 write : string -> string -> unit Lwt.t;
                 append : string -> string -> unit Lwt.t }
let storage = ref { read=(fun _ -> failwith "Sandbox storage: no device");
                    write=(fun _ _ -> failwith "Sandbox storage: no device");
                    append=(fun _ _ -> failwith "Sandbox storage: no device") }
let install_storage s = storage := s

(* Named disks (disk_info, disk_read, disk_write), installed by the
   unikernel for each block device the program names: sector size and
   count; sectors from one on; data written from a sector *)
type disk = {
  info : unit -> (int * int) Lwt.t;
  read : int -> int -> string option Lwt.t;
  write : int -> string -> bool Lwt.t;
}
let disks : (string, disk) Hashtbl.t = Hashtbl.create 3
let install_disk name d = Hashtbl.replace disks name d

let link_event_of = function
  | Mail_opened (id, host) -> LinkOpened (Obj.repr (connection_of id), chars_of_string host)
  | Mail_bytes (id, data) -> LinkBytes (Obj.repr (connection_of id), chars_of_string data)
  | Mail_closed id -> LinkClosed (Obj.repr (connection_of id))

let event_of = function
  | In_mail m -> Linked (Obj.repr (link_event_of m))
  | In_datagram (port, host, source_port, data) ->
      Datagram (nat_of_int port, chars_of_string host, nat_of_int source_port, chars_of_string data)
  | In_timer tag -> Timer (nat_of_int tag)

let rec run : 'a. net -> 'a Prog.io -> 'a Lwt.t = fun net m ->
  match check m with
  | Prog.Ret a -> Lwt.return a
  | Prog.Bind (m, k) -> run net m >>= fun x -> run net (k x)
  | Prog.Print s ->
      print_string (string_of_chars (check s) ^ "\n");
      flush stdout;
      Lwt.return (Obj.magic ())
  | Prog.Sleep n ->
      Mirage_sleep.ns (Duration.of_sec (int_of_nat (check n))) >|= Obj.magic
  | Prog.Monotonic_ms ->
      Lwt.return (Obj.magic (n_of_int64 (milliseconds_of_ns (Mirage_mtime.elapsed_ns ()))))
  | Prog.Sleep_ms n -> sleep_milliseconds n >|= Obj.magic
  | Prog.Forever body ->
      let rec loop () = run net body >>= loop in
      loop ()
  | Prog.Iterate (step, start) ->
      let rec loop s = run net (step s) >>= loop in
      loop start
  | Prog.Now ->
      let _, ((h, m, s), _) = Ptime.to_date_time (Mirage_ptime.now ()) in
      Lwt.return (Obj.magic ((nat_of_int h, nat_of_int m), nat_of_int s))
  | Prog.Random bound ->
      Lwt.return (Obj.magic (nat_of_int (random (int_of_nat (check bound)))))
  | Prog.Random_bytes n ->
      Lwt.return (Obj.magic (chars_of_string (Mirage_crypto_rng.generate (int_of_nat (check n)))))
  | Prog.Write s ->
      print_string (string_of_chars (check s));
      flush stdout;
      Lwt.return (Obj.magic ())
  | Prog.Monotonic_ns ->
      Lwt.return (Obj.magic (ns_of_elapsed (Mirage_mtime.elapsed_ns ())))
  | Prog.Wall_clock ->
      Lwt.return (Obj.magic (seconds_and_ns (Ptime.Span.to_d_ps (Ptime.to_span (Mirage_ptime.now ())))))
  | Prog.Call f -> Lwt.return (Obj.magic ((check f) ()))
  | Prog.Args -> Lwt.return (Obj.magic (List.map chars_of_string (args ())))
  | Prog.Exit code -> raise (Exit_with (int_of_nat (check code)))
  | Prog.Serve (port, handler) ->
      net.serve (int_of_nat (check port)) (fun request ->
          run net (handler (chars_of_string request)) >|= fun response ->
          string_of_chars (check response));
      Lwt.return (Obj.magic ())
  | Prog.Fetch (address, port, request) ->
      net.fetch (string_of_chars (check address)) (int_of_nat (check port))
        (string_of_chars (check request))
      >|= fun reply -> Obj.magic (match reply with
          | Got s -> Reply (chars_of_string s)
          | Net_refused -> Refused
          | Net_timed_out -> TimedOut
          | Net_bad_address -> BadAddress)
  | Prog.Resolve host ->
      net.resolve (string_of_chars (check host))
      >|= fun r -> Obj.magic (match r with
          | Ok address -> Resolved (chars_of_string address)
          | Error why -> Unresolved (chars_of_string why))
  | Prog.Https (verb, host, port, path, headers, body) ->
      let s x = string_of_chars (check x) in
      net.https (s verb) (s host) (int_of_nat (check port)) (s path)
        (List.map (fun kv -> let (k, v) = check kv in (s k, s v)) (check headers)) (s body)
      >|= fun r -> Obj.magic (match r with
          | Ok (status, headers, body) ->
            Answer (nat_of_int status, List.map (fun (k, v) -> (chars_of_string k, chars_of_string v)) headers,
                    chars_of_string body)
          | Error why -> Unanswered (chars_of_string why))
  | Prog.Listen (port, handler) ->
      net.listen (int_of_nat (check port)) (fun id -> run net (handler (connection_of id)));
      Lwt.return (Obj.magic ())
  | Prog.Connect (address, port) ->
      net.connect (string_of_chars (check address)) (int_of_nat (check port))
      >|= fun link -> Obj.magic (match link with
          | Link id -> Connected (Obj.repr (connection_of id))
          | Link_refused -> ConnectRefused
          | Link_timed_out -> ConnectTimedOut
          | Link_bad_address -> ConnectBadAddress)
  | Prog.Connect_within (address, port, ms) ->
      net.connect_within (string_of_chars (check address)) (int_of_nat (check port))
        (fun () -> sleep_milliseconds ms)
      >|= fun link -> Obj.magic (match link with
          | Link id -> Connected (Obj.repr (connection_of id))
          | Link_refused -> ConnectRefused
          | Link_timed_out -> ConnectTimedOut
          | Link_bad_address -> ConnectBadAddress)
  | Prog.Send (c, data) ->
      net.send (link_id c) (string_of_chars (check data))
      >|= fun ok -> Obj.magic (if ok then Sent else SendClosed)
  | Prog.Receive_line c ->
      net.receive_line (link_id c)
      >|= fun line -> Obj.magic (match line with
          | Some l -> Line (chars_of_string l)
          | None -> Closed)
  | Prog.Receive_frame (c, seconds) ->
      net.receive_frame (link_id c) (int_of_nat (check seconds))
      >|= fun f -> Obj.magic (match f with
          | Got_frame data -> Frame (chars_of_string data)
          | Frame_closed -> FrameClosed
          | Frame_timed_out -> FrameTimedOut
          | Frame_too_large -> FrameTooLarge)
  | Prog.Receive (c, ms) ->
      let give_up = match check ms with
        | Prog.N0 -> None
        | Prog.Npos _ -> Some (fun () -> sleep_milliseconds ms) in
      net.receive (link_id c) give_up
      >|= fun r -> Obj.magic (match r with
          | Got_bytes data -> Chunk (chars_of_string data)
          | Raw_closed -> ChunkClosed
          | Raw_timed_out -> ChunkTimedOut)
  | Prog.Local_address ->
      Lwt.return (Obj.magic (Option.map chars_of_string (net.local_address ())))
  | Prog.Close c -> net.close (link_id c) >|= Obj.magic
  | Prog.Listen_mailbox port ->
      net.listen_mailbox (int_of_nat (check port));
      Lwt.return (Obj.magic ())
  | Prog.Mailbox ms ->
      wait_incoming (function In_mail _ -> true | _ -> false) (fun () -> sleep_milliseconds ms)
      >|= fun got -> Obj.magic (List.filter_map (function
          | In_mail m -> Some (link_event_of m) | _ -> None) got)
  | Prog.Select ms ->
      wait_incoming (fun _ -> true) (fun () -> sleep_milliseconds ms)
      >|= fun got -> Obj.magic (List.map event_of got)
  | Prog.Watch c -> net.watch (link_id c); Lwt.return (Obj.magic ())
  | Prog.After (ms, tag) ->
      let tag = int_of_nat (check tag) in
      Lwt.async (fun () -> sleep_milliseconds ms >|= fun () -> post_incoming (In_timer tag));
      Lwt.return (Obj.magic ())
  | Prog.Udp_listen port -> net.udp_listen (int_of_nat (check port)); Lwt.return (Obj.magic ())
  | Prog.Udp_send (address, port, source_port, data) ->
      net.udp_send (string_of_chars (check address)) (int_of_nat (check port))
        (int_of_nat (check source_port)) (string_of_chars (check data)) >|= Obj.magic
  | Prog.Disk_info name ->
      (match Hashtbl.find_opt disks (string_of_chars (check name)) with
       | None -> Lwt.return None
       | Some d -> d.info () >|= fun (size, count) -> Some (nat_of_int size, nat_of_int count))
      >|= Obj.magic
  | Prog.Disk_read (name, sector, count) ->
      (match Hashtbl.find_opt disks (string_of_chars (check name)) with
       | None -> Lwt.return None
       | Some d ->
           d.read (int_of_nat (check sector)) (int_of_nat (check count)) >|= Option.map chars_of_string)
      >|= Obj.magic
  | Prog.Disk_write (name, sector, data) ->
      (match Hashtbl.find_opt disks (string_of_chars (check name)) with
       | None -> Lwt.return false
       | Some d -> d.write (int_of_nat (check sector)) (string_of_chars (check data)))
      >|= Obj.magic
  | Prog.Read_file name ->
      (!storage).read (string_of_chars (check name)) >|= fun value ->
      Obj.magic (Option.map chars_of_string value)
  | Prog.Write_file (name, data) ->
      (!storage).write (string_of_chars (check name)) (string_of_chars (check data)) >|= Obj.magic
  | Prog.Append_file (name, data) ->
      (!storage).append (string_of_chars (check name)) (string_of_chars (check data)) >|= Obj.magic

(* Runs [main]; [serving] is whether the unikernel goes on once [main] has
   ended. *)
(* Memory is small and bursty: a server's connections leave state that
   TCP keeps for some seconds, and its strings (lists of characters) are
   garbage soon. The collector works harder (space_overhead 40, not 120)
   and the heap is compacted once the requests of a burst are over, so
   that a burst's memory goes back before the next. *)
(* Every 5 seconds: compact after a burst; say when live memory passes 80%
   of the unikernel's (once, until it is back under 60%); and every 10
   seconds, say that the unikernel is alive *)
let tune_memory () =
  Gc.set { (Gc.get ()) with Gc.space_overhead = 40 };
  let last = ref 0 and pressed = ref false and tick = ref 0 in
  Lwt.async (fun () ->
      let rec loop () =
        Mirage_sleep.ns (Duration.of_sec 5) >>= fun () ->
        if !served <> !last && !open_connections = 0 then begin
          last := !served; Gc.compact ()
        end;
        let m = Solo5_os.Memory.stat () in
        let live = m.Solo5_os.Memory.live_words and total = m.Solo5_os.Memory.heap_words in
        if not !pressed && live * 10 > total * 8 then begin
          pressed := true;
          event "memory_pressure" ["live_kb", I (kb live); "memory_kb", I (kb total)]
        end
        else if !pressed && live * 10 < total * 6 then pressed := false;
        incr tick;
        if !tick mod 2 = 0 then
          event "alive" ["requests", I !served; "live_kb", I (kb live)];
        loop () in
      loop ())

let main ~network ~serving net =
  (* Lwt does not catch Stack_overflow and Out_of_memory: what escapes is
     reported here, rather than by OCaml's "Fatal error" *)
  Printexc.set_uncaught_exception_handler (fun e _ ->
      report e; event "exit" ["code", I 1; "reason", S "failure"]; exit 1);
  event "start" ["memory_kb", I (kb (Solo5_os.Memory.stat ()).Solo5_os.Memory.heap_words);
                 "network", B network];
  tune_memory ();
  if stats () then
    Lwt.async (fun () ->
        let rec loop () =
          Mirage_sleep.ns (Duration.of_sec 2) >>= fun () -> print_stats (); loop () in
        loop ());
  Lwt.catch
    (fun () ->
       run net (Prog.soma_main ()) >>= fun () ->
       if serving () then fst (Lwt.wait ()) else Lwt.return_unit)
    (function
      | Exit_with code -> event "exit" ["code", I code; "reason", S "program"]; exit code
      | e -> report e; event "exit" ["code", I 1; "reason", S "failure"]; exit 1)
  >|= fun () -> event "exit" ["code", I 0; "reason", S "finished"]
|soma}

let unikernel_ml_base ~network =
  header ^
  if network then {soma|open Lwt.Infix

module Main (S : Tcpip.Stack.V4V6) = struct
  (* an open link: its flow, what it has received past the last line or
     frame taken, and the read under way *)
  type link = {
    flow : S.TCP.flow;
    pending : Buffer.t;
    mutable reading : bool Lwt.t option;
    (* its bytes are posted as incoming (listen_mailbox, watch) *)
    mutable watched : bool;
  }

  let start s =
    let servers = ref 0 in
    (* a connection's first data is the request; the reply is written back
       and the connection closed. An error in the program is reported, and
       the server goes on. *)
    let serve port handler =
      incr servers;
      Soma_rt.event "serving" ["port", Soma_rt.I port];
      S.TCP.listen (S.tcp s) ~port (fun flow ->
          incr Soma_rt.open_connections;
          incr Soma_rt.served;
          (S.TCP.read flow >>= function
            | Ok (`Data b) ->
                Lwt.catch
                  (fun () ->
                     handler (Cstruct.to_string b) >>= fun reply ->
                     S.TCP.write flow (Cstruct.of_string reply) >|= ignore)
                  (fun e -> Soma_rt.report ~during:"request" e; Lwt.return_unit)
            | _ -> Lwt.return_unit)
          >>= fun () -> S.TCP.close flow >|= fun () -> decr Soma_rt.open_connections)
    in
    (* TCP retries a connection for minutes when nothing answers: give up
       after 10 seconds *)
    let dial_within ip port give_up =
      Lwt.pick [
        (S.TCP.create_connection (S.tcp s) (ip, port) >|= function
          | Ok flow -> `Flow flow
          | Error `Refused -> `Refused
          | Error `Timeout -> `Timeout);
        (give_up () >|= fun () -> `Timeout);
      ]
    in
    let dial ip port = dial_within ip port (fun () -> Mirage_sleep.ns (Duration.of_sec 10)) in
    let fetch address port request =
      match Ipaddr.of_string address with
      | Error _ -> Lwt.return Soma_rt.Net_bad_address
      | Ok ip ->
          dial ip port >>= function
          | `Refused -> Lwt.return Soma_rt.Net_refused
          | `Timeout -> Lwt.return Soma_rt.Net_timed_out
          | `Flow flow ->
              S.TCP.write flow (Cstruct.of_string request) >>= fun _ ->
              let reply = Buffer.create 4096 in
              let rec read () =
                S.TCP.read flow >>= function
                | Ok (`Data b) -> Buffer.add_string reply (Cstruct.to_string b); read ()
                | _ -> S.TCP.close flow >|= fun () -> Soma_rt.Got (Buffer.contents reply)
              in
              read ()
    in
    (* links: the open connections by number, each with what it has
       received past the last line or frame taken, and the read under way,
       if any: a receive that times out leaves it, and the next receive
       waits for it, so that no data is read twice or lost *)
    let links = Hashtbl.create 7 and last_link = ref 0 in
    let register flow =
      incr last_link;
      Hashtbl.replace links !last_link
        { flow; pending = Buffer.create 256; reading = None; watched = false };
      !last_link
    in
    let close id =
      match Hashtbl.find_opt links id with
      | None -> Lwt.return_unit
      | Some l -> Hashtbl.remove links id; S.TCP.close l.flow
    in
    (* the next chunk, added to what is pending: [true], or [false] when
       the connection has ended *)
    let next_chunk l =
      let p = match l.reading with
        | Some p -> p
        | None ->
            let p = S.TCP.read l.flow >|= function
              | Ok (`Data b) -> Buffer.add_string l.pending (Cstruct.to_string b); true
              | _ -> false in
            l.reading <- Some p; p in
      p >|= fun alive ->
      (match l.reading with Some q when q == p -> l.reading <- None | _ -> ());
      alive
    in
    let listen port handler =
      incr servers;
      Soma_rt.event "listening" ["port", Soma_rt.I port];
      S.TCP.listen (S.tcp s) ~port (fun flow ->
          incr Soma_rt.open_connections;
          incr Soma_rt.served;
          let id = register flow in
          Lwt.catch (fun () -> handler id)
            (fun e -> Soma_rt.report ~during:"request" e; Lwt.return_unit)
          >>= fun () -> close id >|= fun () -> decr Soma_rt.open_connections)
    in
    let connect address port =
      match Ipaddr.of_string address with
      | Error _ -> Lwt.return Soma_rt.Link_bad_address
      | Ok ip ->
          dial ip port >|= function
          | `Refused -> Soma_rt.Link_refused
          | `Timeout -> Soma_rt.Link_timed_out
          | `Flow flow -> Soma_rt.Link (register flow)
    in
    let connect_within address port give_up =
      match Ipaddr.of_string address with
      | Error _ -> Lwt.return Soma_rt.Link_bad_address
      | Ok ip ->
          dial_within ip port give_up >|= function
          | `Refused -> Soma_rt.Link_refused
          | `Timeout -> Soma_rt.Link_timed_out
          | `Flow flow -> Soma_rt.Link (register flow)
    in
    let send id data =
      match Hashtbl.find_opt links id with
      | None -> Lwt.return false
      | Some l ->
          S.TCP.write l.flow (Cstruct.of_string data) >>= function
          | Ok () -> Lwt.return true
          | Error _ -> close id >|= fun () -> false
    in
    let keep l rest = Buffer.clear l.pending; Buffer.add_string l.pending rest in
    (* the next line: from what was received already, or else read until a
       line break; the end of the connection first is [None] *)
    let receive_line id =
      match Hashtbl.find_opt links id with
      | None -> Lwt.return None
      | Some l ->
          let rec take () =
            match Soma_rt.take_line (Buffer.contents l.pending) with
            | Some (line, rest) -> keep l rest; Lwt.return (Some line)
            | None ->
                next_chunk l >>= fun alive ->
                if alive then take ()
                else (Buffer.clear l.pending; close id >|= fun () -> None)
          in
          take ()
    in
    (* the next frame, waiting [seconds] at most (0: as long as it takes);
       what arrived of a frame when the time is up stays pending *)
    let receive_frame id seconds =
      match Hashtbl.find_opt links id with
      | None -> Lwt.return Soma_rt.Frame_closed
      | Some l ->
          let deadline =
            if seconds <= 0 then fst (Lwt.wait ())
            else Mirage_sleep.ns (Duration.of_sec seconds) >|= fun () -> `Time_up in
          let rec take () =
            match Soma_rt.take_frame (Buffer.contents l.pending) with
            | `Whole (data, rest) -> keep l rest; Lwt.return (Soma_rt.Got_frame data)
            | `Oversized ->
                Buffer.clear l.pending; close id >|= fun () -> Soma_rt.Frame_too_large
            | `Need_more ->
                Lwt.choose [ (next_chunk l >|= fun alive -> `Chunk alive); deadline ]
                >>= function
                | `Chunk true -> take ()
                | `Chunk false -> Buffer.clear l.pending; close id >|= fun () -> Soma_rt.Frame_closed
                | `Time_up -> Lwt.return Soma_rt.Frame_timed_out
          in
          take ()
    in
    (* what has arrived, all of it, or the next bytes to, waiting until
       [give_up] at most; a read that the time cut short stays under way,
       for the next receive *)
    let receive id give_up =
      match Hashtbl.find_opt links id with
      | None -> Lwt.return Soma_rt.Raw_closed
      | Some l ->
          let take () =
            let data = Buffer.contents l.pending in
            Buffer.clear l.pending;
            Lwt.return (Soma_rt.Got_bytes data) in
          if Buffer.length l.pending > 0 then take ()
          else
            let chunk = next_chunk l >|= fun alive -> `Chunk alive in
            (match give_up with
             | None -> chunk
             | Some g -> Lwt.choose [ chunk; (g () >|= fun () -> `Time_up) ])
            >>= function
            | `Chunk true -> take ()
            | `Chunk false -> close id >|= fun () -> Soma_rt.Raw_closed
            | `Time_up -> Lwt.return Soma_rt.Raw_timed_out
    in
    let local_address () =
      List.find_map (fun prefix ->
          match Ipaddr.Prefix.address prefix with
          | Ipaddr.V4 a -> Some (Ipaddr.V4.to_string a)
          | Ipaddr.V6 _ -> None)
        (S.IP.configured_ips (S.ip s))
    in
    (* a connection's bytes, posted as they come, then its end; a
       connection the program closed posts no end *)
    let pump id =
      let rec read () =
        match Hashtbl.find_opt links id with
        | None -> Lwt.return_unit
        | Some l ->
            next_chunk l >>= fun alive ->
            if alive then begin
              let data = Buffer.contents l.pending in
              Buffer.clear l.pending;
              Soma_rt.post_incoming (Soma_rt.In_mail (Soma_rt.Mail_bytes (id, data)));
              read ()
            end
            else if Hashtbl.mem links id then
              (close id >|= fun () -> Soma_rt.post_incoming (Soma_rt.In_mail (Soma_rt.Mail_closed id)))
            else Lwt.return_unit
      in
      (match Hashtbl.find_opt links id with Some l -> l.watched <- true | None -> ());
      Lwt.catch read (fun e -> Soma_rt.report ~during:"request" e; close id)
    in
    let listen_mailbox port =
      incr servers;
      Soma_rt.event "listening" ["port", Soma_rt.I port; "mailbox", Soma_rt.B true];
      S.TCP.listen (S.tcp s) ~port (fun flow ->
          incr Soma_rt.open_connections;
          incr Soma_rt.served;
          let id = register flow in
          Soma_rt.post_incoming
            (Soma_rt.In_mail (Soma_rt.Mail_opened (id, Ipaddr.to_string (fst (S.TCP.dst flow)))));
          pump id >|= fun () -> decr Soma_rt.open_connections)
    in
    let watch id =
      match Hashtbl.find_opt links id with
      | Some l when not l.watched -> Lwt.async (fun () -> pump id)
      | _ -> ()
    in
    let udp_listen port =
      incr servers;
      Soma_rt.event "listening" ["port", Soma_rt.I port; "udp", Soma_rt.B true];
      S.UDP.listen (S.udp s) ~port (fun ~src ~dst:_ ~src_port buf ->
          Soma_rt.post_incoming
            (Soma_rt.In_datagram (port, Ipaddr.to_string src, src_port, Cstruct.to_string buf));
          Lwt.return_unit)
    in
    let udp_send address port source_port data =
      match Ipaddr.of_string address with
      | Error _ -> Lwt.return false
      | Ok dst ->
          let buf = Cstruct.of_string data in
          (if source_port > 0 then S.UDP.write ~src_port:source_port ~dst ~dst_port:port (S.udp s) buf
           else S.UDP.write ~dst ~dst_port:port (S.udp s) buf)
          >|= Result.is_ok
    in
    (* resolve and https: a web image's (unikernel_ml ~web) *)
    let resolve _ = Lwt.return (Error "this image has no resolver: it was built without resolve or https") in
    let https _ _ _ _ _ _ = Lwt.return (Error "this image has no resolver: it was built without resolve or https") in
    Soma_rt.main ~network:true ~serving:(fun () -> !servers > 0)
      { serve; fetch; listen; connect; connect_within; send; receive_line; receive_frame;
        receive; local_address; close;
        listen_mailbox; watch; udp_listen; udp_send; resolve; https }
end
|soma}
  else {soma|let start () = Soma_rt.main ~network:false ~serving:(fun () -> false) Soma_rt.no_network
|soma}

(* A web image's resolve and https: DNS through MirageOS's dns-client (the
   resolvers DHCP gives), and HTTPS as HTTP/1.1 (Soma_rt.http_request,
   http_answer) over tls-mirage on the stack's TCP, the server's
   certificate checked against the NSS certificate authorities for the
   host name *)
let web_ml = {soma|    let module TLS = Tls_mirage.Make (S.TCP) in
    let host_name host = Result.bind (Domain_name.of_string host) Domain_name.host in
    let within seconds what p =
      Lwt.pick [ p; (Mirage_sleep.ns (Duration.of_sec seconds) >|= fun () ->
                     Error (what ^ ": no answer within " ^ string_of_int seconds ^ " seconds")) ] in
    let address_of name =
      D.gethostbyname dns name >|= function
      | Ok ip -> Ok (Ipaddr.V4.to_string ip)
      | Error (`Msg m) -> Error m
    in
    let resolve host =
      match host_name host with
      | Error (`Msg m) -> Lwt.return (Error ("not a host name, " ^ host ^ ": " ^ m))
      | Ok name -> within 10 ("resolving " ^ host) (address_of name)
    in
    let authenticator = lazy (Ca_certs_nss.authenticator ()) in
    let limit = 16 * 1024 * 1024 in
    let https verb host port path headers body =
      match host_name host, Soma_rt.http_request verb host port path headers body with
      | Error (`Msg m), _ -> Lwt.return (Error ("not a host name, " ^ host ^ ": " ^ m))
      | _, Error why -> Lwt.return (Error why)
      | Ok name, Ok request ->
        match Lazy.force authenticator with
        | Error (`Msg m) -> Lwt.return (Error ("no certificate authorities: " ^ m))
        | Ok authenticator ->
          match Tls.Config.client ~authenticator ~peer_name:name () with
          | Error (`Msg m) -> Lwt.return (Error ("TLS: " ^ m))
          | Ok config ->
            within 30 ("https " ^ host) (
              within 10 ("resolving " ^ host) (address_of name) >>= function
              | Error why -> Lwt.return (Error why)
              | Ok address ->
                match Ipaddr.of_string address with
                | Error (`Msg m) -> Lwt.return (Error m)
                | Ok ip ->
                  dial ip port >>= function
                  | `Refused -> Lwt.return (Error (host ^ " (" ^ address ^ ") refused the connection"))
                  | `Timeout -> Lwt.return (Error (host ^ " (" ^ address ^ ") didn't answer within 10 seconds"))
                  | `Flow flow ->
                    incr Soma_rt.open_connections;
                    let finish r = decr Soma_rt.open_connections; r in
                    TLS.client_of_flow config ~host:name flow >>= function
                    | Error e ->
                      S.TCP.close flow >|= fun () ->
                      finish (Error (Format.asprintf "TLS with %s: %a" host TLS.pp_write_error e))
                    | Ok tls ->
                      TLS.write tls (Cstruct.of_string request) >>= function
                      | Error e ->
                        TLS.close tls >|= fun () ->
                        finish (Error (Format.asprintf "sending to %s: %a" host TLS.pp_write_error e))
                      | Ok () ->
                        let answer = Buffer.create 8192 in
                        let rec read () =
                          if Buffer.length answer > limit then
                            Lwt.return (Error (host ^ "'s answer is over 16 MB"))
                          else
                            TLS.read tls >>= function
                            | Ok (`Data b) -> Buffer.add_string answer (Cstruct.to_string b); read ()
                            | Ok `Eof -> Lwt.return (Ok ())
                            (* a server that ends without TLS's close_notify
                               has still sent what it sent *)
                            | Error _ when Buffer.length answer > 0 -> Lwt.return (Ok ())
                            | Error e -> Lwt.return (Error (Format.asprintf "reading from %s: %a" host TLS.pp_error e))
                        in
                        read () >>= fun got ->
                        TLS.close tls >|= fun () ->
                        finish (Result.bind got (fun () -> Soma_rt.http_answer (Buffer.contents answer))))
    in
|soma}

let unikernel_ml ~network ~storage ~web =
  let text = unikernel_ml_base ~network in
  (* a web image: the dns-client device after the stack, and the real
     resolve and https *)
  let text = if not web then text else
      replace_text
        (replace_text
           (replace_text text "    let resolve _ = Lwt.return (Error \"this image has no resolver: it was built without resolve or https\") in\n" "")
           "    let https _ _ _ _ _ _ = Lwt.return (Error \"this image has no resolver: it was built without resolve or https\") in\n" web_ml)
        "module Main (S : Tcpip.Stack.V4V6) = struct" "module Main (S : Tcpip.Stack.V4V6) (D : Dns_client_mirage.S) = struct" in
  let text = if not web then text else replace_text text "let start s =" "let start s dns =" in
  if not storage then text else
  let setup = "Store.connect disk >>= fun files ->\n    Soma_rt.install_storage { read=Store.read files; write=Store.write files; append=Store.append files };\n    " in
  if network then
    replace_text
      (replace_text
         (replace_text text "module Main (S : Tcpip.Stack.V4V6) = struct"
            "module Main (S : Tcpip.Stack.V4V6) (B : Mirage_block.S) = struct\n  module Store = Soma_store.Make(B)")
         "(D : Dns_client_mirage.S) = struct"
         "(D : Dns_client_mirage.S) (B : Mirage_block.S) = struct\n  module Store = Soma_store.Make(B)")
      (if web then "let start s dns =" else "let start s =")
      ((if web then "let start s dns disk =\n    " else "let start s disk =\n    ") ^ setup)
  else header ^ "open Lwt.Infix\nmodule Main (B : Mirage_block.S) = struct\n  module Store = Soma_store.Make(B)\n  let start disk =\n    " ^ setup ^
       "Soma_rt.main ~network:false ~serving:(fun () -> false) Soma_rt.no_network\nend\n"

(* soma_disk.ml: a block device as Soma_rt.disk, sectors checked against
   its size before they reach the device *)
let disk_ml = header ^ {soma|open Lwt.Infix

module Make (B : Mirage_block.S) = struct
  let make (b : B.t) : Soma_rt.disk =
    let info = B.get_info b in
    let fits i sector sectors =
      sector >= 0 && sectors >= 0 &&
      Int64.add (Int64.of_int sector) (Int64.of_int sectors) <= i.Mirage_block.size_sectors in
    let read sector count =
      info >>= fun i ->
      if not (fits i sector count) then Lwt.return None
      else if count = 0 then Lwt.return (Some "")
      else
        let buf = Cstruct.create (count * i.Mirage_block.sector_size) in
        B.read b (Int64.of_int sector) [buf] >|= function
        | Ok () -> Some (Cstruct.to_string buf)
        | Error _ -> None
    in
    let write sector data =
      info >>= fun i ->
      let size = i.Mirage_block.sector_size and n = String.length data in
      if not i.Mirage_block.read_write || n mod size <> 0 || not (fits i sector (n / size)) then
        Lwt.return false
      else if n = 0 then Lwt.return true
      else B.write b (Int64.of_int sector) [Cstruct.of_string data] >|= Result.is_ok
    in
    { Soma_rt.info = (fun () -> info >|= fun i ->
          (i.Mirage_block.sector_size, Int64.to_int i.Mirage_block.size_sectors));
      read; write }
end
|soma}

(* [text] with [old]'s first occurrence at or after [from] replaced *)
let replace_first ?(from = 0) text old replacement =
  let n = String.length old in
  let rec find i =
    if i + n > String.length text then None
    else if String.sub text i n = old then Some i else find (i + 1) in
  match find from with
  | None -> failwith ("Soma: no " ^ old ^ " in a generated file")
  | Some i -> String.sub text 0 i ^ replacement ^ String.sub text (i + n) (String.length text - i - n)

let index_of text sub =
  let n = String.length sub in
  let rec find i =
    if i + n > String.length text then None
    else if String.sub text i n = sub then Some i else find (i + 1) in
  find 0

(* config.ml with a block device for each disk the program names, after
   the other devices: block_of_file NAME, which solo5-hvt attaches as
   --block:NAME=FILE *)
let disks_config disks text =
  if disks = [] then text else
  let blocks = String.concat "" (List.map (fun _ -> "block @-> ") disks) in
  let text =
    if index_of text "main \"Unikernel\" job" <> None then
      replace_text text "main \"Unikernel\" job" ("main \"Unikernel.Main\" (" ^ blocks ^ "job)")
    else replace_first text "job)" (blocks ^ "job)") in
  let text = if index_of text "package \"mirage-block\"" <> None then text else
      replace_text text "package \"duration\""
        "package \"mirage-block\"; package \"cstruct\"; package \"lwt\"; package \"duration\"" in
  let devices = String.concat "" (List.mapi (fun i name ->
      Printf.sprintf "let disk_%d = block_of_file %S\n" i name) disks) in
  let text = replace_text text "let () = register" (devices ^ "let () = register") in
  let applied = String.concat "" (List.mapi (fun i _ -> Printf.sprintf " $ disk_%d" i) disks) in
  match index_of text "let () = register" with
  | None -> failwith "Soma: no register in config.ml"
  | Some at -> replace_first ~from:at text " ]" (applied ^ " ]")

(* unikernel.ml with the disks as the functor's last arguments, each
   installed under its name before the program runs *)
let disks_unikernel disks text =
  if disks = [] then text else
  let params = String.concat "" (List.mapi (fun i _ -> Printf.sprintf " (K%d : Mirage_block.S)" i) disks) in
  let modules = String.concat "" (List.mapi (fun i _ -> Printf.sprintf "\n  module Disk%d = Soma_disk.Make(K%d)" i i) disks) in
  let args = String.concat "" (List.mapi (fun i _ -> Printf.sprintf " disk_%d" i) disks) in
  let installs = String.concat "" (List.mapi (fun i name ->
      Printf.sprintf "\n    Soma_rt.install_disk %S (Disk%d.make disk_%d);" name i i) disks) in
  match index_of text "module Main (" with
  | Some at ->
      let text = replace_first ~from:at text " = struct" (params ^ " = struct" ^ modules) in
      let start = match index_of text "  let start " with
        | Some i -> i | None -> failwith "Soma: no start in unikernel.ml" in
      replace_first ~from:start text " =" (args ^ " =" ^ installs)
  | None ->
      (* no network and no storage: a start without devices *)
      let body = replace_first text "let start () = " "" in
      let body = replace_first body header "" in
      header ^ "open Lwt.Infix\nmodule Main" ^ params ^ " = struct" ^ modules ^
      "\n  let start" ^ args ^ " =" ^ installs ^ "\n    " ^ body ^ "end\n"

(* gradual.ml: the gradual runtime of prog.ml, which extraction only puts
   there when the program has casts, or a stand-in without errors *)
let gradual_ml ~has_casts =
  header ^
  if has_casts then "include Prog.Gradual_rt\n"
  else
    "exception Cast_error of string\n\
     let is_unknown _ = false\n\
     let is_error _ = false\n"

(* soma_wasm.ml: the WebAssembly modules that [main] calls, run by the
   WebAssembly reference interpreter (opam wasm) in the image, with the
   checks of their declared types that Soma makes when it evaluates
   (plugins/soma_wasm): what does not fit raises [Failed], worded as a
   failed cast. Soma's numbers are read and made as extracted in prog.ml,
   which this module cannot name (prog.ml calls it): positive = XI | XO |
   XH, N = N0 | Npos, Z = Z0 | Zpos | Zneg, i64 and i32 a Z, float an
   OCaml float. Without modules, only [Failed]. *)
let wasm_ml modules =
  if modules = [] then header ^ "exception Failed of string\n"
  else header ^ Printf.sprintf {soma|exception Failed of string

(* the modules, by name: their bytes *)
let modules : (string * string) list = [
%s]

let instances = Hashtbl.create 3

let instance name =
  match Hashtbl.find_opt instances name with
  | Some i -> i
  | None ->
    let i = Wasm.Eval.init (Wasm.Decode.decode name (List.assoc name modules)) [] in
    Hashtbl.add instances name i; i

let article k = if String.length k > 0 && String.contains "aeiouAEFHILMNORSX" k.[0] then "an " ^ k else "a " ^ k

(* positives, as Int64s; None when larger than the largest *)
let rec int64_of_positive (o : Obj.t) : int64 option =
  if Obj.is_int o then Some 1L
  else match int64_of_positive (Obj.field o 0) with
    | Some p when p <= Int64.div Int64.max_int 2L ->
      let d = Int64.mul 2L p in
      Some (if Obj.tag o = 0 then Int64.add d 1L else d)
    | _ -> None

let block tag v = let b = Obj.new_block tag 1 in Obj.set_field b 0 v; b

(* a positive from n > 0, read as unsigned *)
let rec positive_of n : Obj.t =
  if n = 1L then Obj.repr 0
  else
    let half = positive_of (Int64.shift_right_logical n 1) in
    if Int64.logand n 1L = 0L then block 1 half else block 0 half

let soma_N n = if n = 0L then Obj.repr 0 else block 0 (positive_of n)
let soma_Z n =
  if n = 0L then Obj.repr 0
  else if n > 0L then block 0 (positive_of n)
  else block 1 (positive_of (Int64.neg n))

let integer_of kind (o : Obj.t) : int64 option =
  if Obj.is_int o then Some 0L
  else match kind, Obj.tag o with
    | "N", _ -> int64_of_positive (Obj.field o 0)
    | _, 0 -> int64_of_positive (Obj.field o 0)
    | _, _ -> Option.map Int64.neg (int64_of_positive (Obj.field o 0))

let to_value (kind, wasm) (o : Obj.t) =
  match wasm with
  | "f64" -> Wasm.Values.Num (Wasm.Values.F64 (Wasm.F64.of_float (Obj.obj o : float)))
  | "f32" -> Wasm.Values.Num (Wasm.Values.F32 (Wasm.F32.of_float (Obj.obj o : float)))
  | _ ->
    match integer_of kind o with
    | None -> raise (Failed (Printf.sprintf "expected %%s, but got %%s too large for one" (article wasm) (article kind)))
    | Some n when wasm = "i32" ->
      if n < Int64.of_int32 Int32.min_int || n > Int64.of_int32 Int32.max_int then
        raise (Failed (Printf.sprintf "expected an i32, but got %%Ld : %%s" n kind));
      Wasm.Values.Num (Wasm.Values.I32 (Int64.to_int32 n))
    | Some n -> Wasm.Values.Num (Wasm.Values.I64 n)

let of_value (kind, wasm) v : Obj.t =
  match v with
  | Wasm.Values.Num (Wasm.Values.F64 x) -> Obj.repr (Wasm.F64.to_float x)
  | Wasm.Values.Num (Wasm.Values.F32 x) -> Obj.repr (Wasm.F32.to_float x)
  | Wasm.Values.Num ((Wasm.Values.I64 _ | Wasm.Values.I32 _) as num) ->
    let n = match num with Wasm.Values.I64 n -> n | Wasm.Values.I32 n -> Int64.of_int32 n | _ -> 0L in
    if kind = "N" && n < 0L then
      raise (Failed (Printf.sprintf "expected an N, but got %%s (%%Ld) : %%s"
                       (String.uppercase_ascii wasm) n wasm));
    if kind = "N" then soma_N n else soma_Z n
  | _ -> raise (Failed ("expected " ^ article kind ^ ", but got a value of another type"))

let call name export params result (args : Obj.t array) : Obj.t =
  let func = match Wasm.Instance.export (instance name) (Wasm.Utf8.decode export) with
    | Some (Wasm.Instance.ExternFunc f) -> f
    | _ -> failwith (name ^ " does not export " ^ export) in
  let values = List.mapi (fun i p -> to_value p args.(i)) params in
  let trapped msg = raise (Failed (Printf.sprintf "expected %%s, but got Trapped %%S : trap" (article (fst result)) msg)) in
  match Wasm.Eval.invoke func values with
  | [r] -> of_value result r
  | _ -> failwith (name ^ "'s " ^ export ^ " did not give one value")
  | exception Wasm.Eval.Trap (_, msg) -> trapped msg
  | exception Wasm.Eval.Exhaustion (_, msg) -> trapped msg
  | exception Wasm.Eval.Crash (_, msg) -> trapped msg
|soma} (String.concat "" (List.map (fun (name, bytes) -> Printf.sprintf "  (%S, %S);\n" name bytes) modules))

(* float64.ml: Rocq's floats in the image, as OCaml's, for the extraction
   commands below (those of ExtrOCamlFloats, but for bool and pairs, which
   stay as extracted; bool is OCaml's) *)
let float64_ml = header ^ {soma|type t = float
let of_float x = x
let to_float x = x
type float_comparison = FEq | FLt | FGt | FNotComparable
type float_class = PNormal | NNormal | PSubn | NSubn | PZero | NZero | PInf | NInf | NaN
let add = ( +. ) and sub = ( -. ) and mul = ( *. ) and div = ( /. )
let sqrt = Float.sqrt and abs = Float.abs and opp x = -. x
let eq (x : float) y = x = y and lt (x : float) y = x < y and le (x : float) y = x <= y
let equal x y = Int64.equal (Int64.bits_of_float x) (Int64.bits_of_float y)
let compare x y = if x < y then FLt else if x > y then FGt else if x = y then FEq else FNotComparable
let classify x =
  match Float.classify_float x with
  | FP_normal -> if x > 0. then PNormal else NNormal
  | FP_subnormal -> if x > 0. then PSubn else NSubn
  | FP_zero -> if 1. /. x > 0. then PZero else NZero
  | FP_infinite -> if x > 0. then PInf else NInf
  | FP_nan -> NaN
let next_up = Float.succ and next_down = Float.pred
(* a float's parts and back, which FloatOps.Prim2SF and SF2Prim read a
   float with (the kernel's kernel/float64_common.ml; [of_uint63] is its C
   stub's: the unsigned 63-bit value, rounded once) *)
let of_uint63 x = Int64.to_float (Uint63.to_uint64 x)
let prec = 53
let normfr_mantissa f =
  let f = abs f in
  if f >= 0.5 && f < 1. then Uint63.of_int (int_of_float (Float.ldexp f prec))
  else Uint63.of_int 0
let eshift = 2101
let frshiftexp f =
  match Float.classify_float f with
  | FP_zero | FP_infinite | FP_nan -> (f, Uint63.of_int 0)
  | FP_normal | FP_subnormal -> let (m, e) = Float.frexp f in (m, Uint63.of_int (e + eshift))
let ldshiftexp f e = Float.ldexp f (Uint63.to_int_min e (2 * eshift) - eshift)
|soma}

(* uint63.ml: Rocq's 63-bit integers in the program, as OCaml's ints, for
   the extraction commands of ExtrOCamlInt63 (a copy of the kernel's
   kernel/uint63_63.ml, without its C stub [to_float]). OCaml's int has 63
   bits on a 64-bit machine, which an image and a binary are; JavaScript's
   has 32, so a page computes them wrong. *)
let uint63_ml = header ^ {soma|type t = int
let uint_size = 63

let maxuint63 = Int64.of_string "0x7FFFFFFFFFFFFFFF"
let maxuint31 = 0x7FFFFFFF

    (* conversion from an int *)
let to_uint64 i = Int64.logand (Int64.of_int i) maxuint63

let of_int i = i
[@@ocaml.inline always]

let to_int2 i = (0,i)

let of_int64 = Int64.to_int
let to_int64 = to_uint64



let hash i = i
[@@ocaml.inline always]

    (* conversion of an uint63 to a string *)
let to_string i = Int64.to_string (to_uint64 i)

(* Compiles an unsigned int to OCaml code *)
let compile i = Printf.sprintf "Uint63.of_int (%i)" i

let zero = 0
let one = 1

    (* logical shift *)
let l_sl x y =
  if 0 <= y && y < 63 then x lsl y else 0

let l_sr x y =
  if 0 <= y && y < 63 then x lsr y else 0

    (* arithmetic shift (for sint63) *)
let a_sr x y =
  if 0 <= y && y < 63 then x asr y
  else if 0 <= x || y < 0 then 0 else -1

let l_and x y = x land y
[@@ocaml.inline always]

let l_or x y = x lor y
[@@ocaml.inline always]

let l_xor x y = x lxor y
[@@ocaml.inline always]

    (* addition of int63 *)
let add x y = x + y
[@@ocaml.inline always]

    (* subtraction *)
let sub x y = x - y
[@@ocaml.inline always]

    (* multiplication *)
let mul x y = x * y
[@@ocaml.inline always]

    (* division *)
let div (x : int) (y : int) =
  if y = 0 then 0 else Int64.to_int (Int64.div (to_uint64 x) (to_uint64 y))

    (* modulo *)
let rem (x : int) (y : int) =
  if y = 0 then x else Int64.to_int (Int64.rem (to_uint64 x) (to_uint64 y))

let diveucl x y = (div x y, rem x y)

    (* signed division *)
let divs (x : int) (y : int) =
  if y = 0 then 0 else x / y

    (* modulo *)
let rems (x : int) (y : int) =
  if y = 0 then x else x mod y

let addmuldiv p x y =
  l_or (l_sl x p) (l_sr y (uint_size - p))

    (* comparison *)
let lt (x : int) (y : int) =
  (x lxor 0x4000000000000000) < (y lxor 0x4000000000000000)
[@@ocaml.inline always]

let le (x : int) (y : int) =
  (x lxor 0x4000000000000000) <= (y lxor 0x4000000000000000)
[@@ocaml.inline always]

    (* signed comparison *)
let lts (x : int) (y : int) =
  x < y
[@@ocaml.inline always]

let les (x : int) (y : int) =
  x <= y
[@@ocaml.inline always]

let to_int_min n m =
  if lt n m then n else m
[@@ocaml.inline always]

    (* division of two numbers by one *)
(* precondition: xh < y *)
(* outputs: q, r s.t. x = q * y + r, r < y *)
let div21 xh xl y =
  (* nh might temporarily grow as large as 2*y - 1 in the loop body,
     so we store it as a 64-bit unsigned integer *)
  let nh = ref xh in
  let nl = ref xl in
  let q = ref 0 in
  for _i = 0 to 62 do
    (* invariants: 0 <= nh < y, nl = (xl*2^i) % 2^63,
       (q*y + nh) * 2^(63-i) + (xl % 2^(63-i)) = (xh%y) * 2^63 + xl *)
    nh := Int64.logor (Int64.shift_left !nh 1) (Int64.of_int (!nl lsr 62));
    nl := !nl lsl 1;
    q := !q lsl 1;
    if Int64.unsigned_compare !nh y >= 0 then
      begin q := !q lor 1; nh := Int64.sub !nh y; end
  done;
  !q, Int64.to_int !nh

let div21 xh xl y =
  let xh = to_uint64 xh in
  let y = to_uint64 y in
  if Int64.compare y xh <= 0 then 0, 0 else div21 xh xl y

     (* exact multiplication *)
(* TODO: check that none of these additions could be a logical or *)


(* size = 32 + 31
   (hx << 31 + lx) * (hy << 31 + ly) =
   hxhy << 62 + (hxly + lxhy) << 31 + lxly
*)

(* precondition : (x lsr 62 = 0 || y lsr 62 = 0) *)
let mulc_aux x y =
  let lx = x land maxuint31 in
  let ly = y land maxuint31 in
  let hx = x lsr 31  in
  let hy = y lsr 31 in
    (* hx and hy are 32 bits value but at most one is 32 *)
  let hxy  = hx * hy in (* 63 bits *)
  let hxly = hx * ly in (* 63 bits *)
  let lxhy = lx * hy in (* 63 bits *)
  let lxy  = lx * ly in (* 62 bits *)
  let l  = lxy lor (hxy lsl 62) (* 63 bits *) in
  let h  = hxy lsr 1 in (* 62 bits *)
  let hl = hxly + lxhy in (* We can have a carry *)
  let h  = if lt hl hxly then h + (1 lsl 31) else h in
  let hl'= hl lsl 31 in
  let l  = l + hl' in
  let h  = if lt l hl' then h + 1 else h in
  let h  = h + (hl lsr 32) in
  (h,l)

let mulc x y =
  if (x lsr 62 = 0 || y lsr 62 = 0) then mulc_aux x y
  else
    let yl = y lxor (1 lsl 62) in
    let (h,l) = mulc_aux x yl in
    (* h << 63 + l = x * yl
       x * y = x * (1 << 62 + yl)  =
       x << 62 + x*yl = x << 62 + h << 63 + l *)
    let l' = l + (x lsl 62) in
    let h = if lt l' l then h + 1 else h in
    (h + (x lsr 1), l')

let equal (x : int) (y : int) = x = y
[@@ocaml.inline always]

let compare (x:int) (y:int) =
  let x = x lxor 0x4000000000000000 in
  let y = y lxor 0x4000000000000000 in
  Int.compare x y

let compares (x : int) (y : int) =
  Int.compare x y

    (* head tail *)

let head0 x =
  let r = ref 0 in
  let x = ref x in
  if !x land 0x7FFFFFFF00000000 = 0 then r := !r + 31
  else x := !x lsr 31;
  if !x land 0xFFFF0000 = 0 then (x := !x lsl 16; r := !r + 16);
  if !x land 0xFF000000 = 0 then (x := !x lsl 8; r := !r + 8);
  if !x land 0xF0000000 = 0 then (x := !x lsl 4; r := !r + 4);
  if !x land 0xC0000000 = 0 then (x := !x lsl 2; r := !r + 2);
  if !x land 0x80000000 = 0 then (x := !x lsl 1; r := !r + 1);
  if !x land 0x80000000 = 0 then (               r := !r + 1);
  !r;;

let tail0 x =
  let r = ref 0 in
  let x = ref x in
  if !x land 0xFFFFFFFF = 0 then (x := !x lsr 32; r := !r + 32);
  if !x land 0xFFFF = 0 then (x := !x lsr 16; r := !r + 16);
  if !x land 0xFF = 0   then (x := !x lsr 8;  r := !r + 8);
  if !x land 0xF = 0    then (x := !x lsr 4;  r := !r + 4);
  if !x land 0x3 = 0    then (x := !x lsr 2;  r := !r + 2);
  if !x land 0x1 = 0    then (                r := !r + 1);
  !r

let is_uint63 t =
  Obj.is_int t
[@@ocaml.inline always]

(* Arithmetic with explicit carries *)

(* Analog of Numbers.Abstract.Cyclic.carry *)
type 'a carry = C0 of 'a | C1 of 'a

let addc x y =
  let r = x + y in
  if lt r x then C1 r else C0 r

let addcarryc x y =
  let r = x + y + 1 in
  if le r x then C1 r else C0 r

let subc x y =
  let r = x - y in
  if le y x then C0 r else C1 r

let subcarryc x y =
  let r = x - y - 1 in
  if lt y x then C0 r else C1 r
|soma}

(* With [nat] as OCaml's [int] (ExtrOcamlNatInt), what ExtrOcamlNatInt
   leaves recursive is OCaml's own: addition, multiplication and
   subtraction (its [plus], [mult] and [minus] are not Nat's add, mul and
   sub here, which counted one at a time: 2^40 overflowed the stack),
   comparisons, division (by zero as
   Rocq's: 0, and the number itself for a remainder), and a string's
   length, a character, a substring and the order of two strings (byte
   by byte, as String.compare's), which count in [nat] or take a string
   apart (walking a native string by its constructors copies what is left
   at each step) *)
let nat_string_extraction = {soma|Extract Inlined Constant Nat.add => "(+)".
Extract Inlined Constant Nat.mul => "( * )".
Extract Inlined Constant Nat.sub => "(fun n m -> Stdlib.max 0 (n - m))".
Extract Inlined Constant Nat.pred => "(fun n -> Stdlib.max 0 (n - 1))".
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.div => "(fun a b -> if b = 0 then 0 else a / b)".
Extract Inlined Constant Nat.modulo => "(fun a b -> if b = 0 then a else a mod b)".
Extract Inlined Constant Stdlib.Strings.String.length => "String.length".
Extract Inlined Constant Stdlib.Strings.String.get =>
  "(fun n s -> if n < String.length s then Some (String.unsafe_get s n) else None)".
Extract Inlined Constant Stdlib.Strings.String.substring =>
  "(fun n m s -> let l = String.length s in if n >= l then """" else String.sub s n (min m (l - n)))".
Extract Inlined Constant Stdlib.Strings.String.compare =>
  "(fun a b -> let c = Stdlib.compare (a : string) b in if c < 0 then Lt else if c = 0 then Eq else Gt)".
|soma}

let float_extraction = {soma|Extract Inductive PrimFloat.float_comparison => "Float64.float_comparison" [ "FEq" "FLt" "FGt" "FNotComparable" ].
Extract Inductive FloatClass.float_class => "Float64.float_class" [ "PNormal" "NNormal" "PSubn" "NSubn" "PZero" "NZero" "PInf" "NInf" "NaN" ].
Extract Constant PrimFloat.float => "Float64.t".
Extract Constant PrimFloat.classify => "Float64.classify".
Extract Constant PrimFloat.abs => "Float64.abs".
Extract Constant PrimFloat.sqrt => "Float64.sqrt".
Extract Constant PrimFloat.opp => "Float64.opp".
Extract Constant PrimFloat.eqb => "Float64.eq".
Extract Constant PrimFloat.ltb => "Float64.lt".
Extract Constant PrimFloat.leb => "Float64.le".
Extract Constant PrimFloat.compare => "Float64.compare".
Extract Constant PrimFloat.Leibniz.eqb => "Float64.equal".
Extract Constant PrimFloat.mul => "Float64.mul".
Extract Constant PrimFloat.add => "Float64.add".
Extract Constant PrimFloat.sub => "Float64.sub".
Extract Constant PrimFloat.div => "Float64.div".
Extract Constant PrimFloat.next_up => "Float64.next_up".
Extract Constant PrimFloat.next_down => "Float64.next_down".
Extract Constant PrimFloat.of_uint63 => "Float64.of_uint63".
Extract Constant PrimFloat.normfr_mantissa => "Float64.normfr_mantissa".
Extract Constant PrimFloat.frshiftexp => "(fun f -> Obj.magic (Float64.frshiftexp f))".
Extract Constant PrimFloat.ldshiftexp => "Float64.ldshiftexp".
Extract Inductive CarryType.carry => "Uint63.carry" [ "Uint63.C0" "Uint63.C1" ].
Extract Constant PrimInt63.int => "Uint63.t".
Extraction Inline PrimInt63.int.
Extract Constant PrimInt63.lsl => "Uint63.l_sl".
Extract Constant PrimInt63.lsr => "Uint63.l_sr".
Extract Constant PrimInt63.asr => "Uint63.a_sr".
Extract Constant PrimInt63.land => "Uint63.l_and".
Extract Constant PrimInt63.lor => "Uint63.l_or".
Extract Constant PrimInt63.lxor => "Uint63.l_xor".
Extract Constant PrimInt63.add => "Uint63.add".
Extract Constant PrimInt63.sub => "Uint63.sub".
Extract Constant PrimInt63.mul => "Uint63.mul".
Extract Constant PrimInt63.mulc => "Uint63.mulc".
Extract Constant PrimInt63.div => "Uint63.div".
Extract Constant PrimInt63.mod => "Uint63.rem".
Extract Constant PrimInt63.divs => "Uint63.divs".
Extract Constant PrimInt63.mods => "Uint63.rems".
Extract Constant PrimInt63.eqb => "Uint63.equal".
Extract Constant PrimInt63.ltb => "Uint63.lt".
Extract Constant PrimInt63.leb => "Uint63.le".
Extract Constant PrimInt63.ltsb => "Uint63.lts".
Extract Constant PrimInt63.lesb => "Uint63.les".
Extract Constant PrimInt63.addc => "Uint63.addc".
Extract Constant PrimInt63.addcarryc => "Uint63.addcarryc".
Extract Constant PrimInt63.subc => "Uint63.subc".
Extract Constant PrimInt63.subcarryc => "Uint63.subcarryc".
Extract Constant PrimInt63.diveucl => "Uint63.diveucl".
Extract Constant PrimInt63.diveucl_21 => "Uint63.div21".
Extract Constant PrimInt63.addmuldiv => "Uint63.addmuldiv".
Extract Constant PrimInt63.compare => "(fun x y -> let c = Uint63.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".
Extract Constant PrimInt63.compares => "(fun x y -> let c = Uint63.compares x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".
Extract Constant PrimInt63.head0 => "Uint63.head0".
Extract Constant PrimInt63.tail0 => "Uint63.tail0".
|soma}

let contains s sub =
  let n = String.length sub in
  let rec at i = i + n <= String.length s && (String.sub s i n = sub || at (i + 1)) in
  at 0

(* Whether the extracted program uses [serve], [fetch], [listen],
   [connect] or [local_address]: a constructor applied, as opposed to its declaration in
   [type 'x io]. ([send], [receive_line] and [close] need a connection,
   which only [listen] and [connect] give.) *)
let is_ident_char ch =
  match ch with 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> true | _ -> false

(* A constructor applied: its name, then "(" after any spaces or line
   breaks (extraction may break the line between them:
   [Listen\n    ((of_num_uint ...), greet)]). *)
let applied prog c =
  let n = String.length prog and k = String.length c in
  let rec from i =
    if i + k > n then false
    else if String.sub prog i k = c && (i = 0 || not (is_ident_char prog.[i - 1])) then
      let rec skip j = if j < n && (prog.[j] = ' ' || prog.[j] = '\n') then skip (j + 1) else j in
      let j = skip (i + k) in
      (j < n && prog.[j] = '(') || from (i + 1)
    else from (i + 1) in
  from 0

(* A constructor without arguments used: its name as a word, but not its
   declaration in [type 'x io] ([| Local_address]) *)
let used_constant prog c =
  let n = String.length prog and k = String.length c in
  let rec from i =
    if i + k > n then false
    else if String.sub prog i k = c && (i = 0 || not (is_ident_char prog.[i - 1]))
            && (i + k = n || not (is_ident_char prog.[i + k])) then
      let rec back j = if j >= 0 && (prog.[j] = ' ' || prog.[j] = '\n') then back (j - 1) else j in
      let j = back (i - 1) in
      (j < 0 || prog.[j] <> '|') || from (i + 1)
    else from (i + 1) in
  from 0

let uses_network prog =
  List.exists (applied prog) ["Serve"; "Fetch"; "Listen"; "Connect"; "Connect_within"; "Listen_mailbox"; "Mailbox";
                              "Watch"; "Udp_listen"; "Udp_send"]
  || used_constant prog "Local_address"

(* [resolve] and [https] need DNS and TLS: a web image, with a network.
   The constructor as a word, applied to anything (extraction writes
   [Resolve host] with no parenthesis), but not its declaration ([Resolve
   of ...]) *)
let mentions prog c =
  let n = String.length prog and k = String.length c in
  let rec from i =
    if i + k > n then false
    else if String.sub prog i k = c && (i = 0 || not (is_ident_char prog.[i - 1]))
            && (i + k = n || not (is_ident_char prog.[i + k]))
            && not (i + k + 4 <= n && String.sub prog (i + k) 4 = " of ") then true
    else from (i + 1) in
  from 0

let uses_web prog = List.exists (mentions prog) ["Resolve"; "Https"]

(* the disks the program names: the string literal each disk action is
   applied to, sorted, so that the project's name does not depend on the
   order the extracted program names them in *)
let disk_names prog =
  let n = String.length prog in
  let names = ref [] in
  List.iter (fun c ->
      let k = String.length c in
      let rec from i =
        if i + k <= n then begin
          if String.sub prog i k = c && (i = 0 || not (is_ident_char prog.[i - 1]))
             && (i + k = n || not (is_ident_char prog.[i + k])) then begin
            let rec skip j = if j < n && (prog.[j] = ' ' || prog.[j] = '\n' || prog.[j] = '(') then skip (j + 1) else j in
            let j = skip (i + k) in
            if i + k + 4 <= n && String.sub prog (i + k) 4 = " of " then ()
            else if j < n && prog.[j] = '"' then begin
              match String.index_from_opt prog (j + 1) '"' with
              | Some e -> let name = String.sub prog (j + 1) (e - j - 1) in
                if not (List.mem name !names) then names := !names @ [name]
              | None -> ()
            end
            else
              error Pp.(str c ++ str "'s disk is not a string literal in the extracted program: " ++
                        str "name a disk with one, as in disk_read \"rootfs\" 0 8, " ++
                        str "since the image declares each disk when it is built.")
          end;
          from (i + 1)
        end in
      from 0) ["Disk_info"; "Disk_read"; "Disk_write"];
  List.iter (fun name ->
      if name = "" || String.length name > 31 ||
         not (String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' -> true | _ -> false) name) then
        error Pp.(str "disk name " ++ qstring name ++ str ": a disk is named with 1 to 31 letters and digits.");
      if name = "storage" then
        error Pp.(str "disk name \"storage\" is the named files' device (read_file, write_file); " ++
                  str "give the disk another name.")) !names;
  List.sort_uniq compare !names


(* Extracts [main] into [dir]/prog.ml, by running the extraction commands
   at the end of the program, after its .vo has been saved. *)
(* [main] is extracted as [soma_main ()], with [main] inlined in it: a
   value of OCaml is computed when its module starts, before the runtime
   could report what goes wrong while building it (a cast that fails, in
   [main := print (f 42)]) *)
(* A module's name in the image: its file's name and digest *)
let module_name file = Filename.basename file ^ "-" ^ String.sub (Digest.to_hex (Digest.file file)) 0 8

let extract ?(calls = []) ?(ocaml_modules = []) ~state dir =
  let cmds = Filename.concat dir "extract.soma" in
  (* each function of a module, a call of Soma_wasm: [Extract Constant]'s
     code is a string, whose quotes are doubled *)
  let rocq_string s = "\"" ^ String.concat "\"\"" (String.split_on_char '"' s) ^ "\"" in
  let call_extraction (name, (c : SomaForeign.image_call)) =
    let args = List.mapi (fun i _ -> Printf.sprintf "a%d" i) c.params in
    let pair (k, w) = Printf.sprintf "(%S, %S)" k w in
    let code = Printf.sprintf "(fun %s -> Obj.magic (Soma_wasm.call %S %S [%s] %s [|%s|]))"
        (String.concat " " args) (module_name c.module_file) c.export
        (String.concat "; " (List.map pair c.params)) (pair c.result)
        (String.concat "; " (List.map (fun a -> "Obj.repr " ^ a) args)) in
    Printf.sprintf "Extract Constant %s => %s.\n" name (rocq_string code) in
  write_file cmds (Printf.sprintf
    "Set Extraction Output Directory %s.\n\
     From Corelib Require PrimFloat FloatClass PrimInt63 CarryType.\n\
     From Stdlib Require ExtrOcamlBasic ExtrOcamlNativeString ExtrOcamlNatInt.\n\
     %s%s%s\
     Definition soma_wire_take_line := Soma.Wire.take_line.\n\
     Definition soma_wire_take_frame (buffer : string) : option (option (string * string)) :=\n\
       match Soma.Wire.take_frame Soma.Wire.max_frame buffer with\n\
       | Soma.Wire.NeedMore => None\n\
       | Soma.Wire.Oversized => Some None\n\
       | Soma.Wire.Whole data rest => Some (Some (data, rest))\n\
       end.\n\
     Definition soma_main (_ : unit) := main.\n\
     Extraction Inline main.\n\
     Extraction \"prog\" soma_main soma_wire_take_line soma_wire_take_frame.\n" (quote_soma_string dir) float_extraction nat_string_extraction
       (String.concat "" (SomaOcamlBindings.extraction_lines ocaml_modules @ List.map call_extraction calls)));
  Dumpglob.push_output Dumpglob.NoGlob;
  (* its Extraction "prog" goes to [dir], the output directory it sets *)
  SomaImport.generated_output := true;
  Fun.protect ~finally:(fun () -> SomaImport.generated_output := false; Dumpglob.pop_output ()) (fun () ->
      ignore (Vernac.load_vernac ~check:true ~state cmds))

let tail_of_file ?(lines = 20) f =
  try
    let all = String.split_on_char '\n' (read_file f) in
    let n = List.length all in
    String.concat "\n" (List.filteri (fun i _ -> i >= n - lines) all)
  with Sys_error _ -> ""

let copy_file ~src ~dst =
  write_file dst (read_file src);
  Unix.chmod dst 0o755


(* The functions of WebAssembly modules that [main] calls (SomaForeign),
   by name: an image runs them, but for those of type Any, whose numbers
   the image cannot read yet *)
let foreign_calls () =
  let main = Nametab.global (Libnames.qualid_of_ident (Id.of_string "main")) in
  let st = Conv_oracle.get_transp_state (Environ.oracle (Global.env ())) in
  let _, assums = Assumptions.assumptions (Library.indirect_accessor [@ocaml.alert "-deprecated"]) st [main] in
  let calls = Printer.ContextObjectMap.fold (fun o _ acc -> match o with
      | Printer.Axiom (Printer.Constant k, _) ->
        (match !SomaForeign.image k with
         | Some c -> (Libnames.string_of_path (Nametab.path_of_global (GlobRef.ConstRef k)), c) :: acc
         | None -> acc)
      | _ -> acc) assums [] in
  List.iter (fun (name, (c : SomaForeign.image_call)) ->
      if List.exists (fun (k, _) -> k = "Any") (c.result :: c.params) then
        error Pp.(str "main calls " ++ str name ++ str ", " ++ str (Filename.basename c.module_file) ++
                  str "'s " ++ str c.export ++ str ", of type Any," ++ spc () ++
                  str "which an image cannot call yet: declare its type in " ++
                  str (Filename.remove_extension (Filename.basename c.module_file) ^ ".definition") ++ str "."))
    calls;
  calls

let standins_mli = {soma|(* Compile-time contracts only: abstract types prevent accidental reliance on
   the representation of promises, network flows, addresses or buffers. These
   are never linked or run in an image.

   Each module is a subset of the library's real interface: only the values
   the generated code uses, with the same types, labels and optional
   arguments (an optional argument may be left out, as a full application
   of the real function may omit it, but none is made required). Where they
   come from:
   - Lwt: lwt 5, src/core/lwt.mli
   - Duration: duration 0.2, src/duration.mli
   - Mirage_sleep: mirage-sleep 4.0, src/mirage_sleep.mli
   - Mirage_mtime: mirage-mtime 5, src/mirage_mtime.mli (elapsed_ns)
     https://mirage.github.io/mirage-mtime/mirage-mtime/Mirage_mtime/index.html
   - Ptime: ptime 1.1, src/ptime.mli (date, time, tz_offset_s, to_date_time,
     span, to_span, Span.to_d_ps)
   - Mirage_ptime: mirage-ptime 5.0, src/mirage_ptime.mli
   - Mirage_crypto_rng: mirage-crypto-rng 1.0, rng/mirage_crypto_rng.mli
     (generate : ?g:g -> int -> string)
   - Solo5_os.Memory: mirage-solo5 0.10, lib/memory.mli
   - Cmdliner: cmdliner 1.3, src/cmdliner.mli (Arg.info, Arg.opt_all, ...)
   - Mirage_runtime: mirage-runtime 4.5, lib/mirage_runtime.mli
   - Cstruct: cstruct 6, lib/cstruct.mli
   - Ipaddr: ipaddr 5, lib/ipaddr.mli (v4v6, Prefix.address)
   - Lwt_condition: lwt 5, src/core/lwt_condition.mli
   - Tcpip.Stack.V4V6 and its TCP: tcpip 8, src/core/stack.ml and
     src/core/tcp.ml (Tcp.S), and its IP, src/core/ip.ml (configured_ips),
     whose TCP flow functions are Mirage_flow.S's
     (mirage-flow 4, src/mirage_flow.mli)
   - for a web image (resolve, https):
     Domain_name: domain-name 0.4, src/domain_name.mli (of_string, host);
     Dns_client_mirage.S: dns-client-mirage 10, mirage/dns_client_mirage.mli
     (gethostbyname); X509.Authenticator.t: x509 1.0;
     Ca_certs_nss.authenticator: ca-certs-nss 3, lib/ca_certs_nss.mli;
     Tls.Config.client: tls 1.0, lib/config.mli; Tls_mirage.Make: tls-mirage
     1.0, mirage/tls_mirage.mli (client_of_flow, and Mirage_flow.S's read,
     write, close, pp_error, pp_write_error) *)
module Lwt : sig
  type 'a t
  val return : 'a -> 'a t
  val return_unit : unit t
  val async : (unit -> unit t) -> unit
  val catch : (unit -> 'a t) -> (exn -> 'a t) -> 'a t
  type 'a u
  val wait : unit -> 'a t * 'a u
  val pick : 'a t list -> 'a t
  val choose : 'a t list -> 'a t
  val cancel : 'a t -> unit
  module Infix : sig
    val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
    val ( >|= ) : 'a t -> ('a -> 'b) -> 'b t
  end
end
module Duration : sig val of_sec : int -> int64 end
module Mirage_sleep : sig val ns : int64 -> unit Lwt.t end
module Mirage_mtime : sig val elapsed_ns : unit -> int64 end
module Ptime : sig
  type t
  type tz_offset_s = int
  type date = int * int * int
  type time = (int * int * int) * tz_offset_s
  val to_date_time : ?tz_offset_s:tz_offset_s -> t -> date * time
  type span
  val to_span : t -> span
  module Span : sig val to_d_ps : span -> int * int64 end
end
module Mirage_ptime : sig val now : unit -> Ptime.t end
module Mirage_crypto_rng : sig
  type g
  val generate : ?g:g -> int -> string
end
module Solo5_os : sig
  module Memory : sig
    type stat = { heap_words : int; live_words : int; stack_words : int; free_words : int }
    val stat : unit -> stat
  end
end
module Cmdliner : sig
  module Term : sig type 'a t end
  module Arg : sig
    type 'a t
    type 'a conv
    type info
    val info : ?docs:string -> ?docv:string -> ?doc:string -> string list -> info
    val string : string conv
    val opt_all : ?vopt:'a -> 'a conv -> 'a list -> info -> 'a list t
    val flag : info -> bool t
    val value : 'a t -> 'a Term.t
    val ( & ) : ('a -> 'b) -> 'a -> 'b
  end
end
module Mirage_runtime : sig
  val register_arg : 'a Cmdliner.Term.t -> unit -> 'a
end
module Cstruct : sig
  type t
  val create : int -> t
  val to_string : ?off:int -> ?len:int -> t -> string
  val of_string : ?allocator:(int -> t) -> ?off:int -> ?len:int -> string -> t
end
module Lwt_mutex : sig
  type t
  val create : unit -> t
  val with_lock : t -> (unit -> 'a Lwt.t) -> 'a Lwt.t
end
module Mirage_block : sig
  type info = { read_write:bool; sector_size:int; size_sectors:int64 }
  module type S = sig
    type t
    type error = private [> `Disconnected ]
    type write_error = private [> `Disconnected | `Is_read_only ]
    val get_info : t -> info Lwt.t
    val read : t -> int64 -> Cstruct.t list -> (unit,error) result Lwt.t
    val write : t -> int64 -> Cstruct.t list -> (unit,write_error) result Lwt.t
  end
end
module Ipaddr : sig
  module V4 : sig
    type t
    val to_string : t -> string
  end
  module V6 : sig type t end
  type ('v4, 'v6) v4v6 = V4 of 'v4 | V6 of 'v6
  type t = (V4.t, V6.t) v4v6
  val of_string : string -> (t, [> `Msg of string ]) result
  val to_string : t -> string
  module Prefix : sig
    type addr = t
    type t
    val address : t -> addr
  end
end
module Domain_name : sig
  type 'a t
  val of_string : string -> ([ `raw ] t, [> `Msg of string ]) result
  val host : 'a t -> ([ `host ] t, [> `Msg of string ]) result
end
module Dns_client_mirage : sig
  module type S = sig
    type t
    val gethostbyname : t -> [ `host ] Domain_name.t -> (Ipaddr.V4.t, [> `Msg of string ]) result Lwt.t
  end
end
module X509 : sig
  module Authenticator : sig type t end
end
module Ca_certs_nss : sig
  val authenticator : unit -> (X509.Authenticator.t, [> `Msg of string ]) result
end
module Tls : sig
  module Config : sig
    type client
    val client : authenticator:X509.Authenticator.t -> ?peer_name:[ `host ] Domain_name.t -> unit ->
      (client, [> `Msg of string ]) result
  end
end
module Tls_mirage : sig
  module Make (F : sig type flow end) : sig
    type flow
    type error
    type write_error
    val pp_error : Format.formatter -> error -> unit
    val pp_write_error : Format.formatter -> write_error -> unit
    val client_of_flow : Tls.Config.client -> ?host:[ `host ] Domain_name.t -> F.flow -> (flow, write_error) result Lwt.t
    val read : flow -> ([ `Data of Cstruct.t | `Eof ], error) result Lwt.t
    val write : flow -> Cstruct.t -> (unit, write_error) result Lwt.t
    val close : flow -> unit Lwt.t
  end
end
module Lwt_condition : sig
  type 'a t
  val create : unit -> 'a t
  val wait : ?mutex:Lwt_mutex.t -> 'a t -> 'a Lwt.t
  val broadcast : 'a t -> 'a -> unit
end
module Tcpip : sig
  module Stack : sig
    module type V4V6 = sig
      type t
      module TCP : sig
        type t
        type flow
        (* tcpip's Tcp.S: type error = private [> Tcp.error ], with
           Tcp.error = [ `Timeout | `Refused ] (src/core/tcp.ml) *)
        type error = private [> `Refused | `Timeout ]
        (* mirage-protocols 7.0.0, src/mirage_protocols.ml:
           Tcp.write_error = [ Tcp.error | Mirage_flow.write_error ], and
           TCP.write_error = private [> Tcp.write_error ]. Tcp.error is
           [ `Refused | `Timeout ]; Mirage_flow.write_error is [ `Closed ].
           https://ocaml.org/p/mirage-protocols/7.0.0/src/mirage-protocols/mirage_protocols.ml.html
           Keep the private open row: implementations can add errors, and
           callers cannot invent additional constructors of this private row. *)
        type write_error = private [> `Refused | `Timeout | `Closed ]
        val listen : t -> port:int -> (flow -> unit Lwt.t) -> unit
        val read : flow -> ([ `Data of Cstruct.t | `Eof ], error) result Lwt.t
        val write : flow -> Cstruct.t -> (unit, write_error) result Lwt.t
        val close : flow -> unit Lwt.t
        val create_connection : t -> Ipaddr.t * int -> (flow, error) result Lwt.t
        val dst : flow -> Ipaddr.t * int
      end
      val tcp : t -> TCP.t
      (* tcpip's Udp.S (src/core/udp.ml): callback, listen, write *)
      module UDP : sig
        type t
        type error
        val listen : t -> port:int -> (src:Ipaddr.t -> dst:Ipaddr.t -> src_port:int -> Cstruct.t -> unit Lwt.t) -> unit
        val write : ?src:Ipaddr.t -> ?src_port:int -> ?ttl:int -> dst:Ipaddr.t -> dst_port:int -> t ->
          Cstruct.t -> (unit, error) result Lwt.t
      end
      val udp : t -> UDP.t
      module IP : sig
        type t
        val configured_ips : t -> Ipaddr.Prefix.t list
      end
      val ip : t -> IP.t
    end
  end
end
|soma}

(* Keep the contracts in a separate directory: real image builds must never
   resolve one of these modules instead of a Mirage library. *)
let check_project ~wasm ~libraries ~native_files dir =
  let checks = Filename.concat dir "no-image" in
  mkdir_p checks;
  write_file (Filename.concat checks "standins.mli") standins_mli;
  write_file (Filename.concat checks "config.ml") (read_file (Filename.concat dir "config.ml"));
  let base = ["uint63.ml"; "float64.ml"; "soma_nat.ml"] in
  (* the C modules' OCaml, checked with the program's; their C, by the
     machine's C compiler, against the header and OCaml's (an image's
     C is compiled for Solo5 only when the image is built) *)
  let c_dir = Filename.concat dir "soma_c" in
  let c_names = if Sys.file_exists c_dir then List.sort compare (Array.to_list (Sys.readdir c_dir)) else [] in
  let c_ml = List.filter (fun f -> Filename.check_suffix f ".ml") c_names in
  let c_c = List.filter (fun f -> Filename.check_suffix f ".c") c_names in
  List.iter (fun f -> write_file (Filename.concat checks f) (read_file (Filename.concat c_dir f))) c_ml;
  let own = c_ml @ List.filter (fun f -> f <> "soma_nat.ml" && f <> "soma_bindings.ml") native_files in
  let program = ["soma_bindings.ml"; "soma_wasm.ml"; "prog.mli"; "prog.ml"] in
  let runtime = ["gradual.ml"; "soma_store.ml"; "soma_rt.ml"; "soma_disk.ml"; "unikernel.ml"] in
  (* A prior check's interfaces must not make a removed module appear to
     exist, or allow a new module to depend on an obsolete interface. *)
  let kept = ["standins.mli"; "config.ml"] @ base @ own @ program @ runtime in
  Array.iter (fun f ->
      if List.exists (Filename.check_suffix f) [".cmi"; ".cmo"; ".cmx"; ".o"] ||
         (List.exists (Filename.check_suffix f) [".ml"; ".mli"] && not (List.mem f kept)) then
        (try Sys.remove (Filename.concat checks f) with Sys_error _ -> ()))
    (Sys.readdir checks);
  List.iter (fun name -> write_file (Filename.concat checks name)
                (read_file (Filename.concat dir name)))
    (base @ List.filter (fun f -> not (List.mem f c_ml)) own @ program @ runtime);
  let packages = List.sort_uniq compare ((if wasm then ["wasm"] else []) @ libraries) in
  let compiler = if packages = [] then "ocamlc" else
      "ocamlfind ocamlc -package " ^ Filename.quote (String.concat "," packages) in
  (* Application modules and bindings use the real declared libraries.
     Only the generated runtime sees the stand-in Mirage interfaces. In
     particular, a declared Lwt.t must not become Standins.Lwt.t. *)
  let own_compile = if own = [] then "" else
      Printf.sprintf "%s -c $(ocamldep -sort %s) && " compiler
        (String.concat " " (List.map Filename.quote own)) in
  let script = Printf.sprintf
      "cd %s && ocamlc -stop-after parsing -c config.ml && ocamlc -c standins.mli && %s -c %s && %s%s -c %s && %s -open Standins -c %s"
      (Filename.quote checks) compiler (String.concat " " base) own_compile compiler
      (String.concat " " program) compiler (String.concat " " runtime) ^
    (if c_c = [] then "" else
       Printf.sprintf " && { ! command -v cc >/dev/null || (cd %s && cc -fsyntax-only -Wall -Werror=implicit-function-declaration -Werror=incompatible-pointer-types -I \"$(ocamlc -where)\" %s); }"
         (Filename.quote c_dir) (String.concat " " c_c)) in
  let log = Filename.concat checks "check.log" in
  (* The compiler on PATH, as Soma's CI has it; otherwise the opam switch
     soma build compiles OCaml programs in (SOMA_OCAML_SWITCH, or the one
     it made under ~/.cache/soma/ocaml), so a machine that builds Soma
     programs can check a Sandbox one without OCaml on PATH (a CI image
     whose only OCaml is that switch). *)
  let runner =
    if SomaOpam.command_exists "ocamlc" then Some []
    else
      let switch, managed = SomaOpam.switch () in
      if SomaOpam.command_exists "opam" && (not managed || Sys.file_exists (Filename.concat switch "_opam"))
      then Some ["opam"; "exec"; "--switch=" ^ switch; "--"]
      else None in
  let runner = match runner with
    | Some r -> r
    | None ->
      let switch, _ = SomaOpam.switch () in
      error Pp.(str "no ocamlc to check " ++ str checks ++ str " with: none on PATH, and no opam switch " ++
                str switch ++ str "." ++ fnl () ++
                str "Put OCaml on PATH (eval $(opam env)), set SOMA_OCAML_SWITCH to an opam switch with OCaml," ++
                spc () ++ str "or soma build any program with a .definition once: it makes that switch.") in
  let inputs = match Sys.getenv_opt "SOMA_BUILD_INPUTS" with
    | None | Some "" -> None
    | Some _ ->
      (try
         (* These require an opam-exec tool/search-path closure or findlib
            configuration coverage, not merely the currently selected dirs. *)
         if runner <> [] || packages <> [] then failwith "uncertified OCaml runner or package lookup";
         let query arguments =
           let out = Filename.temp_file "soma-check-inputs" ".log" in
           Fun.protect ~finally:(fun () -> try Sys.remove out with Sys_error _ -> ()) (fun () ->
               if not (SomaOpam.run ~log:out (runner @ arguments)) then failwith "unknown OCaml check inputs";
               read_file out) in
         let stdlib = String.trim (query ["ocamlc"; "-where"]) in
         if not (Sys.is_directory stdlib) then failwith "unknown OCaml standard library";
         let package_dirs = if packages = [] then [] else
             String.split_on_char '\n' (query (["ocamlfind"; "query"; "-recursive"; "-format"; "%d"] @ packages))
             |> List.filter (fun path -> path <> "") in
         if not (List.for_all Sys.is_directory package_dirs) then failwith "unknown OCaml package directory";
         let tools = ["sh"; "ocamlc"] @ (if own = [] then [] else ["ocamldep"]) in
         SomaBuildInfo.prepare_inputs ~tools
           (stdlib :: package_dirs @ List.map (Filename.concat checks) kept)
       with Sys_error _ | Unix.Unix_error _ | Failure _ -> None) in
  let args = runner @ ["sh"; "-c"; script] in
  let cmd = Filename.quote_command (List.hd args) (List.tl args) ~stdout:log ~stderr:log in
  if Sys.command cmd <> 0 then
    error Pp.(str "OCaml check failed in " ++ str checks ++ str ":" ++ fnl () ++
              str (read_file log));
  SomaBuildInfo.publish_inputs inputs;
  SomaBuildInfo.mark_external ~phase:"bytecode-check" ();
  Feedback.msg_notice Pp.(str "Mirage: checked " ++ str dir ++ str " (no image)")

(* The lock make depends would write, made without opam's current switch:
   opam-monorepo 0.5 asks opam for it and ignores OPAMSWITCH, so with no
   default switch set make depends fails ("No switch is currently set").
   Given the repositories and opam's global variables it needs no switch:
   the switch's own repositories, as their local copies under opam's root
   (the versions its installed dune and compilers came from), with
   dune-universe's opam-overlays before opam's default repository, as the
   Makefile adds it. make depends' other step, opam install --deps-only,
   is not run: its packages are the MirageOS tools (mirage, ocaml-solo5,
   solo5, opam-monorepo) the switch has to have for mirage configure. *)
let monorepo_lock = {sh|R=$(opam var root)/repo && overlays=git+https://github.com/dune-universe/opam-overlays.git && if [ -d "$R/opam-overlays" ]; then overlays=file://$R/opam-overlays; fi && repos= && for r in $(opam repo list --short); do if [ "$r" = default ]; then repos="$repos,$overlays"; overlays=; fi; repos="$repos,file://$R/$r"; done && repos="$repos${overlays:+,$overlays}" && vars="[opam-version,$(opam --version)],[monorepo,opam-monorepo]" && for v in os arch os-family os-distribution; do vars="$vars,[$v,$(opam var $v)]"; done && env OPAMVAR_monorepo=opam-monorepo opam monorepo lock --require-cross-compile --build-only soma-hvt -l mirage/soma-hvt.opam.locked --ocaml-version "$(ocamlc --version)" --add-global-opam-vars="[$vars]" --opam-repositories="[${repos#,}]"|sh}

(* The host backend and image backend use exactly the same declarations.
   Host primitives and Unix libraries still need a real operating system. *)
let ocaml_modules () =
  let modules, libraries = SomaOcamlBindings.checked_modules
      ~reserved:["Unikernel"; "Config"; "Main"; "Key_gen"; "Runtime_args";
                 "Soma_rt"; "Soma_store"; "Soma_disk"; "Soma_wasm"; "Gradual"] () in
  List.iter (fun (m : SomaForeign.ocaml_module) ->
      if m.ml_file = None && m.top = "Soma_host" then
        error Pp.(str "Soma.Host is a host interface, not a Mirage library; use Sandbox in an image.")) modules;
  List.iter (fun l ->
      if List.mem (SomaOcamlBindings.package_of l)
          ["unix"; "threads"; "dynlink"; "compiler-libs"; "runtime_events"; "ocamldoc"] then
        error Pp.(str "OCaml library " ++ str l ++ str " requires the host runtime; use a Mirage-compatible library in a Solo5 image.")) libraries;
  modules, libraries

(* A local opam package adds exact soma.toml [opam] constraints to the
   monorepo solver. Mirage's package DSL only expresses inclusive minimum
   and exclusive maximum versions, not exact versions. *)
let ocaml_dependencies libraries versions =
  "opam-version: \"2.0\"\nversion: \"dev\"\nsynopsis: \"Soma image OCaml dependencies\"\ndepends: [\n" ^
  String.concat "" (List.map (fun p ->
      Printf.sprintf "  %S%s\n" p (match List.assoc_opt p versions with
        | None -> "" | Some v -> Printf.sprintf " {= %S}" v))
      (List.sort_uniq compare (SomaOcamlBindings.packages_of libraries @ List.map fst versions))) ^ "]\n"

(* soma_c/dune: the program's C modules, a library built for Solo5 only
   (the project's other context is the host's), its modules and stubs
   those of the program, unwrapped: soma_bindings.ml calls Arith.sum *)
let c_dune ~modules ~stubs =
  Printf.sprintf ";; Generated by Soma (toplevel/somaMirage.ml): the program's C modules.\n\
                  (library\n (name soma_c)\n (wrapped false)\n\
                 \ (enabled_if (= %%{context_name} \"solo5\"))\n (modules %s)\n\
                 \ (flags (:standard -w -a))\n\
                 \ (foreign_stubs (language c) (names %s) (flags (:standard -O2))))\n"
    (String.concat " " modules) (String.concat " " stubs)

(* The program's C modules, in soma_c/ (none: no such directory), each
   file not among them removed *)
let write_c_files dir modules =
  let c_dir = Filename.concat dir "soma_c" in
  let written = ref [] in
  let c_file name text =
    mkdir_p c_dir; written := name :: !written;
    ignore (update_file (Filename.concat c_dir name) text) in
  List.iter (fun m -> if SomaOcamlBindings.is_c m then
                List.iter (fun (f, text) -> c_file f text) (SomaOcamlBindings.c_files ~read_file m)) modules;
  let names = List.rev !written in
  if names <> [] then begin
    let ml = List.filter (fun f -> Filename.check_suffix f ".ml") names in
    c_file "dune" (c_dune ~modules:(List.map (fun f -> String.capitalize_ascii (Filename.remove_extension f)) ml)
                     ~stubs:(SomaOcamlBindings.c_stub_names names))
  end;
  if Sys.file_exists c_dir then
    Array.iter (fun f -> if not (List.mem f !written) then
                   (try Sys.remove (Filename.concat c_dir f) with Sys_error _ -> ()))
      (Sys.readdir c_dir);
  names

let write_ocaml_files dir modules =
  let file name text = ignore (update_file (Filename.concat dir name) text) in
  ignore (write_c_files dir modules);
  let made = SomaOcamlBindings.write_files ~file ~c_file:(fun _ _ -> ()) ~read_file ~directives:true modules in
  let manifest = Filename.concat dir "ocaml-files" in
  List.iter (fun f ->
      if Filename.basename f = f && Filename.check_suffix f ".ml" && not (List.mem f made) then
        (try Sys.remove (Filename.concat dir f) with Sys_error _ -> ()))
    (SomaOpam.read_lines manifest);
  file "ocaml-files" (String.concat "\n" made ^ "\n");
  made

(* The extraction staging directory and generated project are shared.
   Hold the lock through the final copy: otherwise another build can
   overwrite prog.ml or its native modules while dune is reading them. *)
let with_build_lock f =
  let dir = cache_dir () in
  mkdir_p dir;
  let fd = Unix.openfile (Filename.concat dir "build.lock") [Unix.O_CREAT; Unix.O_RDWR] 0o600 in
  Unix.set_close_on_exec fd;
  Fun.protect ~finally:(fun () -> Unix.close fd) (fun () ->
      Unix.lockf fd Unix.F_LOCK 0;
      f ())

(* Optional freshness evidence for an actual image build. Resolve the switch
   that supplies its compiler/tools, then snapshot those inputs after setup,
   before make build. If the installation cannot be identified, building is
   still supported, but the CLI must not certify a future build as unchanged. *)
let image_build_inputs ~switch ~dir sources =
  match Sys.getenv_opt "SOMA_BUILD_INPUTS" with
  | None | Some "" -> None
  | Some _ ->
    try
      let out = Filename.temp_file "soma-mirage-prefix" ".log" in
      let prefix = Fun.protect ~finally:(fun () -> try Sys.remove out with Sys_error _ -> ()) (fun () ->
          if not (SomaOpam.run ~log:out ["opam"; "var"; "--switch=" ^ switch; "prefix"]) then
            failwith "unknown image compiler prefix";
          Unix.realpath (String.trim (read_file out))) in
      List.iter (fun name -> if not (Sys.is_directory (Filename.concat prefix name)) then
                    failwith "unknown image compiler installation") ["bin"; "lib"];
      let opam_root = getenv_default "OPAMROOT" (Filename.concat (getenv_default "HOME" ".") ".opam") in
      let paths = List.map (Filename.concat prefix)
          ["bin"; "lib"; ".opam-switch/switch-state"; ".opam-switch/switch-config"; ".opam-switch/overlay"] @
          [Filename.concat opam_root "config"] @
          List.map (Filename.concat dir)
            ["duniverse"; "mirage"; "Makefile"; "dune"; "dune-project"; "config.ml";
             "prog.ml"; "prog.mli"; "soma_rt.ml"; "soma_store.ml"; "soma_disk.ml"; "soma_wasm.ml";
             "float64.ml"; "uint63.ml"; "gradual.ml"; "unikernel.ml"] @ sources in
      SomaBuildInfo.prepare_inputs paths
    with Sys_error _ | Unix.Unix_error _ | Failure _ -> None

let build ~state ~source ~vo_file =
  if getenv_default "SOMA_MIRAGE_BUILD" "1" <> "0" && requires_mirage () then with_build_lock (fun () ->
    SomaBuildInfo.mark_external ();
    check_main ();
    let calls = foreign_calls () in
    let ocaml_modules, libraries = ocaml_modules () in
    (* Bind the original bytes before extraction/staging reads them. Capturing
       originals only after copying could certify new originals with old copies. *)
    let original_sources = List.map (fun (_, (call : SomaForeign.image_call)) -> call.module_file) calls @
        List.filter_map (fun (m : SomaForeign.ocaml_module) -> m.ml_file) ocaml_modules in
    let original_inputs = if original_sources = [] then Some [] else
        SomaBuildInfo.prepare_inputs ~tools:[] original_sources in
    SomaBuildInfo.publish_inputs original_inputs;
    (* extracted once to find out which project the program needs *)
    let staging = Filename.concat (cache_dir ()) "extract" in
    mkdir_p staging;
    extract ~calls ~ocaml_modules ~state staging;
    let prog = read_file (Filename.concat staging "prog.ml") in
    let web = uses_web prog in
    let network = uses_network prog || web in
    (* Include constructors applied to a variable, not only parenthesized
       arguments. Their type declarations alone do not need a device. *)
    let storage = List.exists (fun line -> List.exists (fun c ->
        contains line c && not (contains line (c ^ " of ")))
        ["Read_file"; "Write_file"; "Append_file"])
        (String.split_on_char '\n' prog) in
    (* a program that calls modules has a project of its own, with the
       interpreter: the others need not fetch it *)
    let wasm = calls <> [] in
    let native = ocaml_modules <> [] in
    let c = List.exists SomaOcamlBindings.is_c ocaml_modules in
    let disks = disk_names prog in
    let versions = match SomaProject.of_file source with Some p -> p.SomaProject.opam | None -> [] in
    let dependencies = ocaml_dependencies libraries versions in
    (* Temporary CI checkouts with the same dependencies reuse the same
       monorepo. Source changes only rebuild the application, not every
       library. The lock and file manifest make reuse across apps safe. *)
    let project = if native then "-ocaml-" ^ Digest.to_hex
        (Digest.string (String.concat "\n" libraries ^ "\n" ^ dependencies)) else "" in
    let dir = Filename.concat (cache_dir ())
        ((if network then "net" else "plain") ^ (if web then "-web" else "") ^
         (if storage then "-storage" else "") ^ (if wasm then "-wasm" else "") ^
         String.concat "" (List.map (fun d -> "-disk-" ^ d) disks) ^ (if c then "-c" else "") ^ project) in
    mkdir_p dir;
    let file name contents = update_file (Filename.concat dir name) contents in
    let config_changed = file "config.ml" (disks_config disks (config_ml ~c ~network ~wasm ~storage ~web ~libraries ())) in
    let deps_changed = if native then file "soma-ocaml-deps.opam" dependencies else false in
    let native_files = write_ocaml_files dir ocaml_modules in
    let modules = List.sort_uniq compare
        (List.map (fun (_, (c : SomaForeign.image_call)) -> module_name c.module_file, read_file c.module_file) calls) in
    List.iter (fun (name, contents) -> ignore (file name contents)) [
      "unikernel.ml", disks_unikernel disks (unikernel_ml ~network ~storage ~web);
      "soma_store.ml", header ^ SomaStorage.source;
      "soma_disk.ml", disk_ml;
      "soma_rt.ml", runtime_ml;
      "soma_wasm.ml", wasm_ml modules;
      "float64.ml", float64_ml;
      "uint63.ml", uint63_ml;
      "gradual.ml", gradual_ml ~has_casts:(contains prog "module Gradual_rt");
      "prog.ml", prog;
      "prog.mli", read_file (Filename.concat staging "prog.mli");
    ];
    let no_image = getenv_default "SOMA_MIRAGE_NO_IMAGE" "0" = "1" ||
      getenv_default "SOMA_MIRAGE_SWITCH" "" = "" in
    if no_image then check_project ~wasm ~libraries ~native_files dir else begin
    (* configured, and its dependencies fetched: a project whose make
       depends failed or never ran has a Makefile and no duniverse *)
    let configured = Sys.file_exists (Filename.concat dir "Makefile") &&
                     Sys.file_exists (Filename.concat dir "duniverse") in
    let switch = getenv_default "SOMA_MIRAGE_SWITCH" "hvf" in
    let setup = if configured && not config_changed && not deps_changed then ""
      else "mirage configure -t hvt && " ^ monorepo_lock ^
           (if native then " soma-ocaml-deps" else "") ^ " && make pull && " in
    let log = Filename.concat dir "build.log" in
    (* opam-monorepo (make depends) asks opam for the current switch,
       which opam exec --switch does not set when there is no default *)
    let execute commands =
      let script = Printf.sprintf "export OPAMSWITCH=%s && cd %s && %s"
          (Filename.quote switch) (Filename.quote dir) commands in
      let cmd = Filename.quote_command "opam" ["exec"; "--switch=" ^ switch; "--"; "sh"; "-c"; script]
          ~stdout:log ~stderr:log in
      if Sys.command cmd <> 0 then
        error Pp.(str "building the image failed (opam switch " ++ str switch ++
                  str "); the end of " ++ str log ++ str ":" ++ fnl () ++
                  str (tail_of_file log)) in
    if setup <> "" then
      Feedback.msg_notice Pp.(str "Mirage: setting up the MirageOS project in " ++ str dir ++
                              str " (once; fetches the dependencies)");
    if setup <> "" then execute (setup ^ "true");
    let inputs = image_build_inputs ~switch ~dir [] in
    execute "make build";
    let hvt = Filename.remove_extension vo_file ^ ".hvt" in
    copy_file ~src:(List.fold_left Filename.concat dir ["dist"; "soma.hvt"]) ~dst:hvt;
    (* the memory the image runs in, in MB: $SOMA_MIRAGE_MEM, or 256 *)
    let mem = match int_of_string_opt (getenv_default "SOMA_MIRAGE_MEM" "") with
      | Some m when m > 0 -> m
      | _ -> 256 in
    let hvt_args = ["solo5-hvt"; Printf.sprintf "--mem=%d" mem] @
        (if storage then ["--block:storage=storage.img"] else []) @
        List.map (fun d -> Printf.sprintf "--block:%s=%s.img" d d) disks @ ["--"; hvt] in
    let command = (if network then ["solo5-vmnet"; "--"] else []) @ hvt_args in
    SomaBuildInfo.publish_command command;
    SomaBuildInfo.publish_inputs inputs;
    SomaBuildInfo.publish_products [hvt];
    let run = Filename.quote_command (List.hd command) (List.tl command) in
    Feedback.msg_notice Pp.(str "Mirage: built " ++ str hvt ++
                            str "; run it with: " ++ str run)
    end
  )
