(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * MirageOS unikernels, [Soma.Sandbox]

    Not part of the prelude. A program that requires it is a unikernel:
    [rocq c prog.soma] also builds [prog.hvt], a MirageOS image for
    [solo5-hvt] (Hypervisor.framework on Apple Silicon), whose code is the
    program's [main : io unit] extracted to OCaml (see the [Sandbox]
    section of GRADUAL.md).

    [io A] describes what the unikernel does, as data: printing, sleeping,
    looping, reading the clock, serving and fetching over TCP, and links
    that stay open ([listen], [connect], [send], [receive_line],
    [receive_frame], [close]: lines or length-prefixed frames over one TCP
    connection), in order, ending with a result of type
    [A]. Building an [io] does nothing; the image runs [main]. A program
    that uses [serve], [fetch], [listen], [connect], [watch], UDP or
    [local_address] gets a network stack
    and runs under [solo5-vmnet]; one that uses [resolve], [https],
    [fetch] or [connect] gets DNS and TLS as well (MirageOS's dns-client, tls-mirage and the NSS
    certificate authorities). *)

From Stdlib Require Strings.String Strings.Ascii.
From Corelib Require Extraction.
(* In the image, strings are OCaml's, [nat] is OCaml's [int], and [bool],
   [option], pairs and lists are OCaml's (the image's extraction:
   ExtrOcamlNativeString, ExtrOcamlNatInt, ExtrOcamlBasic), as in a
   program built for the machine. *)
From Stdlib Require Import NArith.BinNat.
From Corelib Require PrimInt63.
From Stdlib Require Import Lia.
Require Import Soma.Strings Soma.Show.
From Soma Require Word64.
(** [buffer] and [promise], which OCaml modules name too *)
Require Export Soma.Handles.

(** What [fetch] gets: the reply, or why there is none *)
Inductive fetched : Type :=
| Reply (body : string)   (* what the other side sent back before it closed *)
| Refused                 (* nothing listens at that address and port *)
| TimedOut                (* nothing answered within 10 seconds *)
| BadAddress.             (* neither an IP address nor a name that resolves *)

(** What [resolve] gets: an IPv4 address of the name, or why there is none *)
Inductive resolved : Type :=
| Resolved (address : string)   (* an IPv4 address, as "93.184.215.14" *)
| Unresolved (why : string).    (* not a host name, no such name, no IPv4 address, or no answer *)

(** What [https] gets: the server's answer, or why there is none. Header
    names are in lower case ([header] finds one); the body is the whole
    body, its chunks joined when it came chunked. *)
Inductive answered : Type :=
| Answer (status : nat) (headers : list (string * string)) (body : string)
| Unanswered (why : string).    (* no address, no connection, a certificate not trusted, or no HTTP answer *)

(** * Links: TCP connections that stay open, line by line *)

(** a connection open at the unikernel, as [listen] or [connect] give it;
    the image knows it by its number *)
Inductive connection : Type := Connection (id : nat).

(** What [connect] gets: a connection, or why there is none *)
Inductive connected : Type :=
| Connected (c : connection)  (* the other side accepted *)
| ConnectRefused              (* nothing listens at that address and port *)
| ConnectTimedOut             (* nothing answered within 10 seconds *)
| ConnectBadAddress.          (* neither an IP address nor a name that resolves *)

(** What [receive_line] gets: the next line, without its line break, or
    [Closed] when the connection ended first (a line the other side did
    not finish is dropped) *)
Inductive received : Type :=
| Line (line : string)
| Closed.

(** What [send] did: [Sent], or [SendClosed] when the connection is closed *)
Inductive sent : Type :=
| Sent
| SendClosed.

(** What [receive_frame] gets: the next length-prefixed frame (see
    [frame]), or why there is none *)
Inductive framed : Type :=
| Frame (data : string)  (* a whole frame, without its length prefix *)
| FrameClosed            (* the connection ended first (a frame not finished is dropped) *)
| FrameTimedOut          (* no whole frame within the seconds given; what has
                            arrived of one is kept for the next [receive_frame] *)
| FrameTooLarge.         (* its length is over [max_frame]: the connection is closed *)

(** What [receive] gets: the bytes the connection has received, as TCP
    delivered them, or why there are none *)
Inductive chunk : Type :=
| Chunk (data : string)  (* what had arrived, all of it: never empty *)
| ChunkClosed            (* the connection ended first; it is closed *)
| ChunkTimedOut.         (* nothing arrived within the milliseconds given *)

(** a task [fork] started, whose result [await] gives; the image knows it
    by its number *)
Inductive task (A : Type) : Type := Task (id : nat).

(** What [await] gets: the task's result, or why it has none *)
Inductive awaited (A : Type) : Type :=
| Completed (a : A)       (* its body ended with [a] *)
| TaskFailed (why : string).  (* its body failed (a cast, [raise], an exception), or there is no such task *)

(** a cell holding an [A], shared by whatever has it: [serve] and [listen]
    handlers, [spawn]ed tasks and the main loop; the image knows it by its
    number *)
Inductive cell (A : Type) : Type := Cell (id : nat).

(** What came in on the connections [listen_mailbox] accepted, in the
    order it came: a select over them. A connection's bytes are as TCP
    delivered them (a message may be cut anywhere, or several come in one);
    [take_line] and [split_lines] cut them into lines. *)
Inductive link_event : Type :=
| LinkOpened (c : connection) (host : string)  (* accepted, from [host], an IP address *)
| LinkBytes (c : connection) (data : string)   (* bytes it received *)
| LinkClosed (c : connection).                 (* the other side ended it; it is closed *)

(** What [select] gets: what came in, of every kind, in the order it came *)
Inductive event : Type :=
| Linked (e : link_event)
    (* what a connection of [listen_mailbox], or one [watch]ed, did *)
| Datagram (port : nat) (host : string) (source_port : nat) (data : string)
    (* a UDP datagram to [port] (one of [udp_listen]), from [host], an IP
       address, at [source_port] *)
| Timer (tag : nat).
    (* the [after] of this tag came due *)

(** a signal tasks wait on: [notify] wakes every task waiting, and counts.
    A task reads the count, looks at what it waits for, and waits for a
    count past the one it read ([wait_signal]), so that a [notify] between
    its look and its wait is not missed. Made only by [new_signal]. *)
Inductive signal : Type := Signal (id : nat).

(** A dynamically scoped value, inherited by forked tasks and restored after
    its scope, including across waits. Each task's scope is independent. *)
Inductive context_key (A : Type) : Type := ContextKey (id : nat).

Inductive io : Type -> Type :=
| ret {A : Type} (a : A) : io A
(** [bind m k]: run [m], then [k] on its result *)
| bind {A B : Type} (m : io A) (k : A -> io B) : io B
(** a line on the console *)
| print (s : string) : io unit
| sleep (seconds : nat) : io unit
(** monotonic milliseconds since an arbitrary origin, unaffected by UTC
    adjustments. Binary [N], never a unary timestamp. *)
| monotonic_ms : io N
(** wait at least [milliseconds] milliseconds (binary [N]) *)
| sleep_ms (milliseconds : N) : io unit
(** [body], again and again; it never ends, so its type is any [io A] *)
| forever {A : Type} (body : io unit) : io A
(** [step] from [start], then from what it returned, again and again: a
    loop that carries a state. It never ends, so its type is any [io A]. *)
| iterate {S A : Type} (step : S -> io S) (start : S) : io A
(** the time of day, UTC: [(hour, minute, second)] *)
| now : io (nat * nat * nat)
(** a random number below [bound] ([0] when [bound] is [0]) *)
| random (bound : nat) : io nat
(** [n] random bytes, from the same generator as [random] *)
| random_bytes (n : nat) : io string
(** [s] on the console as it is, flushed: [print] adds a line break,
    [write] adds nothing (a terminal's bytes, a prompt, a partial line) *)
| write (s : string) : io unit
(** monotonic nanoseconds since an arbitrary origin, unaffected by UTC
    adjustments, as a primitive 63-bit integer (OCaml's [int] in the
    image): cheap to read in a loop, and enough for 146 years *)
| monotonic_ns : io PrimInt63.int
(** the wall clock, UTC: the seconds since 1970-01-01 00:00:00 and the
    nanoseconds past them, as [clock_gettime(CLOCK_REALTIME)] gives them *)
| wall_clock : io (PrimInt63.int * PrimInt63.int)
(** run [body] alongside the rest, from now on: [spawn] returns at once.
    The image's actions take turns: one runs until it waits (for time, a
    connection, an event), then another does. A failure in [body] is
    reported and the image goes on; its [exit] stops the image. The image
    keeps running until its tasks have ended. *)
| spawn (body : io unit) : io unit
(** run [body] alongside the rest, as [spawn] does, and give a handle to
    its result: [fork] returns at once *)
| fork {A : Type} (body : io A) : io (task A)
(** wait for the task to end: [Completed] with its result, or
    [TaskFailed] with why. A task can be awaited any number of times,
    by any task; each gets the same answer *)
| await {A : Type} (t : task A) : io (awaited A)
(** [await], waiting [milliseconds] at most: [None] when the task is still
    running then (it goes on) *)
| await_within {A : Type} (t : task A) (milliseconds : N) : io (option (awaited A))
(** a new cell, holding [a] *)
| new_cell {A : Type} (a : A) : io (cell A)
(** what the cell holds *)
| read_cell {A : Type} (c : cell A) : io A
(** the cell holds [a] from now on *)
| write_cell {A : Type} (c : cell A) (a : A) : io unit
(** the cell holds [f] of what it held, which [modify_cell] returns: in
    one step, which no other task's comes between *)
| modify_cell {A : Type} (c : cell A) (f : A -> A) : io A
(** [f tt], called when the image comes to it, in order with the other
    actions: for a function of a C or OCaml module that does something
    ([call (fun _ => peek address 8)]). Such a function, called outside
    [call], may be computed once, early, or not at all, as a value is. *)
| call {A : Type} (f : unit -> A) : io A
(** the arguments given to the image: [solo5-hvt -- prog.hvt --arg=a --arg=b]
    gives [["a", "b"]] *)
| args : io (list string)
(** stop the unikernel with this exit code ([0]: success) *)
| exit {A : Type} (code : nat) : io A
(** answer TCP connections on [port]: what a connection sends first is
    passed to [handler], and what [handler] returns is sent back before the
    connection is closed. [serve] returns at once; the unikernel keeps
    serving after [main] ends. *)
| serve (port : nat) (handler : string -> io string) : io unit
(** connect to [address] (an IP address, as ["192.168.64.1"], or a host
    name, as ["example.org"], looked up as [resolve] does) on [port],
    send [request], and return everything the other side sends back before
    it closes ([Reply]), or why there is nothing: the connection was
    [Refused], nothing answered within 10 seconds ([TimedOut]), or the
    address is neither an IP address nor a name that resolves
    ([BadAddress]; the image's [unresolved] event says why) *)
| fetch (address : string) (port : nat) (request : string) : io fetched
(** the IPv4 address of the host name [host] (as ["mirageos.org"]), asked
    of the DNS resolvers the network gives the unikernel; no answer within
    10 seconds is [Unresolved] *)
| resolve (host : string) : io resolved
(** an HTTPS request, HTTP/1.1 over TLS: [verb] (["GET"], ["POST"], ...)
    [path] (as ["/api/blocks/tip/height"], with its query) on [host], a
    host name, at [port] (443 for HTTPS), with [headers] and [body]. The
    name is resolved, the server's certificate checked against the NSS
    certificate authorities for that name, and the answer read to its end:
    [Answer], or why there is none ([Unanswered]), within 30 seconds and up
    to 16 MB. [Host], [Connection] and [Content-Length] are set by the
    request itself; a header with a line break in it is refused. *)
| https (verb host : string) (port : nat) (path : string) (headers : list (string * string)) (body : string) : io answered
(** accept TCP connections on [port], each with [handler], which reads and
    writes it as long as it likes; the connection is closed when [handler]
    ends. [listen] returns at once; the unikernel keeps listening after
    [main] ends. *)
| listen (port : nat) (handler : connection -> io unit) : io unit
(** open a connection to [address] (an IP address, or a host name, as for
    [fetch]) on [port]; it stays open until [close], or until the other
    side closes it *)
| connect (address : string) (port : nat) : io connected
(** [connect], giving up after [milliseconds] ([ConnectTimedOut]) rather
    than 10 seconds, looking a name up included: for a program that dials
    from its loop *)
| connect_within (address : string) (port : nat) (milliseconds : N) : io connected
(** write [data] on the connection, as it is ([send_line] adds the line
    break) *)
| send (c : connection) (data : string) : io sent
(** the next line the other side sends, up to its line break ["\n"] (a
    ["\r"] before it is dropped too) *)
| receive_line (c : connection) : io received
(** the next frame the other side sends: four bytes of length, most
    significant first, then that many bytes ([frame] makes one,
    [send_frame] sends one). It waits [seconds] seconds at most ([0]: as
    long as it takes). A frame longer than [max_frame] bytes is
    [FrameTooLarge], and the connection is closed. Lines and frames read
    the same bytes, in order: what one leaves, the other gets. *)
| receive_frame (c : connection) (seconds : nat) : io framed
(** what the connection has received, as TCP delivered it, cut nowhere:
    what was left past the last line or frame taken, or else the next
    bytes to arrive, waiting [milliseconds] at most ([0]: as long as it
    takes). For any connection, accepted or opened; lines, frames and
    [receive] read the same bytes, in order. *)
| receive (c : connection) (milliseconds : N) : io chunk
(** the unikernel's own IPv4 address, as the network configured it
    (["10.0.0.2"]); [None] when it has none *)
| local_address : io (option string)
(** close the connection; closing it again does nothing *)
| close (c : connection) : io unit
(** accept TCP connections on [port] into the mailbox: each one's
    opening, the bytes it receives and its end are [mailbox]'s. The
    program can [send] on one and [close] it (which posts no
    [LinkClosed]); [receive_line] and [receive_frame] on it would take
    bytes the mailbox is given. Returns at once; the unikernel keeps
    listening after [main] ends. *)
| listen_mailbox (port : nat) : io unit
(** what came in on [listen_mailbox]'s connections since the last
    [mailbox], oldest first; when nothing has, it waits for something,
    [milliseconds] at most, and is [nil] when the time is up *)
| mailbox (milliseconds : N) : io (list link_event)
(** the connection's bytes as [Linked] events of [select] (and
    [mailbox]): [LinkBytes] as they arrive, then [LinkClosed] when the
    other side ends it. For a connection the program opened, as
    [listen_mailbox] does for those it accepts; [receive] on it would take
    bytes the events are given. Watching it again does nothing. *)
| watch (c : connection) : io unit
(** a [Timer tag] event for [select] once [milliseconds] have passed;
    returns at once *)
| after (milliseconds : N) (tag : nat) : io unit
(** what came in since the last [select], oldest first: what connections
    of [listen_mailbox] and [watch] did, UDP datagrams, timers that came
    due. When nothing has, it waits for something, [milliseconds] at most,
    and is [nil] when the time is up ([0]: it does not wait). A select over
    everything, for a program with one loop. [mailbox] takes only the
    [Linked] events, and leaves the others to [select]. *)
| select (milliseconds : N) : io (list event)
(** receive the UDP datagrams sent to [port] as [Datagram] events of
    [select]; returns at once, and the unikernel keeps receiving after
    [main] ends *)
| udp_listen (port : nat) : io unit
(** send [data] as one UDP datagram to [address] (an IP address) at
    [port], from [source_port] ([0]: one the stack picks): [true] when it
    went out, [false] for an address that is not an IP address or a
    datagram the stack could not send *)
| udp_send (address : string) (port source_port : nat) (data : string) : io bool
(** Named files on the attached [storage] block device. Names are opaque
    keys, not host paths. [None] means missing; [Some ""] means present
    and empty. I/O errors stop the image rather than masquerading as missing.
    Writes replace bytes; append creates missing names and preserves order.
    These operations are serialized, and return after the device write.
    Attach the same disk to retain files across image boots. *)
(** Block devices by name: a disk the image is given, as [solo5-hvt
    --block:rootfs=rootfs.img], read and written by sectors. [name] is a
    string literal ([disk_read "rootfs" 0 8]): the image declares each
    disk the program names when it is built, and [soma run] attaches
    NAME.img. Names are letters and digits, and not [storage], which is
    the named files' device. *)
(** the disk's sector size in bytes and its number of sectors; [None]
    when it was not attached *)
| disk_info (name : string) : io (option (nat * nat))
(** [count] sectors from [sector] on, as bytes; [None] when the disk was
    not attached, the sectors are past its end, or the read failed *)
| disk_read (name : string) (sector count : nat) : io (option string)
(** write [data], whole sectors of it, from [sector] on: [true] when it was
    written, [false] when the disk was not attached or is read-only, the
    data is not whole sectors or goes past the end, or the write failed *)
| disk_write (name : string) (sector : nat) (data : string) : io bool
| read_file (name : string) : io (option string)
| write_file (name data : string) : io unit
| append_file (name data : string) : io unit
(** Buffers, read and written in place. An offset and a length that go
    past the buffer's end are refused: [None], or [false], and nothing
    is written. A byte is a [nat] below 256 ([buffer_set] keeps the low
    8 bits of what it is given); multi-byte numbers are little-endian,
    as AArch64's and x86's memory has them. *)
(** a buffer of [size] bytes, each [0] *)
| new_buffer (size : nat) : io buffer
| buffer_size (b : buffer) : io nat
(** the byte at [offset] *)
| buffer_get (b : buffer) (offset : nat) : io (option nat)
| buffer_set (b : buffer) (offset value : nat) : io bool
(** [length] bytes from [offset], as a string *)
| buffer_read (b : buffer) (offset length : nat) : io (option string)
(** [data]'s bytes, from [offset] on *)
| buffer_write (b : buffer) (offset : nat) (data : string) : io bool
(** [length] bytes of [src] from [src_offset] to [dst] from [dst_offset]
    (the same buffer included: as if through a copy) *)
| buffer_copy (src : buffer) (src_offset : nat) (dst : buffer) (dst_offset length : nat) : io bool
(** [length] bytes from [offset], each [value] *)
| buffer_fill (b : buffer) (offset length value : nat) : io bool
(** the 8 bytes from [offset], as a word *)
| buffer_get_word (b : buffer) (offset : nat) : io (option Word64.word64)
| buffer_set_word (b : buffer) (offset : nat) (w : Word64.word64) : io bool
(** the [width] bytes from [offset] (1, 2 or 4; another width is
    [None]), as a number *)
| buffer_get_uint (b : buffer) (offset width : nat) : io (option nat)
(** [value]'s low [width] bytes (1, 2 or 4; another is [false]) *)
| buffer_set_uint (b : buffer) (offset width value : nat) : io bool
(** [disk_read] into a buffer: [count] sectors from [sector], to [b] from
    [offset], without a string between. [false] as [disk_read] is [None],
    or when they do not fit in [b]. *)
| disk_read_into (name : string) (sector count : nat) (b : buffer) (offset : nat) : io bool
(** [disk_write] from a buffer: its [length] bytes from [offset], whole
    sectors, from [sector] on *)
| disk_write_from (name : string) (sector : nat) (b : buffer) (offset length : nat) : io bool
(** [send] of a buffer's [length] bytes from [offset]; bytes past its end
    fail the task *)
| send_buffer (c : connection) (b : buffer) (offset length : nat) : io sent
(** Signals: tasks wait for one another. *)
| new_signal : io signal
(** count one more, and wake every task waiting for the signal *)
| notify (s : signal) : io unit
(** how many times it was notified *)
| signal_count (s : signal) : io nat
(** wait until the signal's count is past [seen]: [Some] the count, at
    once if it already is; [None] when [milliseconds] pass first ([0]: as
    long as it takes) *)
| wait_signal (s : signal) (seen : nat) (milliseconds : N) : io (option nat)
(** the cell is gone: what it held can be freed, and reading or writing it
    again fails the task *)
| free_cell {A : Type} (c : cell A) : io unit
(** the image forgets the task's result (the task goes on if it has not
    ended): it can be freed, and [await] of it is [TaskFailed] *)
| forget {A : Type} (t : task A) : io unit
(** wait for what OCaml promised: its value, or the task fails as OCaml's
    did *)
| await_promise {A : Type} (p : promise A) : io A
(** yield cooperatively without adding a clock delay *)
| yield : io unit
(** recover an action's failure without starting another task; exit still exits *)
| attempt {A : Type} (body : io A) : io (awaited A)
(** cleanup runs on success, failure and cooperative cancellation *)
| finally {A : Type} (body : io A) (cleanup : io unit) : io A
(** first result, cancelling the other action; tag values in A to distinguish sides *)
| race {A : Type} (left right : io A) : io (awaited A)
(** request cooperative cancellation of a pending forked task; false if absent/done *)
| cancel {A : Type} (t : task A) : io bool
| new_context_key {A : Type} : io (context_key A)
| get_context {A : Type} (key : context_key A) : io (option A)
| with_context {A B : Type} (key : context_key A) (value : option A) (body : io B) : io B
| free_context_key {A : Type} (key : context_key A) : io unit.

Arguments ret {A} a.
Arguments bind {A B} m k.
Arguments forever {A} body.
Arguments iterate {S A} step start.
Arguments exit {A} code.
Arguments call {A} f.
Arguments new_cell {A} a.
Arguments read_cell {A} c.
Arguments write_cell {A} c a.
Arguments modify_cell {A} c f.
Arguments Cell {A} id.
Arguments fork {A} body.
Arguments await {A} t.
Arguments await_within {A} t milliseconds.
Arguments Task {A} id.
Arguments Completed {A} a.
Arguments TaskFailed {A} why.
Arguments free_cell {A} c.
Arguments forget {A} t.
Arguments await_promise {A} p.
Arguments ContextKey {A} id.
Arguments attempt {A} body.
Arguments finally {A} body cleanup.
Arguments race {A} left right.
Arguments cancel {A} t.
Arguments new_context_key {A}.
Arguments get_context {A} key.
Arguments with_context {A B} key value body.
Arguments free_context_key {A} key.

Declare Scope io_scope.
Delimit Scope io_scope with io.
Bind Scope io_scope with io.

(** [x <- m ;; rest]: run [m], call its result [x], then [rest].
    [m ;; rest]: run [m], then [rest]. *)
Notation "x <- m ;; rest" := (bind m (fun x => rest))
  (at level 61, m at next level, right associativity) : io_scope.
Notation "m ;; rest" := (bind m (fun _ => rest))
  (at level 61, right associativity) : io_scope.

Open Scope io_scope.

(** [https]'s usual requests, on port 443 *)
Definition https_get (host path : string) : io answered := https "GET" host 443 path nil "".
Definition https_post (host path content_type body : string) : io answered :=
  https "POST" host 443 path (cons ("content-type", content_type) nil) body.

(** the value of the header [name], given in lower case, as [https] gives
    the headers *)
Fixpoint header (name : string) (headers : list (string * string)) : option string :=
  match headers with
  | nil => None
  | cons (k, v) rest => if String.eqb k name then Some v else header name rest
  end.

Example header_found : header "content-type" (cons ("server", "x") (cons ("content-type", "text/html") nil)) = Some "text/html" := eq_refl.
Example header_missing : header "etag" (cons ("server", "x") nil) = None := eq_refl.

(** Elapsed milliseconds; saturates at zero for reversed arguments. *)
Definition elapsed_ms (start finish : N) : N := (finish - start)%N.

Example elapsed_ms_zero : elapsed_ms 0 0 = 0%N := eq_refl.
Example elapsed_ms_boundary : N.leb 1000 (elapsed_ms 42 1042) = true := eq_refl.
Example elapsed_ms_large : elapsed_ms 4294967296 4294968296 = 1000%N := eq_refl.
Example elapsed_ms_reversed : elapsed_ms 2 1 = 0%N := eq_refl.

(** * Named-file storage model

    A pure specification for a persistent storage interpreter. Names are
    opaque strings, not host paths. [None] distinguishes a missing file
    from an existing empty file. This model does not itself perform I/O. *)
Module Files.

Definition state : Type := list (string * string).
Definition empty : state := nil.

Fixpoint read (name : string) (files : state) : option string :=
  match files with
  | nil => None
  | cons (key, contents) rest =>
    if String.eqb name key then Some contents else read name rest
  end.

(** Replace the first matching entry, or create a new entry. Starting
    with [empty], writes keep at most one entry for each name. *)
Fixpoint write (name contents : string) (files : state) : state :=
  match files with
  | nil => cons (name, contents) nil
  | cons (key, previous) rest =>
    if String.eqb name key then cons (name, contents) rest
    else cons (key, previous) (write name contents rest)
  end.

(** Appending to a missing file creates it, including an empty append. *)
Definition append (name contents : string) (files : state) : state :=
  write name
    (match read name files with
     | None => contents
     | Some previous => String.append previous contents
     end) files.

Theorem read_write : forall files name contents,
  read name (write name contents files) = Some contents.
Proof.
  induction files as [|[key previous] rest IH]; intros name contents;
    cbn [read write].
  - now rewrite String.eqb_refl.
  - destruct (String.eqb name key) eqn:E; cbn [read].
    + now rewrite String.eqb_refl.
    + rewrite E. apply IH.
Qed.

Theorem read_write_other : forall files name other contents,
  String.eqb other name = false ->
  read other (write name contents files) = read other files.
Proof.
  induction files as [|[key previous] rest IH]; intros name other contents H;
    cbn [read write].
  - now rewrite H.
  - destruct (String.eqb name key) eqn:E; cbn [read].
    + apply String.eqb_eq in E. subst key. now rewrite H.
    + destruct (String.eqb other key); [reflexivity|]. apply IH. exact H.
Qed.

Theorem read_append : forall files name contents,
  read name (append name contents files) =
    Some (match read name files with
          | None => contents
          | Some previous => String.append previous contents
          end).
Proof. intros. unfold append. apply read_write. Qed.

(** a write replaces what an earlier write to the same name left: the
    state is as if the earlier write had not happened *)
Theorem write_write : forall files name first second,
  write name second (write name first files) = write name second files.
Proof.
  induction files as [|[key previous] rest IH]; intros name first second;
    cbn [write].
  - now rewrite String.eqb_refl.
  - destruct (String.eqb name key) eqn:E; cbn [write].
    + now rewrite String.eqb_refl.
    + rewrite E. now rewrite IH.
Qed.

(** appending to one name leaves every other name as it was *)
Theorem read_append_other : forall files name other contents,
  String.eqb other name = false ->
  read other (append name contents files) = read other files.
Proof. intros. unfold append. now apply read_write_other. Qed.

Lemma append_assoc : forall a b c : string,
  String.append (String.append a b) c = String.append a (String.append b c).
Proof.
  induction a as [|x a IH]; intros b c; cbn [String.append]; [reflexivity|].
  now rewrite IH.
Qed.

(** two appends keep their order, after what was there *)
Theorem read_append_append : forall files name first second,
  read name (append name second (append name first files)) =
    Some (match read name files with
          | None => String.append first second
          | Some previous => String.append previous (String.append first second)
          end).
Proof.
  intros files name first second.
  rewrite read_append, read_append.
  destruct (read name files); [now rewrite append_assoc|reflexivity].
Qed.

End Files.

(** * Lines and frames: [Soma.Wire] (exported), and sending them *)

Require Export Soma.Wire.

(** send [line] and a line break on [c] *)
Definition send_line (c : connection) (line : string) : io sent :=
  send c (line ++ newline)%str.

(** send [data] as a frame on [c] *)
Definition send_frame (c : connection) (data : string) : io sent :=
  send c (frame data).

