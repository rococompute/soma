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
    that uses [serve], [fetch], [listen] or [connect] gets a network stack
    and runs under [solo5-vmnet]. *)

From Stdlib Require Strings.String Strings.Ascii.
From Corelib Require Extraction.
(* In the image, strings are OCaml's, [nat] is OCaml's [int], and [bool],
   [option], pairs and lists are OCaml's (the image's extraction:
   ExtrOcamlNativeString, ExtrOcamlNatInt, ExtrOcamlBasic), as in a
   program built for the machine. *)
From Stdlib Require Import NArith.BinNat.
From Stdlib Require Import Lia.
Require Import Soma.Strings Soma.Show.

(** What [fetch] gets: the reply, or why there is none *)
Inductive fetched : Type :=
| Reply (body : string)   (* what the other side sent back before it closed *)
| Refused                 (* nothing listens at that address and port *)
| TimedOut                (* nothing answered within 10 seconds *)
| BadAddress.             (* the address is not an IP address *)

(** * Links: TCP connections that stay open, line by line *)

(** a connection open at the unikernel, as [listen] or [connect] give it;
    the image knows it by its number *)
Inductive connection : Type := Connection (id : nat).

(** What [connect] gets: a connection, or why there is none *)
Inductive connected : Type :=
| Connected (c : connection)  (* the other side accepted *)
| ConnectRefused              (* nothing listens at that address and port *)
| ConnectTimedOut             (* nothing answered within 10 seconds *)
| ConnectBadAddress.          (* the address is not an IP address *)

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
(** connect to [address] (an IP address, as ["192.168.64.1"]) on [port],
    send [request], and return everything the other side sends back before
    it closes ([Reply]), or why there is nothing: the connection was
    [Refused], nothing answered within 10 seconds ([TimedOut]), or the
    address is not an IP address ([BadAddress]) *)
| fetch (address : string) (port : nat) (request : string) : io fetched
(** accept TCP connections on [port], each with [handler], which reads and
    writes it as long as it likes; the connection is closed when [handler]
    ends. [listen] returns at once; the unikernel keeps listening after
    [main] ends. *)
| listen (port : nat) (handler : connection -> io unit) : io unit
(** open a connection to [address] (an IP address) on [port]; it stays
    open until [close], or until the other side closes it *)
| connect (address : string) (port : nat) : io connected
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
(** close the connection; closing it again does nothing *)
| close (c : connection) : io unit
(** Named files on the attached [storage] block device. Names are opaque
    keys, not host paths. [None] means missing; [Some ""] means present
    and empty. I/O errors stop the image rather than masquerading as missing.
    Writes replace bytes; append creates missing names and preserves order.
    These operations are serialized, and return after the device write.
    Attach the same disk to retain files across image boots. *)
| read_file (name : string) : io (option string)
| write_file (name data : string) : io unit
| append_file (name data : string) : io unit.

Arguments ret {A} a.
Arguments bind {A B} m k.
Arguments forever {A} body.
Arguments iterate {S A} step start.
Arguments exit {A} code.

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

(** * HTTP, for [serve] and [fetch] *)

(** a line break in HTTP *)
Definition crlf : string :=
  String.String (Ascii.ascii_of_nat 13) (String.String (Ascii.ascii_of_nat 10) String.EmptyString).

(** a line break, ["\n"] *)
Definition newline : string :=
  String.String (Ascii.ascii_of_nat 10) String.EmptyString.

(** send [line] and a line break on [c] *)
Definition send_line (c : connection) (line : string) : io sent :=
  send c (line ++ newline)%str.

(** an HTTP response with status [200 OK] and [body] as plain text *)
Definition http_response (body : string) : string :=
  ("HTTP/1.1 200 OK" ++ crlf ++
   "Content-Type: text/plain; charset=utf-8" ++ crlf ++
   "Content-Length: " ++ to_string (String.length body) ++ crlf ++
   "Connection: close" ++ crlf ++ crlf ++ body)%str.

(** an HTTP [GET] request for [path] *)
Definition http_get (path : string) : string :=
  ("GET " ++ path ++ " HTTP/1.1" ++ crlf ++
   "Host: soma" ++ crlf ++
   "Connection: close" ++ crlf ++ crlf)%str.

Fixpoint drop_through_space (s : string) : string :=
  match s with
  | String.EmptyString => String.EmptyString
  | String.String c rest =>
    if Ascii.eqb c (Ascii.ascii_of_nat 32) then rest else drop_through_space rest
  end.

Fixpoint take_until_space (s : string) : string :=
  match s with
  | String.EmptyString => String.EmptyString
  | String.String c rest =>
    if Ascii.eqb c (Ascii.ascii_of_nat 32) then String.EmptyString
    else String.String c (take_until_space rest)
  end.

(** the path of an HTTP request: ["/hello"] in ["GET /hello HTTP/1.1 ..."] *)
Definition http_path (request : string) : string :=
  take_until_space (drop_through_space request).

(** * Framing: lines and length-prefixed frames out of the bytes received

    TCP delivers bytes in chunks that need not match what was sent: half a
    message, or several at once. A receive keeps what it has received past
    the last message it returned, and returns exactly one message. These
    functions are that, without a network: [take_line] and [take_frame]
    take the first message of what was received, and leave the rest;
    [receive_chunks] feeds chunks one after another, as they would arrive.
    The image (toplevel/somaMirage.ml, [Soma_rt.take_line] and
    [Soma_rt.take_frame]) does the same with OCaml's strings. *)

(** the longest frame [receive_frame] takes, in bytes: 1 MiB *)
Definition max_frame : N := 1048576%N.

(** one byte, [n mod 256] *)
Definition byte (n : N) : string :=
  String.String (Ascii.ascii_of_N (N.modulo n 256)) String.EmptyString.

(** [n] in four bytes, most significant first *)
Definition length_prefix (n : N) : string :=
  (byte (N.div n 16777216) ++ byte (N.div n 65536) ++ byte (N.div n 256) ++ byte n)%str.

(** [data] as a frame: its length in four bytes, then [data] *)
Definition frame (data : string) : string :=
  (length_prefix (N.of_nat (String.length data)) ++ data)%str.

(** send [data] as a frame on [c] *)
Definition send_frame (c : connection) (data : string) : io sent :=
  send c (frame data).

(** the first [n] characters of [s], and the rest; [None] when [s] is
    shorter *)
Fixpoint split_at (n : nat) (s : string) : option (string * string) :=
  match n with
  | O => Some (String.EmptyString, s)
  | S k =>
    match s with
    | String.EmptyString => None
    | String.String c rest =>
      match split_at k rest with
      | Some (taken, after) => Some (String.String c taken, after)
      | None => None
      end
    end
  end.

(** the characters up to the first line break, and what follows it *)
Fixpoint take_raw_line (s : string) : option (string * string) :=
  match s with
  | String.EmptyString => None
  | String.String c rest =>
    if Ascii.eqb c (Ascii.ascii_of_nat 10) then Some (String.EmptyString, rest)
    else
      match take_raw_line rest with
      | Some (line, after) => Some (String.String c line, after)
      | None => None
      end
  end.

(** [s] without a ["\r"] at its end *)
Fixpoint drop_cr (s : string) : string :=
  match s with
  | String.EmptyString => String.EmptyString
  | String.String c String.EmptyString =>
    if Ascii.eqb c (Ascii.ascii_of_nat 13) then String.EmptyString else s
  | String.String c rest => String.String c (drop_cr rest)
  end.

(** the first line of what was received, without its line break (nor a
    ["\r"] before it), and what follows; [None] when there is no whole line
    yet, and all of it is kept *)
Definition take_line (buffer : string) : option (string * string) :=
  match take_raw_line buffer with
  | Some (line, after) => Some (drop_cr line, after)
  | None => None
  end.

(** What [take_frame] finds at the start of what was received *)
Inductive frame_step : Type :=
| NeedMore                     (* no whole frame yet: keep all of it *)
| Whole (data rest : string)   (* a frame, and what follows it *)
| Oversized.                   (* a length over the limit *)

(** the length that four bytes say *)
Definition frame_length (a b c d : Ascii.ascii) : N :=
  (((Ascii.N_of_ascii a * 256 + Ascii.N_of_ascii b) * 256 + Ascii.N_of_ascii c) * 256
   + Ascii.N_of_ascii d)%N.

(** the first frame of what was received, frames of [limit] bytes at most *)
Definition take_frame (limit : N) (buffer : string) : frame_step :=
  match buffer with
  | String.String a (String.String b (String.String c (String.String d rest))) =>
    let n := frame_length a b c d in
    if N.ltb limit n then Oversized
    else
      match split_at (N.to_nat n) rest with
      | Some (data, after) => Whole data after
      | None => NeedMore
      end
  | _ => NeedMore
  end.

(** every whole line of [buffer], in order, and what is kept; [fuel]
    bounds the lines, each of which takes a character at least *)
Fixpoint lines_in (fuel : nat) (buffer : string) : list string * string :=
  match fuel with
  | O => (nil, buffer)
  | S more =>
    match take_line buffer with
    | Some (line, rest) => let r := lines_in more rest in (cons line (fst r), snd r)
    | None => (nil, buffer)
    end
  end.

Definition split_lines (buffer : string) : list string * string :=
  lines_in (S (String.length buffer)) buffer.

(** every whole frame of [buffer], in order, and what is kept (from an
    oversized frame on, all of it) *)
Fixpoint frames_in (fuel : nat) (limit : N) (buffer : string) : list string * string :=
  match fuel with
  | O => (nil, buffer)
  | S more =>
    match take_frame limit buffer with
    | Whole data rest => let r := frames_in more limit rest in (cons data (fst r), snd r)
    | _ => (nil, buffer)
    end
  end.

Definition split_frames (limit : N) (buffer : string) : list string * string :=
  frames_in (S (String.length buffer)) limit buffer.

(** [chunks], received one after another after [kept]: the messages
    [split] finds, in order, and what is kept at the end *)
Fixpoint receive_chunks (split : string -> list string * string) (kept : string)
    (chunks : list string) : list string * string :=
  match chunks with
  | nil => (nil, kept)
  | cons chunk more =>
    let r := split (String.append kept chunk) in
    let after := receive_chunks split (snd r) more in
    (app (fst r) (fst after), snd after)
  end.

(** Lines, on fixed chunks *)

(** a line split across chunks *)
Example line_across_chunks :
  receive_chunks split_lines "" (cons "hel" (cons ("lo" ++ newline)%str nil))
  = (cons "hello" nil, ""%str) := eq_refl.

(** several lines in one chunk *)
Example lines_in_one_chunk :
  receive_chunks split_lines "" (cons ("a" ++ newline ++ "b" ++ newline ++ "c" ++ newline)%str nil)
  = (cons "a" (cons "b" (cons "c" nil)), ""%str) := eq_refl.

(** a line not finished is kept, and finished by the next chunk *)
Example line_partial_kept :
  receive_chunks split_lines "" (cons ("one" ++ newline ++ "tw")%str nil)
  = (cons "one" nil, "tw"%str) := eq_refl.
Example line_partial_finished :
  receive_chunks split_lines "" (cons ("one" ++ newline ++ "tw")%str (cons ("o" ++ newline)%str nil))
  = (cons "one" (cons "two" nil), ""%str) := eq_refl.

(** an empty line is a line; a ["\r"] before the line break is dropped *)
Example line_empty :
  receive_chunks split_lines "" (cons (newline ++ "x" ++ crlf)%str nil)
  = (cons "" (cons "x" nil), ""%str) := eq_refl.

(** a line break alone in a chunk ends the line before it *)
Example line_break_alone :
  receive_chunks split_lines "" (cons "abc" (cons newline nil))
  = (cons "abc" nil, ""%str) := eq_refl.

(** Frames, on fixed chunks *)

(** a frame split across chunks *)
Example frame_across_chunks :
  receive_chunks (split_frames max_frame) ""
    (cons (String.substring 0 6 (frame "hello")) (cons (String.substring 6 3 (frame "hello")) nil))
  = (cons "hello" nil, ""%str) := eq_refl.

(** several frames in one chunk; one of them is empty, one has a line break *)
Example frames_in_one_chunk :
  receive_chunks (split_frames max_frame) ""
    (cons (frame "one" ++ frame "" ++ frame ("two" ++ newline ++ "lines") ++ frame "three")%str nil)
  = (cons "one" (cons "" (cons ("two" ++ newline ++ "lines")%str (cons "three" nil))), ""%str)
  := eq_refl.

(** a frame not finished is kept *)
Example frame_partial_kept :
  receive_chunks (split_frames max_frame) ""
    (cons (frame "one" ++ String.substring 0 5 (frame "two"))%str nil)
  = (cons "one" nil, String.substring 0 5 (frame "two")) := eq_refl.

(** a length prefix that arrives alone is kept, and the frame is taken
    once its bytes follow; so is a prefix that arrives in two halves *)
Example frame_prefix_alone :
  receive_chunks (split_frames max_frame) "" (cons (length_prefix 3) nil)
  = (nil, length_prefix 3) := eq_refl.
Example frame_prefix_then_data :
  receive_chunks (split_frames max_frame) "" (cons (length_prefix 3) (cons "abc" nil))
  = (cons "abc" nil, ""%str) := eq_refl.
Example frame_prefix_halves :
  receive_chunks (split_frames max_frame) ""
    (cons (String.substring 0 2 (frame "abc")) (cons (String.substring 2 5 (frame "abc")) nil))
  = (cons "abc" nil, ""%str) := eq_refl.

(** a length over the limit *)
Example frame_oversized : take_frame 2 (frame "abc") = Oversized := eq_refl.

(** What is kept never holds a whole message *)

Lemma split_at_shorter : forall n s taken after,
  split_at n s = Some (taken, after) -> String.length after <= String.length s.
Proof.
  induction n as [|n IH]; intros s taken after H; cbn [split_at] in H.
  - injection H as Ht Ha. subst after. lia.
  - destruct s as [|c rest].
    + discriminate H.
    + destruct (split_at n rest) as [[t a]|] eqn:E.
      * injection H as Ht Ha. subst after. apply IH in E. simpl. lia.
      * discriminate H.
Qed.

Lemma take_raw_line_shorter : forall s line after,
  take_raw_line s = Some (line, after) -> String.length after < String.length s.
Proof.
  induction s as [|c rest IH]; intros line after H; cbn [take_raw_line] in H.
  - discriminate H.
  - destruct (Ascii.eqb c _).
    + injection H as Hl Ha. subst after. simpl. lia.
    + destruct (take_raw_line rest) as [[l a]|] eqn:E.
      * injection H as Hl Ha. subst after. pose proof (IH l a eq_refl). simpl. lia.
      * discriminate H.
Qed.

Lemma take_line_shorter : forall s line after,
  take_line s = Some (line, after) -> String.length after < String.length s.
Proof.
  intros s line after H. unfold take_line in H.
  destruct (take_raw_line s) as [[l a]|] eqn:E.
  - injection H as Hl Ha. subst after. exact (take_raw_line_shorter s l a E).
  - discriminate H.
Qed.

Lemma take_frame_shorter : forall limit s data after,
  take_frame limit s = Whole data after -> String.length after < String.length s.
Proof.
  intros limit s data after H. unfold take_frame in H.
  destruct s as [|a [|b [|c [|d rest]]]]; cbv beta iota zeta in H; try discriminate H.
  destruct (N.ltb limit (frame_length a b c d)); try discriminate H.
  destruct (split_at (N.to_nat (frame_length a b c d)) rest) as [[t r]|] eqn:E;
    try discriminate H.
  injection H as Ht Hr. subst after. apply split_at_shorter in E. simpl. lia.
Qed.

Lemma lines_in_kept : forall fuel s, String.length s < fuel ->
  take_line (snd (lines_in fuel s)) = None.
Proof.
  induction fuel as [|fuel IH]; intros s H.
  - lia.
  - cbn [lines_in]. destruct (take_line s) as [[line rest]|] eqn:E.
    + cbn [snd]. apply IH. apply take_line_shorter in E. lia.
    + cbn [snd]. exact E.
Qed.

(** after [split_lines], what is kept has no line break *)
Theorem split_lines_kept : forall buffer, take_line (snd (split_lines buffer)) = None.
Proof.
  intros buffer. unfold split_lines. apply lines_in_kept. lia.
Qed.

Lemma frames_in_kept : forall fuel limit s, String.length s < fuel ->
  match take_frame limit (snd (frames_in fuel limit s)) with Whole _ _ => False | _ => True end.
Proof.
  induction fuel as [|fuel IH]; intros limit s H.
  - lia.
  - cbn [frames_in]. destruct (take_frame limit s) as [|data rest|] eqn:E.
    + cbn [snd]. rewrite E. exact I.
    + cbn [snd]. apply IH. apply take_frame_shorter in E. lia.
    + cbn [snd]. rewrite E. exact I.
Qed.

(** after [split_frames], what is kept holds no whole frame *)
Theorem split_frames_kept : forall limit buffer,
  match take_frame limit (snd (split_frames limit buffer)) with Whole _ _ => False | _ => True end.
Proof.
  intros limit buffer. unfold split_frames. apply frames_in_kept. lia.
Qed.

(** How the bytes were cut into chunks changes nothing *)

(** the chunks, one after another *)
Fixpoint concat_chunks (chunks : list string) : string :=
  match chunks with
  | nil => String.EmptyString
  | cons chunk more => String.append chunk (concat_chunks more)
  end.

Lemma append_assoc_str : forall a b c : string,
  String.append (String.append a b) c = String.append a (String.append b c).
Proof.
  induction a as [|x a IH]; intros b c; cbn [String.append].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma append_empty_str : forall a : string, String.append a String.EmptyString = a.
Proof.
  induction a as [|x a IH]; cbn [String.append].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma split_at_app : forall n s t taken after,
  split_at n s = Some (taken, after) ->
  split_at n (String.append s t) = Some (taken, String.append after t).
Proof.
  induction n as [|n IH]; intros s t taken after H.
  - cbn [split_at] in H |- *. injection H as <- <-. reflexivity.
  - destruct s as [|c rest]; cbn [String.append split_at] in H |- *.
    + discriminate H.
    + destruct (split_at n rest) as [[x y]|] eqn:E; [|discriminate H].
      injection H as <- <-. rewrite (IH rest t x y E). reflexivity.
Qed.

Lemma take_raw_line_app : forall s t line after,
  take_raw_line s = Some (line, after) ->
  take_raw_line (String.append s t) = Some (line, String.append after t).
Proof.
  induction s as [|c rest IH]; intros t line after H; cbn [String.append take_raw_line] in H |- *.
  - discriminate H.
  - destruct (Ascii.eqb c _).
    + injection H as <- <-. reflexivity.
    + destruct (take_raw_line rest) as [[l a]|] eqn:E; [|discriminate H].
      injection H as <- <-. rewrite (IH t l a eq_refl). reflexivity.
Qed.

Lemma take_line_app : forall s t line after,
  take_line s = Some (line, after) ->
  take_line (String.append s t) = Some (line, String.append after t).
Proof.
  intros s t line after H. unfold take_line in H |- *.
  destruct (take_raw_line s) as [[l a]|] eqn:E; [|discriminate H].
  injection H as <- <-. rewrite (take_raw_line_app s t l a E). reflexivity.
Qed.

Lemma take_frame_app : forall limit s t data after,
  take_frame limit s = Whole data after ->
  take_frame limit (String.append s t) = Whole data (String.append after t).
Proof.
  intros limit s t data after H. unfold take_frame in H.
  destruct s as [|a [|b [|c [|d rest]]]]; cbv beta iota zeta in H; try discriminate H.
  cbn [String.append]. unfold take_frame. cbv beta iota zeta.
  destruct (N.ltb limit (frame_length a b c d)); [discriminate H|].
  destruct (split_at (N.to_nat (frame_length a b c d)) rest) as [[x y]|] eqn:E;
    [|discriminate H].
  injection H as <- <-. rewrite (split_at_app _ _ t x y E). reflexivity.
Qed.

Lemma lines_in_fuel : forall f g s, String.length s < f -> String.length s < g ->
  lines_in f s = lines_in g s.
Proof.
  induction f as [|f IH]; intros g s Hf Hg; [lia|].
  destruct g as [|g]; [lia|]. cbn [lines_in].
  destruct (take_line s) as [[l r]|] eqn:E; [|reflexivity].
  apply take_line_shorter in E. rewrite (IH g r) by lia. reflexivity.
Qed.

Lemma split_lines_step : forall s line rest, take_line s = Some (line, rest) ->
  split_lines s = (cons line (fst (split_lines rest)), snd (split_lines rest)).
Proof.
  intros s line rest E. pose proof (take_line_shorter _ _ _ E) as L.
  unfold split_lines at 1. cbn [lines_in]. rewrite E. cbv beta iota zeta.
  rewrite (lines_in_fuel (String.length s) (S (String.length rest)) rest) by lia.
  reflexivity.
Qed.

Lemma split_lines_stop : forall s, take_line s = None -> split_lines s = (nil, s).
Proof.
  intros s E. unfold split_lines. cbn [lines_in]. rewrite E. reflexivity.
Qed.

(** the lines of [s] then [t]: those of [s], then those of what [s] left
    followed by [t] *)
Lemma split_lines_app : forall s t,
  split_lines (String.append s t)
  = (app (fst (split_lines s)) (fst (split_lines (String.append (snd (split_lines s)) t))),
     snd (split_lines (String.append (snd (split_lines s)) t))).
Proof.
  assert (forall n s t, String.length s < n ->
    split_lines (String.append s t)
    = (app (fst (split_lines s)) (fst (split_lines (String.append (snd (split_lines s)) t))),
       snd (split_lines (String.append (snd (split_lines s)) t)))) as G.
  { induction n as [|n IH]; intros s t Hs; [lia|].
    destruct (take_line s) as [[l r]|] eqn:E.
    - rewrite (split_lines_step _ _ _ (take_line_app s t l r E)).
      rewrite (split_lines_step _ _ _ E). cbn [fst snd app].
      apply take_line_shorter in E. rewrite (IH r t) by lia. reflexivity.
    - rewrite (split_lines_stop s E). cbn [fst snd app].
      destruct (split_lines (String.append s t)). reflexivity. }
  intros s t. apply (G (S (String.length s))). lia.
Qed.

Lemma receive_lines_kept : forall chunks kept, take_line kept = None ->
  receive_chunks split_lines kept chunks = split_lines (String.append kept (concat_chunks chunks)).
Proof.
  induction chunks as [|chunk more IH]; intros kept K;
    cbn [receive_chunks concat_chunks].
  - rewrite append_empty_str. rewrite (split_lines_stop kept K). reflexivity.
  - rewrite <- append_assoc_str. rewrite (split_lines_app (String.append kept chunk)).
    rewrite (IH _ (split_lines_kept _)). reflexivity.
Qed.

(** the lines received do not depend on how the bytes were cut into
    chunks: they are the lines of all the bytes, and so is what is kept *)
Theorem receive_lines_chunking : forall chunks,
  receive_chunks split_lines String.EmptyString chunks = split_lines (concat_chunks chunks).
Proof.
  intros chunks. apply (receive_lines_kept chunks String.EmptyString). reflexivity.
Qed.

Lemma frames_in_fuel : forall f g limit s, String.length s < f -> String.length s < g ->
  frames_in f limit s = frames_in g limit s.
Proof.
  induction f as [|f IH]; intros g limit s Hf Hg; [lia|].
  destruct g as [|g]; [lia|]. cbn [frames_in].
  destruct (take_frame limit s) as [|data r|] eqn:E; try reflexivity.
  apply take_frame_shorter in E. rewrite (IH g limit r) by lia. reflexivity.
Qed.

Lemma split_frames_step : forall limit s data rest, take_frame limit s = Whole data rest ->
  split_frames limit s
  = (cons data (fst (split_frames limit rest)), snd (split_frames limit rest)).
Proof.
  intros limit s data rest E. pose proof (take_frame_shorter _ _ _ _ E) as L.
  unfold split_frames at 1. cbn [frames_in]. rewrite E. cbv beta iota zeta.
  rewrite (frames_in_fuel (String.length s) (S (String.length rest)) limit rest) by lia.
  reflexivity.
Qed.

Lemma split_frames_stop : forall limit s,
  match take_frame limit s with Whole _ _ => False | _ => True end ->
  split_frames limit s = (nil, s).
Proof.
  intros limit s. unfold split_frames. cbn [frames_in].
  destruct (take_frame limit s); intros H; [reflexivity|contradiction|reflexivity].
Qed.

(** the frames of [s] then [t]: those of [s], then those of what [s] left
    followed by [t] *)
Lemma split_frames_app : forall limit s t,
  split_frames limit (String.append s t)
  = (app (fst (split_frames limit s))
         (fst (split_frames limit (String.append (snd (split_frames limit s)) t))),
     snd (split_frames limit (String.append (snd (split_frames limit s)) t))).
Proof.
  intros limit.
  assert (forall n s t, String.length s < n ->
    split_frames limit (String.append s t)
    = (app (fst (split_frames limit s))
           (fst (split_frames limit (String.append (snd (split_frames limit s)) t))),
       snd (split_frames limit (String.append (snd (split_frames limit s)) t)))) as G.
  { induction n as [|n IH]; intros s t Hs; [lia|].
    destruct (take_frame limit s) as [|d r|] eqn:E.
    - assert (Hstop : split_frames limit s = (nil, s))
        by (apply split_frames_stop; rewrite E; exact I).
      rewrite Hstop. cbn [fst snd app]. destruct (split_frames limit (String.append s t)). reflexivity.
    - rewrite (split_frames_step _ _ _ _ (take_frame_app limit s t d r E)).
      rewrite (split_frames_step _ _ _ _ E). cbn [fst snd app].
      apply take_frame_shorter in E. rewrite (IH r t) by lia. reflexivity.
    - assert (Hstop : split_frames limit s = (nil, s))
        by (apply split_frames_stop; rewrite E; exact I).
      rewrite Hstop. cbn [fst snd app]. destruct (split_frames limit (String.append s t)). reflexivity. }
  intros s t. apply (G (S (String.length s))). lia.
Qed.

Lemma receive_frames_kept : forall limit chunks kept,
  match take_frame limit kept with Whole _ _ => False | _ => True end ->
  receive_chunks (split_frames limit) kept chunks
  = split_frames limit (String.append kept (concat_chunks chunks)).
Proof.
  intros limit.
  induction chunks as [|chunk more IH]; intros kept K;
    cbn [receive_chunks concat_chunks].
  - rewrite append_empty_str. rewrite (split_frames_stop limit kept K). reflexivity.
  - rewrite <- append_assoc_str. rewrite (split_frames_app limit (String.append kept chunk)).
    rewrite (IH _ (split_frames_kept _ _)). reflexivity.
Qed.

(** the frames received do not depend on how the bytes were cut into
    chunks: they are the frames of all the bytes, and so is what is kept *)
Theorem receive_frames_chunking : forall limit chunks,
  receive_chunks (split_frames limit) String.EmptyString chunks
  = split_frames limit (concat_chunks chunks).
Proof.
  intros limit chunks. apply (receive_frames_kept limit chunks String.EmptyString). exact I.
Qed.
