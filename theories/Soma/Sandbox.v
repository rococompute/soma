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
    looping, reading the clock, serving and fetching over TCP, in order,
    ending with a result of type [A]. Building an [io] does nothing; the
    image runs [main]. A program that uses [serve] or [fetch] gets a
    network stack and runs under [solo5-vmnet]. *)

From Stdlib Require Strings.String Strings.Ascii.
From Corelib Require Extraction.
(* strings and characters as OCaml char lists and chars in the image *)
From Stdlib Require ExtrOcamlString.
Require Import Soma.Strings Soma.Show.

Inductive io : Type -> Type :=
| ret {A : Type} (a : A) : io A
(** [bind m k]: run [m], then [k] on its result *)
| bind {A B : Type} (m : io A) (k : A -> io B) : io B
(** a line on the console *)
| print (s : string) : io unit
| sleep (seconds : nat) : io unit
(** [body], again and again; it never ends, so its type is any [io A] *)
| forever {A : Type} (body : io unit) : io A
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
    it closes, or [None] when the connection fails or nothing answers within
    10 seconds *)
| fetch (address : string) (port : nat) (request : string) : io (option string).

Arguments ret {A} a.
Arguments bind {A B} m k.
Arguments forever {A} body.
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

(** * HTTP, for [serve] and [fetch] *)

(** a line break in HTTP *)
Definition crlf : string :=
  String.String (Ascii.ascii_of_nat 13) (String.String (Ascii.ascii_of_nat 10) String.EmptyString).

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
