(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Lines and frames on a connection, [Soma.Wire]

    Not part of the prelude, and not only for unikernels: what a program
    that talks over TCP does with the bytes it receives, without a network,
    so a program built for the machine and a Sandbox image (which exports
    it) split them with the same functions. HTTP's line breaks, requests,
    responses and paths; [frame] and [take_frame] (length-prefixed frames);
    [take_line] (lines); [split_lines], [split_frames] and [receive_chunks]
    (all the messages of what was received, chunk after chunk), with
    theorems that what is kept never holds a whole message and that the
    messages don't depend on how the bytes were cut into chunks.

    With strings as OCaml's and [nat] as its [int] (a Sandbox image, or a
    program that extracts them so), [take_frame] reads the length and
    takes the frame's bytes by offset, with [String.get] and
    [String.substring], rather than taking the string apart a character at
    a time, which copies the rest at each one. [split_at_walk] and
    [take_frame_walk], the same functions a character at a time, are what
    the proofs reason with ([split_at_walk_eq], [take_frame_eq]). *)

From Stdlib Require Strings.String Strings.Ascii.
From Stdlib Require Import NArith.BinNat.
From Stdlib Require Import Lia.
Require Import Soma.Strings Soma.Show.

(** * HTTP, for [serve] and [fetch] *)

(** a line break in HTTP *)
Definition crlf : string :=
  String.String (Ascii.ascii_of_nat 13) (String.String (Ascii.ascii_of_nat 10) String.EmptyString).

(** a line break, ["\n"] *)
Definition newline : string :=
  String.String (Ascii.ascii_of_nat 10) String.EmptyString.

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

(** the first [n] characters of [s], and the rest, a character at a
    time; [None] when [s] is shorter. What the proofs reason with. *)
Fixpoint split_at_walk (n : nat) (s : string) : option (string * string) :=
  match n with
  | O => Some (String.EmptyString, s)
  | S k =>
    match s with
    | String.EmptyString => None
    | String.String c rest =>
      match split_at_walk k rest with
      | Some (taken, after) => Some (String.String c taken, after)
      | None => None
      end
    end
  end.

(** the same, by offset: what runs (see [split_at_walk_eq]) *)
Definition split_at (n : nat) (s : string) : option (string * string) :=
  if Nat.leb n (String.length s)
  then Some (String.substring 0 n s, String.substring n (String.length s - n) s)
  else None.

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

(** the first frame of what was received, frames of [limit] bytes at
    most, a character at a time: what the proofs reason with *)
Definition take_frame_walk (limit : N) (buffer : string) : frame_step :=
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

(** the same, by offset: what runs (see [take_frame_eq]) *)
Definition take_frame (limit : N) (buffer : string) : frame_step :=
  match String.get 0 buffer, String.get 1 buffer, String.get 2 buffer, String.get 3 buffer with
  | Some a, Some b, Some c, Some d =>
    let n := frame_length a b c d in
    if N.ltb limit n then Oversized
    else
      let k := N.to_nat n in
      if Nat.leb (4 + k) (String.length buffer)
      then Whole (String.substring 4 k buffer) (String.substring (4 + k) (String.length buffer - (4 + k)) buffer)
      else NeedMore
  | _, _, _, _ => NeedMore
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

Lemma substring_all : forall s, String.substring 0 (String.length s) s = s.
Proof.
  induction s as [|c s IH]; [reflexivity|]. cbn [String.length String.substring]. rewrite IH. reflexivity.
Qed.

(** taking by offset is taking a character at a time *)
Theorem split_at_walk_eq : forall n s, split_at n s = split_at_walk n s.
Proof.
  unfold split_at. induction n as [|n IH]; intros s.
  - cbn [Nat.leb split_at_walk]. rewrite PeanoNat.Nat.sub_0_r, substring_all.
    destruct s; reflexivity.
  - destruct s as [|c rest]; [reflexivity|].
    cbn [String.length Nat.leb split_at_walk Nat.sub String.substring].
    rewrite <- IH. destruct (Nat.leb n (String.length rest)); reflexivity.
Qed.

Lemma split_at_shorter : forall n s taken after,
  split_at n s = Some (taken, after) -> String.length after <= String.length s.
Proof.
  intros n s. rewrite split_at_walk_eq. revert s.
  induction n as [|n IH]; intros s taken after H; cbn [split_at_walk] in H.
  - injection H as Ht Ha. subst after. lia.
  - destruct s as [|c rest].
    + discriminate H.
    + destruct (split_at_walk n rest) as [[t a]|] eqn:E.
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

(** taking a frame by offset is taking it a character at a time *)
Theorem take_frame_eq : forall limit s, take_frame limit s = take_frame_walk limit s.
Proof.
  intros limit s. unfold take_frame, take_frame_walk.
  destruct s as [|a [|b [|c [|d rest]]]]; try reflexivity.
  cbn [String.get String.length]. cbv zeta.
  destruct (N.ltb limit (frame_length a b c d)); [reflexivity|].
  unfold split_at. cbn [Nat.add Nat.leb Nat.sub String.substring].
  destruct (Nat.leb (N.to_nat (frame_length a b c d)) (String.length rest)); reflexivity.
Qed.

Lemma take_frame_shorter : forall limit s data after,
  take_frame limit s = Whole data after -> String.length after < String.length s.
Proof.
  intros limit s data after H. rewrite take_frame_eq in H. unfold take_frame_walk in H.
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
  intros n s t. rewrite !split_at_walk_eq. revert s t.
  induction n as [|n IH]; intros s t taken after H.
  - cbn [split_at_walk] in H |- *. injection H as <- <-. reflexivity.
  - destruct s as [|c rest]; cbn [String.append split_at_walk] in H |- *.
    + discriminate H.
    + destruct (split_at_walk n rest) as [[x y]|] eqn:E; [|discriminate H].
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
  intros limit s t data after H. rewrite take_frame_eq in H |- *. unfold take_frame_walk in H.
  destruct s as [|a [|b [|c [|d rest]]]]; cbv beta iota zeta in H; try discriminate H.
  cbn [String.append]. unfold take_frame_walk. cbv beta iota zeta.
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
