(************************************************************************)
(*  Soma: cryptography in Soma itself, on Rocq's 63-bit integers         *)
(************************************************************************)

(** * Crypto: SHA-256 (FIPS 180-4) and RSA signatures (PKCS #1 v1.5)

    In Soma, so the kernel computes it (the [Example]s below are checked
    by [vm_compute]) and a program runs it with no library: a binary and a
    unikernel image both extract it to OCaml, with [Uint63] as OCaml's
    ints (the generated uint63.ml). A 32-bit word is an [int] below
    2{^32}; each operation masks its result back to 32 bits.

    A message is read as a list of bytes, through
    [String.list_ascii_of_string], which extraction makes one pass over
    the string (indexing a native string through its constructors would
    copy the rest of it at each character).

    RSA is below SHA-256: [rsa_verify] and [rsa_sign], PKCS #1 v1.5
    signatures of SHA-256 digests on big-endian bytes, as Cryptokit makes
    them, on numbers of 31-bit limbs ([Bignum]). *)

From Stdlib Require Import Strings.String Strings.Ascii Lists.List.
Import ListNotations.
(* last, so that [eqb] and [ltb] are on integers *)
From Corelib Require Import PrimInt63.
(** The internals are in [Sha256], so that [Require Import Crypto] adds
    only the functions below it. *)
Module Sha256.
Local Open Scope uint63_scope.

(** ** 32-bit words *)

Definition mask32 : int := 4294967295.
Definition add32 (a b : int) : int := land (add a b) mask32.
Definition rotr (n x : int) : int := land (lor (lsr x n) (lsl x (sub 32 n))) mask32.
Definition ch (x y z : int) : int := lxor (land x y) (land (lxor x mask32) z).
Definition maj (x y z : int) : int := lxor (lxor (land x y) (land x z)) (land y z).
Definition big_sigma0 (x : int) : int := lxor (lxor (rotr 2 x) (rotr 13 x)) (rotr 22 x).
Definition big_sigma1 (x : int) : int := lxor (lxor (rotr 6 x) (rotr 11 x)) (rotr 25 x).
Definition small_sigma0 (x : int) : int := lxor (lxor (rotr 7 x) (rotr 18 x)) (lsr x 3).
Definition small_sigma1 (x : int) : int := lxor (lxor (rotr 17 x) (rotr 19 x)) (lsr x 10).

(** ** Bytes *)

Definition bit (b : bool) (v : int) : int := if b then v else 0.

(** a character's code, 0 to 255 *)
Definition byte_of_ascii (c : ascii) : int :=
  match c with
  | Ascii a b c d e f g h =>
      lor (lor (lor (bit a 1) (bit b 2)) (lor (bit c 4) (bit d 8)))
          (lor (lor (bit e 16) (bit f 32)) (lor (bit g 64) (bit h 128)))
  end.

(** the character of a code's low 8 bits *)
Definition ascii_of_byte (v : int) : ascii :=
  let b i := eqb (land (lsr v i) 1) 1 in
  Ascii (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7).

(** [map f l], reversed, in tail calls: a long string's bytes would take a
    stack frame each through [map] *)
Fixpoint rev_map_acc {A B} (f : A -> B) (acc : list B) (l : list A) : list B :=
  match l with [] => acc | x :: l => rev_map_acc f (f x :: acc) l end.

Definition map_tail {A B} (f : A -> B) (l : list A) : list B :=
  rev_append (rev_map_acc f [] l) [].

(** a string's bytes *)
Definition bytes_of_string (s : string) : list int :=
  map_tail byte_of_ascii (list_ascii_of_string s).

Definition string_of_bytes (l : list int) : string :=
  string_of_list_ascii (map_tail ascii_of_byte l).

Definition hex_digit (d : int) : ascii :=
  ascii_of_byte (if ltb d 10 then add 48 d else add 87 d).

(** lowercase hex, two digits a byte *)
Definition hex_of_bytes (l : list int) : string :=
  string_of_list_ascii
    (flat_map (fun v => [hex_digit (land (lsr v 4) 15); hex_digit (land v 15)]) l).

(** ** The compression function *)

(** the last sixteen words of the message schedule, oldest first *)
Record schedule := Schedule {
  w0 : int; w1 : int; w2 : int; w3 : int; w4 : int; w5 : int; w6 : int; w7 : int;
  w8 : int; w9 : int; w10 : int; w11 : int; w12 : int; w13 : int; w14 : int; w15 : int }.

(** the schedule one word on: W(t+16) from W(t+14), W(t+9), W(t+1), W(t) *)
Definition next_schedule (s : schedule) : schedule :=
  let 'Schedule x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 := s in
  Schedule x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
    (add32 (add32 (small_sigma1 x14) x9) (add32 (small_sigma0 x1) x0)).

Record state := State { a : int; b : int; c : int; d : int; e : int; f : int; g : int; h : int }.

Definition round_constants : list int := [
  1116352408; 1899447441; 3049323471; 3921009573;
  961987163; 1508970993; 2453635748; 2870763221;
  3624381080; 310598401; 607225278; 1426881987;
  1925078388; 2162078206; 2614888103; 3248222580;
  3835390401; 4022224774; 264347078; 604807628;
  770255983; 1249150122; 1555081692; 1996064986;
  2554220882; 2821834349; 2952996808; 3210313671;
  3336571891; 3584528711; 113926993; 338241895;
  666307205; 773529912; 1294757372; 1396182291;
  1695183700; 1986661051; 2177026350; 2456956037;
  2730485921; 2820302411; 3259730800; 3345764771;
  3516065817; 3600352804; 4094571909; 275423344;
  430227734; 506948616; 659060556; 883997877;
  958139571; 1322822218; 1537002063; 1747873779;
  1955562222; 2024104815; 2227730452; 2361852424;
  2428436474; 2756734187; 3204031479; 3329325298].

Definition initial_state : state := State 1779033703 3144134277 1013904242 2773480762 1359893119 2600822924 528734635 1541459225.

(** one round per constant; the schedule's oldest word is this round's *)
Fixpoint rounds (ks : list int) (r : state) (s : schedule) : state :=
  match ks with
  | [] => r
  | k :: ks =>
      let 'State a b c d e f g h := r in
      let t1 := add32 (add32 (add32 h (big_sigma1 e)) (add32 (ch e f g) k)) (w0 s) in
      let t2 := add32 (big_sigma0 a) (maj a b c) in
      rounds ks (State (add32 t1 t2) a b c (add32 d t1) e f g) (next_schedule s)
  end.

Definition add_states (r s : state) : state :=
  let 'State a b c d e f g h := r in
  let 'State a' b' c' d' e' f' g' h' := s in
  State (add32 a a') (add32 b b') (add32 c c') (add32 d d')
        (add32 e e') (add32 f f') (add32 g g') (add32 h h').

(** the schedule of a block's sixteen words, given last first *)
Definition schedule_of (ws : list int) : schedule :=
  match ws with
  | [x15; x14; x13; x12; x11; x10; x9; x8; x7; x6; x5; x4; x3; x2; x1; x0] =>
      Schedule x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
  | _ => Schedule 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  end.

(** A message, read one byte at a time, so that each step is a tail call
    whatever its length: the state of the blocks so far, the word being
    read, the block's words so far (last first), how many bytes of the
    block have been read, and how many in all. *)
Record reader := Reader {
  digest : state; word : int; words : list int; at_byte : int; total : int }.

Definition start : reader := Reader initial_state 0 [] 0 0.

Definition absorb (r : reader) (v : int) : reader :=
  let 'Reader st w ws k n := r in
  let w := lor (lsl w 8) v in
  if eqb (land k 3) 3 then
    let ws := w :: ws in
    if eqb k 63 then
      Reader (add_states st (rounds round_constants st (schedule_of ws))) 0 [] 0 (add n 1)
    else Reader st 0 ws (add k 1) (add n 1)
  else Reader st w ws (add k 1) (add n 1).

Fixpoint absorb_chars (r : reader) (l : list ascii) : reader :=
  match l with [] => r | c :: l => absorb_chars (absorb r (byte_of_ascii c)) l end.

Fixpoint absorb_bytes (r : reader) (l : list int) : reader :=
  match l with [] => r | v :: l => absorb_bytes (absorb r v) l end.

(** ** Padding *)

Fixpoint zeros (n : nat) : list int := match n with O => [] | S n => 0 :: zeros n end.

(** [n] as a [nat], for [n] at most [fuel] *)
Fixpoint small_nat (fuel : nat) (n : int) : nat :=
  match fuel with
  | O => O
  | S fuel => if eqb n 0 then O else S (small_nat fuel (sub n 1))
  end.

(** 0x80, zeros to 56 bytes past a multiple of 64, and the length in bits
    as 8 big-endian bytes *)
Definition padding (len : int) : list int :=
  let bits := lsl len 3 in
  128 :: zeros (small_nat 64 (land (sub 55 len) 63))
      ++ map (fun sh => land (lsr bits sh) 255) [56; 48; 40; 32; 24; 16; 8; 0].

Definition state_bytes (r : state) : list int :=
  let 'State a b c d e f g h := r in
  flat_map (fun v => map (fun sh => land (lsr v sh) 255) [24; 16; 8; 0]) [a; b; c; d; e; f; g; h].

(** the digest of what has been read, as 32 bytes *)
Definition finish (r : reader) : list int :=
  state_bytes (digest (absorb_bytes r (padding (total r)))).

End Sha256.

(** ** SHA-256 *)

(** the digest of a list of bytes (each below 256), as 32 bytes *)
Definition sha256_of_bytes (l : list int) : list int :=
  Sha256.finish (Sha256.absorb_bytes Sha256.start l).

(** the digest of a string's bytes, as 32 bytes *)
Definition sha256_bytes (s : string) : list int :=
  Sha256.finish (Sha256.absorb_chars Sha256.start (list_ascii_of_string s)).

(** the digest of a string, as 64 lowercase hex digits *)
Definition sha256 (s : string) : string := Sha256.hex_of_bytes (sha256_bytes s).

(** the digest of the strings one after the other, without joining them *)
Definition sha256_concat (l : list string) : string :=
  Sha256.hex_of_bytes (Sha256.finish
    (fold_left (fun r s => Sha256.absorb_chars r (list_ascii_of_string s)) l Sha256.start)).

(** conversions: lowercase hex of bytes, a string's bytes, and back *)
Definition hex_of_bytes : list int -> string := Sha256.hex_of_bytes.
Definition bytes_of_string : string -> list int := Sha256.bytes_of_string.
Definition string_of_bytes : list int -> string := Sha256.string_of_bytes.

(** ** Natural numbers of 31-bit limbs

    A number is a list of limbs, least significant first, each below
    2{^31}: a limb's product with another, plus two carries, fits in 63
    bits. The lists are short (67 limbs for 2048 bits), so these recurse. *)
Module Bignum.
Local Open Scope uint63_scope.

Definition mask31 : int := 2147483647.

Fixpoint zeros (n : nat) : list int := match n with O => [] | S n => 0 :: zeros n end.

(** [l] as exactly [n] limbs: the high ones cut, or zeros added *)
Fixpoint fit (n : nat) (l : list int) : list int :=
  match n, l with
  | O, _ => []
  | S n, [] => 0 :: fit n []
  | S n, x :: l => x :: fit n l
  end.

Fixpoint drop_zeros (l : list int) : list int :=
  match l with x :: r => if eqb x 0 then drop_zeros r else l | [] => [] end.

(** without high zero limbs *)
Definition trim (l : list int) : list int := rev (drop_zeros (rev l)).

(** big-endian bytes as limbs: the bytes from the least significant, into
    an accumulator of [k] bits *)
Fixpoint limbs_acc (le : list int) (acc k : int) (out : list int) : list int :=
  match le with
  | [] => rev_append out (if eqb k 0 then [] else [acc])
  | v :: le =>
      let acc := lor acc (lsl v k) in
      let k := add k 8 in
      if leb 31 k then limbs_acc le (lsr acc 31) (sub k 31) (land acc mask31 :: out)
      else limbs_acc le acc k out
  end.

Definition of_bytes (be : list int) : list int := trim (limbs_acc (rev_append be []) 0 0 []).

(** the bytes of [acc]'s [k] bits, least significant first, onto [out]
    (most significant first) *)
Fixpoint emit (fuel : nat) (acc k : int) (out : list int) : int * int * list int :=
  match fuel with
  | O => (acc, k, out)
  | S fuel => if leb 8 k then emit fuel (lsr acc 8) (sub k 8) (land acc 255 :: out) else (acc, k, out)
  end.

Fixpoint bytes_acc (l : list int) (acc k : int) (out : list int) : list int :=
  match l with
  | [] => let '(_, _, out) := emit 8 acc (add k 7) out in out
  | x :: l =>
      let '(acc, k, out) := emit 8 (lor acc (lsl x k)) (add k 31) out in
      bytes_acc l acc k out
  end.

(** [l] as [n] big-endian bytes: high ones cut, or zeros added *)
Definition to_bytes (n : nat) (l : list int) : list int :=
  rev (fit n (rev (bytes_acc l 0 0 []))).

(** the comparison of [a] and [b], of as many limbs: the most significant
    limb that differs decides *)
Fixpoint compare_from (a b : list int) (acc : comparison) : comparison :=
  match a, b with
  | x :: a, y :: b => compare_from a b (if ltb x y then Lt else if ltb y x then Gt else acc)
  | _, _ => acc
  end.

Definition geb (a b : list int) : bool :=
  match compare_from a b Eq with Lt => false | _ => true end.

(** [a - b], for [a >= b], as many limbs as [a] *)
Fixpoint sub_borrow (a b : list int) (borrow : int) : list int :=
  match a with
  | [] => []
  | x :: a =>
      let '(y, b) := match b with [] => (0, []) | y :: b => (y, b) end in
      let d := sub (add x 2147483648) (add y borrow) in
      land d mask31 :: sub_borrow a b (sub 1 (lsr d 31))
  end.

Fixpoint add_carry1 (a : list int) (c : int) : list int :=
  match a with
  | [] => if eqb c 0 then [] else [c]
  | x :: a => let s := add x c in land s mask31 :: add_carry1 a (lsr s 31)
  end.

(** [a + b] *)
Fixpoint add_carry (a b : list int) (c : int) : list int :=
  match a, b with
  | [], _ => add_carry1 b c
  | _, [] => add_carry1 a c
  | x :: a, y :: b => let s := add (add x y) c in land s mask31 :: add_carry a b (lsr s 31)
  end.

Fixpoint mul_limb (b : list int) (x c : int) : list int :=
  match b with
  | [] => [c]
  | y :: b => let p := add (mul x y) c in land p mask31 :: mul_limb b x (lsr p 31)
  end.

(** [a * b], schoolbook *)
Fixpoint mul_big (a b : list int) : list int :=
  match a with
  | [] => []
  | x :: a => add_carry (mul_limb b x 0) (0 :: mul_big a b) 0
  end.

(** ** Montgomery multiplication modulo an odd [n] of [s] limbs, R = 2{^31s} *)

Record modulus := Modulus {
  m_n : list int;      (* s limbs *)
  m_n1 : list int;     (* s + 1 limbs, the top one 0 *)
  m_zero1 : list int;  (* s + 1 zero limbs *)
  m_inv : int;         (* -n{^-1} mod 2{^31} *)
  m_s : nat;
  m_bits : int }.      (* 31 s, R's bits *)

(** [x], the inverse of the odd [n0] modulo 2{^31}: each step doubles its
    correct low bits, from 3 *)
Definition inverse31 (n0 : int) : int :=
  let step x := mul x (sub 2 (mul n0 x)) in
  land (step (step (step (step n0)))) mask31.

Definition modulus_of (n : list int) : modulus :=
  let s := length n in
  Modulus n (n ++ [0]) (zeros (S s))
    (land (sub 0 (inverse31 (hd 1 n))) mask31) s
    (fold_left (fun k _ => add k 31) n 0).

(** one limb [ai] of [a] into [t] (s + 1 limbs): [(t + ai b + m n) / 2{^31}],
    [m] making it exact. The first limb decides [m]; its sum's low limb is 0. *)
Fixpoint pass_rest (t b n : list int) (ai m c1 c2 : int) : list int :=
  match t, b, n with
  | tj :: t, bj :: b, nj :: n =>
      let x := add (add tj (mul ai bj)) c1 in
      let y := add (add (land x mask31) (mul m nj)) c2 in
      land y mask31 :: pass_rest t b n ai m (lsr x 31) (lsr y 31)
  | [top], [], [] => let y := add (add top c1) c2 in [land y mask31; lsr y 31]
  | _, _, _ => []
  end.

Definition pass (md : modulus) (b : list int) (t : list int) (ai : int) : list int :=
  match t, b, m_n md with
  | t0 :: t, b0 :: b, n0 :: n =>
      let x := add t0 (mul ai b0) in
      let m := land (mul (land x mask31) (m_inv md)) mask31 in
      let y := add (land x mask31) (mul m n0) in
      pass_rest t b n ai m (lsr x 31) (lsr y 31)
  | _, _, _ => t
  end.

(** [t] below [n], for [t] below 2n, as s limbs *)
Definition reduce_once (md : modulus) (t : list int) : list int :=
  removelast (if geb t (m_n1 md) then sub_borrow t (m_n1 md) 0 else t).

(** [a b R{^-1} mod n], for [a] and [b] below [n], of s limbs *)
Definition montmul (md : modulus) (a b : list int) : list int :=
  reduce_once md (fold_left (pass md b) a (m_zero1 md)).

(** [t R{^-s'} ...]: one REDC step on a longer [t], its low limb made 0 and
    dropped, as many limbs (the carry last) *)
Fixpoint redc_rest (t n : list int) (m c : int) : list int :=
  match t with
  | [] => [c]
  | tj :: t =>
      match n with
      | nj :: n => let y := add (add tj (mul m nj)) c in land y mask31 :: redc_rest t n m (lsr y 31)
      | [] => let y := add tj c in land y mask31 :: redc_rest t [] m (lsr y 31)
      end
  end.

Definition redc_step (md : modulus) (t : list int) : list int :=
  match t, m_n md with
  | t0 :: t, n0 :: n =>
      let m := land (mul t0 (m_inv md)) mask31 in
      redc_rest t n m (lsr (add t0 (mul m n0)) 31)
  | _, _ => t
  end.

(** [c R{^-1} mod n], for [c] below [n R] *)
Definition redc (md : modulus) (c : list int) : list int :=
  let s := m_s md in
  let t := fold_left (fun t _ => redc_step md t) (m_n md) (fit (S (s + s)) c) in
  reduce_once md (fit (S s) t).

Fixpoint drop_false (l : list bool) : list bool :=
  match l with false :: l => drop_false l | _ => l end.

(** the bits of bytes, most significant first, from the first 1 (an
    exponent's leading 0s would each square 1) *)
Definition bits_of_bytes (be : list int) : list bool :=
  drop_false (flat_map (fun v => map (fun i => eqb (land (lsr v i) 1) 1) [7; 6; 5; 4; 3; 2; 1; 0]) be).

Fixpoint bits_of_int (fuel : nat) (k : int) (acc : list bool) : list bool :=
  match fuel with
  | O => acc
  | S fuel => if eqb k 0 then acc else bits_of_int fuel (lsr k 1) (eqb (land k 1) 1 :: acc)
  end.

(** [x{^e}] in Montgomery form, from [one], R mod n, by squaring and multiplying *)
Definition pow_bits (md : modulus) (one x : list int) (bits : list bool) : list int :=
  fold_left (fun (acc : list int) (b : bool) => let sq := montmul md acc acc in if b then montmul md sq x else sq)
    bits one.

(** [2 x mod n], for [x] below [n] *)
Definition double (md : modulus) (x : list int) : list int :=
  reduce_once md (add_carry (fit (S (m_s md)) x) (fit (S (m_s md)) x) 0).

Fixpoint double_times (md : modulus) (k : nat) (x : list int) : list int :=
  match k with O => x | S k => double_times md k (double md x) end.

(** R mod n, from 2{^b - 1} (below [n], of b bits), doubled 31s - b + 1 times *)
Definition r_mod (md : modulus) : list int :=
  let s := m_s md in
  let top := last (m_n md) 0 in
  let bits := sub 63 (head0 top) in
  let start := fit s (zeros (pred s) ++ [lsl 1 (sub bits 1)]) in
  double_times md (Sha256.small_nat 32 (sub 32 bits)) start.

(** R{^2} mod n: 2R mod n raised to 31s in Montgomery form, 2{^31s}R *)
Definition r2_mod (md : modulus) (r1 : list int) : list int :=
  pow_bits md r1 (double md r1)
    (bits_of_int 63 (m_bits md) []).

End Bignum.

(** ** RSA: PKCS #1 v1.5 signatures of SHA-256 digests *)

Section Rsa.
Local Open Scope uint63_scope.
Local Open Scope bool_scope.

(** DER's DigestInfo for SHA-256, before the digest *)
Definition digest_info : list int :=
  [48; 49; 48; 13; 6; 9; 96; 134; 72; 1; 101; 3; 4; 2; 1; 5; 0; 4; 32].

(** EMSA-PKCS1-v1_5 of [msg]'s SHA-256, [k] bytes: 0, 1, 0xff bytes, 0,
    DigestInfo and the digest *)
Definition emsa_pkcs1_sha256 (k : nat) (msg : string) : list int :=
  [0; 1] ++ repeat 255 (k - 54) ++ [0] ++ digest_info ++ sha256_bytes msg.

Fixpoint bytes_eqb (a b : list int) : bool :=
  match a, b with
  | [], [] => true
  | x :: a, y :: b => eqb x y && bytes_eqb a b
  | _, _ => false
  end.

(** Whether [sg] ([k] bytes, big-endian) is the signature of [msg] by the
    key of modulus [n] and public exponent [e] (big-endian bytes): [sg]
    below [n], and [sg{^e} mod n] [msg]'s EMSA. [n] is odd, as an RSA
    modulus is. *)
Definition rsa_verify (k : nat) (n e : list int) (msg : string) (sg : list int) : bool :=
  let nl := Bignum.of_bytes n in
  let md := Bignum.modulus_of nl in
  let s := Bignum.m_s md in
  let x := Bignum.of_bytes sg in
  Nat.eqb (length sg) k && eqb (land (hd 0 nl) 1) 1 &&
  Nat.leb (length x) s && negb (Bignum.geb (Bignum.fit s x) nl) &&
  let one := Bignum.r_mod md in
  let xm := Bignum.montmul md (Bignum.fit s x) (Bignum.r2_mod md one) in
  let ym := Bignum.pow_bits md one xm (Bignum.bits_of_bytes e) in
  bytes_eqb (Bignum.to_bytes k (Bignum.montmul md ym (Bignum.fit s [1])))
    (emsa_pkcs1_sha256 k msg).

(** [c{^d} mod pr] in Montgomery form, with [pr]'s modulus and R{^3} mod pr *)
Definition crt_half (c pr d : list int) : Bignum.modulus * list int * list int :=
  let md := Bignum.modulus_of (Bignum.of_bytes pr) in
  let one := Bignum.r_mod md in
  let r2 := Bignum.r2_mod md one in
  let r3 := Bignum.montmul md r2 r2 in
  let cm := Bignum.montmul md (Bignum.redc md c) r3 in
  (md, r3, Bignum.pow_bits md one cm (Bignum.bits_of_bytes d)).

(** The signature of [msg], [k] bytes, by the private key of primes [p]
    and [q], [dp] = d mod (p - 1), [dq] = d mod (q - 1) and [qinv] =
    q{^-1} mod p (big-endian bytes), by the Chinese remainder theorem:
    m1 = c{^dp} mod p, m2 = c{^dq} mod q, h = qinv (m1 - m2) mod p, and
    m2 + h q. *)
Definition rsa_sign (k : nat) (p q dp dq qinv : list int) (msg : string) : list int :=
  let c := Bignum.of_bytes (emsa_pkcs1_sha256 k msg) in
  let '(mp, r3p, m1m) := crt_half c p dp in
  let '(mq, _, m2m) := crt_half c q dq in
  let sp := Bignum.m_s mp in
  let m2 := Bignum.montmul mq m2m (Bignum.fit (Bignum.m_s mq) [1]) in
  let m2p := Bignum.montmul mp (Bignum.redc mp m2) r3p in
  let qinvm := Bignum.montmul mp (Bignum.redc mp (Bignum.of_bytes qinv)) r3p in
  let diff := Bignum.fit sp
    (if Bignum.geb m1m m2p then Bignum.sub_borrow m1m m2p 0
     else Bignum.sub_borrow (Bignum.add_carry m1m (Bignum.m_n mp) 0) m2p 0) in
  let h := Bignum.montmul mp (Bignum.montmul mp diff qinvm) (Bignum.fit sp [1]) in
  Bignum.to_bytes k (Bignum.add_carry (Bignum.mul_big h (Bignum.m_n mq)) m2 0).

(** ** Hex *)

Definition hex_value (c : ascii) : option int :=
  let v := Sha256.byte_of_ascii c in
  if leb 48 v && leb v 57 then Some (sub v 48)
  else if leb 97 v && leb v 102 then Some (sub v 87)
  else if leb 65 v && leb v 70 then Some (sub v 55)
  else None.

Definition is_space (c : ascii) : bool :=
  let v := Sha256.byte_of_ascii c in
  eqb v 32 || eqb v 9 || eqb v 10 || eqb v 13.

Fixpoint hex_digits (l : list ascii) (acc : list int) : option (list int) :=
  match l with
  | [] => Some (rev_append acc [])
  | c :: l =>
      if is_space c then hex_digits l acc
      else match hex_value c with Some v => hex_digits l (v :: acc) | None => None end
  end.

Fixpoint pairs (l : list int) (acc : list int) : option (list int) :=
  match l with
  | [] => Some (rev_append acc [])
  | x :: y :: l => pairs l (lor (lsl x 4) y :: acc)
  | [_] => None
  end.

(** the bytes of hex digits, either case, whitespace skipped; [None] for
    another character or an odd count of digits (Cryptokit's [Hexa]) *)
Definition bytes_of_hex (s : string) : option (list int) :=
  match hex_digits (list_ascii_of_string s) [] with
  | Some ds => pairs ds []
  | None => None
  end.

End Rsa.

(** FIPS 180-4's examples, and the empty string *)
Example sha256_abc : sha256 "abc" =
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"%string.
Proof. vm_compute. reflexivity. Qed.

Example sha256_empty : sha256 "" =
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"%string.
Proof. vm_compute. reflexivity. Qed.

Example sha256_two_blocks :
  sha256 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" =
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"%string.
Proof. vm_compute. reflexivity. Qed.

Example sha256_concat_parts :
  sha256_concat ["ab"; ""; "c"]%string = sha256 "abc".
Proof. vm_compute. reflexivity. Qed.

(** A 512-bit key of Cryptokit's ([RSA.new_key], whose public exponent is
    random) and its signature of "hello", as Cryptokit signs: verified,
    refused for another message, and made again, the same bytes. *)
Module Example512.
Definition hex (s : string) : list int := match bytes_of_hex s with Some l => l | None => [] end.
Definition n := hex
  "709dff91807c436b4270bc447d97d7889b61594afbdb73d508bc53b3b390d9c46f4340ec51d6122c8006cd65feaa020f8cc1e053c2f62e191f0fc8c25122464d".
Definition e := hex
  "a3466ee0fd3c673517e1a2c6de4eb354796f5b3a9b892c6d1b86c89af40a7d7f5c45ba2b91053d6173571b05f91741de90cab2352ef55b656769f9e1f3b015bf".
Definition p := hex
  "c3f96ef4e9232daea2d0ec11d6b65e053492580e9d9aa202906ac495c31169b7".
Definition q := hex
  "931c6fc89f2acd3107d00eea57d96cc79d74dd29ff8d85cfd070720cbc94e01b".
Definition dp := hex
  "ac9117d08671749174f232e3330417b236b2f459308698eb9735745bd2becad7".
Definition dq := hex
  "7ef65e6f72dffd36302d03fef561b836b723b9b040f0ff19548a7509c1c5818d".
Definition qinv := hex
  "789025575c7b18ff3666ae713563ffe3db7b8dd894bace1a5be77badc41b84ec".
Definition sg := hex
  "677b587720bc387298033e81ab83c92b69dab5108b59cfe58e6cb1ea6d0f36fc473ce6b22c9ead03823f8dd81d5cb9c631594b92dc80631e7dd147bbfdcfa858".
End Example512.

Example rsa_verify_512 :
  rsa_verify 64 Example512.n Example512.e "hello" Example512.sg = true.
Proof. vm_compute. reflexivity. Qed.

Example rsa_verify_512_other :
  rsa_verify 64 Example512.n Example512.e "hellp" Example512.sg = false.
Proof. vm_compute. reflexivity. Qed.

Example rsa_sign_512 :
  rsa_sign 64 Example512.p Example512.q Example512.dp Example512.dq Example512.qinv "hello"
  = Example512.sg.
Proof. vm_compute. reflexivity. Qed.
