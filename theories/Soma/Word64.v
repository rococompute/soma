(** Unsigned 64-bit machine words: registers, addresses, page-table
    entries, flags, file offsets.

    In the kernel a word is a binary natural below [2^64] (with the proof
    that it is), and every operation is defined on [N] and reduced modulo
    [2^64]: these definitions are the specification. Compiled (an image or
    an executable), a word is OCaml's [int64] and each operation the
    [Int64] function with unsigned meaning (toplevel/somaMirage.ml,
    [word64_extraction]); the definitions are what the compiled code is
    trusted to compute, as Soma's native [nat] is (NativeSpec.v).

    Conventions, those of AArch64 and of Soma's native [nat]:
    - [add], [sub], [mul] and [neg] wrap around;
    - [divu a 0] is [0] and [remu a 0] is [a];
    - a shift count is taken modulo 64 ([shl w 64] is [w]);
    - [ltb] and [leb] compare unsigned, [slt] and [sle] two's complement. *)
From Stdlib Require Import NArith Lia.
From Stdlib Require Strings.String Strings.Ascii.
Require Import Soma.Strings.
From Stdlib Require Eqdep_dec.
From Corelib Require PrimInt63.
Local Open Scope N_scope.

(** The bits of a primitive 63-bit integer as a binary natural, and back:
    here, so that PrimInt63's names ([add], [land], ...) and numerals are
    imported only for these two *)
Module Int63Bits.
Import PrimInt63.
Local Open Scope uint63_scope.

Definition to_N (x : int) : N :=
  let fix go (fuel : nat) (x : int) (place acc : N) : N :=
    match fuel with
    | O => acc
    | S fuel =>
      let bit := if eqb (land x 1) 0 then 0%N else place in
      go fuel (lsr x 1) (2 * place)%N (acc + bit)%N
    end in
  go 63%nat x 1%N 0%N.

(** the low 63 bits of [n] *)
Definition of_N (n : N) : int :=
  let fix go (fuel : nat) (n : N) (acc place : int) : int :=
    match fuel with
    | O => acc
    | S fuel =>
      let acc := if N.odd n then lor acc place else acc in
      go fuel (N.div2 n) acc (lsl place 1)
    end in
  go 63%nat n 0 1.
End Int63Bits.

(** [2^64] *)
Definition modulus : N := 18446744073709551616.

Lemma modulus_pos : 0 < modulus.
Proof. reflexivity. Qed.

Record word64 : Type := W64 {
  to_N : N;
  to_N_bound : to_N < modulus;
}.

Register word64 as soma.word64.type.

(** [n] modulo [2^64] *)
Definition of_N (n : N) : word64 :=
  {| to_N := n mod modulus; to_N_bound := N.mod_lt n modulus ltac:(discriminate) |}.

Definition zero : word64 := of_N 0.
Definition one : word64 := of_N 1.
(** [2^64 - 1]: every bit set *)
Definition ones : word64 := of_N (modulus - 1).

Definition of_nat (n : nat) : word64 := of_N (N.of_nat n).

(** a primitive 63-bit integer (OCaml's [int] in compiled code), its bits
    as they are: [0 <= x < 2^63] *)
Definition of_int63 (x : PrimInt63.int) : word64 := of_N (Int63Bits.to_N x).

(** the low 63 bits, as a primitive 63-bit integer *)
Definition to_int63 (w : word64) : PrimInt63.int := Int63Bits.of_N (to_N w).

Definition add (a b : word64) : word64 := of_N (to_N a + to_N b).
Definition sub (a b : word64) : word64 := of_N (to_N a + (modulus - to_N b)).
Definition mul (a b : word64) : word64 := of_N (to_N a * to_N b).
Definition neg (a : word64) : word64 := sub zero a.
Definition divu (a b : word64) : word64 := of_N (to_N a / to_N b).
Definition remu (a b : word64) : word64 := of_N (N.modulo (to_N a) (to_N b)).

Definition land (a b : word64) : word64 := of_N (N.land (to_N a) (to_N b)).
Definition lor (a b : word64) : word64 := of_N (N.lor (to_N a) (to_N b)).
Definition lxor (a b : word64) : word64 := of_N (N.lxor (to_N a) (to_N b)).
Definition lnot (a : word64) : word64 := lxor a ones.

(** the shift count, modulo 64 *)
Definition count (k : nat) : N := N.of_nat (Nat.modulo k 64).

Definition shl (a : word64) (k : nat) : word64 := of_N (N.shiftl (to_N a) (count k)).
(** logical: zeros come in at the top *)
Definition shr (a : word64) (k : nat) : word64 := of_N (N.shiftr (to_N a) (count k)).
(** arithmetic: the top bit comes in at the top *)
Definition sar (a : word64) (k : nat) : word64 :=
  let s := N.shiftr (to_N a) (count k) in
  if N.testbit (to_N a) 63 then of_N (N.lor s (N.lxor (modulus - 1) (N.shiftr (modulus - 1) (count k))))
  else of_N s.

Definition eqb (a b : word64) : bool := N.eqb (to_N a) (to_N b).
Definition ltb (a b : word64) : bool := N.ltb (to_N a) (to_N b).
Definition leb (a b : word64) : bool := N.leb (to_N a) (to_N b).

(** the top bit, which two's complement reads as the sign *)
Definition sign_bit : N := 9223372036854775808.
Definition slt (a b : word64) : bool := N.ltb (N.lxor (to_N a) sign_bit) (N.lxor (to_N b) sign_bit).
Definition sle (a b : word64) : bool := N.leb (N.lxor (to_N a) sign_bit) (N.lxor (to_N b) sign_bit).

(** [width] bits from bit [lo] up: [bits esr 26 6] is an exception
    syndrome's class *)
Definition bits (w : word64) (lo width : nat) : word64 :=
  of_N (N.land (N.shiftr (to_N w) (N.of_nat lo)) (N.ones (N.of_nat width))).

(** lowercase hexadecimal, without leading zeros: ["0"], ["ff"],
    ["ffffffffffffffff"] *)
Definition to_hex (w : word64) : String.string :=
  let digit (d : N) : Ascii.ascii :=
    Ascii.ascii_of_N (if N.ltb d 10 then 48 + d else 87 + d) in
  let fix go (fuel : nat) (n : N) (acc : String.string) : String.string :=
    match fuel with
    | O => acc
    | S fuel =>
      let acc := String.String (digit (N.modulo n 16)) acc in
      if N.ltb n 16 then acc else go fuel (N.div n 16) acc
    end in
  go 16%nat (to_N w) String.EmptyString.

(** * Laws *)

Lemma to_N_of_N : forall n, to_N (of_N n) = n mod modulus.
Proof. reflexivity. Qed.

Lemma of_N_small : forall n, n < modulus -> to_N (of_N n) = n.
Proof. intros n H. apply N.mod_small. exact H. Qed.

(** Words are equal exactly when their numbers are: the bound is a
    comparison, whose proofs are all equal *)
Lemma to_N_inj : forall a b, to_N a = to_N b -> a = b.
Proof.
  intros [a Ha] [b Hb]; simpl; intros E; subst b.
  assert (Ha = Hb) as ->; [|reflexivity].
  apply Eqdep_dec.UIP_dec. decide equality.
Qed.

Lemma eqb_spec : forall a b, eqb a b = true <-> a = b.
Proof.
  intros a b; unfold eqb; split.
  - intros H. apply to_N_inj. apply N.eqb_eq. exact H.
  - intros ->. apply N.eqb_refl.
Qed.

Lemma add_comm : forall a b, add a b = add b a.
Proof. intros a b. apply to_N_inj. unfold add, of_N; cbn [to_N]. now rewrite N.add_comm. Qed.

Lemma add_zero : forall a, add a zero = a.
Proof.
  intros a. apply to_N_inj. unfold add, zero, of_N; cbn [to_N].
  rewrite N.Div0.mod_0_l, N.add_0_r. apply N.mod_small. apply to_N_bound.
Qed.

Lemma sub_self : forall a, sub a a = zero.
Proof.
  intros [a Ha]. apply to_N_inj. unfold sub, zero, of_N; cbn [to_N].
  replace (a + (modulus - a)) with modulus by lia.
  rewrite N.Div0.mod_same, N.Div0.mod_0_l. reflexivity.
Qed.

Lemma ltb_spec : forall a b, ltb a b = true <-> to_N a < to_N b.
Proof. intros a b. apply N.ltb_lt. Qed.

(** small numbers are as they are *)
Example of_nat_example : to_N (of_nat 4096) = 4096.
Proof. reflexivity. Qed.

Example wraps : add ones one = zero.
Proof. apply to_N_inj. reflexivity. Qed.

Example hex_example : to_hex (of_N 3735928559) = "deadbeef".
Proof. reflexivity. Qed.

Example sar_example : to_hex (sar (shl one 63) 4) = "f800000000000000".
Proof. reflexivity. Qed.

Example slt_example : slt (neg one) zero = true /\ ltb (neg one) zero = false.
Proof. split; reflexivity. Qed.

Example bits_example : to_N (bits (of_N 0x96000045) 26 6) = 0x25.
Proof. reflexivity. Qed.
