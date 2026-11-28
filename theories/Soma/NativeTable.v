(** Typed observations for Native's default word/string-key hash tables.

    The sequence represents lookup order among equal keys, not hash buckets
    or iteration order. Replacing an existing binding stores the incoming key
    and value; removing it reveals any older duplicate. Other key domains have
    no witness here, rather than an arbitrary comparison interpreter.
    Native hash/equality refinement and unsafe mutable string aliases remain
    implementation obligations. *)
From Corelib Require Import PrimInt63 Uint63Axioms.
From Stdlib Require Import List Strings.String Bool.
Import ListNotations.
Set Implicit Arguments.

Inductive key_domain : Type -> Type :=
| Word_keys : key_domain PrimInt63.int
| String_keys : key_domain string.

Theorem key_domain_nontrivial K (domain : key_domain K) : exists left right : K, left <> right.
Proof.
  destruct domain.
  - exists 0%uint63,1%uint63. intro Same.
    pose proof (f_equal (PrimInt63.eqb 0%uint63) Same) as Bits. vm_compute in Bits. discriminate.
  - exists EmptyString,(String (Ascii.ascii_of_nat 120) EmptyString). discriminate.
Qed.

Theorem unit_keys_unsupported : key_domain unit -> False.
Proof.
  intro Domain. destruct (key_domain_nontrivial Domain) as [left [right Different]].
  destruct left,right. apply Different. reflexivity.
Qed.

Definition equal {K} (domain : key_domain K) : K -> K -> bool :=
  match domain in key_domain T return T -> T -> bool with
  | Word_keys => PrimInt63.eqb
  | String_keys => String.eqb
  end.

Fixpoint lookup {K V} (domain : key_domain K) (key : K) (entries : list (K * V)) : option V :=
  match entries with
  | [] => None
  | (stored,value)::rest => if equal domain stored key then Some value else lookup domain key rest
  end.

Fixpoint replace {K V} (domain : key_domain K) (key : K) (value : V) (entries : list (K * V)) :=
  match entries with
  | [] => [(key,value)]
  | (stored,before)::rest => if equal domain stored key then (key,value)::rest
    else (stored,before)::replace domain key value rest
  end.

Fixpoint remove {K V} (domain : key_domain K) (key : K) (entries : list (K * V)) :=
  match entries with
  | [] => []
  | (stored,value)::rest => if equal domain stored key then rest
    else (stored,value)::remove domain key rest
  end.

Theorem equal_refl K (domain : key_domain K) key : equal domain key key = true.
Proof. destruct domain; cbn; [apply Uint63Axioms.eqb_refl|apply String.eqb_refl]. Qed.

Theorem equal_spec K (domain : key_domain K) left right : equal domain left right = true <-> left = right.
Proof.
  destruct domain; cbn.
  - split; [apply Uint63Axioms.eqb_correct|]. intro Same; subst. apply Uint63Axioms.eqb_refl.
  - apply String.eqb_eq.
Qed.

Theorem equal_other K (domain : key_domain K) left right : left <> right -> equal domain left right = false.
Proof. intro Different. destruct (equal domain left right) eqn:Equal; [apply equal_spec in Equal; contradiction|reflexivity]. Qed.

Theorem lookup_replaced K V (domain : key_domain K) key (value : V) entries :
  lookup domain key (replace domain key value entries) = Some value.
Proof.
  induction entries as [|[stored before] rest IH]; cbn; [now rewrite equal_refl|].
  destruct (equal domain stored key) eqn:Equal; cbn; [now rewrite equal_refl|now rewrite Equal].
Qed.

Theorem replace_incoming_key K V (domain : key_domain K) key stored (value before : V) rest :
  equal domain stored key = true -> replace domain key value ((stored,before)::rest) = (key,value)::rest.
Proof. intro Equal. cbn. now rewrite Equal. Qed.

Theorem lookup_replaced_other K V (domain : key_domain K) key other (value : V) entries :
  key <> other -> lookup domain other (replace domain key value entries) = lookup domain other entries.
Proof.
  intro Different. induction entries as [|[stored before] rest IH]; cbn.
  - now rewrite equal_other.
  - destruct (equal domain stored key) eqn:Equal; cbn.
    + apply equal_spec in Equal. subst stored. now rewrite equal_other.
    + destruct (equal domain stored other); [reflexivity|exact IH].
Qed.

Theorem lookup_removed_other K V (domain : key_domain K) key other (entries : list (K * V)) :
  key <> other -> lookup domain other (remove domain key entries) = lookup domain other entries.
Proof.
  intro Different. induction entries as [|[stored value] rest IH]; cbn; [reflexivity|].
  destruct (equal domain stored key) eqn:Equal; cbn.
  - apply equal_spec in Equal. subst stored. now rewrite equal_other.
  - destruct (equal domain stored other); [reflexivity|exact IH].
Qed.

Theorem remove_first_duplicate K V (domain : key_domain K) key (first second : V) rest :
  remove domain key ((key,first)::(key,second)::rest) = (key,second)::rest.
Proof. cbn. now rewrite equal_refl. Qed.

Theorem lookup_removed_duplicate K V (domain : key_domain K) key (first second : V) rest :
  lookup domain key (remove domain key ((key,first)::(key,second)::rest)) = Some second.
Proof. rewrite remove_first_duplicate. cbn. now rewrite equal_refl. Qed.

Theorem lookup_borrows_value K V (domain : key_domain K) key (value : V) entries :
  lookup domain key entries = Some value -> In (key,value) entries.
Proof.
  induction entries as [|[stored before] rest IH]; cbn; [discriminate|].
  destruct (equal domain stored key) eqn:Equal.
  - apply equal_spec in Equal. subst stored. intro Same. injection Same as Same. subst before. now left.
  - intro Read. right. now apply IH.
Qed.
