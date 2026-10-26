(* A small expression language and its evaluator. *)

Inductive expr :=
| Num (n : nat)
| Plus (a : expr) (b : expr)
| Times (a : expr) (b : expr)
| IfZero (c : expr) (t : expr) (e : expr).

Fixpoint eval (e : expr) : nat :=
  match e with
  | Num n => n
  | Plus a b => eval a + eval b
  | Times a b => eval a * eval b
  | IfZero c t f => match eval c with O => eval t | S _ => eval f end
  end.

Fixpoint size (e : expr) : nat :=
  match e with
  | Num _ => 1
  | Plus a b | Times a b => 1 + size a + size b
  | IfZero c t f => 1 + size c + size t + size f
  end.

Fixpoint simplify (e : expr) : expr :=
  match e with
  | Plus (Num 0) b => simplify b
  | Times (Num 1) b => simplify b
  | Plus a b => Plus (simplify a) (simplify b)
  | Times a b => Times (simplify a) (simplify b)
  | IfZero c t f => IfZero (simplify c) (simplify t) (simplify f)
  | Num n => Num n
  end.

Definition sample : expr := Plus (Num 0) (Times (Num 1) (IfZero (Num 0) (Num 7) (Num 9))).

Definition obs_eval : nat := eval sample.
Definition obs_size : nat := size (simplify sample).
Definition obs_simplify_eval : nat := eval (simplify sample).
