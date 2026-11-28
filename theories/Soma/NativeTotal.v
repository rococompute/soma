(** Universal total correctness for the actual Native small-step relation.
    Accessibility quantifies over every successor, not a selected successful
    execution. Progress is required as well: an unsupported operation is not
    certified merely because it cannot step. Ranks are proof measures, never
    runtime fuel or additional input limits. *)
From Soma Require Import Native NativeSemantics.
From Stdlib Require Import Arith.Wf_nat Arith.PeanoNat Lia.
Set Implicit Arguments.

Section TotalCorrectness.
Variable foreign : forall A : Type, (unit -> A) -> world -> result A -> world -> Prop.
Variable named : forall A B : Type, String.string -> String.string -> A -> world -> result B -> world -> Prop.
Context {A : Type}.

Definition configuration := (world * Native.program A)%type.
Definition transition (next current : configuration) :=
  step foreign named (fst current) (snd current) (fst next) (snd next).
Definition reachable (current final : configuration) :=
  steps foreign named (fst current) (snd current) (fst final) (snd final).
Definition outcome (answer : result A) : Native.program A :=
  match answer with Returned value => Native.Return value | Raised error => Native.Throw error end.
Definition satisfies (post : world -> result A -> Prop) (current : configuration) :=
  exists answer, snd current = outcome answer /\ post (fst current) answer.
Definition safe (post : world -> result A -> Prop) (current : configuration) :=
  forall final, reachable current final ->
    satisfies post final \/ exists next, transition next final.
Definition total (post : world -> result A -> Prop) (current : configuration) :=
  Acc transition current /\ safe post current.

Lemma reachable_preserves_invariant (invariant : configuration -> Prop) :
  (forall current next, invariant current -> transition next current -> invariant next) ->
  forall current final, reachable current final -> invariant current -> invariant final.
Proof.
  intros Preserve [w body] [w' body'] Run Initial.
  unfold reachable in Run; cbn in Run. induction Run.
  - exact Initial.
  - apply IHRun. eapply (Preserve (_,_) (_,_)); eassumption.
Qed.

Theorem rank_gives_accessibility (invariant : configuration -> Prop) (rank : configuration -> nat) :
  (forall current next, invariant current -> transition next current -> invariant next) ->
  (forall current next, invariant current -> transition next current -> rank next < rank current) ->
  forall current, invariant current -> Acc transition current.
Proof.
  intros Preserve Decrease.
  refine (well_founded_induction_type (well_founded_ltof _ rank)
    (fun current => invariant current -> Acc transition current) _).
  intros current IH Valid. constructor. intros next Move.
  apply IH; [eapply Decrease|eapply Preserve]; eassumption.
Qed.

Theorem ranked_total_correctness (invariant : configuration -> Prop)
    (rank : configuration -> nat) (post : world -> result A -> Prop) :
  (forall current next, invariant current -> transition next current -> invariant next) ->
  (forall current next, invariant current -> transition next current -> rank next < rank current) ->
  (forall current, invariant current ->
    satisfies post current \/ exists next, transition next current) ->
  forall current, invariant current -> total post current.
Proof.
  intros Preserve Decrease Progress current Valid. split.
  - eapply rank_gives_accessibility; eassumption.
  - intros final Run. apply Progress.
    eapply reachable_preserves_invariant; eassumption.
Qed.

Lemma safe_after_step post current next :
  safe post current -> transition next current -> safe post next.
Proof.
  intros Safe Move final Run. apply Safe.
  unfold transition in Move. unfold reachable in *. eapply Steps_cons; eassumption.
Qed.

Theorem total_preserved_by_step post current next :
  total post current -> transition next current -> total post next.
Proof.
  intros [Accessible Safe] Move. split.
  - now apply (Acc_inv Accessible).
  - eapply safe_after_step; eassumption.
Qed.

Theorem total_preserved_by_execution post w body w' body' :
  steps foreign named w body w' body' ->
  total post (w, body) -> total post (w', body').
Proof.
  intro Run. induction Run; intro Total; [exact Total|].
  apply IHRun. eapply total_preserved_by_step; eassumption.
Qed.

Theorem total_has_successful_or_exceptional_execution post current :
  total post current -> exists final,
    reachable current final /\ satisfies post final.
Proof.
  intros [Accessible Safe]. revert Safe.
  induction Accessible as [current All IH]. intro Safe.
  destruct (Safe current (Steps_refl foreign named (fst current) (snd current)))
    as [Done|[next Move]].
  - exists current. split; [apply Steps_refl|exact Done].
  - destruct (IH next Move (safe_after_step Safe Move)) as [final [Run Done]].
    exists final. split; [|exact Done].
    unfold reachable in *. unfold transition in Move. eapply Steps_cons; eassumption.
Qed.

Theorem accessible_excludes_divergence current :
  Acc transition current -> ~ diverges foreign named (fst current) (snd current).
Proof.
  intro Accessible. induction Accessible as [current All IH].
  destruct current as [w body]. cbn. intro Divergence.
  inversion Divergence; subst.
  eapply (IH (_, _)); eassumption.
Qed.

Theorem total_excludes_divergence post current :
  total post current -> ~ diverges foreign named (fst current) (snd current).
Proof. intros [Accessible _]. now apply accessible_excludes_divergence. Qed.

Theorem total_maximal_execution_satisfies post current final :
  total post current -> reachable current final ->
  (forall next, ~ transition next final) -> satisfies post final.
Proof.
  intros [_ Safe] Run Terminal. destruct (Safe final Run) as [Done|[next Move]];
    [exact Done|exfalso; exact (Terminal next Move)].
Qed.

Theorem stuck_without_postcondition_is_not_total post current :
  ~ satisfies post current -> (forall next, ~ transition next current) ->
  ~ total post current.
Proof.
  intros Wrong Stuck [_ Safe].
  destruct (Safe current (Steps_refl foreign named (fst current) (snd current)))
    as [Done|[next Move]]; [exact (Wrong Done)|exact (Stuck next Move)].
Qed.

Theorem return_is_total post w (value : A) :
  post w (Returned value) -> total post (w, Native.Return value).
Proof.
  intro Post.
  assert (forall next, ~ transition next (w, Native.Return value)) as NoStep.
  { intros [next following] Move. unfold transition in Move; cbn in Move. inversion Move. }
  split.
  - constructor. intros next Move. exfalso. exact (NoStep next Move).
  - intros [final last] Run. unfold reachable in Run; cbn in Run.
    inversion Run; subst.
    + left. exists (Returned value). auto.
    + exfalso. eapply (NoStep (_, _)); eassumption.
Qed.

Theorem throw_is_total post w error :
  post w (Raised error) -> total post (w, Native.Throw error).
Proof.
  intro Post.
  assert (forall next, ~ transition next (w, Native.Throw error)) as NoStep.
  { intros [next following] Move. unfold transition in Move; cbn in Move. inversion Move. }
  split.
  - constructor. intros next Move. exfalso. exact (NoStep next Move).
  - intros [final last] Run. unfold reachable in Run; cbn in Run.
    inversion Run; subst.
    + left. exists (Raised error). auto.
    + exfalso. eapply (NoStep (_, _)); eassumption.
Qed.

Definition returned_value {T} (body : Native.program T) : option T :=
  match body in Native.program R return option R with
  | Native.Return value => Some value
  | _ => None
  end.
Definition thrown_value {T} (body : Native.program T) : option exception_value :=
  match body with Native.Throw error => Some error | _ => None end.

Lemma outcome_injective (left right : result A) : outcome left = outcome right -> left = right.
Proof.
  destruct left, right; intro Equal; try discriminate.
  - pose proof (f_equal (@returned_value A) Equal) as Values. cbn in Values.
    injection Values as Same. now subst.
  - pose proof (f_equal (@thrown_value A) Equal) as Errors. cbn in Errors.
    injection Errors as Same. now subst.
Qed.

Theorem total_outcome_requires_postcondition post w answer :
  total post (w, outcome answer) -> post w answer.
Proof.
  intros [_ Safe].
  destruct (Safe (w, outcome answer) (Steps_refl foreign named w (outcome answer)))
    as [[observed [Equal Post]]|[[next following] Move]].
  - cbn in *. apply outcome_injective in Equal. now subst.
  - unfold transition in Move; cbn in Move. destruct answer; inversion Move.
Qed.

Theorem successors_give_total post current :
  (exists next, transition next current) ->
  (forall next, transition next current -> total post next) -> total post current.
Proof.
  intros Progress Successors. destruct current as [w body]. split.
  - constructor. intros next Move. exact (proj1 (Successors next Move)).
  - intros [final last] Run. unfold reachable in Run; cbn in Run. inversion Run; subst.
    + right. exact Progress.
    + match goal with Move : step _ _ _ _ _ _ |- _ =>
        exact (proj2 (Successors (_, _) Move) (final, last) ltac:(assumption)) end.
Qed.

Theorem spinning_loop_is_not_total S post w (initial : S) :
  ~ total post (w, Native.Loop (fun state => Native.Return (@Native.Continue S A state)) initial).
Proof.
  intro Total. apply (total_excludes_divergence Total).
  apply spinning_loop_diverges.
Qed.

Inductive counted_steps : nat -> configuration -> configuration -> Prop :=
| Counted_refl current : counted_steps 0 current current
| Counted_cons count current next final :
    transition next current -> counted_steps count next final ->
    counted_steps (S count) current final.

Theorem ranked_execution_length (invariant : configuration -> Prop) (rank : configuration -> nat) :
  (forall current next, invariant current -> transition next current -> invariant next) ->
  (forall current next, invariant current -> transition next current -> rank next < rank current) ->
  forall count current final, counted_steps count current final -> invariant current ->
    count + rank final <= rank current.
Proof.
  intros Preserve Decrease count current final Run.
  induction Run; intro Valid; [lia|].
  specialize (IHRun (Preserve _ _ Valid H)).
  pose proof (Decrease _ _ Valid H). lia.
Qed.
End TotalCorrectness.

Section InvocationRules.
Variable foreign : forall T : Type, (unit -> T) -> world -> result T -> world -> Prop.
Variable named : forall X Y : Type, String.string -> String.string -> X -> world -> result Y -> world -> Prop.

Theorem total_requires_every_foreign_return A B post w (primitive : unit -> A)
    (next : A -> Native.program B) w' value :
  total foreign named post (w, Native.Invoke primitive next) ->
  foreign primitive w (Returned value) w' -> total foreign named post (w', next value).
Proof.
  intros Total Call. eapply total_preserved_by_step; [exact Total|].
  unfold transition; cbn. now apply Step_invoke.
Qed.

Theorem total_requires_every_foreign_exception A B post w (primitive : unit -> A)
    (next : A -> Native.program B) w' error :
  total foreign named post (w, Native.Invoke primitive next) ->
  foreign primitive w (Raised error) w' -> post w' (Raised error).
Proof.
  intros Total Call. apply (@total_outcome_requires_postcondition foreign named B post w' (Raised error)).
  eapply total_preserved_by_step; [exact Total|].
  unfold transition; cbn. now apply Step_invoke_raise.
Qed.

(** A successful true-returning execution cannot excuse an allowed false
    outcome. This rejects the existential/selected-path reading of total. *)
Theorem allowed_false_return_rejects_true_only_spec w (primitive : unit -> bool) :
  foreign primitive w (Returned false) w ->
  ~ total foreign named (fun _ answer => answer = Returned true)
      (w, Native.Invoke primitive Native.Return).
Proof.
  intros Call Total.
  pose proof (total_requires_every_foreign_return Total Call) as FalseReturn.
  pose proof (@total_outcome_requires_postcondition foreign named bool _ w
    (Returned false) FalseReturn). discriminate.
Qed.
End InvocationRules.

Section EntryRules.
Variable foreign : forall T : Type, (unit -> T) -> world -> result T -> world -> Prop.
Variable named : forall X Y : Type, String.string -> String.string -> X -> world -> result Y -> world -> Prop.

Definition entry_total {A} (post : world -> result A -> Prop) (code : Native.entry A) w :=
  (match code in Native.entry T return (world -> result T -> Prop) -> Prop with
  | Native.Export body => fun condition => total foreign named condition (w, body)
  end) post.

Theorem total_entry_runs_satisfy A post (code : Native.entry A) w w' answer :
  entry_total post code w -> entry_runs foreign named w code w' answer -> post w' answer.
Proof.
  destruct code as [T body]. cbn [entry_total entry_runs]. destruct answer;
    intros Total Run;
    eapply (@total_outcome_requires_postcondition foreign named T post w');
    eapply total_preserved_by_execution; eassumption.
Qed.

Theorem total_entry_has_execution A post (code : Native.entry A) w :
  entry_total post code w -> exists w' answer,
    entry_runs foreign named w code w' answer /\ post w' answer.
Proof.
  destruct code as [T body]. cbn [entry_total]. intro Total.
  destruct (total_has_successful_or_exceptional_execution Total)
    as [[w' following] [Run [answer [Equal Post]]]].
  cbn in Equal, Post, Run. subst following. exists w', answer. split; [|exact Post].
  destruct answer; exact Run.
Qed.
End EntryRules.

(** Tables still have no rules in NativeSemantics. Accessibility alone
    would certify it vacuously; the progress half of total rejects it. *)
Theorem unsupported_table_is_not_total
    (foreign : forall T : Type, (unit -> T) -> world -> result T -> world -> Prop)
    (named : forall X Y : Type, String.string -> String.string -> X -> world -> result Y -> world -> Prop)
    post w capacity :
  ~ @total foreign named (Native.table unit unit) post (w, @Native.New_table unit unit capacity).
Proof.
  apply stuck_without_postcondition_is_not_total.
  - intros [answer [Equal _]]. destruct answer; discriminate.
  - intros [next following] Move. unfold transition in Move; cbn in Move. inversion Move.
Qed.
