(** Owned table operations progress from typed heap evidence, terminate in one
    step and frame unrelated cells. Foreign callback progress is not assumed.
    These are logical Native rules; bucket representation, unsafe aliases,
    allocation failure and physical compiler/runtime refinement remain open. *)
From Soma Require Import Native NativeSemantics NativeTotal NativeTable.
From Stdlib Require Import List Strings.String.
Set Implicit Arguments.

Theorem table_contents_update_exists K V id (domain : key_domain K) (before after : list (K * V)) cells :
  table_contents id domain before cells -> exists changed, table_updates id domain after cells changed.
Proof.
  intro Read. induction Read.
  - eexists. constructor.
  - destruct IHRead as [changed Update]. eexists. constructor; eassumption.
Qed.

Definition table_operation {A} (body : Native.program A) :=
  match body with
  | Native.New_table _ | Native.Table_mem _ _ | Native.Table_find _ _ |
    Native.Table_find_opt _ _ | Native.Table_replace _ _ _ | Native.Table_remove _ _ => true
  | _ => false
  end.

Section Execution.
Variable foreign : forall A : Type, (unit -> A) -> world -> NativeSemantics.result A -> world -> Prop.
Variable named : forall A B : Type, string -> string -> A -> world -> NativeSemantics.result B -> world -> Prop.

Theorem table_step_is_terminal A w (body : Native.program A) final following :
  step foreign named w body final following -> table_operation body = true ->
  exists answer, following = NativeTotal.outcome answer.
Proof.
  intro Move. destruct Move; cbn [table_operation]; intro Supported; try discriminate.
  all: try (match goal with |- exists answer, Native.Return ?value = _ =>
    exists (Returned value); reflexivity end).
  destruct (NativeTable.lookup domain key entries) as [value|];
    [exists (Returned value)|exists (Raised (ExceptionValue 0))]; reflexivity.
Qed.

Lemma table_with_step_is_total A w (body : Native.program A) :
  table_operation body = true ->
  (exists final following, step foreign named w body final following) ->
  NativeTotal.total foreign named (fun _ _ => True) (w,body).
Proof.
  intros Operation [final [following Move]]. apply successors_give_total.
  - exists (final,following). exact Move.
  - intros [last terminal] Next. unfold transition in Next; cbn in Next.
    destruct (table_step_is_terminal Next Operation) as [answer Equal]. subst terminal.
    destruct answer; [apply return_is_total|apply throw_is_total]; exact I.
Qed.

Theorem new_table_is_total K V w capacity (domain : key_domain K) :
  NativeTotal.total foreign named (fun _ _ => True) (w,@Native.New_table K V capacity).
Proof.
  apply table_with_step_is_total; [reflexivity|].
  do 2 eexists. exact (@Step_new_table foreign named K V w capacity domain).
Qed.

Theorem table_mem_is_total K V w id (domain : key_domain K) entries key :
  table_contents (V:=V) id domain entries (cells w) ->
  NativeTotal.total foreign named (fun _ _ => True) (w,Native.Table_mem (@Native.Table K V id) key).
Proof. intro Read. apply table_with_step_is_total; [reflexivity|]. do 2 eexists. exact (@Step_table_mem foreign named K V w id domain entries key Read). Qed.

Theorem table_find_is_total K V w id (domain : key_domain K) entries key :
  table_contents (V:=V) id domain entries (cells w) ->
  NativeTotal.total foreign named (fun _ _ => True) (w,Native.Table_find (@Native.Table K V id) key).
Proof. intro Read. apply table_with_step_is_total; [reflexivity|]. do 2 eexists. exact (@Step_table_find foreign named K V w id domain entries key Read). Qed.

Theorem table_find_opt_is_total K V w id (domain : key_domain K) entries key :
  table_contents (V:=V) id domain entries (cells w) ->
  NativeTotal.total foreign named (fun _ _ => True) (w,Native.Table_find_opt (@Native.Table K V id) key).
Proof. intro Read. apply table_with_step_is_total; [reflexivity|]. do 2 eexists. exact (@Step_table_find_opt foreign named K V w id domain entries key Read). Qed.

Theorem table_replace_is_total K V w id (domain : key_domain K) entries key value :
  table_contents (V:=V) id domain entries (cells w) ->
  NativeTotal.total foreign named (fun _ _ => True) (w,Native.Table_replace (@Native.Table K V id) key value).
Proof.
  intro Read. destruct (table_contents_update_exists (NativeTable.replace domain key value entries) Read) as [changed Update].
  apply table_with_step_is_total; [reflexivity|]. do 2 eexists. eapply Step_table_replace; eassumption.
Qed.

Theorem table_remove_is_total K V w id (domain : key_domain K) entries key :
  table_contents (V:=V) id domain entries (cells w) ->
  NativeTotal.total foreign named (fun _ _ => True) (w,Native.Table_remove (@Native.Table K V id) key).
Proof.
  intro Read. destruct (table_contents_update_exists (NativeTable.remove domain key entries) Read) as [changed Update].
  apply table_with_step_is_total; [reflexivity|]. do 2 eexists. eapply Step_table_remove; eassumption.
Qed.

Theorem replaced_table_reads_original_value K V w changed id (domain : key_domain K) entries key value :
  table_contents (V:=V) id domain entries (cells w) ->
  table_updates id domain (NativeTable.replace domain key value entries) (cells w) changed ->
  steps foreign named w
    (Native.Bind (Native.Table_replace (@Native.Table K V id) key value)
      (fun _ => Native.Table_find (Native.Table id) key))
    (replace_cells w changed) (Native.Return value).
Proof.
  intros Read Update.
  eapply Steps_cons; [apply Step_bind; eapply Step_table_replace; eassumption|].
  eapply Steps_cons; [apply Step_bind_return|].
  eapply Steps_cons; [eapply Step_table_find; cbn [replace_cells]; exact (table_updates_read_back Update)|].
  rewrite lookup_replaced. constructor.
Qed.

Theorem missing_table_key_raises_existing_not_found K V w id (domain : key_domain K) entries key :
  table_contents (V:=V) id domain entries (cells w) -> NativeTable.lookup domain key entries = None ->
  step foreign named w (Native.Table_find (@Native.Table K V id) key) w (Native.Throw (ExceptionValue 0)).
Proof.
  intros Read Missing.
  replace (Native.Throw (ExceptionValue 0)) with
    (match NativeTable.lookup domain key entries with Some value => Native.Return value | None => Native.Throw (ExceptionValue 0) end)
    by now rewrite Missing.
  exact (@Step_table_find foreign named K V w id domain entries key Read).
Qed.
End Execution.
