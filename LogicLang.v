Load Utils.

(* Main definitions *)

Inductive term : Type :=
  | term_var (var : string)
  | term_O
  | term_S (t1 : term)
  | term_plus (t1 t2 : term)
  | term_mult (t1 t2 : term).

Coercion term_var : string >-> term.
Notation "'𝖮'" := term_O.
Notation "'𝖲' t1" := (term_S t1) (at level 10).
Notation "t1 '⨣' t2" := (term_plus t1 t2) (at level 20).
Notation "t1 '⨰' t2" := (term_mult t1 t2) (at level 15).

Inductive prop : Type :=
  | prop_pred (pred : string)
  | prop_eq (t1 t2 : term)
  | prop_false
  | prop_neg (p1 : prop)
  | prop_and (p1 p2 : prop)
  | prop_or (p1 p2 : prop)
  | prop_implies (p1 p2 : prop)
  | prop_iff (p1 p2 : prop)
  | prop_forall (var : string) (p1 : prop)
  | prop_exists (var : string) (p1 : prop).

Coercion prop_pred : string >-> prop.
Notation "t1 '≡' t2" := (prop_eq t1 t2) (at level 25).
Notation "'⊥'" := prop_false.
Notation "'¬' p1" := (prop_neg p1) (at level 30).
Notation "p1 '∧' p2" := (prop_and p1 p2) (at level 35).
Notation "p1 '∨' p2" := (prop_or p1 p2) (at level 40).
Notation "p1 '⇒' p2" := (prop_implies p1 p2) (at level 45, right associativity).
Notation "p1 '⇔' p2" := (prop_iff p1 p2) (at level 45).
Notation "'∀' var , p1" := (prop_forall var p1) (at level 55, right associativity).
Notation "'∃' var , p1" := (prop_exists var p1) (at level 55, right associativity).

(* Name generation *)

Fixpoint generate_names (old_name : string) (additional_names_count : nat) : list string :=
  match additional_names_count with
  | 0 => [old_name]
  | S additional_names_count' => old_name :: generate_names (old_name ++ "'") additional_names_count'
  end.

Theorem generate_names_length : forall old_name additional_names_count,
  length (generate_names old_name additional_names_count) = S additional_names_count.
Proof.
  intros old_name additional_names_count.
  generalize dependent old_name.
  induction additional_names_count as [| additional_names_count' IH]; intros old_name; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma generate_names_NoDup_helper : forall old_name additional_names_count,
  ~ In old_name (generate_names (old_name ++ "'") additional_names_count).
Proof.
  intros old_name additional_names_count H.
  create_var suffix "".
  replace "'" with ("'" ++ suffix)%string in H by (subst suffix; reflexivity).
  clear Heqsuffix.
  generalize dependent suffix.
  induction additional_names_count as [| additional_names_count' IH];
  intros suffix H; unfold generate_names in H; fold generate_names in H.
  - inversion H.
    + clear - H0. induction old_name.
      * discriminate H0.
      * injection H0 as H0. apply IHold_name. apply H0.
    + inversion H0.
  - inversion H.
    + clear - H0. induction old_name.
      * discriminate H0.
      * injection H0 as H0. apply IHold_name. apply H0.
    + eapply IH. rewrite <- ! append_assoc in H0. apply H0.
Qed.

Theorem generate_names_NoDup : forall old_name additional_names_count,
  NoDup (generate_names old_name additional_names_count).
Proof.
  intros old_name additional_names_count.
  generalize dependent old_name.
  induction additional_names_count as [| additional_names_count' IH]; intros old_name; simpl.
  - apply NoDup_cons.
    + intros H. inversion H.
    + apply NoDup_nil.
  - apply NoDup_cons.
    + apply generate_names_NoDup_helper.
    + apply IH.
Qed.

Fixpoint rename_to_unused_inner (used_names : list string) (generated_names : list string) : option string :=
  match generated_names with
  | [] => None
  | generated_names_h :: generated_names_t =>
    if inb String.eqb generated_names_h used_names
    then rename_to_unused_inner (remove' String.eqb generated_names_h used_names) generated_names_t
    else Some generated_names_h
  end.

Lemma rename_to_unused_inner_correct_1 : forall used_names generated_names,
  length used_names < length generated_names ->
  exists new_name, rename_to_unused_inner used_names generated_names = Some new_name.
Proof.
  intros used_names generated_names H.
  generalize dependent used_names.
  induction generated_names as [| generated_names_h generated_names_t IH]; intros used_names H; simpl in *.
  - lia.
  - destruct (inb_spec String.eqb String.eqb_spec generated_names_h used_names).
    + apply IH. specialize (In_remove'_length String.eqb String.eqb_spec _ _ i). lia.
    + eexists. reflexivity.
Qed.

Lemma rename_to_unused_inner_correct_2 : forall used_names generated_names new_name,
  ~ In new_name generated_names ->
  ~ rename_to_unused_inner used_names generated_names = Some new_name.
Proof.
  intros used_names generated_names new_name H1 H2.
  generalize dependent used_names.
  induction generated_names as [| generated_names_h generated_names_t IH]; intros used_names H2; simpl in *.
  - discriminate H2.
  - destruct (inb_spec String.eqb String.eqb_spec generated_names_h used_names).
    + eapply IH.
      * intros H3. apply H1. right. apply H3.
      * apply H2.
    + injection H2 as H2. apply H1. left. apply H2.
Qed.

Lemma rename_to_unused_inner_correct_3 : forall used_names generated_names new_name,
  NoDup generated_names ->
  length used_names < length generated_names ->
  rename_to_unused_inner used_names generated_names = Some new_name ->
  ~ In new_name used_names.
Proof.
  intros used_names generated_names new_name H1 H2 H3 H4.
  generalize dependent used_names.
  induction generated_names as [| generated_names_h generated_names_t IH];
  intros used_names H2 H3 H4; simpl in *.
  - lia.
  - inversion H1. subst x l. destruct (inb_spec String.eqb String.eqb_spec generated_names_h used_names).
    + destruct (String.eqb_spec new_name generated_names_h).
      * subst generated_names_h. eapply (rename_to_unused_inner_correct_2 _ _ _ H5). apply H3.
      * apply (IH H6 (remove' String.eqb generated_names_h used_names)).
        -- specialize (In_remove'_length String.eqb String.eqb_spec _ _ i). lia.
        -- apply H3.
        -- apply (remove'_In String.eqb String.eqb_spec).
           ++ apply H4.
           ++ apply n.
    + injection H3 as H3. congruence.
Qed.

Definition rename_to_unused (used_names : list string) (old_name : string) : string :=
  match rename_to_unused_inner used_names (generate_names old_name (length used_names)) with
  | Some new_name => new_name
  | None => ""
  end.

Theorem rename_to_unused_correct : forall used_names old_name,
  ~ In (rename_to_unused used_names old_name) used_names.
Proof.
  intros used_names old_name. unfold rename_to_unused.
  remember (rename_to_unused_inner used_names (generate_names old_name (length used_names))) as inner.
  destruct inner.
  - eapply rename_to_unused_inner_correct_3.
    + apply generate_names_NoDup.
    + rewrite -> generate_names_length. unfold lt. apply le_n.
    + symmetry. apply Heqinner.
  - destruct (
      rename_to_unused_inner_correct_1
      used_names
      (generate_names old_name (length used_names))
      ltac:(rewrite -> generate_names_length; lia)
    ) as [new_name Hnew_name].
    congruence.
Qed.

(* Free *)

Inductive FreeInTerm (var : string) : term -> Prop :=
  | FreeInTerm_var :
    FreeInTerm var (term_var var)
  | FreeInTerm_S : forall t1,
    FreeInTerm var t1 ->
    FreeInTerm var (𝖲 t1)
  | FreeInTerm_plus_1 : forall t1 t2,
    FreeInTerm var t1 ->
    FreeInTerm var (t1 ⨣ t2)
  | FreeInTerm_plus_2 : forall t1 t2,
    FreeInTerm var t2 ->
    FreeInTerm var (t1 ⨣ t2)
  | FreeInTerm_mult_1 : forall t1 t2,
    FreeInTerm var t1 ->
    FreeInTerm var (t1 ⨰ t2)
  | FreeInTerm_mult_2 : forall t1 t2,
    FreeInTerm var t2 ->
    FreeInTerm var (t1 ⨰ t2).

Fixpoint free_in_termb (var : string) (t : term) : bool :=
  match t with
  | term_var var' => String.eqb var' var
  | 𝖮 => false
  | 𝖲 t1 => free_in_termb var t1
  | t1 ⨣ t2 => free_in_termb var t1 || free_in_termb var t2
  | t1 ⨰ t2 => free_in_termb var t1 || free_in_termb var t2
  end.

Theorem free_in_termb_spec : forall var t,
  reflect (FreeInTerm var t) (free_in_termb var t).
Proof.
  intros var t. induction t; simpl.
  - destruct (String.eqb_spec var0 var).
    + apply ReflectT. subst var0. apply FreeInTerm_var.
    + apply ReflectF. intros H. inversion H; congruence.
  - apply ReflectF. intros H. inversion H.
  - destruct IHt.
    + apply ReflectT. apply FreeInTerm_S; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct IHt1, IHt2.
    + apply ReflectT. apply FreeInTerm_plus_1; assumption.
    + apply ReflectT. apply FreeInTerm_plus_1; assumption.
    + apply ReflectT. apply FreeInTerm_plus_2; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct IHt1, IHt2.
    + apply ReflectT. apply FreeInTerm_mult_1; assumption.
    + apply ReflectT. apply FreeInTerm_mult_1; assumption.
    + apply ReflectT. apply FreeInTerm_mult_2; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
Qed.

Fixpoint get_free_in_term (t : term) : list string :=
  match t with
  | term_var var => [var]
  | 𝖮 => []
  | 𝖲 t1 => get_free_in_term t1
  | t1 ⨣ t2 => get_free_in_term t1 ++ get_free_in_term t2
  | t1 ⨰ t2 => get_free_in_term t1 ++ get_free_in_term t2
  end.

Theorem get_free_in_term_correct : forall var t,
  In var (get_free_in_term t) <-> FreeInTerm var t.
Proof.
  intros var t. induction t; simpl.
  - split; intros H.
    + destruct H as [H | H].
      * subst var0. apply FreeInTerm_var.
      * exfalso. apply H.
    + inversion H. left. reflexivity.
  - split; intros H.
    + exfalso. apply H.
    + inversion H.
  - split; intros H.
    + apply FreeInTerm_S. apply IHt; assumption.
    + inversion H. apply IHt; assumption.
  - rewrite -> in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply FreeInTerm_plus_1. apply IHt1. apply H.
      * apply FreeInTerm_plus_2. apply IHt2. apply H.
    + inversion H.
      * left. apply IHt1. apply H1.
      * right. apply IHt2. apply H1.
  - rewrite -> in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply FreeInTerm_mult_1. apply IHt1. apply H.
      * apply FreeInTerm_mult_2. apply IHt2. apply H.
    + inversion H.
      * left. apply IHt1. apply H1.
      * right. apply IHt2. apply H1.
Qed.

Inductive FreeInProp (var : string) : prop -> Prop :=
  | FreeInProp_eq_1 : forall t1 t2,
    FreeInTerm var t1 ->
    FreeInProp var (t1 ≡ t2)
  | FreeInProp_eq_2 : forall t1 t2,
    FreeInTerm var t2 ->
    FreeInProp var (t1 ≡ t2)
  | FreeInProp_neg : forall p1,
    FreeInProp var p1 ->
    FreeInProp var (¬ p1)
  | FreeInProp_and_1 : forall p1 p2,
    FreeInProp var p1 ->
    FreeInProp var (p1 ∧ p2)
  | FreeInProp_and_2 : forall p1 p2,
    FreeInProp var p2 ->
    FreeInProp var (p1 ∧ p2)
  | FreeInProp_or_1 : forall p1 p2,
    FreeInProp var p1 ->
    FreeInProp var (p1 ∨ p2)
  | FreeInProp_or_2 : forall p1 p2,
    FreeInProp var p2 ->
    FreeInProp var (p1 ∨ p2)
  | FreeInProp_implies_1 : forall p1 p2,
    FreeInProp var p1 ->
    FreeInProp var (p1 ⇒ p2)
  | FreeInProp_implies_2 : forall p1 p2,
    FreeInProp var p2 ->
    FreeInProp var (p1 ⇒ p2)
  | FreeInProp_iff_1 : forall p1 p2,
    FreeInProp var p1 ->
    FreeInProp var (p1 ⇔ p2)
  | FreeInProp_iff_2 : forall p1 p2,
    FreeInProp var p2 ->
    FreeInProp var (p1 ⇔ p2)
  | FreeInProp_forall : forall var' p1,
    var' <> var ->
    FreeInProp var p1 ->
    FreeInProp var (∀ var', p1)
  | FreeInProp_exists : forall var' p1,
    var' <> var ->
    FreeInProp var p1 ->
    FreeInProp var (∃ var', p1).

Fixpoint free_in_propb (var : string) (p : prop) : bool :=
  match p with
  | prop_pred _ => false
  | t1 ≡ t2 => free_in_termb var t1 || free_in_termb var t2
  | ⊥ => false
  | ¬ p1 => free_in_propb var p1
  | p1 ∧ p2 => free_in_propb var p1 || free_in_propb var p2
  | p1 ∨ p2 => free_in_propb var p1 || free_in_propb var p2
  | p1 ⇒ p2 => free_in_propb var p1 || free_in_propb var p2
  | p1 ⇔ p2 => free_in_propb var p1 || free_in_propb var p2
  | ∀ var', p1 => negb (String.eqb var' var) && free_in_propb var p1
  | ∃ var', p1 => negb (String.eqb var' var) && free_in_propb var p1
  end.

Theorem free_in_propb_spec : forall var p,
  reflect (FreeInProp var p) (free_in_propb var p).
Proof.
  intros var p. induction p; simpl.
  - apply ReflectF. intros H. inversion H; congruence.
  - destruct (free_in_termb_spec var t1), (free_in_termb_spec var t2).
    + apply ReflectT. apply FreeInProp_eq_1; assumption.
    + apply ReflectT. apply FreeInProp_eq_1; assumption.
    + apply ReflectT. apply FreeInProp_eq_2; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - apply ReflectF. intros H. inversion H; congruence.
  - destruct IHp.
    + apply ReflectT. apply FreeInProp_neg; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct IHp1, IHp2.
    + apply ReflectT. apply FreeInProp_and_1; assumption.
    + apply ReflectT. apply FreeInProp_and_1; assumption.
    + apply ReflectT. apply FreeInProp_and_2; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct IHp1, IHp2.
    + apply ReflectT. apply FreeInProp_or_1; assumption.
    + apply ReflectT. apply FreeInProp_or_1; assumption.
    + apply ReflectT. apply FreeInProp_or_2; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct IHp1, IHp2.
    + apply ReflectT. apply FreeInProp_implies_1; assumption.
    + apply ReflectT. apply FreeInProp_implies_1; assumption.
    + apply ReflectT. apply FreeInProp_implies_2; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct IHp1, IHp2.
    + apply ReflectT. apply FreeInProp_iff_1; assumption.
    + apply ReflectT. apply FreeInProp_iff_1; assumption.
    + apply ReflectT. apply FreeInProp_iff_2; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct (String.eqb_spec var0 var), IHp.
    + apply ReflectF. intros H. inversion H; congruence.
    + apply ReflectF. intros H. inversion H; congruence.
    + apply ReflectT. apply FreeInProp_forall; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct (String.eqb_spec var0 var), IHp.
    + apply ReflectF. intros H. inversion H; congruence.
    + apply ReflectF. intros H. inversion H; congruence.
    + apply ReflectT. apply FreeInProp_exists; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
Qed.

Fixpoint get_free_in_prop (p : prop) : list string :=
  match p with
  | prop_pred _ => []
  | t1 ≡ t2 => get_free_in_term t1 ++ get_free_in_term t2
  | ⊥ => []
  | ¬ p1 => get_free_in_prop p1
  | p1 ∧ p2 => get_free_in_prop p1 ++ get_free_in_prop p2
  | p1 ∨ p2 => get_free_in_prop p1 ++ get_free_in_prop p2
  | p1 ⇒ p2 => get_free_in_prop p1 ++ get_free_in_prop p2
  | p1 ⇔ p2 => get_free_in_prop p1 ++ get_free_in_prop p2
  | ∀ var, p1 => remove' String.eqb var (get_free_in_prop p1)
  | ∃ var, p1 => remove' String.eqb var (get_free_in_prop p1)
  end.

Theorem get_free_in_prop_correct : forall var p,
  In var (get_free_in_prop p) <-> FreeInProp var p.
Proof.
  intros var p. induction p; simpl.
  - split; intros H.
    + exfalso. apply H.
    + inversion H.
  - rewrite -> in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply FreeInProp_eq_1. apply get_free_in_term_correct. apply H.
      * apply FreeInProp_eq_2. apply get_free_in_term_correct. apply H.
    + inversion H.
      * left. apply get_free_in_term_correct. apply H1.
      * right. apply get_free_in_term_correct. apply H1.
  - split; intros H.
    + exfalso. apply H.
    + inversion H.
  - split; intros H.
    + apply FreeInProp_neg. apply IHp; assumption.
    + inversion H. apply IHp; assumption.
  - rewrite -> in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply FreeInProp_and_1. apply IHp1. apply H.
      * apply FreeInProp_and_2. apply IHp2. apply H.
    + inversion H.
      * left. apply IHp1. apply H1.
      * right. apply IHp2. apply H1.
  - rewrite -> in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply FreeInProp_or_1. apply IHp1. apply H.
      * apply FreeInProp_or_2. apply IHp2. apply H.
    + inversion H.
      * left. apply IHp1. apply H1.
      * right. apply IHp2. apply H1.
  - rewrite -> in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply FreeInProp_implies_1. apply IHp1. apply H.
      * apply FreeInProp_implies_2. apply IHp2. apply H.
    + inversion H.
      * left. apply IHp1. apply H1.
      * right. apply IHp2. apply H1.
  - rewrite -> in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply FreeInProp_iff_1. apply IHp1. apply H.
      * apply FreeInProp_iff_2. apply IHp2. apply H.
    + inversion H.
      * left. apply IHp1. apply H1.
      * right. apply IHp2. apply H1.
  - rewrite <- (remove'_In_iff String.eqb String.eqb_spec). split; intros H.
    + destruct H as [H1 H2]. apply FreeInProp_forall.
      * apply not_eq_sym. apply H2.
      * apply IHp. apply H1.
    + inversion H. split.
      * apply IHp; assumption.
      * apply not_eq_sym. assumption.
  - rewrite <- (remove'_In_iff String.eqb String.eqb_spec). split; intros H.
    + destruct H as [H1 H2]. apply FreeInProp_exists.
      * apply not_eq_sym. apply H2.
      * apply IHp. apply H1.
    + inversion H. split.
      * apply IHp; assumption.
      * apply not_eq_sym. assumption.
Qed.

(* Bound *)

Inductive BoundInProp (var : string) : prop -> Prop :=
  | BoundInProp_neg : forall p1,
    BoundInProp var p1 ->
    BoundInProp var (¬ p1)
  | BoundInProp_and_1 : forall p1 p2,
    BoundInProp var p1 ->
    BoundInProp var (p1 ∧ p2)
  | BoundInProp_and_2 : forall p1 p2,
    BoundInProp var p2 ->
    BoundInProp var (p1 ∧ p2)
  | BoundInProp_or_1 : forall p1 p2,
    BoundInProp var p1 ->
    BoundInProp var (p1 ∨ p2)
  | BoundInProp_or_2 : forall p1 p2,
    BoundInProp var p2 ->
    BoundInProp var (p1 ∨ p2)
  | BoundInProp_implies_1 : forall p1 p2,
    BoundInProp var p1 ->
    BoundInProp var (p1 ⇒ p2)
  | BoundInProp_implies_2 : forall p1 p2,
    BoundInProp var p2 ->
    BoundInProp var (p1 ⇒ p2)
  | BoundInProp_iff_1 : forall p1 p2,
    BoundInProp var p1 ->
    BoundInProp var (p1 ⇔ p2)
  | BoundInProp_iff_2 : forall p1 p2,
    BoundInProp var p2 ->
    BoundInProp var (p1 ⇔ p2)
  | BoundInProp_forall_self : forall p1,
    BoundInProp var (∀ var, p1)
  | BoundInProp_forall_inner : forall var' p1,
    BoundInProp var p1 ->
    BoundInProp var (∀ var', p1)
  | BoundInProp_exists_self : forall p1,
    BoundInProp var (∃ var, p1)
  | BoundInProp_exists_inner : forall var' p1,
    BoundInProp var p1 ->
    BoundInProp var (∃ var', p1).

Fixpoint bound_in_propb (var : string) (p : prop) : bool :=
  match p with
  | prop_pred _ => false
  | t1 ≡ t2 => false
  | ⊥ => false
  | ¬ p1 => bound_in_propb var p1
  | p1 ∧ p2 => bound_in_propb var p1 || bound_in_propb var p2
  | p1 ∨ p2 => bound_in_propb var p1 || bound_in_propb var p2
  | p1 ⇒ p2 => bound_in_propb var p1 || bound_in_propb var p2
  | p1 ⇔ p2 => bound_in_propb var p1 || bound_in_propb var p2
  | ∀ var', p1 => String.eqb var' var || bound_in_propb var p1
  | ∃ var', p1 => String.eqb var' var || bound_in_propb var p1
  end.

Theorem bound_in_propb_spec : forall var p,
  reflect (BoundInProp var p) (bound_in_propb var p).
Proof.
  intros var p. induction p; simpl.
  - apply ReflectF. intros H. inversion H; congruence.
  - apply ReflectF. intros H. inversion H; congruence.
  - apply ReflectF. intros H. inversion H; congruence.
  - destruct IHp.
    + apply ReflectT. apply BoundInProp_neg; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct IHp1, IHp2.
    + apply ReflectT. apply BoundInProp_and_1; assumption.
    + apply ReflectT. apply BoundInProp_and_1; assumption.
    + apply ReflectT. apply BoundInProp_and_2; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct IHp1, IHp2.
    + apply ReflectT. apply BoundInProp_or_1; assumption.
    + apply ReflectT. apply BoundInProp_or_1; assumption.
    + apply ReflectT. apply BoundInProp_or_2; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct IHp1, IHp2.
    + apply ReflectT. apply BoundInProp_implies_1; assumption.
    + apply ReflectT. apply BoundInProp_implies_1; assumption.
    + apply ReflectT. apply BoundInProp_implies_2; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct IHp1, IHp2.
    + apply ReflectT. apply BoundInProp_iff_1; assumption.
    + apply ReflectT. apply BoundInProp_iff_1; assumption.
    + apply ReflectT. apply BoundInProp_iff_2; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct (String.eqb_spec var0 var), IHp.
    + apply ReflectT. subst var0. apply BoundInProp_forall_self; assumption.
    + apply ReflectT. subst var0. apply BoundInProp_forall_self; assumption.
    + apply ReflectT. apply BoundInProp_forall_inner; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
  - destruct (String.eqb_spec var0 var), IHp.
    + apply ReflectT. subst var0. apply BoundInProp_exists_self; assumption.
    + apply ReflectT. subst var0. apply BoundInProp_exists_self; assumption.
    + apply ReflectT. apply BoundInProp_exists_inner; assumption.
    + apply ReflectF. intros H. inversion H; congruence.
Qed.

Fixpoint get_bound_in_prop (p : prop) : list string :=
  match p with
  | prop_pred _ => []
  | t1 ≡ t2 => []
  | ⊥ => []
  | ¬ p1 => get_bound_in_prop p1
  | p1 ∧ p2 => get_bound_in_prop p1 ++ get_bound_in_prop p2
  | p1 ∨ p2 => get_bound_in_prop p1 ++ get_bound_in_prop p2
  | p1 ⇒ p2 => get_bound_in_prop p1 ++ get_bound_in_prop p2
  | p1 ⇔ p2 => get_bound_in_prop p1 ++ get_bound_in_prop p2
  | ∀ var, p1 => var :: get_bound_in_prop p1
  | ∃ var, p1 => var :: get_bound_in_prop p1
  end.

Theorem get_bound_in_prop_correct : forall var p,
  In var (get_bound_in_prop p) <-> BoundInProp var p.
Proof.
  intros var p. induction p; simpl.
  - split; intros H.
    + exfalso. apply H.
    + inversion H.
  - split; intros H.
    + exfalso. apply H.
    + inversion H.
  - split; intros H.
    + exfalso. apply H.
    + inversion H.
  - split; intros H.
    + apply BoundInProp_neg. apply IHp; assumption.
    + inversion H. apply IHp; assumption.
  - rewrite -> in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply BoundInProp_and_1. apply IHp1. apply H.
      * apply BoundInProp_and_2. apply IHp2. apply H.
    + inversion H.
      * left. apply IHp1. apply H1.
      * right. apply IHp2. apply H1.
  - rewrite -> in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply BoundInProp_or_1. apply IHp1. apply H.
      * apply BoundInProp_or_2. apply IHp2. apply H.
    + inversion H.
      * left. apply IHp1. apply H1.
      * right. apply IHp2. apply H1.
  - rewrite -> in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply BoundInProp_implies_1. apply IHp1. apply H.
      * apply BoundInProp_implies_2. apply IHp2. apply H.
    + inversion H.
      * left. apply IHp1. apply H1.
      * right. apply IHp2. apply H1.
  - rewrite -> in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply BoundInProp_iff_1. apply IHp1. apply H.
      * apply BoundInProp_iff_2. apply IHp2. apply H.
    + inversion H.
      * left. apply IHp1. apply H1.
      * right. apply IHp2. apply H1.
  - split; intros H.
    + destruct H as [H | H].
      * subst var0. apply BoundInProp_forall_self.
      * apply BoundInProp_forall_inner. apply IHp. apply H.
    + inversion H.
      * left. reflexivity.
      * right. apply IHp; assumption.
  - split; intros H.
    + destruct H as [H | H].
      * subst var0. apply BoundInProp_exists_self.
      * apply BoundInProp_exists_inner. apply IHp. apply H.
    + inversion H.
      * left. reflexivity.
      * right. apply IHp; assumption.
Qed.

(* renamings *)

Definition RenamingsEquiv (renamings_x renamings_y : list (string * string)) : Prop :=
  forall var_a var_b, In (var_a, var_b) renamings_x <-> In (var_a, var_b) renamings_y.

Fixpoint renamings_equivb_one (renamings_x renamings_y : list (string * string)) : bool :=
  match renamings_x with
  | [] => true
  | (var_a, var_b) :: renamings_x_t =>
    inb (prod_eqb String.eqb String.eqb) (var_a, var_b) renamings_y &&
    renamings_equivb_one renamings_x_t renamings_y
  end.

Theorem renamings_equivb_one_spec : forall renamings_x renamings_y,
  reflect
  (forall var_a var_b, In (var_a, var_b) renamings_x -> In (var_a, var_b) renamings_y)
  (renamings_equivb_one renamings_x renamings_y).
Proof.
  intros renamings_x renamings_y. induction renamings_x as [| [var_a var_b] renamings_x_t IH]; simpl.
  - apply ReflectT. intros var_a var_b H. exfalso. apply H.
  - destruct (
      inb_spec
      (prod_eqb String.eqb String.eqb)
      (prod_eqb_spec String.eqb String.eqb String.eqb_spec String.eqb_spec)
      (var_a, var_b)
      renamings_y
    ).
    + destruct IH.
      * apply ReflectT. intros var_a' var_b' [H | H].
        -- injection H as H_a H_b. subst var_a' var_b'. apply i.
        -- apply i0. apply H.
      * apply ReflectF. intros H. apply n. intros var_a' var_b' H'. apply H. right. apply H'.
    + apply ReflectF. intros H. apply n. apply H. left. reflexivity.
Qed.

Definition renamings_equivb (renamings_x renamings_y : list (string * string)) : bool :=
  renamings_equivb_one renamings_x renamings_y && renamings_equivb_one renamings_y renamings_x.

Theorem renamings_equivb_spec : forall renamings_x renamings_y,
  reflect (RenamingsEquiv renamings_x renamings_y) (renamings_equivb renamings_x renamings_y).
Proof.
  intros renamings_x renamings_y. unfold RenamingsEquiv, renamings_equivb.
  destruct
    (renamings_equivb_one_spec renamings_x renamings_y),
    (renamings_equivb_one_spec renamings_y renamings_x).
  - apply ReflectT. intros var_a var_b. split.
    + apply i.
    + apply i0.
  - apply ReflectF. intros H. apply n. intros var_a var_b H'. apply H. apply H'.
  - apply ReflectF. intros H. apply n. intros var_a var_b H'. apply H. apply H'.
  - apply ReflectF. intros H. apply n. intros var_a var_b H'. apply H. apply H'.
Qed.

(* NameEquiv *)

Ltac NameEquiv_refl_helper renamings Hall_eq n :=
  induction renamings as [| renamings_h renamings_t IH]; [
    intros H; apply H |
    simpl in Hall_eq; destruct renamings_h as [renamings_h_a renamings_h_b]; simpl; intros [H | H]; [
      specialize (Hall_eq renamings_h_a renamings_h_b (or_introl eq_refl));
      subst renamings_h_a renamings_h_b; apply n; simpl; left; reflexivity |
      apply IH; [
        intros var_a var_b HIn; apply Hall_eq; simpl; right; apply HIn |
        intros HIn; apply n; simpl; right; apply HIn |
        apply H
      ]
    ]
  ].

Inductive TermNameEquiv : list (string * string) -> term -> term -> Prop :=
  | TermNameEquiv_var_external : forall renamings var,
    ~ In var (map fst renamings) ->
    ~ In var (map snd renamings) ->
    TermNameEquiv renamings (term_var var) (term_var var)
  | TermNameEquiv_var_internal : forall renamings var_a var_b,
    In (var_a, var_b) renamings ->
    TermNameEquiv renamings var_a var_b
  | TermNameEquiv_O : forall renamings,
    TermNameEquiv renamings 𝖮 𝖮
  | TermNameEquiv_S : forall renamings t1_a t1_b,
    TermNameEquiv renamings t1_a t1_b ->
    TermNameEquiv renamings (𝖲 t1_a) (𝖲 t1_b)
  | TermNameEquiv_plus : forall renamings t1_a t2_a t1_b t2_b,
    TermNameEquiv renamings t1_a t1_b ->
    TermNameEquiv renamings t2_a t2_b ->
    TermNameEquiv renamings (t1_a ⨣ t2_a) (t1_b ⨣ t2_b)
  | TermNameEquiv_mult : forall renamings t1_a t2_a t1_b t2_b,
    TermNameEquiv renamings t1_a t1_b ->
    TermNameEquiv renamings t2_a t2_b ->
    TermNameEquiv renamings (t1_a ⨰ t2_a) (t1_b ⨰ t2_b).

Theorem TermNameEquiv_refl : forall renamings t,
  (forall var_a var_b, In (var_a, var_b) renamings -> var_a = var_b) ->
  TermNameEquiv renamings t t.
Proof.
  intros renamings t Hall_eq. generalize dependent renamings. induction t; intros renamings Hall_eq.
  - destruct (
      inb_spec
      (prod_eqb String.eqb String.eqb)
      (prod_eqb_spec String.eqb String.eqb String.eqb_spec String.eqb_spec)
      (var, var)
      renamings
    ).
    + apply TermNameEquiv_var_internal. apply i.
    + apply TermNameEquiv_var_external.
      * NameEquiv_refl_helper renamings Hall_eq n.
      * NameEquiv_refl_helper renamings Hall_eq n.
  - apply TermNameEquiv_O.
  - apply TermNameEquiv_S. apply (IHt _ Hall_eq).
  - apply TermNameEquiv_plus.
    + apply (IHt1 _ Hall_eq).
    + apply (IHt2 _ Hall_eq).
  - apply TermNameEquiv_mult.
    + apply (IHt1 _ Hall_eq).
    + apply (IHt2 _ Hall_eq).
Qed.

Fixpoint term_name_equivb (renamings : list (string * string)) (t_a : term) (t_b : term) : bool :=
  match t_a, t_b with
  | term_var var_a, term_var var_b =>
    (
      String.eqb var_a var_b &&
      negb (inb String.eqb var_a (map fst renamings)) &&
      negb (inb String.eqb var_b (map snd renamings))
    ) ||
    inb (prod_eqb String.eqb String.eqb) (var_a, var_b) renamings
  | 𝖮, 𝖮 => true
  | 𝖲 t1_a, 𝖲 t1_b => term_name_equivb renamings t1_a t1_b
  | t1_a ⨣ t2_a, t1_b ⨣ t2_b => term_name_equivb renamings t1_a t1_b && term_name_equivb renamings t2_a t2_b
  | t1_a ⨰ t2_a, t1_b ⨰ t2_b => term_name_equivb renamings t1_a t1_b && term_name_equivb renamings t2_a t2_b
  | _, _ => false
  end.

Theorem term_name_equivb_spec : forall renamings t_a t_b,
  reflect (TermNameEquiv renamings t_a t_b) (term_name_equivb renamings t_a t_b).
Proof.
  intros renamings t_a. generalize dependent renamings.
  induction t_a; intros renamings t_b; destruct t_b; simpl; try (apply ReflectF; intros H; inversion H).
  - destruct (
      inb_spec
      (prod_eqb String.eqb String.eqb)
      (prod_eqb_spec String.eqb String.eqb String.eqb_spec String.eqb_spec)
      (var, var0)
      renamings
    ).
    + rewrite -> orb_true_r. apply ReflectT. apply TermNameEquiv_var_internal; assumption.
    + rewrite -> orb_false_r.
      destruct
        (String.eqb_spec var var0),
        (inb_spec String.eqb String.eqb_spec var (map fst renamings)),
        (inb_spec String.eqb String.eqb_spec var0 (map snd renamings));
      simpl;
      try (apply ReflectF; intros H; inversion H; congruence).
      * apply ReflectT. subst var0. apply TermNameEquiv_var_external; assumption.
  - apply ReflectT. apply TermNameEquiv_O.
  - destruct (IHt_a renamings t_b).
    + apply ReflectT. apply TermNameEquiv_S; assumption.
    + apply ReflectF. intros H. inversion H. congruence.
  - destruct (IHt_a1 renamings t_b1), (IHt_a2 renamings t_b2).
    + apply ReflectT. apply TermNameEquiv_plus; assumption.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
  - destruct (IHt_a1 renamings t_b1), (IHt_a2 renamings t_b2).
    + apply ReflectT. apply TermNameEquiv_mult; assumption.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
Qed.

Inductive PropNameEquiv : list (string * string) -> prop -> prop -> Prop :=
  | PropNameEquiv_pred : forall renamings pred,
    PropNameEquiv renamings (prop_pred pred) (prop_pred pred)
  | PropNameEquiv_eq : forall renamings t1_a t2_a t1_b t2_b,
    TermNameEquiv renamings t1_a t1_b ->
    TermNameEquiv renamings t2_a t2_b ->
    PropNameEquiv renamings (t1_a ≡ t2_a) (t1_b ≡ t2_b)
  | PropNameEquiv_false : forall renamings,
    PropNameEquiv renamings ⊥ ⊥
  | PropNameEquiv_neg : forall renamings t1_a t1_b,
    PropNameEquiv renamings t1_a t1_b ->
    PropNameEquiv renamings (¬ t1_a) (¬ t1_b)
  | PropNameEquiv_and : forall renamings t1_a t2_a t1_b t2_b,
    PropNameEquiv renamings t1_a t1_b ->
    PropNameEquiv renamings t2_a t2_b ->
    PropNameEquiv renamings (t1_a ∧ t2_a) (t1_b ∧ t2_b)
  | PropNameEquiv_or : forall renamings t1_a t2_a t1_b t2_b,
    PropNameEquiv renamings t1_a t1_b ->
    PropNameEquiv renamings t2_a t2_b ->
    PropNameEquiv renamings (t1_a ∨ t2_a) (t1_b ∨ t2_b)
  | PropNameEquiv_implies : forall renamings t1_a t2_a t1_b t2_b,
    PropNameEquiv renamings t1_a t1_b ->
    PropNameEquiv renamings t2_a t2_b ->
    PropNameEquiv renamings (t1_a ⇒ t2_a) (t1_b ⇒ t2_b)
  | PropNameEquiv_iff : forall renamings t1_a t2_a t1_b t2_b,
    PropNameEquiv renamings t1_a t1_b ->
    PropNameEquiv renamings t2_a t2_b ->
    PropNameEquiv renamings (t1_a ⇔ t2_a) (t1_b ⇔ t2_b)
  | PropNameEquiv_forall_external : forall renamings var t1_a t1_b,
    ~ In var (map fst renamings) ->
    ~ In var (map snd renamings) ->
    PropNameEquiv renamings t1_a t1_b ->
    PropNameEquiv renamings (∀ var, t1_a) (∀ var, t1_b)
  | PropNameEquiv_forall_new : forall renamings var_a t1_a var_b t1_b,
    ~ In var_a (map fst renamings) ->
    ~ In var_b (map snd renamings) ->
    PropNameEquiv ((var_a, var_b) :: renamings) t1_a t1_b ->
    PropNameEquiv renamings (∀ var_a, t1_a) (∀ var_b, t1_b)
  | PropNameEquiv_forall_internal : forall renamings var_a t1_a var_b t1_b,
    In (var_a, var_b) renamings ->
    PropNameEquiv renamings t1_a t1_b ->
    PropNameEquiv renamings (∀ var_a, t1_a) (∀ var_b, t1_b)
  | PropNameEquiv_exists_external : forall renamings var t1_a t1_b,
    ~ In var (map fst renamings) ->
    ~ In var (map snd renamings) ->
    PropNameEquiv renamings t1_a t1_b ->
    PropNameEquiv renamings (∃ var, t1_a) (∃ var, t1_b)
  | PropNameEquiv_exists_new : forall renamings var_a t1_a var_b t1_b,
    ~ In var_a (map fst renamings) ->
    ~ In var_b (map snd renamings) ->
    PropNameEquiv ((var_a, var_b) :: renamings) t1_a t1_b ->
    PropNameEquiv renamings (∃ var_a, t1_a) (∃ var_b, t1_b)
  | PropNameEquiv_exists_internal : forall renamings var_a t1_a var_b t1_b,
    In (var_a, var_b) renamings ->
    PropNameEquiv renamings t1_a t1_b ->
    PropNameEquiv renamings (∃ var_a, t1_a) (∃ var_b, t1_b).

Theorem PropNameEquiv_refl : forall renamings p,
  (forall var_a var_b, In (var_a, var_b) renamings -> var_a = var_b) ->
  PropNameEquiv renamings p p.
Proof.
  intros renamings p Hall_eq. generalize dependent renamings. induction p; intros renamings Hall_eq.
  - apply PropNameEquiv_pred.
  - apply PropNameEquiv_eq.
    * apply (TermNameEquiv_refl _ _ Hall_eq).
    * apply (TermNameEquiv_refl _ _ Hall_eq).
  - apply PropNameEquiv_false.
  - apply PropNameEquiv_neg. apply (IHp _ Hall_eq).
  - apply PropNameEquiv_and.
    + apply (IHp1 _ Hall_eq).
    + apply (IHp2 _ Hall_eq).
  - apply PropNameEquiv_or.
    + apply (IHp1 _ Hall_eq).
    + apply (IHp2 _ Hall_eq).
  - apply PropNameEquiv_implies.
    + apply (IHp1 _ Hall_eq).
    + apply (IHp2 _ Hall_eq).
  - apply PropNameEquiv_iff.
    + apply (IHp1 _ Hall_eq).
    + apply (IHp2 _ Hall_eq).
  - destruct (
      inb_spec
      (prod_eqb String.eqb String.eqb)
      (prod_eqb_spec String.eqb String.eqb String.eqb_spec String.eqb_spec)
      (var, var)
      renamings
    ).
    + apply PropNameEquiv_forall_internal. apply i. apply (IHp _ Hall_eq).
    + apply PropNameEquiv_forall_external.
      * NameEquiv_refl_helper renamings Hall_eq n.
      * NameEquiv_refl_helper renamings Hall_eq n.
      * apply (IHp _ Hall_eq).
  - destruct (
      inb_spec
      (prod_eqb String.eqb String.eqb)
      (prod_eqb_spec String.eqb String.eqb String.eqb_spec String.eqb_spec)
      (var, var)
      renamings
    ).
    + apply PropNameEquiv_exists_internal. apply i. apply (IHp _ Hall_eq).
    + apply PropNameEquiv_exists_external.
      * NameEquiv_refl_helper renamings Hall_eq n.
      * NameEquiv_refl_helper renamings Hall_eq n.
      * apply (IHp _ Hall_eq).
Qed.

Fixpoint prop_name_equivb (renamings : list (string * string)) (p_a : prop) (p_b : prop) : bool :=
  match p_a, p_b with
  | prop_pred pred_a, prop_pred pred_b => String.eqb pred_a pred_b
  | t1_a ≡ t2_a, t1_b ≡ t2_b => term_name_equivb renamings t1_a t1_b && term_name_equivb renamings t2_a t2_b
  | ⊥, ⊥ => true
  | ¬ t1_a, ¬ t1_b => prop_name_equivb renamings t1_a t1_b
  | t1_a ∧ t2_a, t1_b ∧ t2_b => prop_name_equivb renamings t1_a t1_b && prop_name_equivb renamings t2_a t2_b
  | t1_a ∨ t2_a, t1_b ∨ t2_b => prop_name_equivb renamings t1_a t1_b && prop_name_equivb renamings t2_a t2_b
  | t1_a ⇒ t2_a, t1_b ⇒ t2_b => prop_name_equivb renamings t1_a t1_b && prop_name_equivb renamings t2_a t2_b
  | t1_a ⇔ t2_a, t1_b ⇔ t2_b => prop_name_equivb renamings t1_a t1_b && prop_name_equivb renamings t2_a t2_b
  | (∀ var_a, t1_a), (∀ var_b, t1_b) =>
    (
      String.eqb var_a var_b &&
      negb (inb String.eqb var_a (map fst renamings)) &&
      negb (inb String.eqb var_b (map snd renamings)) &&
      prop_name_equivb renamings t1_a t1_b
    ) ||
    (
      negb (inb String.eqb var_a (map fst renamings)) &&
      negb (inb String.eqb var_b (map snd renamings)) &&
      prop_name_equivb ((var_a, var_b) :: renamings) t1_a t1_b
    ) ||
    (
      inb (prod_eqb String.eqb String.eqb) (var_a, var_b) renamings &&
      prop_name_equivb renamings t1_a t1_b
    )
  | (∃ var_a, t1_a), (∃ var_b, t1_b) =>
    (
      String.eqb var_a var_b &&
      negb (inb String.eqb var_a (map fst renamings)) &&
      negb (inb String.eqb var_b (map snd renamings)) &&
      prop_name_equivb renamings t1_a t1_b
    ) ||
    (
      negb (inb String.eqb var_a (map fst renamings)) &&
      negb (inb String.eqb var_b (map snd renamings)) &&
      prop_name_equivb ((var_a, var_b) :: renamings) t1_a t1_b
    ) ||
    (
      inb (prod_eqb String.eqb String.eqb) (var_a, var_b) renamings &&
      prop_name_equivb renamings t1_a t1_b
    )
  | _, _ => false
  end.

Theorem prop_name_equivb_spec : forall renamings p_a p_b,
  reflect (PropNameEquiv renamings p_a p_b) (prop_name_equivb renamings p_a p_b).
Proof.
  intros renamings p_a. generalize dependent renamings.
  induction p_a; intros renamings p_b; destruct p_b; simpl; try (apply ReflectF; intros H; inversion H).
  - destruct (String.eqb_spec pred pred0).
    + apply ReflectT. subst pred0. apply PropNameEquiv_pred.
    + apply ReflectF. intros H. inversion H. congruence.
  - destruct
      (term_name_equivb_spec renamings t1 t0),
      (term_name_equivb_spec renamings t2 t3).
    + apply ReflectT. apply PropNameEquiv_eq; assumption.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
  - apply ReflectT. apply PropNameEquiv_false.
  - destruct (IHp_a renamings p_b).
    + apply ReflectT. apply PropNameEquiv_neg; assumption.
    + apply ReflectF. intros H. inversion H. congruence.
  - destruct (IHp_a1 renamings p_b1), (IHp_a2 renamings p_b2).
    + apply ReflectT. apply PropNameEquiv_and; assumption.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
  - destruct (IHp_a1 renamings p_b1), (IHp_a2 renamings p_b2).
    + apply ReflectT. apply PropNameEquiv_or; assumption.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
  - destruct (IHp_a1 renamings p_b1), (IHp_a2 renamings p_b2).
    + apply ReflectT. apply PropNameEquiv_implies; assumption.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
  - destruct (IHp_a1 renamings p_b1), (IHp_a2 renamings p_b2).
    + apply ReflectT. apply PropNameEquiv_iff; assumption.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
    + apply ReflectF. intros H. inversion H. congruence.
  - destruct
      (String.eqb_spec var var0),
      (inb_spec String.eqb String.eqb_spec var (map fst renamings)),
      (inb_spec String.eqb String.eqb_spec var0 (map snd renamings)),
      (IHp_a renamings p_b),
      (IHp_a ((var, var0) :: renamings) p_b),
      (
        inb_spec
        (prod_eqb String.eqb String.eqb)
        (prod_eqb_spec String.eqb String.eqb String.eqb_spec String.eqb_spec)
        (var, var0)
        renamings
      ),
      (IHp_a renamings p_b);
    simpl;
    try subst var0;
    try (apply ReflectF; intros H; inversion H; congruence);
    try (apply ReflectT; apply PropNameEquiv_forall_external; assumption);
    try (apply ReflectT; apply PropNameEquiv_forall_new; assumption);
    try (apply ReflectT; apply PropNameEquiv_forall_internal; assumption).
  - destruct
      (String.eqb_spec var var0),
      (inb_spec String.eqb String.eqb_spec var (map fst renamings)),
      (inb_spec String.eqb String.eqb_spec var0 (map snd renamings)),
      (IHp_a renamings p_b),
      (IHp_a ((var, var0) :: renamings) p_b),
      (
        inb_spec
        (prod_eqb String.eqb String.eqb)
        (prod_eqb_spec String.eqb String.eqb String.eqb_spec String.eqb_spec)
        (var, var0)
        renamings
      ),
      (IHp_a renamings p_b);
    simpl;
    try subst var0;
    try (apply ReflectF; intros H; inversion H; congruence);
    try (apply ReflectT; apply PropNameEquiv_exists_external; assumption);
    try (apply ReflectT; apply PropNameEquiv_exists_new; assumption);
    try (apply ReflectT; apply PropNameEquiv_exists_internal; assumption).
Qed.

(* Rename *)

Fixpoint rename_var_in_term (old_var new_var : string) (t : term) : term :=
  match t with
  | term_var var => if String.eqb var old_var then term_var new_var else term_var var
  | 𝖮 => 𝖮
  | 𝖲 t1 => 𝖲 (rename_var_in_term old_var new_var t1)
  | t1 ⨣ t2 => (rename_var_in_term old_var new_var t1) ⨣ (rename_var_in_term old_var new_var t2)
  | t1 ⨰ t2 => (rename_var_in_term old_var new_var t1) ⨰ (rename_var_in_term old_var new_var t2)
  end.

Theorem rename_var_in_term_correct_same : forall var t,
  rename_var_in_term var var t = t.
Proof.
  intros var t. induction t; simpl.
  - destruct (String.eqb_spec var0 var).
    + subst var0. reflexivity.
    + reflexivity.
  - reflexivity.
  - rewrite -> IHt. reflexivity.
  - rewrite -> IHt1. rewrite -> IHt2. reflexivity.
  - rewrite -> IHt1. rewrite -> IHt2. reflexivity.
Qed.

Theorem rename_var_in_term_correct : forall old_var new_var t,
  ~ FreeInTerm new_var t ->
  TermNameEquiv [(old_var, new_var)] t (rename_var_in_term old_var new_var t).
Proof.
  intros old_var new_var t HNotFreeInTerm. induction t; simpl.
  - destruct (String.eqb_spec var old_var).
    * apply TermNameEquiv_var_internal. simpl. left. f_equal. symmetry. assumption.
    * apply TermNameEquiv_var_external; simpl; intros [H | H]; try congruence. apply HNotFreeInTerm.
      subst new_var. apply FreeInTerm_var.
  - apply TermNameEquiv_O.
  - apply TermNameEquiv_S. apply IHt. intros HFreeInTerm. apply HNotFreeInTerm.
    apply FreeInTerm_S. apply HFreeInTerm.
  - apply TermNameEquiv_plus.
    + apply IHt1. intros HFreeInTerm. apply HNotFreeInTerm. apply FreeInTerm_plus_1. apply HFreeInTerm.
    + apply IHt2. intros HFreeInTerm. apply HNotFreeInTerm. apply FreeInTerm_plus_2. apply HFreeInTerm.
  - apply TermNameEquiv_mult.
    + apply IHt1. intros HFreeInTerm. apply HNotFreeInTerm. apply FreeInTerm_mult_1. apply HFreeInTerm.
    + apply IHt2. intros HFreeInTerm. apply HNotFreeInTerm. apply FreeInTerm_mult_2. apply HFreeInTerm.
Qed.

Fixpoint rename_var_in_prop (old_var new_var : string) (p : prop) : prop :=
  match p with
  | prop_pred pred => prop_pred pred
  | t1 ≡ t2 => (rename_var_in_term old_var new_var t1) ≡ (rename_var_in_term old_var new_var t2)
  | ⊥ => ⊥
  | ¬ p1 => ¬ (rename_var_in_prop old_var new_var p1)
  | p1 ∧ p2 => (rename_var_in_prop old_var new_var p1) ∧ (rename_var_in_prop old_var new_var p2)
  | p1 ∨ p2 => (rename_var_in_prop old_var new_var p1) ∨ (rename_var_in_prop old_var new_var p2)
  | p1 ⇒ p2 => (rename_var_in_prop old_var new_var p1) ⇒ (rename_var_in_prop old_var new_var p2)
  | p1 ⇔ p2 => (rename_var_in_prop old_var new_var p1) ⇔ (rename_var_in_prop old_var new_var p2)
  | ∀ var, p1 => ∀ (if String.eqb var old_var then new_var else var), (rename_var_in_prop old_var new_var p1)
  | ∃ var, p1 => ∃ (if String.eqb var old_var then new_var else var), (rename_var_in_prop old_var new_var p1)
  end.

Theorem rename_var_in_prop_correct_same : forall var p,
  rename_var_in_prop var var p = p.
Proof.
  intros var p. induction p; simpl.
  - reflexivity.
  - rewrite -> ! rename_var_in_term_correct_same. reflexivity.
  - reflexivity.
  - rewrite -> IHp. reflexivity.
  - rewrite -> IHp1. rewrite -> IHp2. reflexivity.
  - rewrite -> IHp1. rewrite -> IHp2. reflexivity.
  - rewrite -> IHp1. rewrite -> IHp2. reflexivity.
  - rewrite -> IHp1. rewrite -> IHp2. reflexivity.
  - rewrite -> IHp. destruct (String.eqb_spec var0 var).
    + subst var0. reflexivity.
    + reflexivity.
  - rewrite -> IHp. destruct (String.eqb_spec var0 var).
    + subst var0. reflexivity.
    + reflexivity.
Qed.

Theorem rename_var_in_prop_correct_different : forall old_var new_var p,
  old_var <> new_var ->
  ~ BoundInProp new_var p ->
  ~ FreeInProp new_var p ->
  PropNameEquiv [(old_var, new_var)] p (rename_var_in_prop old_var new_var p).
Proof.
  intros old_var new_var p Hdifferent HNotBoundInProp HNotFreeInProp. induction p; simpl.
  - apply PropNameEquiv_pred.
  - apply PropNameEquiv_eq.
    + apply rename_var_in_term_correct. intros HFreeInTerm. apply HNotFreeInProp.
      apply FreeInProp_eq_1. apply HFreeInTerm.
    + apply rename_var_in_term_correct. intros HFreeInTerm. apply HNotFreeInProp.
      apply FreeInProp_eq_2. apply HFreeInTerm.
  - apply PropNameEquiv_false.
  - apply PropNameEquiv_neg. apply IHp.
    + intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_neg. apply HBoundInProp.
    + intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_neg. apply HFreeInProp.
  - apply PropNameEquiv_and.
    + apply IHp1.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_and_1. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_and_1. apply HFreeInProp.
    + apply IHp2.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_and_2. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_and_2. apply HFreeInProp.
  - apply PropNameEquiv_or.
    + apply IHp1.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_or_1. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_or_1. apply HFreeInProp.
    + apply IHp2.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_or_2. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_or_2. apply HFreeInProp.
  - apply PropNameEquiv_implies.
    + apply IHp1.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_implies_1. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_implies_1. apply HFreeInProp.
    + apply IHp2.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_implies_2. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_implies_2. apply HFreeInProp.
  - apply PropNameEquiv_iff.
    + apply IHp1.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_iff_1. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_iff_1. apply HFreeInProp.
    + apply IHp2.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_iff_2. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_iff_2. apply HFreeInProp.
  - destruct (String.eqb_spec var old_var).
    + subst var. apply PropNameEquiv_forall_internal.
      * simpl. left. reflexivity.
      * apply IHp.
        -- intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_forall_inner; assumption.
        -- intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_forall; assumption.
    + apply PropNameEquiv_forall_external.
      * simpl. intros [H | H]; congruence.
      * simpl. intros [H | H]; try congruence. subst var. apply HNotBoundInProp. apply BoundInProp_forall_self.
      * apply IHp.
        -- intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_forall_inner; assumption.
        -- intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_forall.
           ++ intros H. apply HNotBoundInProp. subst var. apply BoundInProp_forall_self.
           ++ apply HFreeInProp.
  - destruct (String.eqb_spec var old_var).
    + subst var. apply PropNameEquiv_exists_internal.
      * simpl. left. reflexivity.
      * apply IHp.
        -- intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_exists_inner; assumption.
        -- intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_exists; assumption.
    + apply PropNameEquiv_exists_external.
      * simpl. intros [H | H]; congruence.
      * simpl. intros [H | H]; try congruence. subst var. apply HNotBoundInProp. apply BoundInProp_exists_self.
      * apply IHp.
        -- intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_exists_inner; assumption.
        -- intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_exists.
           ++ intros H. apply HNotBoundInProp. subst var. apply BoundInProp_exists_self.
           ++ apply HFreeInProp.
Qed.

Fixpoint rename_bound_var_in_prop (old_var new_var : string) (p : prop) : prop :=
  match p with
  | prop_pred pred => prop_pred pred
  | t1 ≡ t2 => t1 ≡ t2
  | ⊥ => ⊥
  | ¬ p1 => ¬ (rename_bound_var_in_prop old_var new_var p1)
  | p1 ∧ p2 => (rename_bound_var_in_prop old_var new_var p1) ∧ (rename_bound_var_in_prop old_var new_var p2)
  | p1 ∨ p2 => (rename_bound_var_in_prop old_var new_var p1) ∨ (rename_bound_var_in_prop old_var new_var p2)
  | p1 ⇒ p2 => (rename_bound_var_in_prop old_var new_var p1) ⇒ (rename_bound_var_in_prop old_var new_var p2)
  | p1 ⇔ p2 => (rename_bound_var_in_prop old_var new_var p1) ⇔ (rename_bound_var_in_prop old_var new_var p2)
  | ∀ var, p1 =>
    if String.eqb var old_var
    then ∀ new_var, (rename_var_in_prop old_var new_var p1)
    else ∀ var, (rename_bound_var_in_prop old_var new_var p1)
  | ∃ var, p1 =>
    if String.eqb var old_var
    then ∃ new_var, (rename_var_in_prop old_var new_var p1)
    else ∃ var, (rename_bound_var_in_prop old_var new_var p1)
  end.

Theorem rename_bound_var_in_prop_correct_same : forall var p,
  rename_bound_var_in_prop var var p = p.
Proof.
  intros var p. induction p; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite -> IHp. reflexivity.
  - rewrite -> IHp1. rewrite -> IHp2. reflexivity.
  - rewrite -> IHp1. rewrite -> IHp2. reflexivity.
  - rewrite -> IHp1. rewrite -> IHp2. reflexivity.
  - rewrite -> IHp1. rewrite -> IHp2. reflexivity.
  - rewrite -> IHp. destruct (String.eqb_spec var0 var).
    + subst var0. rewrite -> rename_var_in_prop_correct_same. reflexivity.
    + reflexivity.
  - rewrite -> IHp. destruct (String.eqb_spec var0 var).
    + subst var0. rewrite -> rename_var_in_prop_correct_same. reflexivity.
    + reflexivity.
Qed.

Theorem rename_bound_var_in_prop_correct_different : forall old_var new_var p,
  old_var <> new_var ->
  ~ BoundInProp new_var p ->
  ~ FreeInProp new_var p ->
  PropNameEquiv [] p (rename_bound_var_in_prop old_var new_var p).
Proof.
  intros old_var new_var p Hdifferent HNotBoundInProp HNotFreeInProp. induction p; simpl.
  - apply PropNameEquiv_pred.
  - apply PropNameEquiv_eq.
    + apply TermNameEquiv_refl. intros var_a var_b H. exfalso. apply H.
    + apply TermNameEquiv_refl. intros var_a var_b H. exfalso. apply H.
  - apply PropNameEquiv_false.
  - apply PropNameEquiv_neg. apply IHp.
    + intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_neg. apply HBoundInProp.
    + intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_neg. apply HFreeInProp.
  - apply PropNameEquiv_and.
    + apply IHp1.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_and_1. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_and_1. apply HFreeInProp.
    + apply IHp2.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_and_2. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_and_2. apply HFreeInProp.
  - apply PropNameEquiv_or.
    + apply IHp1.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_or_1. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_or_1. apply HFreeInProp.
    + apply IHp2.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_or_2. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_or_2. apply HFreeInProp.
  - apply PropNameEquiv_implies.
    + apply IHp1.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_implies_1. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_implies_1. apply HFreeInProp.
    + apply IHp2.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_implies_2. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_implies_2. apply HFreeInProp.
  - apply PropNameEquiv_iff.
    + apply IHp1.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_iff_1. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_iff_1. apply HFreeInProp.
    + apply IHp2.
      * intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_iff_2. apply HBoundInProp.
      * intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_iff_2. apply HFreeInProp.
  - destruct (String.eqb_spec var old_var).
    + subst var. apply PropNameEquiv_forall_new.
      * intros H. destruct H.
      * intros H. destruct H.
      * apply rename_var_in_prop_correct_different.
        -- apply Hdifferent.
        -- intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_forall_inner; assumption.
        -- intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_forall; assumption.
    + apply PropNameEquiv_forall_external.
      * intros H. destruct H.
      * intros H. destruct H.
      * apply IHp.
        -- intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_forall_inner; assumption.
        -- intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_forall.
           ++ intros H. apply HNotBoundInProp. subst var. apply BoundInProp_forall_self.
           ++ apply HFreeInProp.
  - destruct (String.eqb_spec var old_var).
    + subst var. apply PropNameEquiv_exists_new.
      * intros H. destruct H.
      * intros H. destruct H.
      * apply rename_var_in_prop_correct_different.
        -- apply Hdifferent.
        -- intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_exists_inner; assumption.
        -- intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_exists; assumption.
    + apply PropNameEquiv_exists_external.
      * intros H. destruct H.
      * intros H. destruct H.
      * apply IHp.
        -- intros HBoundInProp. apply HNotBoundInProp. apply BoundInProp_exists_inner; assumption.
        -- intros HFreeInProp. apply HNotFreeInProp. apply FreeInProp_exists.
           ++ intros H. apply HNotBoundInProp. subst var. apply BoundInProp_exists_self.
           ++ apply HFreeInProp.
Qed.

Fixpoint rename_bound_vars_in_prop (used_vars : list string) (p : prop) (rename_vars : list string) : prop :=
  match rename_vars with
  | [] => p
  | rename_vars_h :: rename_vars_t =>
    rename_bound_var_in_prop
    rename_vars_h
    (rename_to_unused (get_bound_in_prop p ++ get_free_in_prop p ++ used_vars) rename_vars_h)
    (rename_bound_vars_in_prop used_vars p rename_vars_t)
  end.

Definition rename_all_bound_vars_in_prop (used_vars : list string) (p : prop) : prop :=
  rename_bound_vars_in_prop used_vars p used_vars.

(* Subst *)

Fixpoint subst_in_term (subst_var : string) (subst_t : term) (t : term) : term :=
  match t with
  | term_var var => if String.eqb var subst_var then subst_t else term_var var
  | 𝖮 => 𝖮
  | 𝖲 t1 => 𝖲 (subst_in_term subst_var subst_t t1)
  | t1 ⨣ t2 => (subst_in_term subst_var subst_t t1) ⨣ (subst_in_term subst_var subst_t t2)
  | t1 ⨰ t2 => (subst_in_term subst_var subst_t t1) ⨰ (subst_in_term subst_var subst_t t2)
  end.

Fixpoint simple_subst_in_prop (subst_var : string) (subst_t : term) (p : prop) : prop :=
  match p with
  | prop_pred pred => prop_pred pred
  | t1 ≡ t2 => (subst_in_term subst_var subst_t t1) ≡ (subst_in_term subst_var subst_t t2)
  | ⊥ => ⊥
  | ¬ p1 => ¬ (simple_subst_in_prop subst_var subst_t p1)
  | p1 ∧ p2 => (simple_subst_in_prop subst_var subst_t p1) ∧ (simple_subst_in_prop subst_var subst_t p2)
  | p1 ∨ p2 => (simple_subst_in_prop subst_var subst_t p1) ∨ (simple_subst_in_prop subst_var subst_t p2)
  | p1 ⇒ p2 => (simple_subst_in_prop subst_var subst_t p1) ⇒ (simple_subst_in_prop subst_var subst_t p2)
  | p1 ⇔ p2 => (simple_subst_in_prop subst_var subst_t p1) ⇔ (simple_subst_in_prop subst_var subst_t p2)
  | ∀ var, p1 =>
    if String.eqb var subst_var
    then ∀ var, p1
    else ∀ var, (simple_subst_in_prop subst_var subst_t p1)
  | ∃ var, p1 =>
    if String.eqb var subst_var
    then ∃ var, p1
    else ∃ var, (simple_subst_in_prop subst_var subst_t p1)
  end.

Definition subst_in_prop (subst_var : string) (subst_t : term) (p : prop) : prop :=
  simple_subst_in_prop subst_var subst_t (rename_all_bound_vars_in_prop (get_free_in_term subst_t) p).

(* Axioms *)

Definition axiom_peano_S_inj : prop := ∀ "x", ∀ "y", 𝖲 "x" ≡ 𝖲 "y" ⇒ "x" ≡ "y".

Definition axiom_peano_neq_O_S : prop := ∀ "x", ¬ (𝖮 ≡ 𝖲 "x").

Definition axiom_peano_ind : _ -> _ -> prop := fun (var : string) (p1 : prop) =>
  (subst_in_prop var 𝖮 p1) ∧ (∀ "x", (subst_in_prop var "x" p1) ⇒ (subst_in_prop var (𝖲 "x") p1)) ⇒
  ∀ "y", (subst_in_prop var "y" p1).

Definition axiom_peano_plus_O : prop := ∀ "y", 𝖮 ⨣ "y" ≡ "y".

Definition axiom_peano_plus_S : prop := ∀ "x", ∀ "y", 𝖲 "x" ⨣ "y" ≡ 𝖲 ("x" ⨣ "y").

Definition axiom_peano_mult_O : prop := ∀ "y", 𝖮 ⨰ "y" ≡ 𝖮.

Definition axiom_peano_mult_S : prop := ∀ "x", ∀ "y", 𝖲 "x" ⨰ "y" ≡ "x" ⨰ "y" ⨣ "y".

Compute get_free_in_term "y".

Compute rename_all_bound_vars_in_prop ["y"] (∀ "y", "z" ≡ "y").

Compute subst_in_prop "x" "y" ("y" ≡ "x").

Compute axiom_peano_ind "x" ("y" ≡ "x").
