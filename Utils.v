Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Lia.

Open Scope string_scope.
Open Scope list_scope.

Ltac create_var var value :=
  let Heq := fresh "Heq" var in
  refine ((fun var (Heq : var = value) => _) value eq_refl).

Theorem append_assoc : forall s1 s2 s3,
  (s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3)%string.
Proof.
  intros s1 s2 s3. induction s1.
  - reflexivity.
  - simpl. f_equal. apply IHs1.
Qed.

Fixpoint inb {A : Type} (eqb : A -> A -> bool) (a : A) (l : list A) : bool :=
  match l with
  | [] => false
  | lh :: lt => eqb lh a || inb eqb a lt
  end.

Lemma inb_spec : forall {A : Type} (eqb : A -> A -> bool),
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a l, reflect (In a l) (inb eqb a l).
Proof.
  intros A eqb eqb_spec a l. induction l as [| lh lt IH].
  - apply ReflectF. simpl. intros H. apply H.
  - simpl. destruct (eqb_spec lh a).
    + subst. apply ReflectT. left. reflexivity.
    + simpl. destruct IH.
      * apply ReflectT. right. apply i.
      * apply ReflectF. intros [H1 | H2]; congruence.
Qed.

Fixpoint remove' {A : Type} (eqb : A -> A -> bool) (a : A) (l : list A) : list A :=
  match l with
  | [] => []
  | lh :: lt => if eqb lh a then remove' eqb a lt else lh :: remove' eqb a lt
  end.

Lemma In_remove'_length_weak : forall {A : Type} (eqb : A -> A -> bool),
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a l, length (remove' eqb a l) <= length l.
Proof.
  intros A eqb eqb_spec a l. induction l as [| lh lt IH].
  - reflexivity.
  - simpl. destruct (eqb_spec lh a).
    + lia.
    + simpl. lia.
Qed.

Theorem In_remove'_length : forall {A : Type} (eqb : A -> A -> bool),
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a l, In a l -> length (remove' eqb a l) < length l.
Proof.
  intros A eqb eqb_spec a l HIn. induction l as [| lh lt IH].
  - inversion HIn.
  - simpl. destruct (eqb_spec lh a).
    + specialize (In_remove'_length_weak eqb eqb_spec a lt). lia.
    + simpl. inversion HIn.
      * congruence.
      * apply Lt.lt_n_S. apply IH. apply H.
Qed.

Theorem remove'_not_In : forall {A : Type} (eqb : A -> A -> bool),
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a l, ~ In a (remove' eqb a l).
Proof.
  intros A eqb eqb_spec a l HIn. induction l as [| lh lt IH].
  - inversion HIn.
  - simpl in HIn. destruct (eqb_spec lh a).
    + apply IH. apply HIn.
    + simpl in HIn. destruct HIn as [HIn | HIn].
      * congruence.
      * apply IH. apply HIn.
Qed.

Theorem remove'_In : forall {A : Type} (eqb : A -> A -> bool),
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a b l, In b l -> b <> a -> In b (remove' eqb a l).
Proof.
  intros A eqb eqb_spec a b l HIn Hneq. induction l as [| lh lt IH].
  - destruct HIn.
  - simpl. simpl in HIn. destruct HIn as [HIn | HIn].
    + destruct (eqb_spec lh a).
      * congruence.
      * simpl. left. apply HIn.
    + destruct (eqb_spec lh a).
      * apply IH. apply HIn.
      * simpl. right. apply IH. apply HIn.
Qed.

Theorem remove'_In_iff : forall {A : Type} (eqb : A -> A -> bool),
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a b l, (In b l /\ b <> a) <-> In b (remove' eqb a l).
Proof.
  intros A eqb eqb_spec a b l. split.
  - intros [HIn Hneq]. apply remove'_In; assumption.
  - intros HIn_remove'. split.
    + induction l as [| lh lt IH]; simpl in *.
      * apply HIn_remove'.
      * destruct (eqb_spec lh a).
        -- right. apply IH. apply HIn_remove'.
        -- simpl in HIn_remove'. destruct HIn_remove' as [HIn_remove' | HIn_remove'].
           ++ left. apply HIn_remove'.
           ++ right. apply IH. apply HIn_remove'.
    + induction l as [| lh lt IH]; simpl in *.
      * exfalso. apply HIn_remove'.
      * destruct (eqb_spec lh a).
        -- apply IH. apply HIn_remove'.
        -- simpl in HIn_remove'. destruct HIn_remove' as [HIn_remove' | HIn_remove'].
           ++ subst lh. apply n.
           ++ apply IH. apply HIn_remove'.
Qed.

Definition prod_eqb {U V : Type} (eqb_u : U -> U -> bool) (eqb_v : V -> V -> bool)
                    (prod_a : U * V) (prod_b : U * V) : bool :=
  eqb_u (fst prod_a) (fst prod_b) && eqb_v (snd prod_a) (snd prod_b).

Lemma prod_eqb_spec : forall {U V : Type} (eqb_u : U -> U -> bool) (eqb_v : V -> V -> bool),
  (forall u_a u_b, reflect (u_a = u_b) (eqb_u u_a u_b)) ->
  (forall v_a v_b, reflect (v_a = v_b) (eqb_v v_a v_b)) ->
  forall prod_a prod_b, reflect (prod_a = prod_b) (prod_eqb eqb_u eqb_v prod_a prod_b).
Proof.
  intros U V eqb_u eqb_v eqb_u_spec eqb_v_spec prod_a prod_b.
  destruct prod_a as [u_a v_a], prod_b as [u_b v_b].
  unfold prod_eqb. simpl.
  destruct (eqb_u_spec u_a u_b), (eqb_v_spec v_a v_b).
  - simpl. apply ReflectT. f_equal; assumption.
  - simpl. apply ReflectF. intros H. injection H as H_a H_b. congruence.
  - simpl. apply ReflectF. intros H. injection H as H_a H_b. congruence.
  - simpl. apply ReflectF. intros H. injection H as H_a H_b. congruence.
Qed.

(* Unused for now: *)

Ltac specialize_any H :=
  match type of H with ?T -> _ =>
  let X := fresh in
  assert (X : T);
  [ | specialize (H X); clear X ] end.
