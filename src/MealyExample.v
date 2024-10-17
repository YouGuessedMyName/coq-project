Require Export LTS.
Require Import Lists.List.
Require Export CodeMap.
Require Export Contraction.
Require Export Concretization.

Import ListNotations.

(** * The Mealy Machine **)
(** The example Mealy machine from Section 2 of the paper. **)

Inductive Q : Type := q0 | q1 | q2 | q3.

Inductive I := ia | ib.
Inductive O := o0 | o1.

Definition Transition : Q -> I*O -> Q -> Prop :=
  fun q io q' =>
  match (q,q') with
  | (q0,q1) => io = (ib,o0)
  | (q1,q0) => io = (ib,o0)
  | (q1,q2) => io = (ia,o0)
  | (q2,q1) => io = (ib,o0)
  | (q2,q3) => io = (ia,o0)
  | (q3,q2) => io = (ia,o0)
  | (q3,q0) => io = (ib,o1)
  | (q0,q3) => io = (ia,o0)
  | _ => False
  end.

Definition SI : (I*O) -> (I*O) -> Prop
   := fun '(i1,_) '(i2,_) => i1 = i2.

(** We combine all ingredients to define the LTS: **)
Definition ExampleMealy : LTS (I*O) := {|
      states := Q;
      initial := q0;
      transition := Transition;
  |}.

(** * A first Action Code **)

(** In the first code example, we only have output 0,
 so we omit this in the definition of the abstract
 action alphabet. **)
Inductive X := XA | XB.
Definition R1 : X -> option (list (I*O)) :=
  fun x => match x with
  | XA => Some [(ia,o0); (ia,o0)]
  | XB => Some [(ib,o0); (ib,o0)]
  end.

Lemma R1_ne_word : code_ne_word R1.
Proof.
  intros x Contr. destruct x; discriminate.
Qed.

Lemma R1_prefix_free : prefix_free R1.
Proof.
  intros b1 b2 Pref.
  necessarily_some (R1 b1) Rb1; try (inversion Pref; fail).
  necessarily_some (R1 b2) Rb2; try (inversion Pref; fail).
  destruct b1; destruct b2; simpl in *; autodestruct;
    subst Rb1; subst Rb2; auto.
  all: inversion Pref.
  all: inversion H1.
Qed.

Definition R1_code : Code (I*O) X :=
  Build_Code _ _ R1 R1_ne_word R1_prefix_free.

Lemma mealy_example_code1_is_complete :
  icomplete R1 SI ExampleMealy.
Proof.
  Definition R := R1.
  replace R1 with R; [|auto].
  intros q w R_w u io io'.
  intros Eq_Rw Run_Rwu Run_Rwio1 Run_q' H_SI.
  destruct io as [i o].
  destruct io' as [i' o'].
  inv_clear H_SI.
  subst i'.
  destruct Run_q' as [q' Step_o2].
  destruct Run_Rwio1 as [x Pref_Rx].
  necessarily_some (R x) Rx.
  simpl in Eq_Rx.
  apply prefix_of_app in Pref_Rx.
  destruct Pref_Rx as [tl Pref_Rx].
  rewrite <- app_assoc in Pref_Rx.
  subst Rx.
  apply path_app_rev in Run_Rwu.
  destruct Run_Rwu as [p [Run_w Run_u]].
  symmetry in Eq_Rx.
  apply (@ViaFiniteExists _ _ [XA; XB]); simpl.
  destruct x; simpl in Eq_Rx; inversion Eq_Rx as [Eq_list];
    apply app_eq_fixed_list in Eq_list; simpl in Eq_list;
    repeat (destruct_sum || autodestruct_once); subst; simpl;
    simpl in Eq_Rx; inversion Eq_Rx;
    try (apply gtrans_singleton in Run_u).
  (** Solve almost all cases for the involved transitions: **)
  all: destruct p; destruct q; try (inversion Run_u; fail).
  all: destruct q'; destruct o'; try (inversion Step_o2; fail).
  all: try (left ; apply prefix_of_reflexive).
  all: try (left ; constructor; constructor; fail).
  all: try (right ; apply prefix_of_reflexive).
  all: try (right ; constructor; constructor; fail).
  (** The remaining case is tricky:
   We have run from [q0] to [q3] for R^* w. Such a run
   however can not exist.
   **)
  exfalso.
  (** We do induction on w and strengthen the hypothesis: **)
  assert (initial ExampleMealy = q0 \/ initial ExampleMealy = q2). {
    left. auto.
  }
  generalize Eq_Rw Run_w H.
  generalize (initial ExampleMealy) R_w.
  clear Run_w R_w Eq_Rw.
  induction w as [|x ?];
    intros q R_w Eq_Rw Run_w q_cases.
  * inversion Eq_Rw. subst R_w. inversion Run_w. subst.
    destruct q_cases; discriminate.
  * simpl in Eq_Rw.
    necessarily_some (R x) Rx.
    necessarily_some (R^* w) R_tl.
    simpl in Eq_Rw.
    autodestruct.
    subst R_w.
    apply path_app_rev in Run_w.
    destruct Run_w as [p [? ?]].
    assert (p = q0 \/ p = q2). {
      destruct p;
        try (left; auto; fail);
        try (right; auto; fail);
        exfalso.
      all:
        destruct x; simpl in Eq_Rx0; autodestruct; subst Rx.
      all: inversion H0; subst.
      all: inversion H7; subst.
      all: inversion H9; subst.
      all: destruct q_a; inversion H6.
      all: destruct q; inversion H5.
      all: destruct q_cases; discriminate.
    }
    eapply (IHw p); eauto.
Qed.

Theorem dec_replace :
 forall P Q:Prop, (P <-> Q) -> decidable P -> decidable Q.
Proof.
  intros.
  destruct H0.
  - left. apply (proj1 H). auto.
  - right. intro Contr. apply H0. apply H. auto.
Qed.

(** Having I-completeness, we can apply the Galois connection: **)
Lemma simulation_from_mealy_to_own_concretization :
  ExampleMealy ⊑ (concretization SI R1_code (contraction R ExampleMealy)).
Proof.
  constructor.
  apply concretization_galois_forward; auto.
  * apply mealy_example_code1_is_complete.
  * intro io. destruct io. reflexivity.
  * intro w.
    pose (l := [XA; XB]).
    assert (forall b: X, List.In b l) as Enum_X. {
      intro x. subst l. simpl.
      destruct x; auto.
    }
    unfold code_has_run.
    eapply dec_replace with
      (P:= (FiniteExists l (fun b=> some_lift_pred (prefix_of w) (R1_code b)))). {
      split.
      apply ViaFiniteExists.
      apply ShowFiniteExists; auto.
    }
    apply FiniteExistsDecidable; auto.
    intros b.
    destruct (R1_code b) as [Rb|]; simpl.
    - apply prefix_of_decidable.
      intros [i o] [i' o'].
      destruct i; destruct o; destruct i'; destruct o'; auto.
      all: try (right; intro Contr; inversion Contr).
    - right. auto.
  * apply simulation_id.
Qed.
