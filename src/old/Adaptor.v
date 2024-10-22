Require Export LTS.
Require Import Lists.List.
Require Export CodeMap.
Require Export ACUtil.
Require Export Contraction.
Require Export Coq.Logic.ProofIrrelevance.

Import ListNotations.


(** Here, we formalize some parts of the Adaptors section. **)

(** * Determinate Action Codes **)

(** In contrast to the paper, we keep the notion of [Determinate]
 generic in two relations, one on A, one on B, which models when
 two actions i/o and i'/o/ have the same input component: **)
Definition Determinate {A B: Type} (R: CodeMap A B) (rel_a: relation A)
                       (rel_b: relation B)
  := forall (w: list A) (i1 i2: A) (u1 u2: list A) (b1 b2: B),
    R b1 = Some (w ++ [i1] ++ u1) ->
    R b2 = Some (w ++ [i2] ++ u2) ->
    rel_b b1 b2 ->
    rel_a i1 i2.

(** If we instantiate the two relations to be the identity relation,
    then every code fulfills this the property: **)
Example every_code_is_idrel_determinate {A B: Type} (R: CodeMap A B) :
  Determinate R idRel idRel.
Proof.
  unfold_goal.
  intros ? ? ? ? ? ? ? R1 R2.
  intros.
  unfold idRel in *.
  subst.
  rewrite R1 in R2.
  injection R2 as R2.
  apply app_strip_common_prefix in R2.
  inversion R2.
  subst. auto.
Qed.

(** As a technical lemma, we need that [Determinate] is symmetric: **)
Lemma determinate_symmetric {A B: Type} (R: CodeMap A B) (rel_a: relation A)
                       (rel_b: relation B):
  Determinate R rel_a rel_b <-> Determinate R (converse rel_a) (converse rel_b).
Proof.
  symmetric_cases.
  intros R_det w.
  intros.
  unfold converse.
  eapply R_det; eauto.
Qed.

(** We can now prove that the [contraction] operator for [Determinate] codes
 preserves determinism. In the induction, we use the following
 base case twice; hence, it is a separate lemma: **)

(** Determinate action codes preserve determinism: **)
Lemma determinate_contraction_determinism_base_case
  {A B: Type} (R: Code A B) (rel_a: relation A) (rel_b: relation B)
  (M: LTS A) :
  Determinate R rel_a rel_b ->
  M is rel_a deterministic ->
  forall (v w2: list A) (b1 b2: B) (p q q1 q2: states M),
    rel_b b1 b2 ->
    R b1 = Some (v) ->
    R b2 = Some (v ++ w2) ->
    (p == v ==> q) ->
    (q == w2 ==> q2) ->
    b1 = b2 /\ q = q2.
Proof.
  intros.
  assert (b1 = b2). {
    apply (proj_code_prefix_free R).
    rewrite H2.
    rewrite H3.
    constructor.
    apply prefix_of_app.
    exists w2. reflexivity.
  }
  subst.
  rewrite H2 in H3.
  inversion H3.
  apply app_yields_prefix in H7.
  subst.
  inversion H5.
  subst.
  auto.
Qed.

(** The proof by induction keeps track of a bit more information:
    Essentially we have two paths, one for R b1, another for R b2 and
    we have proven already, that both paths agree on the prefix v:
    **)
Lemma determinate_contraction_determinism_induction
  {A B: Type} (R: Code A B) (rel_a: relation A) (rel_b: relation B)
  (M: LTS A) :
  Determinate R rel_a rel_b ->
  M is rel_a deterministic ->
  forall (v w1 w2: list A) (b1 b2: B) (p q q1 q2: states M),
    rel_b b1 b2 ->
    R b1 = Some (v ++ w1) ->
    R b2 = Some (v ++ w2) ->
    (p == v ==> q) ->
    (q == w1 ==> q1) ->
    (q == w2 ==> q2) ->
    b1 = b2 /\ q1 = q2.
Proof.
  intros R_det M_det v w1.
  revert v.
  induction w1;
    intros v w2 b1 b2 p q q1 q2 rel_b12 Eq_b1 Eq_b2 Run_v Run_w1 Run_w2.
  - rewrite app_nil_r in *.
    inversion Run_w1.
    subst.
    eapply determinate_contraction_determinism_base_case; eauto.
  - destruct w2.
    * inversion Run_w2. subst.
      rewrite app_nil_r in *.
      assert (b2 = b1 /\ q2 = q1). {
        eapply determinate_contraction_determinism_base_case
        with (rel_a := converse rel_a) (rel_b := converse rel_b); eauto.
        eapply (proj1 (determinate_symmetric _ _ _)).
        auto.
        apply (proj1 (deterministic_symmetric _ _)).
        auto.
      }
      autodestruct.
      split; auto.
    * inversion Run_w1.
      inversion Run_w2. subst.
      assert (rel_a a a0) as Rel. {
        eapply R_det; eauto; simpl; eauto.
      }
      eapply M_det in Rel; eauto.
      destruct Rel.
      (* now, we've zipped the successor states together. *)
      subst a0. subst q_a0.
      eapply IHw1 with (v := v ++ [a]); eauto;
      try rewrite <- app_assoc; simpl; eauto.
      eapply path_app; eauto.
      apply gtrans_singleton. auto.
Qed.

(** From above induction, we conclude that the [contraction] operator
    for [Determinate] codes preserves determinism -- all generic
    in relations that specify the type of determinism: **)
Proposition determinate_contraction_determinism
  {A B: Type} (R: Code A B) (rel_a: relation A) (rel_b: relation B)
  (M: LTS A) :
  Determinate R rel_a rel_b ->
  M is rel_a deterministic ->
  (contraction R M) is rel_b deterministic.
Proof.
  intros R_det M_det.
  intros q q1 q2 b1 b2 Step_b1 Step_b2 r_b12.
  simpl in Step_b1.
  simpl in Step_b2.
  necessarily_some (R b1) w1.
  necessarily_some (R b2) w2.
  eapply determinate_contraction_determinism_induction
    with (R:=R) (rel_a:=rel_a) (rel_b:=rel_b); auto.
  rewrite app_nil_l. simpl. apply Eq_w1.
  rewrite app_nil_l. simpl. apply Eq_w2.
  constructor.
  eauto.
  eauto.
Qed.

(** When instantiating that for [idRel], we directly obtain
    that the contraction operator sends deterministic LTSs
    to deterministic LTSs. **)
Corollary contraction_preserves_determinism
  {A B: Type} (R: Code A B) (M: LTS A) :
  M is deterministic ->
  (contraction R M) is  deterministic.
Proof.
  intros.
  eapply determinate_contraction_determinism.
  apply every_code_is_idrel_determinate.
  auto.
Qed.
