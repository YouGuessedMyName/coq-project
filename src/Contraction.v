Require Export LTS.
Require Import Lists.List.
Require Export CodeMap.
Require Export ACUtil.

(** * Definition **)
(**
For the definition of contraction, it suffices to have a code map without
any properties:
**)

Definition contraction {A B: Type} (R: CodeMap A B) (M: LTS A) : LTS B.
Proof.
  apply new_LTS with (states := states M).
  - apply (initial M). (* initial state is as in M *)
  - intros q b q'.
    (* when a transition q--b--> q' exists: *)
    destruct (R b) as [a_list|].
    * (* it exists if the code is defined an M has a run *)
      apply (q ==a_list==> q').
    * (* it does not exist otherwise *)
      apply False.
Defined.

(** We have defined the contraction operator via tactics. Still,
 the proof term is quite readable.
  << Print contraction. >> yields:
<<
contraction =
fun (A B : Type) (R : CodeMap A B) (M : LTS A) =>
{|
  states := states M;
  initial := initial M;
  transition :=
    fun (q : states M) (b : B) (q' : states M) =>
    let o := R b in
    match o with
    | Some a => (fun a_list : list A => (M |- q ══ a_list ==> q')) a
    | None => False
    end
|}
     : forall A B : Type, CodeMap A B -> LTS A -> LTS B
>>
 **)

(** * Properties **)

(** It is straightforward that contraction is monotone: **)
Lemma contraction_monotone {A B: Type} (R: CodeMap A B) (M N: LTS A) :
  Simulation M N -> Simulation (contraction R M) (contraction R N).
Proof.
  intros S.
  apply Build_Simulation with (rel := fun (q: states (contraction R M)) (p: states (contraction R N)) => S q p).
  - simpl. destruct S. auto.
  - intros q q' p b S_q_p Step_b.
    simpl in Step_b.
    necessarily_some (R b) R_b.
    destruct S.
    simpl in S_q_p.
    eapply step_closed_sequence in Step_b; eauto.
    destruct Step_b as [p' ?].
    exists p'.
    simpl.
    rewrite Eq_R_b.
    auto.
Qed.

(**
 Contraction interacts nicely with the kleisli extension of code maps:
 paths in the contracted LTS correspond to paths in the original LTS:
**)
Lemma contraction_kleisli_ext {A B: Type} (R: CodeMap A B) (M: LTS A) :
  forall (q q': states (contraction R M)) (w_b: list B),
    (q == w_b ==> q')
    <->
      exists w_a: list A, kleisli_ext R w_b = Some w_a
                     /\ (M |- q == w_a ==> q').
Proof.
  intros *.
  split.
  *** (* -> *)
    revert q q'.
    induction w_b.
    - exists nil. split. auto.
      inversion H. subst. constructor.
    - intros.
      inversion H; subst.
      apply IHw_b in H5.
      inversion H5 as [w_a_tl].
      unfold transition in H3.
      simpl in H3.
      case_eq_subst (R a).
      exists (l ++ w_a_tl).
      split.
      * rewrite ->CaseEq.
        apply proj1 in H0.
        rewrite ->H0.
        simpl.
        reflexivity.
      * apply proj2 in H0.
        apply path_app with (p := q_a); assumption.
  *** (* <- *)
    revert q'.
    revert q.
    induction w_b as [|b].
    - intros. simpl in H. destruct H. destruct H.
      inversion H. subst. inversion H0. subst.
      constructor.
    - intros. destruct H. destruct H.
      simpl in H.
      case_eq_subst (R b).
      case_eq_subst (kleisli_ext R w_b).
      inversion H. subst.
      apply path_app_rev in H0.
      clear H.
      destruct H0. destruct H.
      econstructor.
      + cbv. rewrite ->CaseEq. eassumption.
      + apply IHw_b. eexists. split. reflexivity.
        assumption.
Qed.

(** In order to show that contraction preserves action code composition,
we show that the following function is an isomorphism. **)
Definition contraction_composed_iso {A B C: Type}
  (R: Code A B) (S: Code B C) (M: LTS A) :
    states (contraction S (contraction R M))
    -> states (contraction (compose_code R S) M).
Proof.
  unfold contraction.
  simpl.
  apply id.
Defined.

(** In the iso proof, we need a simulation in form of a relation,
    so we will take the [graph] of above map.
**)

Theorem contraction_code_composition {A B C: Type}
  (R: Code A B) (S: Code B C) (M: LTS A) :
  contraction S (contraction R M) ≅ contraction (compose_code R S) M.
Proof.
  constructor 1 with (rel := graph (contraction_composed_iso R S M)).
  - cbv. reflexivity.
  - (* simulation from left to right *)
    intros ? ? ? c Rel_q_p Step_q.
    exists q'.
    split; revgoals.
    * unfold graph; reflexivity.
    * (* first show that p=q *)
      unfold graph in Rel_q_p.
      unfold contraction_composed_iso in Rel_q_p.
      unfold id in Rel_q_p.
      subst.
      (* now inspect the given transition *)
      unfold transition in Step_q.
      simpl in Step_q.
      case_eq_subst (S c).
      pose (Hw_a := Step_q).
      apply contraction_kleisli_ext in Hw_a.
      inversion Hw_a.
      rewrite <-compose_code_comm_proj.
      unfold compose_codemap.
      rewrite ->CaseEq.
      inversion H.
      rewrite ->H0.
      unfold contraction_composed_iso.
      unfold id.
      assumption.
  - (* simulation from right to left *)
    intros ? ? ? c Rel_q_p Step_q.
    exists q'.
    split.
    * (* show that p = q *)
      cbv in Rel_q_p; subst.
      (* now inspect the given transition *)
      unfold transition in Step_q.
      simpl in Step_q.
      rewrite <-compose_code_comm_proj in Step_q.
      simpl in *.
      unfold compose_codemap in Step_q.
      case_eq_subst (S c).
      case_eq_subst (kleisli_ext R l).
      apply contraction_kleisli_ext.
      exists l0.
      split; assumption.
    * cbv. reflexivity.
  - cbv. intros. subst. reflexivity.
  - cbv. intros. subst. reflexivity.
Qed.
