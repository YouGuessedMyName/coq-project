Require Export LTS.
Require Import Lists.List.
Require Export CodeMap.
Require Export ACUtil.
Require Export Coq.Init.Specif.
Require Export Coq.Init.Logic.
Require Export Coq.Logic.ProofIrrelevance.

Import ListNotations.


(** * Definitions **)

(** A refined LTS has states structured as follows: a state of the old LTS
    together with a prefix of A-elements that is a proper prefix
    of some word in the code R. **)
Structure RefinedStates {A B: Type} {R: CodeMap A B} {M: LTS B} : Type :=
  mk_rs
  { rs_q : states M;
    rs_w : list A;
    rs_prop : rs_w = nil \/ exists (b : B), (rs_q ↓ b) /\ below_code rs_w (R b)
  }.

(** When considering equality, we ignore the [Prop] part of above structure
 using [proof_irrelevance].**)
Lemma rs_equal {A B: Type} {R: CodeMap A B} {M: LTS B} {t t': @RefinedStates A B R M}:
  (rs_q t = rs_q t') ->
  (rs_w t = rs_w t') -> t = t'.
Proof.
  intros.
  destruct t.
  destruct t'.
  simpl in *.
  subst.
  f_equal; apply proof_irrelevance.
Qed.

Definition rs_proj {A B: Type} {R: CodeMap A B} {M: LTS B} : @RefinedStates A B R M -> (states M * list A)
  := fun x => (rs_q x, rs_w x).

Definition nil_state {A B: Type} {R: CodeMap A B} {M: LTS B} (q: states M): @RefinedStates A B R M.
  apply mk_rs with (rs_q := q) (rs_w := []).
  left. reflexivity.
Defined.

(** separate the last element of the list **)

(** The transitions in the refinement are defined by the following rules: **)
Inductive RefTransInd {A B: Type} {R: CodeMap A B} {M: LTS B} :
  (states M * list A) -> A -> (states M * list A) -> Prop
  :=
  (** We can always accumulating prefix if the involed states exist: **)
  | RuleMid : forall
              (q: states M) (w: list A) (a: A),
           (* ------------------------------------------------ *)
              RefTransInd (q,w) a  (q,w ++ [a])
  (** As soon as the prefix becomes R b, we take the corresponding
      transition in M:
   **)
  | RuleEnd : forall
              (q q': states M) (w: list A) (a: A) (b: B),
              (q --b--> q')  ->  R b = Some (w ++ [a]) ->
           (* --------------------------------------------- *)
              RefTransInd (q,w) a (q',[])
.


(** We can directly define it as a match clause: **)
Definition RefTransCompact {A B: Type} {R: CodeMap A B}
  {M: LTS B} :
  RefinedStates -> A -> RefinedStates -> Prop
  := fun (qw: RefinedStates) (a: A) (qw': RefinedStates) =>
        let (q,w) := (rs_q (R:=R) qw, rs_w qw)  in
        let (q',w') := (rs_q (R:=R) qw', rs_w qw') in
        (* rule 1: accumulate prefix to complete some A-word known in the code *)
        (q = q' /\ w ++ [a] = w')
          \/
        (* rule 2: if `w a` is known to the code, take it if the original M
           can do the corresponding transition *)
        (exists b: B, R b = Some (w ++ [ a ]) /\ (M |- q --b--> q') /\ w' = [])
.

(** Both versions are equivalent: **)
Lemma RefTrans_equivalent {A B: Type} {R: CodeMap A B} {M: LTS B} :
  forall (qw qw': RefinedStates) (a: A),
    RefTransCompact (R:=R) qw a qw'
                      <->
    RefTransInd (R:=R) (rs_q qw, rs_w qw) a (rs_q qw', rs_w (M:=M) qw').
Proof.
  intros. split; intro H.
  - destruct H.
    * destruct H as [H1 H2].
      rewrite <-H1. rewrite <-H2.
      constructor.
    * destruct H as [b [EqRb [? ?]]].
      rewrite H0.
      econstructor; eauto.
  - inversion H; subst; unfold_goal.
    * left. rewrite  H4. rewrite H5. auto.
    * right.
      exists b. autosplit; eauto.
Qed.

(** Now, we can bring all ingredients together for the definition of the
    refined LTS:  **)
Definition refinement {A B: Type} (R: CodeMap A B) (M: LTS B) : LTS A :=
  {|
    states := @RefinedStates A B R M;
    initial := nil_state (initial M);
    transition := RefTransCompact
  |}.

(** * Helper Lemmas **)
Lemma rs_w_is_not_full {A B: Type} (R: Code A B) (M: LTS B) :
  forall (qw : states (refinement R M)) (b: B), R b <> Some (rs_w qw).
Proof.
  intros.
  intro H.
  case_eq_subst qw.
  destruct rs_prop0.
  * subst.
    case_eq_subst R.
    unfold code_ne_word in c.
    apply c in H.
    contradiction.
  * destruct e as [b'].
    destruct a.
    unfold below_code in b0.
    clear CaseEq.
    case_eq_subst (R b'); try contradiction.
    destruct b0.
    apply H0.
    (* use that R is prefix free *)
    destruct R.
    assert (b = b').
    apply p.
    simpl in *.
    rewrite ->H.
    rewrite ->CaseEq.
    constructor.
    assumption.
    subst.
    rewrite ->H in CaseEq.
    inversion CaseEq.
    reflexivity.
Qed.

(** whenever we have built up a non-empty prefix, we can complete it to a full
transition in the original LTS: **)

Lemma states_can_be_completed {A B: Type} (R: Code A B) (M: LTS B)
  (b: B) (u: list A): forall (qw: states (refinement R M)) (q': states M),
      ((rs_q qw) --b--> q')
      -> (R b = Some (rs_w qw ++ u))
      -> (qw ==u==> nil_state q').
Proof.
  pose (list_extract_last u) as H.
  destruct H.
  - (* case u=nil is contradictory *)
    intros. subst.
    rewrite ->app_nil_r in H1.
    exfalso.
    eapply rs_w_is_not_full.
    eassumption.
  - (* do the actual induction here *)
    destruct H as [w]. destruct H.
    subst.
    induction w; intros; simpl.
    * apply gtrans_singleton.
      simpl in *.
      right.
      exists b. auto.
    * assert (exists qwa : RefinedStates, rs_q qwa = rs_q qw /\ rs_w (R:=R) qwa = rs_w qw ++ [a]) as Pqwa.
      + unshelve epose (mk_rs A B R M (rs_q qw) (rs_w qw ++ [a]) _) as qwa.
        right. exists b. split. exists q'. assumption.
        unfold below_code. rewrite ->H0.
        split. simpl. intro Contr.
        apply app_strip_common_prefix in Contr.
        assert ([a] ++ [] = [a] ++ (w ++ [x])) by (simpl; assumption).
        apply app_strip_common_prefix in H1.
        destruct w; simpl in H1; discriminate.
        apply prefix_of_app.
        exists (w ++ [x]).
        rewrite <-app_assoc.
        simpl. reflexivity.
        exists qwa.
        split; unfold qwa; simpl; reflexivity.
      + destruct Pqwa as [qwa].
        destruct H1.
        (* essentially: econstructor with `qwa` *)
        unshelve econstructor. exact qwa.
        simpl. left. split; auto.
        apply IHw.
        rewrite ->H1. assumption.
        rewrite ->H0. rewrite->H2. simpl.
        f_equal.
        rewrite <-app_assoc.
        reflexivity.
Qed.

Lemma transitions_to_nil_state {A B: Type} (R: Code A B) (M: LTS B) (b: B)
  (qw: states (refinement R M)) (w: list A) (q': states M):
     R b = Some (rs_w qw ++ w)
     -> (refinement R M |- qw == w ==> (nil_state q'))
     -> (M |- rs_q qw --b--> q').
Proof.
  destruct (list_extract_last w).
  - (* contradictory *)
    intro Rb.
    subst.
    rewrite ->app_nil_r in Rb.
    exfalso.
    eapply rs_w_is_not_full. eassumption.
  - destruct H as [tl]. destruct H.
    subst.
    revert qw.
    induction tl; intros.
    * simpl in *.
      apply gtrans_singleton in H0.
      destruct H0.
      + simpl in H0. apply proj2 in H0.
        exfalso.
        eapply app_cons_not_nil. eauto.
      + destruct H0 as [b'].
        destruct H0.
        destruct H1.
        assert (b = b').
        destruct R. apply p.
        simpl in *.
        rewrite ->H.
        rewrite ->H0.
        constructor.
        apply prefix_of_reflexive.
        simpl in H1.
        subst. assumption.
    * inversion H0. subst.
      destruct H4.
      + destruct H1.
        (* put q_a in the goal, because we apply the IH for q_a: *)
        rewrite ->H1.
        apply IHtl.
        ** rewrite <-H2.
           rewrite <-app_assoc.
           assumption.
        ** assumption.
      + (* this case is contradictory *)
        destruct H1 as [b'].
        destruct H1.
        assert (b' = b).
        ** (* use that R is prefix free *)
           destruct R. simpl in *. apply p.
           rewrite ->H.
           rewrite ->H1.
           constructor.
           apply prefix_of_app.
           exists (tl ++ [x]).
           rewrite <-app_assoc.
           simpl.
           reflexivity.
        ** subst.
           (* b' = b but R b' <> R b *)
           exfalso.
           rewrite H in H1.
           inversion H1.
           apply app_cons_not_nil with (x:= tl) (a := x) (y:=[]).
           eapply app_strip_common_prefix with (pref := rs_w qw ++ [a]).
           symmetry.
           rewrite <-app_assoc.
           rewrite app_nil_r.
           simpl.
           assumption.
Qed.

Theorem refinement_defined_transition {A B: Type} (R: Code A B) (M: LTS B)
  (b: B): forall (q q': states M) (Rb : list A), Some Rb = R b ->
                  (M |- q -- b --> q')
     <->    (refinement R M |-  (nil_state q) == Rb ==> (nil_state q')).
Proof.
  split; intros.
  - eapply states_can_be_completed; eauto.
  - apply transitions_to_nil_state with (b:=b) in H0; auto.
Qed.

Lemma refinement_pref_transition_equiv {A B: Type} (R: Code A B) (M: LTS B)
  : forall (qw qw': states (refinement R M)) (a: A),
    (qw -- a --> qw')
       <-> exists b : B, exists q'' : states M, exists u : list A,
            Some (rs_w qw ++ [a] ++ u) = R b
            /\ (rs_q qw --b--> q'')
            /\ (qw' ==u==> nil_state q'')
            (* This last conjunct is only here to make it an equivalence: *)
            /\ (u <> [] -> (rs_q qw = rs_q qw' /\ rs_w qw ++ [a] = rs_w qw')).
Proof.
  intros.
  split; intros H.
  *** inversion H.
      - destruct H0.
        destruct (rs_prop qw').
        * rewrite ->H2 in H1.
          exfalso.
          eapply app_cons_not_nil.
          eauto.
        * destruct H2 as [b].
          destruct H2.
          destruct H2 as [q''].
          apply below_code_app in H3.
          destruct H3 as [a'].
          destruct H3 as [u].
          exists b. exists q''. exists (a'::u).
          split; [|split; [|split]].
          + rewrite app_assoc. rewrite ->H1. assumption.
          + rewrite H0. assumption.
          + eapply states_can_be_completed; eauto.
          + auto.
      - destruct H0 as [b].
        destruct H0.
        destruct H1.
        exists b. exists (rs_q qw'). exists nil.
        split; [|split; [|split]].
        + rewrite app_nil_r. auto.
        + assumption.
        + replace (nil_state (rs_q qw')) with qw'.
          constructor.
          apply rs_equal; auto.
        + intro; contradiction.
  *** destruct H as [b].
      destruct H as [q''].
      destruct H as [u].
      destruct H.
      simpl.
      destruct H0.
      destruct u eqn: Eq.
      destruct H1.
      - rewrite ->app_nil_r in H.
        (* we are in an 'end' transition *)
        right.
        exists b.
        inversion H1.
        subst.
        split; [|split]; try auto.
      - inversion H1.
        subst.
        (* we are in a 'mid' transition *)
        left.
        split; apply H3; simpl; auto; discriminate.
Qed.

Corollary refinement_pref_transition {A B: Type} (R: Code A B) (M: LTS B)
  : forall (qw qw': states (refinement R M)) (a: A),
    (qw -- a --> qw')
       -> exists b : B, exists q'' : states M, exists u : list A,
            Some (rs_w qw ++ [a] ++ u) = R b
            /\ (rs_q qw --b--> q'')
            /\ (qw' ==u==> nil_state q'').
Proof.
  intros.
  apply refinement_pref_transition_equiv in H.
  destruct H as [b [q'' [u ?]]].
  destruct H as [? [? [? ?]]].
  exists b. exists q''. exists u. auto.
Qed.

Lemma refinement_forward_closure {A B: Type} (R: Code A B) (M: LTS B)
  : forall (qw: states (refinement R M)) (a: A)
       (b : B) (q'' : states M) (u : list A),
       R b = Some (rs_w qw ++ [a] ++ u)
       -> (rs_q qw --b--> q'')
       -> exists qw': states (refinement R M),
         (qw --a--> qw')
         /\ (u <> [] -> rs_q qw' = rs_q qw /\ rs_w qw' = rs_w qw ++ [a])
         /\ (u = [] -> qw' = nil_state q'').
Proof.
  intros.
  destruct u.
  - rewrite app_nil_r in *.
    exists (nil_state q'').
    split; [|split].
    * simpl. right.
    exists b. split; auto.
    * intro Contr. exfalso. apply Contr. auto.
    * intro. auto.
  - unshelve (eexists (mk_rs _ _ _ M (rs_q qw) (rs_w qw ++ [a]) _)). {
      right.
      exists b.
      split.
      exists q''. assumption.
      apply below_code_app.
      exists a0. exists u. rewrite <-app_assoc. auto.
    }
    simpl.
    split; [|split].
    * left. split; auto.
    * intro. split; auto.
    * intro. discriminate.
Qed.

Lemma transitions_from_nil_state {A B: Type} (R: Code A B)
  (M: LTS B) (b: B) (q: states M) (w: list A) (q': states M):
     below_code w (R b)
     -> (M |- q --b--> q')
     -> exists qw: states (refinement R M),
       (refinement R M |- nil_state q ==w==> qw) /\ rs_q qw = q /\ rs_w qw = w.
Proof.
  induction w using @rev_ind.
  - intros.
    exists (nil_state q).
    split; auto.
    constructor.
  - intros.
    destruct (R b) as [R_b|] eqn: EqRb; try contradiction.
    assert (below_code w (R b)). {
      unfold below_code in H.
      destruct H.
      simpl.
      apply prefix_of_app in H1.
      destruct H1 as [u ?].
      rewrite <-app_assoc in H1.
      rewrite EqRb.
      simpl.
      split.
      * intro. subst.
        apply app_yields_prefix in H2.
        inversion H2.
      * apply prefix_of_app.
        exists (x::u). auto.
    }
    rewrite_premise IHw; try assumption.
    rewrite_premise IHw; try assumption.
    destruct IHw as [qw].
    destruct_conjunctions.
    simpl in H.
    destruct H.
    apply prefix_of_app in H5.
    destruct H5 as [u ?].
    rewrite <-app_assoc in H5.
    rewrite <-H5 in EqRb.
    rewrite <-H4 in EqRb.
    eapply refinement_forward_closure in EqRb; revgoals.
    * rewrite H3. eassumption.
    * destruct EqRb as [qw'].
      destruct_conjunctions.
      (* show that u <> [] *)
      assert (u <> []). {
        rewrite <-H5 in H.
        intro.
        subst.
        rewrite app_nil_r in H.
        auto.
      }
      rewrite_premise H7; try assumption.
      destruct_conjunctions.
      exists qw'.
      split.
      eapply path_app; try eassumption.
      apply gtrans_singleton.
      assumption.
      rewrite H7.
      rewrite H10.
      rewrite H4.
      split; auto.
    * rewrite <-EqRb. assumption.
Qed.

(** * Properties: Monotonicity, Determinism **)

Lemma refinement_monotone {A B: Type} (R: Code A B) (M N: LTS B) :
  Simulation M N -> Simulation (refinement R M) (refinement R N).
Proof.
  intros S.
  pose (T := fun (qw: states (refinement R M)) (pv: states (refinement R N)) =>
               S (rs_q qw) (rs_q pv) /\ rs_w qw = rs_w pv).
  apply Build_Simulation with (rel := T).
  - unfold_goal. unfold_goal.
    destruct S. auto.
  - intros qw qw' pv a T_rel Step_a.
    destruct T_rel as [S_rel Eq_prefix].
    apply refinement_pref_transition_equiv in Step_a.
    autodestruct.
    destruct (list_eq_nil_tnd x1).
    * subst x1. simpl_impl.
      inversion H1. subst.
      clear H1.
      eapply (proj_sim_step S) in H0; eauto.
      autodestruct.
      exists (nil_state x1).
      split.
      + simpl. right. exists x. split.
        rewrite <- Eq_prefix. auto.
        autosplit; auto.
      + simpl; autosplit; auto.
    * rewrite_premise H2; auto. autodestruct.
      unshelve epose (mk_rs _ _ _ _ (rs_q pv) (rs_w qw ++ [a]) _).
      + apply R.
      + right. exists x.
        eapply (proj_sim_step S) in H0; eauto.
        autodestruct.
        autosplit; eauto.
        simpl.
        destruct R.
        unfold_goal.
        simpl in H.
        rewrite <- H.
        autosplit.
        intros ?.
        apply app_strip_common_prefix in H6.
        autodestruct.
        auto.
        apply prefix_of_app.
        exists x1. rewrite <-app_assoc. auto.
    + exists r. autosplit; simpl.
      left. rewrite <- Eq_prefix. auto.
      rewrite <- H2. auto.
      auto.
Qed.

Lemma refinement_preserves_determinism {A B: Type} (R: Code A B) (M N: LTS B) :
     M is deterministic -> (refinement R M) is deterministic.
Proof.
  intros M_det qw qw1 qw2 a a' Step1 Step2.
  intros; subst a'.
  autosplit.
  apply RefTrans_equivalent in Step1.
  apply RefTrans_equivalent in Step2.
  inversion Step1; inversion Step2; subst.
  * rewrite H4 in H9.
    rewrite H in H8.
    apply rs_equal; auto.
  * exfalso.
    rewrite H4 in H10.
    eapply rs_w_is_not_full. eauto.
  * exfalso.
    rewrite H11 in H5.
    eapply rs_w_is_not_full. eauto.
  * assert (b = b0 /\ rs_q qw1 = rs_q qw2). {
      eapply M_det; eauto.
      apply (proj_code_prefix_free R).
      rewrite H5. rewrite H12.
      constructor.
      apply prefix_of_reflexive.
    }
    autodestruct. subst.
    rewrite H4 in H11.
    apply rs_equal; eauto.
Qed.

(** * Adjunction / Galois insertion **)

Require Export Contraction.
(**
 For the forward version, we require that R is defined for
 all action labels that appear in N.
 **)
Lemma refinement_galois_forward {A B: Type} {R: Code A B}
      (N: LTS B) (M: LTS A) :
    Included _ (LTS_uses_action N) (in_dom R) ->
    Simulation (refinement R N) M -> Simulation N (contraction R M).
Proof.
  intros R_total S.
  destruct S as [S S_initial S_step].
  pose (T := fun (p: states N) (q: states (contraction R M)) =>
                  S (nil_state p) q).
  apply (Build_Simulation) with (rel:=T).
  - unfold relates_initial. unfold T.
    unfold relates_initial in S_initial.
    simpl in S_initial.
    simpl. assumption.
  - intros p p' q b T_p_q Step_b.
    assert (is_some (R b)). {
      apply R_total.
      exists p. exists p'. auto.
    }
    destruct (R b) as [R_b|] eqn: EqRb; try contradiction.
    apply (refinement_defined_transition R _ _ _ _ R_b) in Step_b; try auto.
    apply step_closed_sequence with (p:= q) (rel:=S) in Step_b; try auto.
    destruct Step_b as [q' [? ?]].
    exists q'; split; auto.
    simpl. rewrite ->EqRb. assumption.
Qed.

Lemma refinement_galois_backward {A B: Type} {R: Code A B}
      (N: LTS B) (M: LTS A) :
     M is deterministic ->
     Simulation N (contraction R M) -> Simulation (refinement R N) M.
Proof.
  intros M_det S.
  pose (T := fun (pw: states (refinement R N)) (q: states M) =>
                  let (p,w) := (rs_q pw, rs_w pw) in
                  exists q0 : states (contraction R M),
                    S p q0 /\ (M |- q0 == w ==> q)).
  simpl in T.
  apply Build_Simulation with (rel:=T).
  - unfold relates_initial. unfold T.
    exists (initial M). destruct S. simpl in *. split; simpl; auto.
    constructor; auto.
  - intros pw pw' q a T_pw_q Step_a.
    apply refinement_pref_transition_equiv in Step_a.
    destruct Step_a as [b [pw'' [u [EqRb [Step_b [Run_u If_Mid]]]]]].
    destruct T_pw_q as [q0 [S_p_q0 Run_w]].
    eapply (proj_sim_step S) in Step_b; try eassumption.
    destruct Step_b as [q'' [Step_b S_pw''_q'']].
    simpl in Step_b.
    rewrite <-EqRb in Step_b.
    apply path_app_rev in Step_b.
    destruct Step_b as [q_dup [Run_w_dup Run_a_u]].
    apply path_app_rev in Run_a_u.
    assert (q = q_dup). {
      (* strengthen target *)
      eapply (fun H: _ /\ _ => proj2 H).
      eapply (deterministic_sequence M_det); try eauto.
      apply list_rel_lift_id. reflexivity.
    }
    subst q_dup.
    clear Run_w_dup.
    destruct Run_a_u as [q' [Step_a Run_q_u]].
    apply gtrans_singleton in Step_a.
    exists q'; split; auto.
    unfold T; simpl.
    destruct (list_eq_nil_tnd u); subst; simpl_impl.
    * (* the transition completes (R b) *)
      (* thus we have a new witnessing state in T *)
      inversion Run_q_u. subst.
      inversion Run_u. subst.
      exists q''; split; simpl; eauto.
    * (* the transition is still below (R b) *)
      (* thus we have the same witnessing state in T *)
      rewrite_premise If_Mid; auto.
      exists q0.
      rewrite <- (proj1 If_Mid).
      rewrite <- (proj2 If_Mid).
      split; auto.
      eapply path_app; eauto.
      apply gtrans_singleton; auto.
Qed.

(** For the proof of Galois insertion, we use the following lemma
    that whenever we reach a state via an complete code word,
    then the reached state must have prefix [], i.e. it must
    be a nil_state.
 **)
Lemma path_with_complete_code {A B: Type} {R: Code A B}
      (N: LTS B) (b: B) (w: list A) (p p': states (refinement R N)):
    R b = Some (rs_w p ++ w)
    -> (refinement R N |- p == w ==> p')
    -> exists q': states N,
          (p' = nil_state q') /\ (rs_q p --b--> q').
Proof.
  destruct w as [|a w _] using rev_ind. {
    (* first case is a contradiction *)
    intros EqRb.
    rewrite app_nil_r in EqRb.
    eapply rs_w_is_not_full in EqRb.
    contradiction.
  }
  intros EqRb Step_w.
  apply path_app_rev in Step_w.
  destruct Step_w as [p_mid [Step_w Step_a]].
  apply gtrans_singleton in Step_a.
  assert (rs_q p_mid = rs_q p /\ rs_w p_mid = rs_w p ++ w). {
    revert p EqRb Step_w.
    induction w; intros p EqRb Step_w.
    * inversion Step_w. subst.
      rewrite app_nil_r.
      auto.
    * inversion Step_w. subst.
      apply RefTrans_equivalent in H2.
      inversion H2; subst.
      ** apply IHw in H4.
         + destruct H4.
           rewrite H.
           split; auto.
           rewrite H1.
           rewrite <- H6.
           rewrite <- app_assoc.
           reflexivity.
         + rewrite <- H6.
           rewrite <- app_assoc.
           assumption.
      ** assert (w ++ [a] = []). {
           eapply code_delta_empty.
           apply H7.
           rewrite <- app_assoc.
           eassumption.
         }
         exfalso.
         eapply app_cons_not_nil.
         eauto.
  }
  destruct Step_a. {
    (* first case is contradictory *)
    exfalso.
    eapply rs_w_is_not_full.
    rewrite <- (proj2 H0).
    rewrite (proj2 H).
    rewrite <- app_assoc.
    eassumption.
  }
  destruct H0 as [b' [EqRb' [Step_b' ?]]].
  assert (b' = b). {
    eapply proj_code_prefix_free.
    rewrite EqRb.
    rewrite EqRb'.
    constructor.
    rewrite (proj2 H).
    rewrite <- app_assoc.
    apply prefix_of_reflexive.
  }
  subst b'.
  exists (rs_q p').
  split.
  * apply rs_equal. reflexivity.
    rewrite H0. reflexivity.
  * rewrite <- (proj1 H).
    assumption.
Qed.

(** We can even show that we have a Galois insertion:
**)
Theorem refinement_galois_insertion {A B: Type} {R: Code A B}
      (N: LTS B) :
    (* If R is defined for all action labels used in N: *)
    Included _ (LTS_uses_action N) (in_dom R) ->
    (* then we have a Galois insertion: *)
    contraction R (refinement R N) ≅ N.
Proof.
  intros R_total.
  pose (iso := fun (p: states (contraction R (refinement R N))) (q: states N)
       => p = nil_state q).
  apply (Build_Isomorphism _ _ iso).
  * cbv. reflexivity.
  * intros p p' q b pq Step_b.
    unfold iso in pq. subst p.
    simpl in Step_b.
    necessarily_some (R b) R_b.
    eapply path_with_complete_code in Step_b; eauto.
    destruct Step_b as [q' [Eq_p' Step_b]].
    subst p'.
    exists q'.
    split; auto.
    cbv. auto.
  * intros q q' p b pq Step_b.
    exists (nil_state q').
    split.
    + assert (LTS_uses_action N b) as Using. {
        exists q. exists q'. auto.
      }
      apply R_total in Using.
      necessarily_some (R b) R_b. {
        destruct R.
        cbv in Using.
        simpl in Eq_R_b.
        rewrite Eq_R_b in Using.
        contradiction.
      }
      simpl.
      rewrite Eq_R_b.
      unfold converse in pq.
      unfold iso in pq.
      subst p.
      eapply (refinement_defined_transition _ _); eauto.
    + simpl.
      reflexivity.
  * intros x y1 y2 E1 E2.
    unfold iso in *.
    subst x.
    inversion E2.
    auto.
  * intros x y1 y2 E1 E2.
    unfold converse in *.
    unfold iso in *.
    subst y1.
    subst y2.
    reflexivity.
Qed.
