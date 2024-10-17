Require Export LTS.
Require Import Lists.List.
Require Export CodeMap.
Require Export ACUtil.
Require Export Refinement.

Import ListNotations.

(** * Isomorphism Definition **)

(** In the following, we show that the refinement operator
  preserves the action code composition. To this end, we consider the
  following isomorphism:
**)
Definition ref_code_iso {A B C: Type}
  (R: Code A B) (S: Code B C) (M: LTS C)
  (q_u_v: states (refinement R (refinement S M)))
  (p_w: states (refinement (compose_code R S) M))
  :=
  let (q_u, v) := rs_proj q_u_v in
  let (q,u) := rs_proj q_u in
  match kleisli_ext R u with
  | Some Ru => rs_q p_w = q /\ rs_w p_w = Ru ++ v
  | None => False
  end.

Definition ref_code_iso_on_words {A B C: Type}
  (R: Code A B) (S: Code B C) (M: LTS C) :
  (states (refinement R (refinement S M)))
  -> option (list A)
  := fun q_u_v =>
      let (q_u, v) := rs_proj q_u_v in
      let (q,u) := rs_proj q_u in
      Some (@app A) <*> (R^* u) <*> Some v.

(** * Proofs and helper results **)
(** The proof is separated into two directions and uses
    some auxiliary lemmas. **)


Lemma iso_kleisli_lift_defined {A B C: Type}
  (R: Code A B) (S: Code B C) (M: LTS C) (a: A)
  (q_u_v: states (refinement R (refinement S M)))
  (q_u_v': states (refinement R (refinement S M)))
  :
  (q_u_v --a--> q_u_v')
  -> is_some (kleisli_ext R (rs_w (rs_q q_u_v)))
  -> is_some (kleisli_ext R (rs_w (rs_q q_u_v'))).
Proof.
  intros.
  inversion H.
  - destruct H1.
    rewrite <-H1.
    assumption.
  - destruct H1 as [b [? [? ?]]].
    inversion H2.
    * destruct H4.
      rewrite <-H5.
      rewrite ->kleisli_ext_app.
      simpl.
      rewrite ->H1.
      rewrite app_nil_r.
      destruct (R^* (rs_w (rs_q q_u_v))); auto.
    * destruct H4 as [c [? [? ?]]].
      rewrite H6. simpl. auto.
Qed.


Lemma option_fapp_is_some {A B: Type} {f: option (A -> B)} {x: option A} :
  is_some (f <*> x) <-> is_some f /\ is_some x.
Proof.
  destruct f; destruct x; split; simpl; auto;
    intros H; destruct H; auto.
Qed.

Lemma exists_some_iff_is_some {A: Type} {x: option A} :
  is_some x <-> exists a: A, x = Some a.
Proof.
  split; intros H; destruct x; simpl in H;
    try destruct H; subst; simpl; auto; try discriminate.
  exists a; auto.
Qed.

Lemma app_nil {A: Type} (l1 l2: list A):
  l1 ++ l2 = [] <-> l1 = [] /\ l2 = [].
 Proof.
   destruct l1; destruct l2; split; intros; auto; try discriminate.
   destruct H. discriminate H0.
   destruct H. discriminate H.
   destruct H. discriminate H.
Qed.

(** The first direction: **)

Theorem refinement_preserves_code_composition_forward_sim {A B C: Type}
  (R: Code A B) (S: Code B C) (M: LTS C) :
  (forall c: dom S, is_some (R^* (total_code S c))) ->
    step_closed _ _ (ref_code_iso R S M).
Proof.
  intro S_range.
  intros q_u_v q_u_v' q_Ruv a H_iso Step.
    unfold ref_code_iso in H_iso.
    simpl in H_iso.
    destruct ((R^*) (rs_w (rs_q q_u_v))) as [Ru|] eqn: EqRu; try contradiction.
    assert (is_some (R^* (rs_w (rs_q q_u_v')))) as Have_Ru'. {
      eapply iso_kleisli_lift_defined.
      apply Step.
      rewrite EqRu.
      simpl. auto.
    }
    assert (is_some (ref_code_iso_on_words R S M q_u_v')) as TargetWord. {
      unfold ref_code_iso_on_words.
      simpl.
      apply option_fapp_is_some.
      split; simpl; auto.
      apply option_fapp_is_some.
      split; simpl; auto.
    }
    apply exists_some_iff_is_some in TargetWord.
    destruct TargetWord as [w H_w].
    unfold transition.
    unfold ref_code_iso.
    simpl.
    apply refinement_pref_transition_equiv in Step.
    destruct Step as [b [q'' [w_a [HRb [Step_b [Run_w_a Hw_a]]]]]].
    apply refinement_pref_transition_equiv in Step_b.
    destruct Step_b as [c [q''' [w_b [HRc [Step_c [Run_w_b Hw_b]]]]]].
    assert (is_some (R^* w_b)) as is_some_Rw_b. {
      unshelve eassert (is_some (R^* (total_code S (exist _ c _ )))).
      simpl.
      rewrite <-HRc. simpl. auto.
      apply S_range.
      unfold total_code in H.
      simpl in H.
      rewrite <-HRc in H.
      rewrite kleisli_ext_app in H.
      apply option_fapp_is_some in H.
      apply proj2 in H.
      rewrite kleisli_ext_app in H.
      apply option_fapp_is_some in H.
      apply proj2 in H.
      assumption.
    }
    apply exists_some_iff_is_some in is_some_Rw_b.
    destruct is_some_Rw_b as [Rw_b EqRw_b].
    assert (compose_code R S c = Some ((Ru ++ rs_w q_u_v) ++ [a] ++ (w_a ++ Rw_b))) as Eq_RSc. {
      rewrite <-compose_code_comm_proj.
      unfold compose_codemap.
      rewrite <-HRc.
      rewrite kleisli_ext_app.
      rewrite EqRu.
      rewrite kleisli_ext_app.
      simpl.
      rewrite <-HRb.
      rewrite app_nil_r.
      rewrite EqRw_b.
      unfold option_fapp.
      repeat (progress rewrite <-app_assoc).
      reflexivity.
    }
    copy_hyp Step_c ExTargetState.
    rewrite <-(proj1 H_iso) in ExTargetState.
    rewrite <-(proj2 H_iso) in Eq_RSc.
    unshelve apply (@refinement_forward_closure A C (compose_code R S) M q_Ruv a c q''' (w_a ++ Rw_b) Eq_RSc) in ExTargetState.
    destruct ExTargetState as [q_Ruv' [Step_a' [TailCase1 TailCase2]]].

    exists q_Ruv'.
    split.
    * destruct (w_a ++ Rw_b); simpl_impl.
      + rewrite app_nil_r in *.
        right.
        exists c.
        split; [|split]; auto.
        rewrite ->(proj1 H_iso).
        rewrite ->TailCase2.
        simpl.
        apply Step_c.
        rewrite ->TailCase2.
        simpl.
        reflexivity.
      + left.
        destruct TailCase1.
        split; auto.
    * apply exists_some_iff_is_some in Have_Ru'.
      destruct Have_Ru' as [Ru' EqRu'].
      destruct (list_empty_or_not w_b) as [|E_w_b];
        [subst; inversion EqRw_b
        | assert (isNonEmpty Rw_b) as E_Rw_b; [eapply kleisli_ext_preserves_nonempty; eauto; fail|]
        ];
        destruct (list_empty_or_not w_a) as [|E_w_a];
        subst; simpl in *; simpl_impl;
        try rewrite app_nil_r in *.
      (* rewrite ->EqRu'. *)
      (* apply klesli_ext_preserves_nonempty *)
      (* first case: *)
      + inversion Run_w_b.
        inversion Run_w_a.
        subst.
        simpl in *. subst.
        inversion EqRu'. subst.
        simpl_impl. subst.
        simpl.
        auto.
      + apply nonempty_iff_not_nil in E_w_a.
        rewrite_premise TailCase1; [|apply E_w_a].
        rewrite_premise Hw_a; [|apply E_w_a].
        rewrite <-(proj1 Hw_a).
        rewrite ->EqRu.
        split.
        ++ rewrite ->(proj1 TailCase1).
          rewrite (proj1 H_iso).
           f_equal.
        ++ rewrite ->(proj2 TailCase1).
          rewrite <-(proj2 Hw_a).
          rewrite ->(proj2 H_iso).
          rewrite <-app_assoc.
          reflexivity.
      + apply nonempty_iff_not_nil in E_w_b.
        rewrite_premise Hw_b; [|apply E_w_b].
        apply nonempty_iff_not_nil in E_Rw_b.
        rewrite_premise TailCase1; [|apply E_Rw_b].
        inversion Run_w_a.
        subst.
        simpl.
        rewrite <-(proj2 Hw_b).
        rewrite kleisli_ext_app.
        rewrite ->EqRu.
        simpl.
        rewrite <-HRb.
        unfold option_fapp.
        split.
        ++ rewrite (proj1 TailCase1).
           rewrite <-(proj1 Hw_b).
           apply (proj1 H_iso).
        ++ rewrite app_nil_r.
           rewrite app_nil_r.
           rewrite (proj2 TailCase1).
           rewrite (proj2 H_iso).
           rewrite <-app_assoc.
           reflexivity.
      + apply nonempty_iff_not_nil in E_w_a.
        apply nonempty_iff_not_nil in E_w_b.
        apply nonempty_iff_not_nil in E_Rw_b.
        rewrite_premise Hw_a; [|apply E_w_a].
        rewrite_premise Hw_b; [|apply E_w_b].
        assert (w_a ++ Rw_b <> []). {
          intro Contr.
          apply app_nil in Contr.
          destruct Contr.
          auto.
        }
        rewrite_premise TailCase1; [|assumption; fail].
        rewrite <-(proj1 Hw_a).
        rewrite ->EqRu.
        rewrite ->(proj1 TailCase1).
        rewrite ->(proj2 TailCase1).
        rewrite ->(proj1 H_iso).
        rewrite ->(proj2 H_iso).
        rewrite <-(proj2 Hw_a).
        rewrite <-app_assoc.
        split;auto.
Qed.

Lemma kleisli_ext_cons_reflection {A B: Type} (R: Code A B)
  (b: B) (bs: list B) (a: A) (suffix_a: list A):
  R^* (b :: bs) = Some (a :: suffix_a)
  -> exists rest: list A, R b = Some (a :: rest)
      /\ Some (@app A rest) <*> (R^* bs) = Some suffix_a.
Proof.
  simpl.
  destruct (R b) as [R_b|] eqn: EqRb; try discriminate.
  destruct (R^* bs) as [R_bs|] eqn: EqRbs; try discriminate.
  simpl.
  intro.
  destruct R_b as [|a' rest].
  * exfalso.
    destruct R.
    simpl in *.
    apply c in EqRb. assumption.
  * exists rest.
    simpl in H.
    inversion H.
    subst.
    split; simpl; auto.
Qed.

Lemma kleisli_ext_letter_find {A B: Type} (R: Code A B)
  (b: B) (bs: list B) (prefix: list A) (a: A) (suffix: list A):
  R^* (b :: bs) = Some (prefix ++ a :: suffix)
  -> (exists rest: list A, R b = Some (prefix ++ a :: rest)
      /\ Some (@app A rest) <*> (R^* bs) = Some suffix)
   \/ (exists prefix': list A,
       Some (@app A) <*> R b <*> Some prefix' = Some prefix
      /\ (R^* bs) = Some (prefix' ++ a :: suffix)).
Proof.
  intro H.
  simpl in H.
  destruct (R b) as [R_b|] eqn: EqRb; try discriminate.
  destruct (R^* bs) as [R_bs|] eqn: EqRbs; try discriminate.
  simpl in H.
  inversion H.
  apply app_eq_app_disjoint in H1.
  destruct H1 as [mid Comp].
  destruct Comp; [left|right].
  - (* R_b contains the a (because 'mid' is nonempty)*)
    destruct H0.
    destruct mid as [|a' rest]; simpl_impl.
    destruct H1.
    simpl in H2.
    inversion H2.
    replace a' with a in *.
    exists rest.
    split.
    * f_equal. auto.
    * unfold option_fapp. auto.
  - exists mid.
    destruct H0.
    split.
    * unfold option_fapp. f_equal. auto.
    * f_equal. auto.
Qed.


Theorem kleisli_ext_app_reflection {A B: Type} (R: Code A B)
  (bs: list B) (prefix_a: list A) (a: A) (suffix_a: list A):
  R^* bs = Some (prefix_a ++ [a] ++ suffix_a)
  -> exists prefix_b: list B, exists b: B, exists suffix_b: list B,
    exists mid1: list A, exists mid2: list A,
      bs = prefix_b ++ [b] ++ suffix_b
      /\ Some (@app A) <*> (R^* prefix_b) <*> Some mid1 = Some prefix_a
      /\ R b = Some (mid1 ++ [a] ++ mid2)
      /\ Some (@app A) <*> Some mid2 <*> (R^* suffix_b) = Some suffix_a.
Proof.
  revert prefix_a.
  revert a.
  revert suffix_a.
  induction bs as [|b bs]; intros.
  - exfalso.
    simpl in H.
    inversion H.
    eapply app_cons_not_nil.
    eassumption.
  - apply kleisli_ext_letter_find in H.
    destruct H.
    * destruct H as [rest [? ?]].
      exists []. exists b. exists bs.
      exists prefix_a. exists rest.
      repeat (progress split); simpl; auto.
    * destruct H as [prefix' [? ?]].
      simpl in IHbs.
      apply IHbs in H0.
      clear IHbs.
      destruct H0 as [prefix_b [b' [suffix_b [mid1 [mid2 P]]]]].
      exists (b::prefix_b). exists b'. exists suffix_b.
      exists mid1. exists mid2.
      destruct P.
      destruct H1.
      destruct H2.
      repeat (progress split).
      + simpl. f_equal. assumption.
      + simpl.
        unfold option_fapp.
        destruct (R b) as [R_b|]; [|discriminate].
        destruct (R^* prefix_b) as [R_prefix_b|]; [|discriminate].
        simpl.
        f_equal.
        unfold option_fapp in *.
        inversion H1.
        rewrite <-app_assoc.
        rewrite ->H5.
        inversion H.
        auto.
      + simpl. auto.
      + assumption.
Qed.


Lemma rs_w_does_not_start_with_codeword {A B: Type} (R: Code A B)
  {M: LTS B} (y: RefinedStates (R:=R) (M:=M)) :
  does_not_start_with_codeword (R:=R) (rs_w y).
Proof.
  intros.
  intros b Contr.
  destruct R as [R R_not_empty R_prefix_free].
  simpl in *.
  destruct (R b) as [R_b|] eqn: EqRb; inversion_clear Contr.
  subst.
  destruct (rs_prop y) as [P|P].
  +++ rewrite P in H. inversion H. subst.
      eapply R_not_empty. eassumption.
  +++ destruct P as [b' [_ P]].
      unfold below_code in P.
      destruct (R b') as [R_b'|] eqn: EqRb'; try contradiction.
      destruct P.
      assert (b = b'). {
        apply R_prefix_free.
        rewrite -> EqRb.
        rewrite -> EqRb'.
        constructor.
        eapply prefix_of_transitive; eassumption.
      }
      assert (R_b = R_b'). {
        subst.
        rewrite EqRb in EqRb'.
        inversion EqRb'. auto.
      }
      subst.
      apply H0.
      apply prefix_of_antisymmetric; assumption.
Qed.

(** The second direction: **)
Theorem refinement_preserves_code_composition_backward_sim {A B C: Type}
  (R: Code A B) (S: Code B C) (M: LTS C) :
    step_closed _ _ (converse (ref_code_iso R S M)).
Proof.
  intros q_Ruv q_Ruv' q_u_v a Iso Step_a.
  unfold converse in Iso.
  unfold ref_code_iso in Iso.
  simpl in Iso.
  destruct ((R^*) (rs_w (rs_q q_u_v))) as [Ru|] eqn: EqRu; try contradiction.
  apply refinement_pref_transition_equiv in Step_a.
  destruct Step_a as [c [q'' [w [EqRSc [Step_c [Run_w Prop_w]]]]]].
  assert (compose_code R S c = compose_codemap R S c). {
    (* why can't I rewrite directly in EqRSc? *)
    rewrite <-compose_code_comm_proj.
    reflexivity.
  }
  rewrite H in EqRSc; clear H.
  unfold compose_codemap in EqRSc.
  destruct (S c) as [S_c|] eqn: Eq_S_c; try discriminate.
  rewrite (proj2 Iso) in EqRSc.
  rewrite <-app_assoc in EqRSc.
  assert (prefix_of (rs_w (rs_q q_u_v)) S_c). {
    apply code_kleisli_ext_prefix_reflection with (R:=R).
    * destruct R. assumption.
    * destruct R. assumption.
    * rewrite EqRu.
      rewrite <-EqRSc.
      constructor.
      apply prefix_of_app.
      eexists. eauto.
  }
  apply prefix_of_app in H.
  destruct H as [rest_b ?].
  rewrite <-H in EqRSc.
  rewrite kleisli_ext_app in EqRSc.
  rewrite EqRu in EqRSc.
  destruct (R^* rest_b) as [R_rest_b|] eqn: Eq_R_rest_b; try discriminate.
  unfold option_fapp in EqRSc.
  inversion EqRSc; clear EqRSc.
  apply app_strip_common_prefix in H1.
  destruct rest_b as [|b rest_b']. {
    simpl in Eq_R_rest_b.
    inversion Eq_R_rest_b.
    subst.
    exfalso.
    eapply app_cons_not_nil.
    eassumption.
  }
  subst S_c.
  rewrite (proj1 Iso) in Step_c.
  eapply (refinement_forward_closure S) in Step_c as Step_b; try (simpl; eassumption).
  destruct Step_b as [q_u' [Step_b [If_b_mid If_b_end]]].
  simpl in Eq_R_rest_b.
  destruct (R b) as [R_b|] eqn: EqRb; try discriminate.
  destruct (R^* rest_b') as [R_rest_b'|] eqn: EqR_rest_b'; try discriminate.
  simpl in Eq_R_rest_b.
  inv_clear Eq_R_rest_b.
  subst R_rest_b.
  assert (exists l, R_b = rs_w q_u_v ++ [a] ++ l /\ w = l ++ R_rest_b'). {
    replace (rs_w q_u_v ++ a :: w)
              with ((rs_w q_u_v ++ [a]) ++ w) in H0;
      [|rewrite <-app_assoc; simpl; auto; fail].
    symmetry in H0.
    apply app_eq_app_disjoint in H0.
    destruct H0 as [l].
    destruct H; destruct H; simpl in H.
    ** (* contradiction, because H0 entails that
          rs_w q_u_v has R_b as a prefix.  *)
       exfalso. destruct H0.
       destruct (list_extract_last l); try contradiction.
       destruct H2.
       destruct H2.
       subst.
       rewrite ->app_assoc in H0.
       apply app_inj_tail in H0.
       apply proj1 in H0.
       clear H.
       assert (prefix_of R_b (rs_w q_u_v)). {
         apply prefix_of_app.
         eexists. eauto.
       }
       destruct (rs_prop q_u_v).
       ++ rewrite H1 in H. inversion H.
          destruct R as [R R_ne ?].
          apply R_ne with (b:=b).
          rewrite H2.
          simpl in EqRb.
          auto.
       ++ destruct H1. destruct H1.
          unfold below_code in H2.
          destruct (R x1) eqn: EqRx1; try contradiction.
          assert (b = x1). {
            destruct R as [R' R_ne R_pref].
            apply R_pref.
            simpl in EqRb.
            rewrite EqRb.
            simpl in EqRx1.
            rewrite EqRx1.
            constructor.
            eapply prefix_of_transitive.
            eassumption.
            destruct H2. auto.
          }
          subst x1.
          rewrite EqRb in EqRx1.
          inversion EqRx1.
          subst l.
          assert (rs_w q_u_v = R_b). {
            destruct H2.
            apply prefix_of_antisymmetric; try assumption.
          }
          destruct H2.
          contradiction.
    ** exists l. rewrite app_assoc. split; auto.
  }
  destruct H as [rest_a [? ?]].
  subst R_b.
  eapply (refinement_forward_closure R) in Step_b as Step_a; try eassumption.
  destruct Step_a as [q_u_v' [Step_a [If_a_mid If_a_end]]].

  exists q_u_v'. split; try assumption.
  unfold converse.
  unfold ref_code_iso.
  simpl.
  destruct (list_eq_nil_tnd rest_a);
    [subst; simpl_impl; rewrite If_a_end; simpl
    |rewrite_premise If_a_mid; [|assumption];
     rewrite (proj1 If_a_mid);
     rewrite (proj2 If_a_mid)
    ];
  (destruct (list_eq_nil_tnd rest_b');
    [subst; simpl_impl; try rewrite If_b_end; simpl
    |rewrite_premise If_b_mid; [|assumption]]).
  - simpl in EqR_rest_b'.
    inversion EqR_rest_b'.
    subst.
    simpl in Run_w.
    inversion Run_w.
    simpl.
    auto.
  - rewrite (proj2 If_b_mid).
    rewrite kleisli_ext_app.
    rewrite EqRu.
    simpl.
    rewrite EqRb.
    repeat rewrite app_nil_r.
    unfold option_fapp.
    simpl in Prop_w.
    rewrite_premise Prop_w; revgoals. {
      eapply kleisli_ext_preserves_neq_nil; eauto.
    }
    rewrite <-(proj1 Prop_w).
    rewrite <-(proj2 Prop_w).
    rewrite (proj2 Iso).
    rewrite (proj1 If_b_mid).
    repeat rewrite <-app_assoc.
    repeat rewrite app_nil_r.
    split; auto.
    apply (proj1 Iso).
  - rewrite EqRu.
    rewrite_premise Prop_w; revgoals. {
      destruct rest_a; try contradiction.
      simpl. discriminate.
    }
    rewrite <-(proj1 Prop_w).
    rewrite <-(proj2 Prop_w).
    rewrite ->(proj1 Iso).
    rewrite ->(proj2 Iso).
    rewrite <-app_assoc.
    split; auto.
  - clear If_a_end.
    clear If_b_end.
    rewrite EqRu.
    assert (w <> []). {
      destruct rest_a.
      contradiction.
      simpl in H1.
      subst. discriminate.
    }
    rewrite_premise Prop_w; [|assumption].
    rewrite <-(proj1 Prop_w).
    rewrite <-(proj2 Prop_w).
    rewrite <-(proj1 Iso).
    rewrite ->(proj2 Iso).
    rewrite <-app_assoc.
    split; auto.
Qed.

(** * Main Theorem **)
(** Bringing it all together:**)
Theorem refinement_preserves_code_composition {A B C: Type}
  (R: Code A B) (S: Code B C) (M: LTS C) :
  (forall c: dom S, is_some (R^* (total_code S c))) ->
  refinement R (refinement S M)
          ≅
  refinement (compose_code R S) M.
Proof.
  intro S_range.
  apply Build_Isomorphism with (rel:=ref_code_iso R S M).
  - cbv. auto.
  - apply (refinement_preserves_code_composition_forward_sim R S M S_range).
  - clear S_range. (* not yet needed for this direction *)
    apply (refinement_preserves_code_composition_backward_sim R S M).
  - intros x y1 y2 Eq1 Eq2.
    unfold ref_code_iso in *.
    simpl in *.
    destruct (R^* (rs_w (rs_q x))); try contradiction.
    destruct Eq1.
    destruct Eq2.
    destruct y1. destruct y2.
    simpl in *. subst.
    apply rs_equal; simpl; auto.
  - intros x y1 y2 Eq1 Eq2.
    unfold converse in *.
    unfold ref_code_iso in *.
    simpl in *.
    destruct (R^* (rs_w (rs_q y1))) eqn: EqY1; try contradiction.
    destruct (R^* (rs_w (rs_q y2))) eqn: EqY2; try contradiction.
    destruct Eq1.
    destruct Eq2.
    assert (rs_q y1 = rs_q y2). {
      apply rs_equal.
      rewrite <-H. rewrite <-H1.
      reflexivity.
      eapply kleisli_ext_injective_with_suffix with (R:=R).
      + apply (rs_w_does_not_start_with_codeword R y1).
      + apply (rs_w_does_not_start_with_codeword R y2).
      + eassumption.
      + eassumption.
      + rewrite H0 in H2.
        assumption.
    }
    apply rs_equal.
    * assumption.
    * rewrite H3 in EqY1.
      rewrite EqY2 in EqY1.
      inversion EqY1.
      subst.
      rewrite H0 in H2.
      eapply app_strip_common_prefix.
      eassumption.
Qed.
