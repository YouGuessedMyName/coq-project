Require Export LTS.
Require Import Lists.List.
Require Export CodeMap.
Require Export Contraction.
Require Export ACUtil.
Require Export Coq.Init.Specif.
Require Export Coq.Init.Logic.
Require Export Coq.Logic.ProofIrrelevance.
Require Export Decidable.
Require Export Coq.Relations.Relation_Definitions.

Import ListNotations.

(** * Definitions **)
(** ** Concretization Operator **)

(** For one of the directions of the Galois connection, we need an
 oracle that decides if a given [w : list A] is the prefix of
 any [R b]. **)
Definition CodeMapInverseDecidable {A B: Type} (R: CodeMap A B) :=
  (forall w: list A, decidable (code_has_run R w)).

(** In the concretization of an LTS [M], the 'normal' states will be of this shape:
 They are tuples of a state of M together with a word [list A], which grows along
 the transitions. As soon as the word is known to the code [R], an actual
 transition of the underlying LTS [M] is performed. Thus,
 the accumulated word are proper prefixes of words known to the code [R]: **)
Structure PrefixedState {A B: Type} {R: CodeMap A B} {M: LTS B} : Type
  := mk_ps {
    ps_state : states M;
    ps_prefix : list A;
    ps_prop : ps_prefix = [] \/ exists b: B, below_code ps_prefix (R b);
    }.

(** The following projection drops the property of a [PrefixedState] **)
Definition ps_proj {A B: Type} {R: CodeMap A B} {M: LTS B} :
  PrefixedState (R:=R) -> states M * list A
  := fun qw => (ps_state qw, ps_prefix qw).

Notation "'Concretized' ( q , w )" := (mk_ps _ _ _ _ q w _)
                                    (at level 40) : type_scope.

Definition nil_state {A B: Type} {R: CodeMap A B} {M: LTS B} (q: states M): option (@PrefixedState A B R M).
  unshelve eapply (Some (Concretized (q, []))).
  left. reflexivity.
Defined.

(** ** Transitions **)

(** The transition relation can be defined "bottom up" via inductive
 rules or equivalently "top down" as a predicate using match-clauses.
 Let's start with the rules:
**)
Inductive ConcrTransInd {A B: Type} {R: CodeMap A B}
  {same_input: relation A} {M: LTS B} :
  option (states M * list A) -> A -> option (states M * list A) -> Prop
  :=
  (** We can always accumulating prefix if the involed states exist: **)
  | RuleMid : forall
              (q: states M) (w: list A) (a: A),
           (* ------------------------------------------------ *)
              ConcrTransInd (Some (q,w)) a (Some (q,w ++ [a]))

  (** As soon as the prefix becomes R b, we take the corresponding
      transition in M:
   **)
  | RuleEnd : forall
              (q q': states M) (w: list A) (a: A) (b: B),
              (q --b--> q')  ->  R b = Some (w ++ [a]) ->
           (* --------------------------------------------- *)
              ConcrTransInd (Some (q,w)) a (Some (q',[]))

  (** If the accumulated prefix is not below of any defined code word,
      we go to the chaos state:
   **)
  | RuleToChaos : forall
              (q: states M) (w: list A) (a: A),
              (forall (b: B) (u: list A) (a': A), same_input a a' ->
                    R b <> Some (w ++ [a'] ++ u)) ->
           (* --------------------------------------------- *)
              ConcrTransInd (Some (q,w)) a None
  (** Once on the chaos state, we allow any action:
   **)
  | RuleOnChaos : forall (a: A),
           (* ------------------------- *)
              ConcrTransInd None a None
.

(** The above inductive rules are equivalent to the following explicitly defined
    match-clause: **)

Definition ConcrTransCompact {A B: Type} {R: CodeMap A B}
  {same_input: relation A} {M: LTS B} :
  option (@PrefixedState A B R M) -> A -> option (@PrefixedState A B R M) -> Prop
  := fun qw a qw' =>
        match qw with
        | Some qw => let (q,w) := ps_proj qw in
            match qw' with
            | Some qw' => let (q',w') := ps_proj qw' in
                  (* transitions between ordinary states: *)
                  match w' with
                  | [] => (* completing the high-level transition: *)
                      exists b: B, (q --b--> q') /\ R b = Some (w ++ [a])
                  | _ => (* accumulating prefix: *)
                      (q = q' /\ w ++ [a] = w')
                  end
            | None =>
                  (* transition from ordinary to chaos state: *)
                  (* we have a transition if the action code R *)
                  (* does not have any transition for the input-part of `a` *)
                   forall (b: B) (a': A) (u: list A),
                   same_input a a' ->
                   R b <> Some (w ++ [a'] ++ u)
            end
        | None => qw' = None
        end.

Lemma ConcrTrans_equivalent {A B: Type} {R: CodeMap A B}
  {same_input: relation A} {M: LTS B} :
  forall (qw qw': option PrefixedState) (a: A),
    ConcrTransCompact (R:=R) (same_input:=same_input) qw a qw'
                      <->
    ConcrTransInd (R:=R) (same_input:=same_input)
      (option_map (fun qw => (ps_state qw, ps_prefix qw)) qw) a (option_map (fun qw' => (ps_state qw', ps_prefix (M:=M) qw')) qw').
Proof.
  split.
  - intros H.
    destruct qw; destruct qw'; revgoals; simpl in H.
    * constructor.
    * discriminate.
    * constructor. simpl. auto.
    * simpl. destruct (list_extract_last (ps_prefix p0)) as [Eq|Eq]; try rewrite ->Eq in *.
      + simpl. autodestruct. econstructor; eassumption.
      + autodestruct. rewrite H0.
        destruct (ps_prefix p0) eqn: eqPrefP0. {
          exfalso. eapply app_cons_not_nil; eauto.
        }
        rewrite ->H0 in *.
        autodestruct.
        rewrite <- H.
        rewrite <- H1.
        constructor.
  - intros H; inversion H; subst;
      destruct qw; destruct qw'; try discriminate.
    * simpl in *.
      inversion H1; inversion H3; subst.
      destruct (ps_prefix p ++ [a]) eqn: Eq. {
        exfalso.
        eapply app_cons_not_nil.
        eauto.
      }
      autosplit; eauto.
    * simpl in *.
      inversion H0. inversion H1. subst.
      exists b. split; eauto.
    * simpl. inversion H0. subst w. simpl in *.
      eauto.
    * constructor.
Qed.

(** The actual definition of the [concretization] operator: **)

Definition concretization {A B: Type} (same_input: A -> A -> Prop) (R: CodeMap A B) (M: LTS B) : LTS A
  := {|
    states := option (@PrefixedState A B R M);
    initial := nil_state (initial M);
    transition := @ConcrTransCompact A B R same_input M;
  |}.

(** For the equality of states, we disregard the [ps_prop], using [proof_irrelevance],
 so two prefixed states are equal iff the have the same [ps_state] and [ps_prefix]
 components. **)
Lemma ps_equal {A B: Type} {R: CodeMap A B} {M: LTS B} {t t': @PrefixedState A B R M}:
  (ps_proj t = ps_proj t') -> t = t'.
Proof.
  intros.
  destruct t.
  destruct t'.
  unfold ps_proj in H.
  simpl in *.
  inversion H.
  subst.
  f_equal; apply proof_irrelevance.
Qed.

(** ** Completeness of Codes

 We have two notions that capture that a code has "enough"
 transitions compared to a system [M: LTS A].

 **)

Definition output_enabled {A B: Type}
  (R: CodeMap A B) (same_input: A->A->Prop) (M: LTS A) : Prop
  := forall (w: list A) (i: A) (io: A),
    code_has_run R (w ++ [i])
    -> LTS_uses_action M io
    -> same_input io i
    -> code_has_run R (w ++ [io]).

(** For the identity relation, every code satisfies this property
    for every LTS: **)
Example idRel_output_enabled {A B: Type} (R: CodeMap A B) (M: LTS A) :
  output_enabled R idRel M.
Proof.
  unfold_goal.
  intros. unfold idRel in *. subst io.
  assumption.
Qed.

(**
 The second notion is the history dependent variant of the first notion:
**)
Definition icomplete {A B: Type}
  (R: CodeMap A B) (same_input: A->A->Prop) (M: LTS A) : Prop
  := forall (q: states M) (w: list B) (R_w u: list A) (a a': A),
    (R^* w = Some R_w)
    -> (initial M ==(R_w ++ u)==> q)
    -> code_has_run R (u ++ [a])
    -> (exists q': states M, (q -- a' --> q'))
    ->  same_input a' a
    -> code_has_run R (u ++ [a']).

(** Again, the identity relation makes all codes satisfy this
 property for all LTSs: **)
Example idRel_icomplete {A B: Type} (R: CodeMap A B) (M: LTS A) :
  icomplete R idRel M.
Proof.
  unfold_goal.
  intros. unfold idRel in *. subst a'.
  assumption.
Qed.

(** The history-dependent notionis implied by the stateless notion: **)
Lemma output_enabled_implies_icomplete {A B: Type}
  (R: CodeMap A B) (same_input: A->A->Prop) (M: LTS A):
  output_enabled R same_input M
  -> icomplete R same_input M.
Proof.
  intros R_output_enabled_for_M.
  intros q w *. intros.
  eapply R_output_enabled_for_M; eauto.
  exists q. auto.
Qed.
(** The implication in the converse direction does not hold,
a counter example can be found in the example section further below **)


(** * Technical Lemmas

We first establish a series of lemmas to reason about states and
transitions in the contraction.
 **)
Lemma concretization_prefix_not_full
  {A B: Type} {R: Code A B} {M: LTS B} (qw: @PrefixedState A B R M)
  (b: B):
  R b <> Some (ps_prefix qw).
Proof.
  destruct R as [R R_ne R_pf].
  simpl.
  intro Contr.
  destruct (ps_prop qw).
  * apply (R_ne b).
    simpl in *.
    rewrite ->H in Contr.
    auto.
  * destruct H as [b' ?].
    unfold below_code in H.
    simpl in H.
    destruct (R b') as [R_b'|] eqn: EqRb'; try contradiction.
    destruct H.
    assert (b = b'). {
      apply R_pf.
      rewrite -> EqRb'.
      rewrite -> Contr.
      constructor.
      assumption.
    }
    subst.
    rewrite Contr in EqRb'.
    injection EqRb' as EqRb'.
    subst.
    contradiction.
Qed.

Lemma only_valid_state_can_reach_valid_state
  {A B: Type} {R: CodeMap A B} {M: LTS B}
  (rel: A -> A -> Prop) (q q': states (concretization rel R M))
  (u: list A):
  (q == u ==> q') -> is_some q' -> is_some q.
Proof.
  revert q q'.
  induction u; intros.
  - inversion H; subst. auto.
  - inversion H; subst.
    assert (is_some q_a). {
      eapply IHu; eauto.
    }
    destruct q_a; try contradiction.
    destruct q; simpl in H4; try discriminate.
    auto.
Qed.

Lemma concretization_path_reflection {A B: Type} {R: CodeMap A B} {M: LTS B}
  (rel: A -> A -> Prop) (w: list A) (qv qv': PrefixedState):
  (concretization rel R M |- Some qv ==w==> Some qv')
  -> exists u: list B, match (R^* u) with
                 | Some R_u => ps_prefix qv ++ w = R_u ++ ps_prefix qv'
                 | None => False
                 end.
Proof.
  revert qv qv'.
  induction w; intros qv qv' run; inversion run; subst.
  - exists nil. simpl. rewrite app_nil_r. auto.
  - assert (is_some q_a). {
      eapply only_valid_state_can_reach_valid_state; eauto.
      simpl. auto.
    }
    destruct q_a as [q_a|]; [|contradiction]. clear H.
    apply IHw in H4.
    destruct H4 as [u ?].
    simpl in H2.
    necessarily_some (R^* u) R_u.
    destruct (ps_prefix q_a) eqn: EqPref_q_a in H2.
    * destruct H2 as [b [? ?]].
      exists (b::u).
      simpl.
      rewrite H1.
      rewrite Eq_R_u.
      simpl.
      rewrite EqPref_q_a in H.
      simpl in H.
      rewrite H.
      repeat rewrite <-app_assoc.
      simpl. auto.
    * exists u. rewrite Eq_R_u.
      destruct H2.
      rewrite <-EqPref_q_a in H1.
      rewrite <-H.
      rewrite <-H1.
      rewrite <-app_assoc. simpl. auto.
Qed.

Lemma concretization_transition_within_code
  {A B: Type} {R: Code A B} {M: LTS B}
  {rel: A -> A -> Prop} {qw qw': PrefixedState}
  {a:  A} (b: B):
  below_code (ps_prefix qw ++ [a]) (R b) ->
  (concretization rel R M |- Some qw --a--> Some qw') ->
  (ps_prefix qw ++ [a] = ps_prefix qw' /\ ps_state qw = ps_state qw').
Proof.
  intro H.
  unfold below_code in H.
  destruct (R b) as [R_b|] eqn: EqRb; try contradiction.
  destruct H.
  intro Step_a.
  simpl in Step_a.
  destruct qw' as [q' w' H_w'].
  simpl in *.
  destruct w'. {
    (* first case is contradictory *)
    destruct Step_a as [b' [? ?]].
    replace b with b' in *.
    + rewrite -> H2 in EqRb.
      injection EqRb as EqRb.
      contradiction.
    + destruct R as [R R_ne R_pf].
      simpl in *.
      apply R_pf.
      rewrite -> H2.
      rewrite -> EqRb.
      constructor.
      assumption.
  }
  destruct Step_a.
  split; auto.
Qed.


Lemma list_eq_app_nil {A: Type} {l u: list A} :
  l = l ++ u <-> u = nil.
Proof.
  split; intro H. induction l. simpl in *. auto.
  apply IHl.
  simpl in H.
  injection H as H.
  rewrite <-H. auto.
  rewrite H. rewrite app_nil_r. auto.
Qed.

Lemma concretization_transition_below_code
  {A B: Type} {R: Code A B} {M: LTS B}
  (rel: A -> A -> Prop) (qw: PrefixedState)
  (b: B) (a: A):
     below_code (ps_prefix qw ++ [a]) (R b)
     -> exists qw': PrefixedState,
       ps_state qw = ps_state qw'
       /\ ps_prefix qw ++ [a] = ps_prefix qw'
       /\ (concretization rel R M |- Some qw --a--> Some qw').
Proof.
  intro H.
  necessarily_some (R b) R_b.
  unshelve eexists (Concretized (ps_state qw, (ps_prefix qw ++ [a]))).
  right.
  destruct R as [R ? ?].
  exists b. rewrite Eq_R_b. assumption.
  autosplit. simpl.
  case_match. {
    apply app_eq_nil in Heql.
    destruct Heql. discriminate.
  }
  autosplit.
Qed.


Lemma concretization_transition_in_code
  {A B: Type} {R: Code A B} {M: LTS B}
  (rel: A -> A -> Prop) (qw: PrefixedState) (st: option PrefixedState)
  (u: list A) (b: B)
  (rel_reflexive: reflexive _ rel)
  :
  R b = Some (ps_prefix qw ++ u) -> (
      (concretization rel R M |- Some qw ==u==> st)
                         <->
     (match st with
      | None => False
      | Some qw' => (ps_state qw --b--> ps_state qw') /\ ps_prefix qw' = []
      end)
  ).
Proof.
  destruct (list_extract_last u). {
    (* the first case u = [] is contradictory *)
    subst. rewrite app_nil_r.
    intros.
    apply concretization_prefix_not_full in H.
    contradiction.
  }
  destruct H as [u' [a ?]].
  subst u.
  revert qw a.
  rename u' into u.
  induction u; intros qw a_last EqRb; split; intros Hyp; simpl in *.
  - apply gtrans_singleton in Hyp.
    necessarily_some st qw'. {
      eapply Hyp.
      apply rel_reflexive.
      eassumption.
    }
    simpl in Hyp.
    case_eq (ps_prefix qw'); intros * EqPref; revgoals. {
      exfalso.
      pattern (ps_prefix qw') at 1 in Hyp.
      rewrite -> EqPref in Hyp at 1.
      rewrite -> (proj2 Hyp) in EqRb.
      eapply concretization_prefix_not_full.
      eassumption.
    }
    rewrite EqPref in Hyp.
    autosplit; auto.
    destruct Hyp as [b' [? ?]].
    assert (b = b'). {
      apply (proj_code_prefix_free R).
      rewrite -> H0.
      rewrite -> EqRb.
      constructor.
      apply prefix_of_reflexive.
    }
    subst. auto.
  - necessarily_some st qw'.
    apply gtrans_singleton.
    simpl.
    simpl in EqRb.
    destruct Hyp.
    rewrite H0.
    exists b. split; auto.
  - inversion Hyp. subst.
    destruct q_a as [q_a|]; revgoals. {
      exfalso.
      unfold transition in H2.
      simpl in H2.
      eapply H2.
      apply rel_reflexive.
      eassumption.
    }
    pose (H_q_a := H2).
    eapply concretization_transition_within_code with (b:=b) in H_q_a.
    destruct H_q_a.
    simpl in H2.
    destruct (ps_prefix q_a) eqn: Eq_q_a in H2 at 1. {
      exfalso.
      rewrite -> Eq_q_a in H.
      destruct (ps_prefix qw); simpl in H; discriminate.
    }
    clear Eq_q_a.
    rewrite -> H0.
    eapply IHu.
    rewrite <- H. rewrite <- app_assoc.
    simpl. eassumption.
    assumption.
    unfold_goal.
    rewrite -> EqRb.
    replace (a :: u ++ [a_last]) with ([a] ++ (u ++ [a_last])).
    split.
    rewrite app_assoc.
    rewrite list_eq_app_nil.
    intro Contr.
    eapply app_cons_not_nil; eauto.
    apply prefix_of_app. exists (u++[a_last]).
    rewrite <-app_assoc. auto.
    auto.
  - epose (qwa := concretization_transition_below_code rel qw b a).
    rewrite_premise qwa.
    destruct qwa as [qwa [? [? ?]]].
    econstructor; eauto.
    apply IHu.
    rewrite <- H0. rewrite <- app_assoc. auto.
    rewrite <- H. auto.
    apply below_code_app_nonempty.
    sig_exists (u ++ [a_last]).
    * apply app_cons_nonempty.
    * rewrite EqRb.
      repeat (progress simpl || rewrite <- app_assoc).
      auto.
Qed.

Lemma concretization_path_in_code
  {A B: Type} {R: Code A B} {M: LTS B}
  (rel: A -> A -> Prop) (q: states M) (st: option PrefixedState)
  (u: list A) (b: list B)
  (rel_reflexive: reflexive _ rel)
  :
  R^* b = Some u -> (
      (concretization rel R M |- nil_state q ==u==> st)
                         <->
     (match st with
      | None => False
      | Some qw' => (q ==b==> ps_state qw') /\ ps_prefix qw' = []
      end)
  ).
Proof.
  revert q u.
  induction b as [|b bs]; intros q u EqR;
    [simpl in EqR; inversion EqR; subst|];
    split; intro Hyp.
  - inversion Hyp. simpl. autosplit.
  - necessarily_some st qw'.
    destruct_conjunctions.
    eassert (nil_state q = Some qw'). {
      unfold nil_state.
      f_equal.
      eapply ps_equal.
      unfold ps_proj.
      inversion H.
      subst.
      simpl.
      rewrite H0.
      auto.
    }
    rewrite H1.
    autosplit.
  - simpl in EqR.
    necessarily_some (R b) R_b.
    necessarily_some (R^* bs) R_bs.
    simpl in EqR.
    injection EqR as EqR.
    subst u.
    apply path_app_rev in Hyp.
    destruct Hyp as [p [? Run_bs]].
    unfold nil_state in H.
    eapply concretization_transition_in_code in H; eauto.
    necessarily_some p pw.
    eassert (Some pw = nil_state (ps_state pw)). {
      unfold nil_state.
      f_equal.
      apply ps_equal.
      unfold ps_proj.
      rewrite (proj2 H).
      simpl. auto.
    }
    rewrite H0 in Run_bs.
    eapply IHbs in Run_bs; auto.
    necessarily_some st qw'.
    destruct_conjunctions.
    simpl in H.
    autosplit; auto.
    econstructor; eauto.
  - simpl in EqR.
    necessarily_some (R b) R_b.
    necessarily_some (R^* bs) R_bs.
    simpl in EqR.
    injection EqR as EqR.
    subst u.
    necessarily_some st qw'.
    destruct_conjunctions.
    inversion H. subst.
    eapply path_app.
    * eapply concretization_transition_in_code with (st:=nil_state q_a); try eassumption.
      unfold nil_state.
      simpl.
      autosplit. auto.
    * eapply IHbs; auto.
Qed.


Lemma concretization_inspect_run_below_code {A B: Type} (R: Code A B)
     (same_input: A -> A -> Prop)
     (M: LTS B) (q: PrefixedState) (q': states (concretization same_input R M))
     (b: B)
     (u: list A) :
  (reflexive _ same_input)
    -> below_code (ps_prefix q ++ u) (R b)
    -> (concretization same_input R M |- Some q ==u==> q')
    -> match q' with
      | Some q' => ps_state q' = ps_state q /\ ps_prefix q' = ps_prefix q ++ u
      | None => False
      end.
Proof.
  intro si_refl.
  revert q.
  induction u; intros * Pref Run_u; inversion Run_u; subst.
  - simpl. auto. rewrite app_nil_r.
    autosplit.
  - destruct q_a as [q_a|].
    * unfold transition in H2.
      simpl in H2.
      destruct (ps_prefix q_a) eqn: EqPref.
      + destruct H2 as [b' [? ?]].
        necessarily_some (R b) Rb.
        destruct Pref.
        apply prefix_of_app in H2.
        destruct H2 as [l ?].
        subst Rb.
        assert (b' = b). {
          apply (proj_code_prefix_free R).
          rewrite H0.
          rewrite Eq_Rb.
          constructor.
          apply prefix_of_app.
          exists (u ++ l).
          repeat rewrite <- app_assoc.
          simpl.
          auto.
        }
        subst b'.
        rewrite H0 in Eq_Rb.
        injection Eq_Rb as Eq_Rb.
        rewrite <- app_assoc in Eq_Rb.
        apply app_strip_common_prefix in Eq_Rb.
        simpl in Eq_Rb.
        injection Eq_Rb as Eq_Rb.
        symmetry in Eq_Rb.
        apply app_eq_nil in Eq_Rb.
        destruct_conjunctions.
        subst u l.
        rewrite app_nil_r in *.
        contradiction.
      + rewrite <-EqPref in *.
        apply IHu in H4.
        destruct q' as [q'|]; [|contradiction].
        destruct_conjunctions.
        autosplit.
        rewrite H1. auto.
        rewrite H0. rewrite <-H2.
        rewrite <-app_assoc. auto.
        destruct_conjunctions.
        rewrite <-H0. rewrite <-app_assoc. simpl. auto.
   * exfalso.
     unfold transition in H2. simpl in H2.
     unfold below_code in Pref.
     necessarily_some (R b) Rb.
     destruct Pref as [? Pref].
     apply prefix_of_app in Pref.
     destruct Pref as [l ?].
     rewrite <-app_assoc in H0.
     symmetry in H0.
     subst Rb.
     eapply H2 with (u := u ++ l); eauto.
Qed.

Lemma icomplete_for_concretization {A B: Type} (R: Code A B)
     (same_input: A -> A -> Prop)
     (M: LTS B) :
     (reflexive _ same_input) ->
    icomplete R same_input (concretization same_input R M).
Proof.
  intros si_refl.
  intros ? ? ? ? ? ?.
  intros Eq_Rw Run_Rw_u Run_Rua Step_a' si_a'_a.
  apply path_app_rev in Run_Rw_u.
  destruct Run_Rw_u as [q0 [Run_Rw Run_u]].
  eapply concretization_path_in_code in Run_Rw; eauto.
  destruct q0 as [q0|]; [|contradiction].
  destruct Step_a' as [q' ?].
  destruct Run_Rua as [b ?].
  necessarily_some (R b) Rb. simpl in H0.
  eapply concretization_inspect_run_below_code in Run_u; eauto; revgoals. {
    apply prefix_of_app in H0. destruct H0 as [l ?].
    rewrite <-app_assoc in *.
    unfold_goal.
    rewrite -> Eq_Rb.
    destruct_conjunctions.
    rewrite H2 in *.
    rewrite <- H0.
    simpl.
    autosplit.
    * intro Contr. apply app_yields_prefix in Contr.
      discriminate.
    * apply prefix_of_app. clear. eexists. eauto.
  }
  destruct q as [q|]; [|contradiction].
  destruct_conjunctions.
  unshelve eassert (q0 = Concretized (ps_state q, [])); try (left; reflexivity). {
    apply ps_equal.
    unfold ps_proj.
    f_equal; simpl; auto.
  }
  rewrite H5 in *. simpl in H3, H4, H2. clear H2 H3 H5.
  destruct q' as [q'|].
  - simpl in H.
    destruct (ps_prefix q') eqn: EqPref'.
    * destruct H as [b' [_ Eq_Rb']].
      exists b'.
      rewrite Eq_Rb'. simpl. rewrite H4.
      apply prefix_of_reflexive.
    * rewrite <-EqPref' in *.
      destruct (ps_prop q') as [|[b' ?]]. {
        exfalso.
        rewrite EqPref' in *.
        discriminate.
      }
      exists b'.
      necessarily_some (R b') (Rb').
      simpl in H2. simpl.
      destruct_conjunctions.
      subst u.
      rewrite H5.
      auto.
  - exfalso.
    apply prefix_of_app in H0.
    destruct H0 as [l ?].
    subst Rb.
    rewrite <-app_assoc in *.
    simpl in H.
    simpl in Eq_Rb.
    subst u.
    eapply H with (b:=b) (a':=a); eauto.
Qed.

(** * The Galois-Connection **)
(** In the forward-direction of the Galois connection, we use
 the left-completeness of [R], but almost don't need any axioms of [Code], we
 only need it in the contradictory case.
 **)

Lemma concretization_galois_forward {A B: Type} (R: Code A B)
     (same_input: A->A->Prop) (N: LTS A) (M: LTS B) :
  icomplete R same_input N ->
  reflexive _ same_input ->
  CodeMapInverseDecidable R ->
  Simulation (contraction R N) M
             ->
  Simulation N (concretization same_input R M).
Proof.
  intros R_icomplete si_refl R_inv S.
  pose (T := fun (q: states N) (pw: states (concretization same_input R M)) =>
            match pw with
            | Some pw =>
                  let (p,w) := ps_proj pw in
                  exists q0: states N,  (N |- q0 ==w==> q) /\ S q0 p
            | None =>
                  (* all states p' are related to the chaos state *)
                  True
            end
      ).
  apply Build_PathSimulation with (rel:=T).
  *** unfold_goal.
      eexists; split. econstructor.
      apply (proj_sim_initial S).
  *** intros anch q q' pw a Reach_q Reach_pw T_q_pw Step_a.
      destruct pw as [pw|];
      simpl in T_q_pw; revgoals.
      - (* chaos state *)
        exists None.
        split; auto.
        unfold_goal.
        auto.
      - destruct pw as [p w Prop_w].
        simpl in T_q_pw.
        destruct T_q_pw as [q0 [Run_w S_q_p]].
        destruct (R_inv (w ++ [a])) as [ExRb|ExRb].
        * (* if w ++ [a] is a prefix of some (R b) *)
          destruct ExRb as [b Pref_b].
          destruct (R b) as [R_b|] eqn: EqRb; try contradiction.
          simpl in Pref_b.
          apply prefix_of_app in Pref_b.
          destruct Pref_b as [u].
          destruct (list_eq_nil_tnd u).
          ** subst. (* if R b = w ++ [a] *)
             rewrite app_nil_r in *.
             assert (contraction R N |- q0 --b--> q') as Step_b. {
               unfold_goal. rewrite ->EqRb.
               eapply path_app. eassumption.
               apply gtrans_singleton. eassumption.
             }
             eapply (proj_sim_step S) in Step_b; try eassumption.
             destruct Step_b as [p' [? ?]].
             exists (nil_state p'); split; simpl.
             exists b; split; assumption.
             exists q'; split; try assumption.
             constructor.
          ** unshelve eexists (Some (Concretized (p,w ++ [a]))); try split.
             + right. exists b. unfold_goal. rewrite ->EqRb.
               split.
               rewrite <-H.
               rewrite list_eq_app_nil. auto.
               apply prefix_of_app. exists u. rewrite H. reflexivity.
             + simpl.
               destruct (w ++ [a]) eqn: Eq at 1. {
                 destruct w; simpl in *; discriminate.
               }
               clear Eq.
               split; reflexivity.
             + simpl. exists q0. split.
               eapply path_app; try eassumption.
               apply gtrans_singleton. assumption.
               assumption.
        * (* w ++ [a] is not a prefix of any (R b) *)
          (* then, we need to show that there isn't any related
             a' such that w ++ [a'] is in the code *)
          (* Here, the relation is relevant! *)
          exists None. split; simpl; auto.
          clear  S T S_q_p.
          (* we need to show that w ++ [a] is really not in R *)
          intros b a' u Rel_a_a' Contr.
          apply ExRb.
          assert (code_has_run R (w ++ [a'])) as R_run_wa'. {
            exists b. rewrite Contr. simpl.
            apply prefix_of_app. eexists. rewrite <-app_assoc. simpl. auto.
          }
          apply concretization_path_reflection in Reach_pw.
          destruct Reach_pw as [v ?].
          necessarily_some (R^* v) R_v.
          simpl in H.
          subst anch.
          eapply R_icomplete; eauto.
Qed.

(** In the backwards-direction, we only need that the [same_input] relation
 is reflexive, but we don't need any left-completeness: **)

Lemma concretization_galois_backward {A B: Type}
     (R: Code A B) (same_input: A -> A -> Prop)
     (N: LTS A) (M: LTS B) :
  reflexive _ same_input ->
  Simulation N (concretization same_input R M)
             ->
  Simulation (contraction R N) M.
Proof.
  intros si_refl S.
  pose (T := fun (q: states (contraction R N)) (p: states M) =>
         S q (nil_state p)).
  apply Build_Simulation with (rel:=T).
  +++ unfold_goal.
      unfold T.
      replace (nil_state (initial M)) with (initial (concretization idRel R M));
         try (simpl; auto; apply (proj_sim_initial S)).
  +++ intros q q' p b T_q_p Step_b.
      unfold transition in Step_b.
      simpl in Step_b.
      necessarily_some (R b) R_b.
      unfold T in T_q_p.
      apply (step_closed_sequence _ _ S (proj_sim_step S)
               _ _ _ R_b  T_q_p) in Step_b.
      destruct Step_b as [pw' [Step_R_b S_q'_pw']].
      unfold nil_state in Step_R_b.
      eapply concretization_transition_in_code with (b:=b) in Step_R_b.
      * necessarily_some pw' p'_w'.
        simpl in Step_R_b.
        destruct Step_R_b.
        exists (ps_state p'_w').
        split; auto.
        unfold_goal.
        replace (nil_state (ps_state p'_w')) with (Some p'_w'); auto.
        unfold nil_state.
        f_equal.
        apply ps_equal.
        unfold ps_proj.
        rewrite ->H0. simpl. auto.
      * assumption.
      * simpl. assumption.
Qed.

(** The two directions above combine into the following equivalence: **)

Theorem concretization_galois_connection {A B: Type} (R: Code A B)
     (same_input: A -> A -> Prop)
     (M: LTS A) (N: LTS B) :
      reflexive _ same_input ->
      icomplete R same_input M ->
      CodeMapInverseDecidable R -> (
            (contraction R M) ⊑ N
                      <->
        M ⊑ (concretization same_input R N)
  ).
Proof.
  intros si_refl si_complete ?.
  split; intro Premise; destruct Premise as [S]; constructor.
  * eapply concretization_galois_forward; eauto.
  * eapply concretization_galois_backward; eauto.
Qed.

(** For plain LTSs and simply the identity relation [idRel], the assumptions
 on the relations are always fulfilled and thus disappear: **)

Corollary concretization_galois_connection_lts {A B: Type} (R: Code A B)
     (M: LTS A) (N: LTS B) :
      CodeMapInverseDecidable R -> (
            (contraction R M) ⊑ N
                      <->
        M ⊑ (concretization idRel R N)
  ).
Proof.
  intros ?.
  apply concretization_galois_connection;
    auto;
    try apply idRel_icomplete;
    try apply idRel_reflexive.
Qed.

(** If the code map is defined for all labels in in the high-level LTS,
 then we even have a Galois insertion. That is, contraction is left-inverse
 to concretization: **)

Theorem concretization_galois_insertion {A B: Type} (R: Code A B)
     (rel: relation A) (M: LTS B) :
  reflexive _ rel ->
  (forall b: B, LTS_uses_action M b -> is_some (R b)) ->
  M ≅ contraction R (concretization rel R M).
Proof.
  intros si_refl R_total.
  pose (iso := fun (q: states M) (p: states (contraction R (concretization rel R M)))
       => match p with
        | Some p => (q, []) = ps_proj p
        | None => False
        end).
  apply (Build_Isomorphism _ _ iso).
  * autosplit.
  * intros q q' p b iso_q_p Step_b.
    exists (nil_state q').
    split; [|autosplit].
    necessarily_some (R b) Rb. {
      pose (C := R_total b).
      rewrite_premise C.
      rewrite Eq_Rb in C.
      contradiction.
      eexists. eexists. eauto.
    }
    simpl.
    rewrite Eq_Rb.
    destruct p as [p|]; [|contradiction].
    simpl in iso_q_p.
    unfold ps_proj in iso_q_p.
    inversion iso_q_p.
    eapply concretization_transition_in_code; eauto.
    rewrite <- H1. simpl. eauto.
    rewrite <- H0.
    simpl.
    autosplit. auto.
  * intros q q' p b iso_q_p Step_b.
    cbv in iso_q_p.
    destruct q as [q|]; [|contradiction].
    inversion iso_q_p.
    destruct q as [q_ w prop_q] eqn: Eq_q.
    subst q_. subst w.
    simpl in Step_b.
    necessarily_some (R b) Rb.
    eapply concretization_transition_in_code in Step_b; eauto.
    necessarily_some q' q''.
    destruct Step_b.
    exists (ps_state q'').
    split; auto.
    destruct q''. simpl.
    cbv.
    simpl in H0. subst. auto.
  * intros ? *. intros.
    unfold iso in *.
    destruct y1; destruct y2; try contradiction.
    f_equal. apply ps_equal. rewrite <-H. rewrite <-H0. auto.
  * intros ? *. intros.
    unfold converse in *.
    unfold iso in *.
    destruct x; try contradiction.
    rewrite <-H in H0.
    inversion H0. subst. auto.
Qed.

(** * Preservation Properties **)

(** As a corollary of the Galois connection, we have that the concretization operator is monotone: **)

Corollary concretization_monotone {A B: Type} (R: Code A B)
                                  (rel: relation A)
     (M N: LTS B) :
  (reflexive _ rel) ->
  CodeMapInverseDecidable R ->
  Simulation M N ->
  Simulation (concretization rel R M) (concretization rel R N).
Proof with eauto.
  intros.
  eapply concretization_galois_forward...
  - apply icomplete_for_concretization...
  - eapply simulation_compose...
    eapply concretization_galois_backward...
    apply simulation_id.
Qed.

(** This is just a lemma for two symmetric cases in the preservation of determinism: **)

Lemma concretization_always_same_transition_type {A B: Type} (R: Code A B)
     (rel: relation A) (M: LTS B)
     (q: states (concretization rel R M))
     (a: A) (q': PrefixedState) :
  reflexive _ rel ->
  (concretization rel R M |- q --a--> Some q') ->
  (concretization rel R M |- q --a--> None) ->
  False.
Proof.
  intros si_refl step_some step_none.
  apply ConcrTrans_equivalent in step_some.
  apply ConcrTrans_equivalent in step_none.
  destruct q; simpl in *.
  - inversion step_some; subst.
    * destruct (ps_prop q') as [P_q'|P_q'].
      + rewrite P_q' in H4.
        eapply app_cons_not_nil.
        eauto.
      + autodestruct.
        necessarily_some (R x) Rx.
        simpl in H0.
        inversion step_none; subst.
        autodestruct.
        eapply prefix_of_app in H1.
        autodestruct.
        eapply H5; eauto.
        rewrite app_assoc.
        rewrite H4.
        rewrite Eq_Rx.
        rewrite H1.
        auto.
    * inversion step_none; subst.
      eapply H2; eauto.
      rewrite app_nil_r. eauto.
  - inversion step_some.
Qed.

(** If M is a deterministic LTS, then so is [concretization rel R M], in for
    arbitrary relations. (Note that rel is not used in the notion of determinism).
 **)

Proposition concretization_preserves_determinism {A B: Type} (R: Code A B)
     (rel: relation A) (M: LTS B) :
  reflexive _ rel ->
  M is deterministic ->
  (concretization rel R M) is deterministic.
Proof.
  intros si_refl M_det.
  intros q q1 q2 a a' step1 step2 Eq_a.
  subst a'.
  split; auto.
  destruct q1 as [q1|]; destruct q2 as [q2|].
  - apply ConcrTrans_equivalent in step1.
    apply ConcrTrans_equivalent in step2.
    destruct q as [q|]; inversion step1; inversion step2; subst.
    * f_equal. apply ps_equal; unfold ps_proj.
      rewrite <- H. rewrite <- H4. rewrite <- H8. rewrite <- H9. auto.
    * exfalso.
      rewrite H4 in H10.
      eapply concretization_prefix_not_full; eauto.
    * exfalso.
      rewrite H11 in H5.
      eapply concretization_prefix_not_full; eauto.
    * f_equal. apply ps_equal; unfold ps_proj.
      assert (b = b0 /\ ps_state q1 = ps_state q2). {
        eapply M_det; eauto.
        eapply proj_code_prefix_free.
        rewrite H5.
        rewrite H12.
        constructor.
        apply prefix_of_reflexive.
      }
      destruct q1; destruct q2. autodestruct. simpl in *. subst. auto.
  - exfalso. eapply concretization_always_same_transition_type; eassumption.
  - exfalso. eapply concretization_always_same_transition_type; eassumption.
  - auto.
Qed.


(** * Examples / Counterexamples **)

(** In the following, we provide a few examples which distinguish
    properties. We show that the converse implication of
    [output_enabled_implies_icomplete] does not hold: there
    is an example LTS / Mealy machine M and an action code R
    (together with the usual same-input-relation) such that:
    R is [icomplete] for M but R is not [output_enabled] for M.
 **)
(** The example models simple boolean operations 'toggle'
   and 'echo'/'identity': **)
Module BooleanActionMachine.
  (** In the concrete machine a first transition determins the
    operation of choice -- without any output yet.
    Then in a second transition, the parameter to the operation
    is provided as input, and the machine produces the computed
    output and returns to the initial state, waiting for the next
    operation.
   **)
  Inductive ConcreteInput : Type :=
    | OpToggle : ConcreteInput
    | OpEcho : ConcreteInput
    | Data : bool -> ConcreteInput.
  Definition A := ConcreteInput * option bool.
  Inductive ConcreteStates := AskOperation | StateToggle | StateEcho.
  Inductive ConcreteTransitions :
    ConcreteStates -> A -> ConcreteStates -> Prop :=
    | T1 : ConcreteTransitions AskOperation (OpToggle, None) StateToggle
    | T2 : ConcreteTransitions AskOperation (OpEcho, None) StateEcho
    | T3 : forall b: bool, ConcreteTransitions StateToggle (Data b, Some (negb b)) AskOperation
    | T4 : forall b: bool, ConcreteTransitions StateEcho (Data b, Some b) AskOperation
    .
    Definition M : LTS A := {|
        states := ConcreteStates;
        initial := AskOperation;
        transition := ConcreteTransitions;
      |}.
    (** In the action code, we flatten this structure,
     such that the user/environment provides the operation
     and the parameter in a single run, resulting in an
     immediate output:
     **)
    Inductive BigStep :=
      | Toggle : bool -> BigStep
      | Echo : bool -> BigStep.
    Definition B := BigStep.
    (** The following action code resolves bigstep to their
    low-level operation sequence. This CodeMap is even total: **)
    Definition R_total : B -> list A := fun b =>
      match b with
      | Toggle b => [(OpToggle, None); (Data b, Some (negb b))]
      | Echo b => [(OpEcho, None); (Data b, Some b)]
      end.
    Definition R : Code A B.
    Proof.
      eapply (Build_Code _ _ (fun f=> (Some (R_total f)))).
      - intro b. destruct b; unfold R_total; intros; discriminate.
      - intros op op' Pref.
          destruct op as [b|b];
          destruct op' as [b'|b'];
          inversion Pref as [? ? Pref'];
          eapply prefix_of_app in Pref';
          destruct Pref' as [diff Eq];
          simpl in Eq; try discriminate;
          injection Eq as Eq; subst b'; try reflexivity.
    Defined.

    Definition SameInp : A -> A -> Prop := fun '(i1,_) '(i2,_) => i1=i2.
    Theorem R_not_output_enabled :
      ~ output_enabled R SameInp M.
    Proof.
      epose (r := [(OpEcho, None)]).
      epose (i1 := (Data true, Some true)).
      epose (i2 := (Data true, Some false)).
      assert (code_has_run R (r ++ [i1])). {
        exists (Echo true).
        simpl. apply prefix_of_app. eexists. simpl. eauto.
      }
      assert (LTS_uses_action M i2). {
        exists StateToggle. exists AskOperation.
        constructor.
      }
      assert (~ code_has_run R (r ++ [i2])) as no_run. {
        intro Contr.
        destruct Contr as [b ?].
        simpl in *.
        apply prefix_of_app in H1.
        destruct H1 as [u].
        subst i2.
        destruct b; simpl in H1.
        discriminate.
        inversion H1.
        discriminate.
      }
      intro R_output_enabled.
      apply no_run.
      eapply R_output_enabled; eauto; reflexivity.
    Qed.


    Theorem R_icomplete :
      icomplete R SameInp M.
    Proof.
      intros q w Rw u i1 i2 EqRw.
      intros run_Rw_u R_has_run Mht si.
      destruct Mht as [q' Step_i2].
      apply path_app_rev in run_Rw_u.
      destruct run_Rw_u as [q0 [run_Rw run_u]].
      pose (R_run := R_has_run).
      destruct R_run as [b R_run].
      simpl in R_run.
      apply prefix_of_app in R_run.
      destruct R_run as [l R_run].
      rewrite <- app_assoc in R_run.
      assert (List.In i1 (R_total b)) as Def_i1. {
        rewrite <- R_run.
        apply in_elt.
      }
      destruct i2 as [i2 o2].
      apply app_eq_fixed_list in R_run.
      destruct b;
      simpl in R_run;
      repeat (autodestruct_once || destruct_sum); subst i1; simpl in si; subst i2; try subst x;
      inversion Step_i2;
      inversion run_u; subst.
      * inversion H8; subst.
        exists (Toggle b). simpl. apply prefix_of_reflexive.
      * inversion H8; subst. inversion H6.
      * exists (Toggle b). simpl. apply prefix_of_app.
        eexists. simpl. eauto.
      * inversion H8. subst. inversion H6.
      * exists (Echo b). simpl. apply prefix_of_reflexive.
      * exists (Echo b); simpl; apply prefix_of_app; eexists; simpl; eauto.
  Qed.
End BooleanActionMachine.


(** The second example LTS shows that [concretization] does not commute
    with the composition of action codes ([compose_code]). **)
Module CompositionFailure.
(** To this end, we use the [SingletonLTS] consisting of one state
 and no transitions and the following action labels and codes. **)
(** The involved action label sets are all singleton: **)
Inductive A := a.
Inductive B := b.
Inductive C := c.

Definition R_map : CodeMap A B :=
  fun must_be_i_b => Some [a; a].
Example R : Code A B.
Proof.
  apply (Build_Code _ _ R_map).
  - intros ? ?. discriminate.
  - intros b b' H. destruct b; destruct b'. auto.
Defined.

Definition S := EmptyCode B C.

(** We can show directly that no isomorphism exists. For the proof,
 it may help to look at the visualizations in the paper.
 **)

Theorem contraction_does_not_preserve_code_composition :
  (* The existence of an isomorphism ... *)
  ((concretization idRel (compose_code R S) SingletonLTS)
       ≅
     (concretization idRel R (concretization idRel S SingletonLTS))
  (* ... leads to a contradiction: *)
  ) -> False.
Proof.
  intros Iso.
  assert (forall (A: Type), reflexive A idRel) as i_r. {
    intro. apply idRel_reflexive.
  }
  (* First, introduce shorter names for the two resulting systems in LTS(A):*)
  pose (M := SingletonLTS : LTS C).
  (* g is for γ, gR=γ_R, gS=γS, gRS=γ_(R*S)  *)
  pose (gRS_M := concretization idRel (compose_code R S) M).
  pose (gS_M := concretization idRel S M).
  pose (gR_gS_M := concretization idRel R gS_M).
  assert (gRS_M |- initial gRS_M ==[a;a]==> None) as To_sink. {
    constructor 2 with (q_a := None).
    - simpl.
      intros.
      unfold compose_codemap.
      intros. discriminate.
    - apply gtrans_singleton. simpl.
      auto.
  }
  pose (sink_gS_M := None : states gS_M).
  assert (gR_gS_M |- initial gR_gS_M ==[a;a]==> nil_state sink_gS_M) as To_valid. {
    eapply concretization_transition_in_code with (b:=b); auto.
    simpl.
    autosplit.
    intros.
    intro. discriminate.
  }
  assert (gR_gS_M is deterministic) as gR_gS_M_det. {
    apply concretization_preserves_determinism; auto.
    apply concretization_preserves_determinism; auto.
    unfold_goal. intros.
    destruct q1; destruct q2.
    autosplit; auto.
  }
  pose (fake_sink := nil_state sink_gS_M: states gR_gS_M).
  assert (Iso None fake_sink) as IsoSink. {
    apply step_closed_sequence with (rel:=Iso) (p:=initial gR_gS_M) in To_sink;
      try (destruct Iso; auto; fail).
    destruct To_sink as [p' [? ?]].
    assert (p' = (nil_state sink_gS_M)). {
      eapply (deterministic_sequence gR_gS_M_det) in H.
      ++ destruct H. eauto.
      ++ eauto.
      ++ apply list_rel_lift_id. reflexivity.
    }
    subst.
    auto.
  }
  (* the real sink has a self-loop: *)
  assert (gRS_M |- None --a--> None) as SinkLoop. {
    simpl. auto.
  }
  (* None and fake_sink were shown to be isomorphic: *)
  assert (gR_gS_M |- fake_sink --a--> fake_sink) as ContradictionLoop. {
    destruct Iso as [Iso ? StepClosed ? l_uniq ?].
    simpl in IsoSink.
    eapply StepClosed in SinkLoop; eauto.
    destruct SinkLoop as [q [Trans]].
    replace q with fake_sink in *.
    apply Trans.
    eapply l_uniq; eauto.
  }
  (* But actually, fake_sink=(sink,epsilon) does not have a self-loop: *)
  inversion ContradictionLoop. autodestruct.
Qed.

End CompositionFailure.
