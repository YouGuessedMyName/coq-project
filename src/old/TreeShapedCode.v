Require Export LTS.
Require Import Lists.List.
Require Export CodeMap.
Require Export ACUtil.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.Decidable.
Require Export Coq.Logic.ProofIrrelevance.

Import ListNotations.

(** * Preliminary Definitions **)
(** The following type expresses a run by explicitly mentioning the used
    intermediate states and actions. Since we want to distinguish
    different runs between the same states, [Run] is a [Type] and
    not just [Prop] (With [Prop], all runs would collapse by proof irrelevance).
 **)
Inductive Run {A: Type} {M: LTS A} : states M -> states M -> Type :=
  | RunNil : forall q q': states M, (q = q') -> Run q q'
  | RunSnoc : forall (q q' q'': states M) (a: A),
      Run q q' -> (M |- q' --a--> q'') -> Run q q''.

Definition RunNil' {A: Type} {M: LTS A} (q: states M):
  Run q q.
Proof.
  constructor. auto.
Defined.

(** We can project away all the states and then yield a list of action labels: **)
Definition proj_run_actions {A: Type} {M: LTS A} {q q': states M}
  (r: Run q q'): list A.
Proof.
  induction r.
  - exact [].
  - exact (IHr ++ [a]).
Defined.

Lemma proj_run_actions_correct {A: Type} {M: LTS A} (q q': states M) (r: Run q q'):
  (M |- q == (proj_run_actions r) ==> q').
Proof.
  induction r; simpl.
  - subst.
    constructor.
  - eapply path_app; eauto. apply gtrans_singleton. auto.
Qed.

Proposition exists_run {A: Type} {M: LTS A}
  (q q': states M) (w: list A):
  (M |- q == w ==> q')
    -> exists r: Run q q', proj_run_actions r = w.
Proof.
  revert q q'.
  induction w as [|a ?] using rev_ind; intros q q' Hyp.
  - inversion Hyp. subst q0. subst q'.
    exists (RunNil' q).
    simpl. auto.
  - apply path_app_rev in Hyp.
    destruct Hyp as [p [R_w R_x]].
    apply gtrans_singleton in R_x.
    apply IHw in R_w.
    destruct R_w as [r Eq_r].
    unshelve eexists (RunSnoc q p q' a _ _); try eassumption.
    simpl.
    rewrite Eq_r.
    reflexivity.
Qed.

(** An LTS is tree shaped if each state is reached from the initial
    state by a unique run. We split this into being [Reachable], which
    is a [Type], and the uniqueness, which is a [Prop]. We need the
    reachability to be a type, because otherwise, we can't extract
    the witness in [RunTree] later. **)
Definition Reachable {A: Type} (M: LTS A) : Type :=
  forall (q: states M), Run (initial M) q.

Definition UniquelyReachable {A: Type} (M: LTS A) : Prop :=
  forall (q: states M) (r1 r2: Run (initial M) q), r1 = r2.

(** A leaf in a (usually tree shaped) LTS is a state that can't do
    any transition. **)
Definition Leaf {A: Type} {M: LTS A} (q: states M) : Prop :=
  ~ exists a: A, exists q': states M, (q -- a --> q').

Example InfiniteChainLTS_has_no_leaves {A: Type} (a: A):
  forall q: states (InfiniteChainLTS a), ~ (Leaf q).
Proof.
  intros q isLeaf.
  apply isLeaf.
  exists a. exists (S q).
  simpl. split; auto.
Qed.

Definition NonRootLeaves {A: Type} (M: LTS A) : Type :=
  { q: states M | Leaf q /\ q <> initial M }.

Definition proj_nonrootleaves {A: Type} {M: LTS A} :
  NonRootLeaves M -> states M.
Proof.
  intros x.
  destruct x.
  assumption.
Defined.

Coercion proj_nonrootleaves : NonRootLeaves >-> states.

(** An LTS is grounded if every state has a path to a leaf:
 **)
Definition Grounded {A: Type} (M: LTS A) : Prop :=
  forall (q: states M), exists q': states M, Leaf q' /\ inhabited (Run q q').

(**
    Here, it is important that we allow arbitrary [Leaf] instead of
    restricting to [NonRootLeaves], because otherwise, the LTS
    with only one state would not be grounded:
 **)
Example SingletonLTS_is_grounded {A: Type} :
  Grounded (A:=A) SingletonLTS.
Proof.
  intros q.
  simpl in *.
  exists q; split; simpl.
  - intro.
    autodestruct.
  - constructor. constructor; auto.
Qed.


(** The infinite chain example however is not grounded: **)
Example InfiniteChainLTS_is_not_grounded {A: Type} (a: A):
  ~ Grounded (InfiniteChainLTS a).
Proof.
  intro Contr.
  destruct (Contr 0).
  autodestruct.
  eapply InfiniteChainLTS_has_no_leaves.
  eauto.
Qed.

Lemma hd_rel_left_unique_on_trees  {A: Type} (M N: LTS A) :
  N is deterministic ->
  UniquelyReachable M ->
  left_unique (history_dependent_subrel
                 (fun (q: states M) (p: states N) => True)).
Proof.
  intros N_det Uniq_M x y1 y2 Hxy1 Hxy2.
  unfold history_dependent_subrel in *.
  destruct Hxy1 as [w [Hxw [Hy1w _]]].
  destruct Hxy2 as [w' [Hxw' [Hy2w _]]].
  assert (w = w'). {
    apply exists_run in Hxw.
    apply exists_run in Hxw'.
    destruct Hxw as [r1].
    destruct Hxw' as [r2].
    assert (r1 = r2). {
      apply Uniq_M.
    }
    subst r2.
    rewrite H in H0.
    auto.
  }
  subst w'.
  eapply deterministic_sequence; eauto.
  apply list_rel_lift_id. reflexivity.
Qed.

Theorem tree_isomorphism_if_same_traces {A: Type} (M N: LTS A) :
  M is deterministic ->
  N is deterministic ->
  UniquelyReachable M ->
  UniquelyReachable N ->
  Same_set _ (traces M) (traces N) ->
  M ≅ N.
Proof.
  intros M_det N_det Uniq_M Uniq_N TraceEquiv.
  pose (S := fun (q: states M) (p: states N) => True).
  apply Build_PathIsomorphism with (rel := S);
    unfold S; clear S.
  - unfold_goal. auto.
  - destruct TraceEquiv.
    apply trace_inclusion_yields_step_closed; auto.
  - destruct TraceEquiv.
    apply trace_inclusion_yields_step_closed; auto.
  - apply hd_rel_left_unique_on_trees; auto.
  - unfold right_unique. unfold converse.
    pose (T := fun (q: states N) (p: states M) => True).
    assert (left_unique (history_dependent_subrel T)) as Flipped. {
      apply hd_rel_left_unique_on_trees; auto.
    }
    unfold left_unique in *.
    intros. eapply Flipped.
    all: unfold history_dependent_subrel in *.
    all: autodestruct.
    eexists; eauto.
    eexists; eauto.
Qed.

(** * Definition of Tree-Shaped Action Code **)
(** to make the use of the projections easier, we have A and B
as implicit parameters: **)
Record TreeShapedCode' {A B: Type} := {
    tsc_lts :> LTS' (Alphabet:=A);
    tsc_det : (tsc_lts is deterministic) ;
    (** The fact that we are tree-shaped is split into
     being reachable (a [Type]) and having unique
     runs (a [Prop]): **)
    tsc_run : Reachable tsc_lts;
    tsc_uniq_run : UniquelyReachable tsc_lts;
    tsc_label : NonRootLeaves tsc_lts -> B;
    tsc_injective_label : Injective tsc_label;
  }.

(** We now make A and B explicit for nicer statements: **)
Definition TreeShapedCode (A B: Type) :=
  TreeShapedCode' (A:=A) (B:=B).

Definition TreeRepresentsMap {A B: Type}
   (M: TreeShapedCode A B) (f: B -> option (list A)) : Prop
   := forall (b: B) (w: list A),
       f b = Some w
            <->
       (exists q: NonRootLeaves M, (M |- initial M == w ==> q)
                             /\ tsc_label M q = b).
(** * From Tree-Shaped Codes to Map-Based Codes **)

(** ** Uniqueness **)
(** We can directly start with proving uniqueness:
    For a fixed tree-shaped code M, there is at most
    one [CodeMap] satisfying [TreeRepresentsMap]:
    **)
Lemma TreeDefinesMapUniquely
  {A B: Type} (M: TreeShapedCode A B)
  (f g : CodeMap A B):
      TreeRepresentsMap M f ->
      TreeRepresentsMap M g ->
      (forall b: B, f b = g b).
Proof.
  intros H_f H_g b.
  destruct (f b) eqn: Eq_f_b.
  - apply H_f in Eq_f_b.
    apply H_g in Eq_f_b.
    auto.
  - destruct (g b) eqn: Eq_g_b.
    * apply H_g in Eq_g_b.
      apply H_f in Eq_g_b.
      rewrite Eq_g_b in Eq_f_b.
      discriminate.
    * trivial.
Qed.

(** ** Existence **)
(** So the rest of this section is concerned with proving existence. **)

(** In the direction from tree-shaped to partial map, we require that
    for each b in B, we have a decision procedure telling us
    whether the is a leaf labelled b. **)
(** The [DecisionProc] type corresponds to [decidable], but is a type
 and so has extractable witnesses: **)
Definition DecisionProc (P: Type) := sumor P (P -> False).
Definition TreeShapeTND {A B: Type} (M: TreeShapedCode A B) :=
  forall b: B, DecisionProc ({ l: NonRootLeaves M | tsc_label M l = b}).
Definition RunTree {A B: Type} (M: TreeShapedCode A B) :
  TreeShapeTND M -> (B -> option (list A)).
Proof.
  intros tnd b.
  destruct (tnd b).
  - apply Some.
    destruct s as [l ?].
    exact (proj_run_actions (tsc_run M l)).
  - exact None.
Defined.

Proposition RunTree_is_ne_word {A B: Type} (M: TreeShapedCode A B)
  (tnd: TreeShapeTND M):
  code_ne_word (RunTree M tnd).
Proof.
  intros b Contr.
  unfold RunTree in Contr.
  destruct (tnd b); try discriminate.
  destruct s as [l ?].
  injection Contr as Contr.
  assert (initial M == [] ==> l) as Run. {
    rewrite <- Contr.
    apply proj_run_actions_correct.
  }
  inversion Run; subst.
  destruct l. simpl in H0. subst x. autodestruct.
Qed.

Lemma TreeToMap {A B: Type} (M: TreeShapedCode A B)
  (tnd: TreeShapeTND M) :
  TreeRepresentsMap M (RunTree M tnd).
Proof.
  intros b w.
  split.
  - intro EqRunTree.
    unfold RunTree in EqRunTree.
    destruct (tnd b).
    * destruct s as [l Eq_l].
      exists l.
      autodestruct.
      subst w.
      split; auto.
      eapply proj_run_actions_correct.
    * discriminate.
  - intro Ex_q.
    destruct Ex_q as [q [Run_w l_q_is_b]].
    unfold RunTree.
    destruct (tnd b).
    * destruct s as [l Eq_l].
      f_equal.
      simpl.
      assert (q = l). {
        apply (tsc_injective_label M).
        subst b. auto.
      }
      subst q.
      apply exists_run in Run_w.
      destruct Run_w as [r Eq_r].
      assert (r = tsc_run M l). {
        apply tsc_uniq_run.
      }
      subst r.
      assumption.
    * exfalso.
      apply f.
      econstructor.
      eassumption.
Qed.

Lemma sig_proof_irrelevance {X:Type} {P:X -> Prop}
  (x1 x2: {x: X|P x}):
  proj1_sig x1 = proj1_sig x2 -> x1 = x2.
Proof.
  destruct x1. destruct x2.
  simpl. intro Hyp.
  subst x0.
  f_equal.
  apply proof_irrelevance.
Qed.

Proposition RunTree_is_prefix_free {A B: Type} (M: TreeShapedCode A B)
  (tnd: TreeShapeTND M):
  prefix_free (RunTree M tnd).
Proof.
  pose (R:= RunTree M tnd).
  replace (RunTree M tnd) with R; auto.
  intros b1 b2 Pref.
  inversion Pref.
  apply prefix_of_app in H1.
  destruct H1 as [u ?].
  symmetry in H.
  eapply TreeToMap in H.
  destruct H as [l1 [Run_l1 Label1]].
  symmetry in H0.
  eapply TreeToMap in H0.
  destruct H0 as [l2 [Run_l2 Label2]].
  subst y.
  apply path_app_rev in Run_l2.
  destruct Run_l2 as [l1' [Run_l1' Run_l2]].
  assert (x = x /\ l1' = l1). {
    eapply deterministic_sequence; eauto.
    apply (tsc_det M).
    apply list_rel_lift_id.
    reflexivity.
  }
  apply proj2 in H.
  subst l1'.
  destruct u.
  - (* if the path l1 ==> l2 is empty: *)
    inversion Run_l2.
    subst.
    assert (l1 = l2). {
      (* unfold NonRootLeaves in *. *)
      eapply sig_proof_irrelevance.
      apply H0.
    }
    clear H0.
    subst l2.
    reflexivity.
  - (* if l1 ==> l2 is nonempty: *)
    inversion Run_l2. subst.
    destruct l1 as [l1 [isLeaf ?]].
    exfalso.
    apply isLeaf.
    exists a. exists q_a. auto.
Qed.

(** Bringing all the previous results together: **)

(** For each tree-shaped code, we have a map-based code.
    Note that we have proven uniqueness already in
    [TreeDefinesMapUniquely] above.
**)
Theorem EveryTreeShapedCodeInducesSomeMapBasedCode
  {A B: Type} (M: TreeShapedCode A B) :
  TreeShapeTND M ->
  (exists f: Code A B, TreeRepresentsMap M f).
Proof.
  intro tnd.
  unshelve eexists (Build_Code _ _ (RunTree M tnd) _ _).
  - apply RunTree_is_ne_word.
  - apply RunTree_is_prefix_free.
  - apply TreeToMap.
Qed.



(** * From Map-Based Codes to Tree-Shaped Codes **)


(** ** Uniqueness **)
Lemma MapDefinesTreeUniquely
  {A B: Type} (f : CodeMap A B)
  (M N: TreeShapedCode A B) :
      Grounded M ->
      Grounded N ->
      TreeRepresentsMap M f ->
      TreeRepresentsMap N f ->
      M ≅ N.
Proof.
  intros G_M G_N M_f N_f.
  eapply tree_isomorphism_if_same_traces;
    try (destruct M; destruct N; eauto; fail).
  (** Now, it remains to show that M and N have
   the same traces: **)
  symmetric_cases.
  intros w Run_w.
  destruct Run_w as [q ?].
  destruct (G_M q) as [l [isLeaf [r]]].
  pose (v := proj_run_actions r).
  assert (M |- initial M == w ++ v ==> l) as Run_to_l. {
    eapply path_app; eauto.
    apply proj_run_actions_correct.
  }
  (** let's distinguish if w++v is empty  **)
  destruct (list_eq_nil_tnd (w ++ v)). {
    (** The case of an empty path is trivial
     because every LTS has the empty trace: **)
    apply app_eq_nil in H0.
    destruct H0.
    subst w.
    exists (initial N).
    constructor.
  }
  (** since w++v is non-empty, l can't be the root: **)
  assert_in_subtype l (NonRootLeaves M). {
    split; auto.
    intro Contr.
    apply H0.
    subst l.
    apply exists_run in Run_to_l.
    destruct Run_to_l as [r1 Eq_r1].
    assert (r1 = (RunNil (initial M) (initial M) eq_refl)). {
      apply tsc_uniq_run.
    }
    subst r1.
    rewrite <- Eq_r1.
    reflexivity.
  }
  pose (b:= tsc_label M l).
  assert (f b = Some (w ++ v)) as Eq. {
    apply M_f.
    exists l. split; auto.
  }
  apply N_f in Eq.
  destruct Eq as [p [R_q L_q]].
  apply path_app_rev in R_q.
  destruct R_q as [p' [? ?]].
  exists p'. auto.
Qed.

(** In above uniqueness result, we need that both M and N
    are grounded. To see this, we consider two examples of
    tree-shaped codes. The first example is a code on [SingletonLTS]:
 **)
Example SingletonLTS_has_no_leaves {A: Type}:
  NonRootLeaves (@SingletonLTS A) -> False.
Proof.
  intro r.
  destruct r as [l [? ?]].
  destruct l.
  contradiction.
Qed.

Example SingletonLTS_tree {A B: Type}: TreeShapedCode A B.
Proof.
  constructor 1 with
    (tsc_lts := SingletonLTS)
    (tsc_label := fun r => False_rect B (SingletonLTS_has_no_leaves r)).
  - intro. intros. inversion H.
  - intro. destruct q. constructor; auto.
  - intro. intros r1 r2.
    destruct r1. destruct r2.
    f_equal. apply proof_irrelevance.
    inversion t.
    inversion t.
  - intros x1 x2 ?.
    inner_contradiction.
Defined.

(** The other example code is on the [InfiniteChainLTS]: **)

Example InfiniteChainLTS_tree {A B: Type} (a: A): TreeShapedCode A B.
Proof.
  assert (NonRootLeaves (InfiniteChainLTS a) -> False) as No_NRL. {
    intro r.
    destruct r as [? []].
    eapply InfiniteChainLTS_has_no_leaves.
    eassumption.
  }
  constructor 1 with
    (tsc_lts := InfiniteChainLTS a)
    (tsc_label := fun r => False_rect B (No_NRL r)).
  - intros q q1 q2 a1 a2 T1 T2.
    destruct T1. destruct T2. subst.
    auto.
  - intro q.
    induction q.
    * constructor 1. auto.
    * econstructor 2. eassumption. simpl. eauto.
  -
    intros q r1. induction r1; intro r2.
    * destruct r2.
      ++ subst. f_equal. apply proof_irrelevance.
      ++ exfalso.
         subst.
         pose (Hyp := proj_run_actions_correct _ _ r2).
         apply InfiniteChainLTS_monotone in Hyp.
         inversion t. subst.
         eapply PeanoNat.Nat.nle_succ_diag_l.
         eauto.
    * destruct r2.
      ++ exfalso. subst.
         inversion t. subst.
         pose (Hyp := proj_run_actions_correct _ _ r1).
         apply InfiniteChainLTS_monotone in Hyp.
         eapply PeanoNat.Nat.nle_succ_diag_l.
         eauto.
      ++ inversion t. inversion t0. subst.
         injection H1 as H1.
         subst.
         f_equal.
         apply IHr1.
         apply proof_irrelevance.
  - intros x1 x2.
    inner_contradiction.
Defined.

(** Thus, the two LTSs represent the same [CodeMap] but are
 not isomorphic: **)
Example groundedness_is_needed_for_uniqueness {A B: Type} {a:A}:
  let M := SingletonLTS_tree in
  let N := InfiniteChainLTS_tree a in
  (* Both LTSs represent the same code: *)
     TreeRepresentsMap M (EmptyCode A B)
  /\ TreeRepresentsMap N (EmptyCode A B)
  (* But they are not isomorphic: *)
  /\ (M≅N -> False)
  (* and the reason is that one of them was not grounded: *)
  /\ Grounded M
  /\ (~ (Grounded N)).
Proof.
  split; [|split; [|split; [|split]]].
  - intros b w; split; intro Hyp.
    * inversion Hyp.
    * destruct Hyp as [? [? ?]].
      simpl in H0.
      inner_contradiction.
  - intros b w; split; intro Hyp.
    * inversion Hyp.
    * destruct Hyp as [? [? ?]].
      simpl in H0.
      inner_contradiction.
  - intros Iso.
    destruct Iso as [Iso].
    eapply (s0 _) in r; revgoals. {
      simpl.
      eauto.
    }
    destruct r as [? [Contr ?]].
    destruct Contr.
  - apply SingletonLTS_is_grounded.
  - apply InfiniteChainLTS_is_not_grounded.
Qed.


(** ** Existence **)
(** this definition is so complicated such that
    we can extract the witnessing b on the one hand
   and such that every w appears at most once on the other hand.
 **)
Definition PrefixStates {A B: Type} (f: B -> option (list A))
  := sum { w: list A & {b: B | f b = Some w} }
         { w: list A | w = [] \/ exists b: B, below_code w (f b) }.

Definition proj_prefixstate {A B: Type} {f: B -> option (list A)}:
  PrefixStates f -> list A.
Proof.
  intro x.
  destruct x.
  - apply (projT1 s).
  - apply (proj1_sig s).
Defined.


(** As usual, we disregard the prop when reasoning about equality.
    Because of the complicated definition of [PrefixStates], we need
    both code axioms in the proof. **)
Lemma ps_equal_helper {A B: Type} {f: Code A B} (w: PrefixStates f) (b: B):
  f b = Some (proj_prefixstate w) ->
  exists x: _, w = inl x.
Proof.
  intros.
  destruct w as [w|w].
  - exists w. reflexivity.
  - exfalso.
    destruct w as [w Hyp].
    destruct Hyp.
    * simpl in H.
      subst.
      apply (proj_code_ne_word f) in H.
      contradiction.
    * simpl in H.
      destruct e as [b'].
      unfold below_code in *.
      necessarily_some (f b') f_b'.
      destruct H0.
      apply H0.
      assert (b = b'). {
        apply (proj_code_prefix_free f).
        rewrite Eq_f_b'.
        rewrite H.
        constructor.
        auto.
      }
      subst.
      rewrite H in Eq_f_b'.
      inversion Eq_f_b'.
      auto.
Qed.

Lemma ps_equal {A B: Type} {f: Code A B} (w1 w2: PrefixStates f):
  proj_prefixstate w1 = proj_prefixstate w2 -> w1 = w2.
Proof.
  intros Eq.
  destruct w1 as [[p1]|[p1]] eqn: Eq_w1;
  destruct w2 as [[p2]|[p2]] eqn: Eq_w2.
  - simpl in Eq.
    subst.
    f_equal.
    f_equal.
    apply sig_proof_irrelevance.
    destruct s as [b].
    destruct s0 as [b'].
    simpl.
    apply (proj_code_prefix_free f).
    rewrite e.
    rewrite e0.
    constructor.
    apply prefix_of_reflexive.
  - exfalso.
    rewrite <- Eq_w2 in *.
    simpl in Eq.
    subst p1.
    destruct s as [b].
    destruct (ps_equal_helper _ _ e).
    subst w2.
    discriminate.
  - exfalso.
    rewrite <- Eq_w1 in *.
    simpl in Eq.
    subst p2.
    destruct s as [b].
    destruct (ps_equal_helper _ _ e).
    subst w1.
    discriminate.
  - f_equal.
    simpl in Eq.
    apply sig_proof_irrelevance.
    simpl.
    assumption.
Qed.

(* The coercion often causes unexpected behaviour / confusing statements *)
(*
Coercion proj_prefixstate : PrefixStates >-> list.
*)

Definition InitialPrefixStates {A B: Type} (f: B -> option (list A))
  : PrefixStates f.
Proof.
  unshelve eapply (inr (exist _ [] _)).
  simpl. left. reflexivity.
Defined.

Definition PrefixTreeLTS {A B: Type} (f: B -> option (list A)): LTS A
  := {|
    states := PrefixStates f;
    initial := InitialPrefixStates f;
    transition := (fun w a w' => proj_prefixstate w ++ [a] = proj_prefixstate w');
  |}.

Lemma PrefixTreeLTS_mk_state {A B: Type} (f: Code A B)
  (w: list A) (b: B):
  option_rel_lift prefix_of (Some w) (f b) ->
  exists (q: PrefixStates f), proj_prefixstate q = w.
Proof.
  intro Hyp.
  necessarily_some (f b) f_b. {
    inversion Hyp.
  }
  inversion Hyp.
  subst.
  apply prefix_of_app in H1.
  destruct H1 as [u].
  destruct (list_eq_nil_tnd u).
  - subst u.
    rewrite app_nil_r in *.
    unshelve eexists (inl (existT _ w _)). {
      simpl.
      exists b.
      subst f_b. auto.
    }
    simpl.
    reflexivity.
  - unshelve eexists (inr (exist _ w _)). {
      simpl.
      right.
      exists b.
      unfold below_code.
      rewrite Eq_f_b.
      split.
      * intro Contr. subst.
        apply app_yields_prefix in Contr.
        contradiction.
      * apply prefix_of_app.
        exists u.
        auto.
    }
    simpl.
    reflexivity.
Qed.

Lemma PrefixTreeLTS_progress {A B: Type} (f: Code A B)
  (w: states (PrefixTreeLTS f)) (b: B):
  below_code (proj_prefixstate w) (f b) -> exists (a: A), exists (w': PrefixStates f),
      (PrefixTreeLTS f |- w --a--> w').
Proof.
  intro Pref.
  unfold below_code in *.
  destruct w.
  - exfalso.
    necessarily_some (f b) f_b.
    destruct Pref.
    destruct s as [w' [b' Eq_b']].
    simpl in *.
    assert (b' = b). {
      apply (proj_code_prefix_free f).
      rewrite Eq_b'.
      rewrite Eq_f_b.
      constructor.
      auto.
    }
    subst b'.
    rewrite Eq_b' in Eq_f_b.
    inversion Eq_f_b.
    subst.
    contradiction.
  - necessarily_some (f b) f_b.
    destruct Pref as [? Pref].
    apply prefix_of_app in Pref.
    destruct Pref as [u H_u].
    destruct u.
    * exfalso. subst.
      rewrite app_nil_r in *.
      contradiction.
    * exists a.
      assert (option_rel_lift prefix_of (Some (proj_prefixstate (inr s) ++ [a])) (f b)) as Q'. {
        rewrite Eq_f_b.
        constructor.
        apply prefix_of_app.
        exists u.
        rewrite <- app_assoc.
        auto.
      }
      apply PrefixTreeLTS_mk_state in Q'.
      destruct Q' as [q'].
      exists q'.
      simpl.
      rewrite H0.
      reflexivity.
Qed.

Lemma PrefixTree_leaf {A B: Type} {f: Code A B}
  (q: states (PrefixTreeLTS f)):
  (exists b: B, f b = Some (proj_prefixstate q))
  -> Leaf q.
Proof.
  intro H.
  destruct H as [b H].
  intro H'.
  destruct H' as [a [q' T]].
  destruct q'.
  - destruct s as [w' ?].
    destruct s as [b' Eq_b].
    simpl in T.
    assert (b = b'). {
      apply (proj_code_prefix_free f).
      rewrite H.
      rewrite Eq_b.
      constructor.
      apply prefix_of_app.
      eexists.
      eauto.
    }
    subst b'.
    rewrite H in Eq_b.
    inversion Eq_b. subst.
    apply app_yields_prefix in H1.
    discriminate.
  - destruct s.
    destruct o.
    * subst.
      simpl in T.
      eapply app_cons_not_nil.
      eauto.
    * simpl in T.
      destruct e as [b'].
      necessarily_some (f b') f_b'.
      subst x.
      destruct H0.
      apply prefix_of_app in H1.
      destruct H1 as [u H1].
      rewrite <- app_assoc in H1.
      assert (b = b'). {
        eapply proj_code_prefix_free.
        rewrite Eq_f_b'.
        rewrite H.
        constructor.
        apply prefix_of_app.
        exists (a :: u).
        subst.
        auto.
      }
      subst f_b'.
      subst b'.
      rewrite Eq_f_b' in H.
      inversion H.
      symmetry in H2.
      apply app_yields_prefix in H2.
      discriminate.
Qed.


Definition LabelPrefixTreeLTS {A B: Type} {f: Code A B}:
  NonRootLeaves (PrefixTreeLTS f) -> B.
Proof.
  intro l.
  destruct l as [l [IsLeaf NotInitial]].
  pose (q := l).
  destruct l.
  - destruct s.
    destruct s as [b].
    exact b.
  - exfalso.
    destruct s as [w Hyp].
    destruct Hyp.
    * apply NotInitial.
      simpl.
      subst w.
      apply ps_equal.
      simpl.
      reflexivity.
    * apply IsLeaf.
      clear IsLeaf.
      clear NotInitial.
      destruct e as [b ?].
      simpl in *.
      assert (below_code w (f b)) as Hyp by assumption.
      assert (w = proj_prefixstate q). {
        subst q.
        simpl.
        auto.
      }
      rewrite H in Hyp.
      apply PrefixTreeLTS_progress in Hyp.
      destruct Hyp as [a [w' Trans]].
      exists a. exists w'.
      inversion Trans.
      auto.
Defined.


Lemma LabelPrefixTree_correct {A B: Type} {f: Code A B}
  {q: NonRootLeaves (PrefixTreeLTS f)}:
  f (LabelPrefixTreeLTS q) = Some (proj_prefixstate (proj1_sig q)).
Proof.
  destruct q.
  destruct a.
  destruct x.
  * simpl.
    case_match.
    simpl.
    case_match.
    auto.
  * simpl.
    inner_contradiction.
Qed.

Definition PrefixStates_closed_under_prefix {A B: Type} {f: CodeMap A B}
  (w: list A) {delta: list A} (q: PrefixStates f):
  w ++ delta = (proj_prefixstate q)
  -> {qw: PrefixStates f| proj_prefixstate qw = w}.
Proof.
  intro Pref.
  destruct delta as [|a delta].
  - eapply exist.
    rewrite app_nil_r in Pref.
    symmetry.
    apply Pref.
  - unshelve eapply exist.
    * apply inr.
      eapply (exist _ w).
      right.
      destruct q.
      + destruct s.
        destruct s as [b ?].
        simpl in Pref.
        exists b.
        rewrite e.
        simpl.
        split.
        intro. subst.
        apply app_yields_prefix in H.
        discriminate.
        apply prefix_of_app.
        exists (a::delta).
        auto.
      + destruct s as [w'].
        destruct o. {
          exfalso.
          subst.
          simpl in *.
          eapply app_cons_not_nil.
          eauto.
        }
        destruct e as [b].
        exists b.
        simpl in Pref.
        apply below_code_app in b0.
        autodestruct.
        apply below_code_app.
        subst w'.
        repeat rewrite <- app_assoc in *.
        simpl in *.
        eexists.
        eexists.
        eauto.
    * simpl.
      auto.
Qed.

Proposition PrefixTree_gtrans {A B: Type} {f: Code A B}
    {q q': states (PrefixTreeLTS f)} (w: list A):
  proj_prefixstate q ++ w = proj_prefixstate q'
        <-> (q == w ==> q').
Proof.
  split.
  - revert q q'. induction w; intros q q' H.
    * rewrite app_nil_r in *.
      replace q' with q.
      constructor.
      apply ps_equal.
      auto.
    * pose (Lem := @PrefixStates_closed_under_prefix _ _ f (proj_prefixstate q ++ [a]) w q').
      rewrite <- app_assoc in Lem.
      simpl in Lem.
      destruct (Lem H) as [qw Qw] eqn: Eq.
      econstructor.
      simpl.
      eauto.
      apply IHw.
      rewrite Qw.
      rewrite <- app_assoc.
      auto.
  - intro H. induction H.
    rewrite app_nil_r.
    auto.
    rewrite <- IHgtrans.
    simpl in H.
    rewrite <- H.
    rewrite <- app_assoc.
    auto.
Qed.

Proposition PrefixTree_run {A B: Type} {f: CodeMap A B}
    {q q': states (PrefixTreeLTS f)} (r: Run q q'):
  proj_prefixstate q ++ proj_run_actions r = proj_prefixstate q'.
Proof.
  induction r.
  - rewrite app_nil_r.
    subst.
    reflexivity.
  - simpl.
    rewrite app_assoc.
    rewrite IHr.
    apply t.
Qed.



Proposition PrefixTreeLoopFree {A B: Type} {f: CodeMap A B}
    {q: states (PrefixTreeLTS f)} (r: Run q q):
  RunNil q q eq_refl = r.
Proof.
  assert (proj_run_actions r = []). {
    pose (H := PrefixTree_run r).
    symmetry in H.
    apply app_yields_prefix in H.
    auto.
  }
  eassert (forall (q' q'': states (PrefixTreeLTS f)) (r': Run q' q''),
             proj_run_actions r' = [] -> exists P: _, r' = RunNil q' q'' P) as Hyp. {
    intros.
    destruct r'.
    subst.
    - exists (eq_refl).
      cbv.
      auto.
    - exfalso.
      simpl in H.
      eapply app_cons_not_nil.
      eauto.
  }
  apply Hyp in H.
  destruct H.
  subst r.
  cbv.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition PrefixTreeCode {A B: Type} (f: Code A B):
  TreeShapedCode A B.
Proof.
  econstructor 1 with
    (tsc_lts := PrefixTreeLTS f)
    (tsc_label := LabelPrefixTreeLTS (f:=f)).
  - intros q q1 q2 a1 a2 Step1 Step2 H.
    subst. autosplit.
    inversion Step1.
    inversion Step2.
    rewrite H0 in H1.
    apply ps_equal.
    auto.
  - intro q.
    pose (w := rev (proj_prefixstate q)).
    assert (rev w = (proj_prefixstate q)). {
      rewrite <- rev_involutive.
      f_equal.
    }
    revert H.
    generalize q.
    pattern w.
    generalize w.
    clear w q.
    intro w.
    induction w; intros q Eq.
    * simpl in Eq.
      assert (q = initial _). {
        apply ps_equal.
        rewrite <- Eq.
        reflexivity.
      }
      subst q.
      constructor; auto.
    * simpl in Eq.
      pose (Q' := Eq).
      eapply PrefixStates_closed_under_prefix in Q'.
      destruct Q' as [q'].
      econstructor 2.
      apply (IHw q').
      auto.
      simpl.
      rewrite e.
      rewrite <-Eq.
      reflexivity.
  - intros q r1.
    induction r1; intro r2.
    * subst. apply PrefixTreeLoopFree.
    * destruct r2.
      + exfalso.
        simpl in t.
        rewrite <- (PrefixTree_run  r1) in t.
        rewrite <- app_assoc in *.
        symmetry in t.
        subst.
        apply app_yields_prefix in t.
        eapply app_cons_not_nil.
        eauto.
      + assert (a0 = a /\ q' = q'0). {
          simpl in t.
          simpl in t0.
          rewrite <- t in t0.
          apply app_inj_tail in t0.
          autodestruct.
          subst.
          autosplit.
          apply ps_equal.
          auto.
        }
        destruct H.
        subst a0. subst q'0.
        f_equal.
        apply IHr1.
        apply proof_irrelevance.
  - intros l1 l2 Eq.
    apply sig_proof_irrelevance.
    apply ps_equal.
    assert (forall (T: Type) (x y: T), Some x = Some y -> x = y) as SomeInjective. {
      intros.
      congruence.
    }
    apply SomeInjective.
    rewrite <-LabelPrefixTree_correct.
    rewrite <-LabelPrefixTree_correct.
    rewrite Eq.
    reflexivity.
Defined.

(** With the entire tree defined, we can now show that it indeed implements
    the original code map. (We have proven uniqueness already in
    [MapDefinesTreeUniquely].) **)
Theorem MapToTree {A B: Type} {f: Code A B} :
  TreeRepresentsMap (PrefixTreeCode f) f.
Proof.
  split.
  - intro H.
    assert (option_rel_lift prefix_of (Some w) (f b)) as Q. {
      rewrite H.
      constructor.
      apply prefix_of_reflexive.
    }
    apply (PrefixTreeLTS_mk_state f w b) in Q.
    destruct Q as [q Q].
    sig_exists q.
    split.
    * apply PrefixTree_leaf.
      exists b.
      subst.
      auto.
    * subst w.
      intro Contr. subst q.
      simpl in *.
      apply (proj_code_ne_word f) in H.
      auto.
    * simpl.
      split.
      + subst.
        apply PrefixTree_gtrans.
        simpl.
        auto.
      + simpl.
        case_match.
        case_match.
        case_match.
        subst.
        simpl in H.
        rewrite <- e in H.
        apply (proj_code_prefix_free f).
        rewrite H.
        rewrite e.
        constructor.
        apply prefix_of_reflexive.
        simpl.
        exfalso.
        destruct s.
        destruct o.
        *** subst.
            simpl in H.
            eapply (proj_code_ne_word f).
            eauto.
        *** subst.
            simpl in H.
            destruct e as [b' Eq_b'].
            necessarily_some (f b') f_b'.
            simpl in *.
            destruct Eq_b'.
            subst.
            assert (b = b'). {
              apply (proj_code_prefix_free f b b').
              rewrite Eq_f_b'.
              rewrite H.
              constructor.
              auto.
            }
            subst.
            rewrite H in Eq_f_b'.
            inversion Eq_f_b'.
            subst. apply H0.
            auto.
  - intro H.
    destruct H as [q [? ?]].
    subst b.
    simpl.
    rewrite LabelPrefixTree_correct.
    apply exists_run in H.
    destruct H as [r H].
    pose (T := PrefixTree_run r).
    f_equal.
    subst w.
    simpl in T.
    auto.
Qed.
