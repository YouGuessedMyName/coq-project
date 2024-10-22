Require Export Coq.Logic.FinFun.
Require Import Lists.List.
Require Export Coq.Logic.ProofIrrelevance.
Require Export Coq.Sets.Ensembles.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Relations.Relation_Definitions.
Require Export ACUtil.

Import ListNotations.

(** Definitions **)
(** The LTS' has the alphabet type as an implicit argument.
    So, the record members have an implicit argument for the
    alphabet type.
 **)
Structure LTS' {Alphabet: Type} : Type :=
  new_LTS {
  states : Type;
  initial : states;
  transition : states -> Alphabet -> states -> Prop;
  }.

(** Usually, we mention the alphabet type explicitly in
statements, so `LTS` has `Alphabet` as an explicit argument: **)
Definition LTS (Alphabet: Type) : Type := @LTS' Alphabet.

Notation "x ↓ a"  := (exists y : _ , (transition _ x a y)) (at level 303, no associativity) : type_scope.
Notation "x -- a --> y" := (transition _ x a y) (at level 302, no associativity) : type_scope.
Notation "M |- x -- a --> y" := (transition M x a y) (at level 300, no associativity) : type_scope.
Notation "x ⎯⎯ a --> y" := (transition _ x a y) (at level 300, no associativity) : type_scope.
Notation "x ⎯⎯ a --> y (∈ M )" := (transition M x a y) (at level 301, no associativity) : type_scope.

Definition LTS_uses_action {A: Type} (M: LTS A) : A -> Prop
  := fun a => exists q q': states M, (q -- a --> q') .

(** the generalized tranitions describe paths in an LTS **)
Inductive gtrans [A: Type] (M: LTS A) : states M -> list A -> states M -> Prop :=
  | seq_nil : forall q: states M, gtrans M q nil q
  | seq_cons : forall (q: states M) (a: A) (q_a: states M) (w: list A) (q_tl: states M),
      (q --a--> q_a) -> (gtrans M q_a w q_tl) -> (gtrans M q (a::w) q_tl).

Notation "x == a ==> y" := (gtrans _ x a y) (at level 300, no associativity) : type_scope.
Notation "M |- x == a ==> y" := (gtrans M x a y) (at level 300, no associativity) : type_scope.
(* the last defined notation seems to be used for printing *)
Notation "x ══ a ==> y" := (gtrans _ x a y) (at level 300, no associativity) : type_scope.
Notation "M |- x ══ a ==> y" := (gtrans M x a y) (at level 300, no associativity) : type_scope.

(** Just a straightforward induction to see whether all the definitions
and notations make sense: **)
Lemma path_app [A: Type] (M : LTS A) (q p r: states M) (w v : list A):
  (M |- q == w ==> p) -> (p == v ==> r) -> (q == w++v ==> r).
Proof.
  intros *.
  intros Hw Hv.
  induction Hw; simpl.
  * assumption.
  * econstructor.
    apply H.
    apply IHHw.
    assumption.
Qed.

Lemma gtrans_singleton [A: Type] (M : LTS A) (q p: states M) (a: A) :
  (M |- q == a::nil ==> p) <-> (M |- q --a--> p).
Proof.
  split.
  - intro H. inversion H. subst. inversion H5. subst. assumption.
  - intro H. econstructor. eassumption.
    constructor.
Qed.

(** the statement in the converse direction: *)
Lemma path_app_rev [A: Type] (M : LTS A) (q r: states M) (w v : list A):
  (q ==(w ++ v)==> r)
      -> exists p: states M, (M |- q ==w==> p) /\ (p ==v==> r).
Proof.
  revert q.
  induction w.
  * simpl. intros q H. exists q.
    split; auto. constructor.
  * intros q H.
    inversion H. subst.
    pose (IH_qa := IHw q_a H5).
    inversion IH_qa as [p].
    exists p.
    inversion H0.
    split.
    - econstructor; eassumption.
    - assumption.
Qed.

Definition relates_initial {A: Type} (M N : LTS A)
    (rel: states M -> states N -> Prop) : Type :=
      rel (initial M) (initial N).

Definition step_closed {A: Type} (M N : LTS A)
    (rel: states M -> states N -> Prop) : Type :=
      forall (q q': states M) (p: states N) (a: A),
        rel q p -> (q --a--> q') ->
          exists p': states N, (p --a--> p') /\ rel q' p'.

Lemma step_closed_sequence {A: Type} (M N : LTS A)
    (rel: states M -> states N -> Prop) :
      step_closed M N rel ->
      forall (q q': states M) (p: states N) (w: list A),
        rel q p -> (q ==w==>q') ->
          exists p': states N, (p ==w==> p') /\ rel q' p'.
Proof.
  intros Step q q' p w.
  revert q q' p.
  induction w; intros.
  - exists p. inversion H0. split.
    constructor. subst. assumption.
  - inversion H0. subst.
    destruct (Step q q_a p a H H4) as [p_a].
    destruct H1.
    apply IHw with (p:=p_a) in H6; try assumption.
    destruct H6 as [p' [? ?]].
    exists p'. split; auto. econstructor; eassumption.
Qed.

(** * Simulations **)

(** We consider LTSs with an initial state, so we also require
    that simulations relate the initial states: **)
Inductive Simulation {A: Type} (M N : LTS A) : Type :=
  Build_Simulation: forall rel: states M -> states N -> Prop,
    relates_initial M N rel -> step_closed M N rel -> Simulation M N.

Definition proj_sim_rel {A: Type} {M N : LTS A} : Simulation M N -> (states M -> states N -> Prop).
  intro S. destruct S. assumption.
Defined.

Coercion proj_sim_rel : Simulation >-> Funclass.

Definition proj_sim_initial {A: Type} {M N : LTS A} (S: Simulation M N):
  relates_initial M N S.
Proof.
  destruct S. simpl. assumption.
Defined.

Definition proj_sim_step {A: Type} {M N : LTS A} (S: Simulation M N):
  step_closed M N S.
Proof.
  destruct S. simpl. assumption.
Defined.

Lemma simulation_compose {A: Type} (M N K: LTS A) :
  Simulation M N -> Simulation N K -> Simulation M K.
Proof.
  intros S T.
  destruct S as [S S_init S_step].
  destruct T as [T T_init T_step].
  pose (ST:=fun (m:states M) (k:states K) =>
       exists n: states N, S m n /\ T n k).
  apply Build_Simulation with (rel:=ST); unfold_goal.
  - exists (initial N); split; auto.
  - intros m m' k a rel Step.
    destruct rel as [n [S_m_n T_n_k]].
    eapply S_step in Step; eauto.
    destruct Step as [n' [Step ?]].
    eapply T_step in Step; eauto.
    destruct Step as [k' [Step ?]].
    exists k'. split; auto.
    eexists; split; eauto.
Qed.

(** We sometimes consider the following history-dependent
 variation of [step_closed]: **)
Definition step_closed_hd {A: Type} (M N: LTS A)
      (rel: states M -> states N -> Prop): Prop :=
    forall (w: list A) (q q': states M) (p: states N) (a: A),
        ((initial M) == w ==> q) ->
        ((initial N) == w ==> p) ->
        (rel q p) ->
        (q --a--> q') ->
          exists p': states N, (p --a--> p') /\ rel q' p'.

Definition history_dependent_subrel {A: Type} {M N: LTS A}
      (rel: states M -> states N -> Prop): (states M -> states N -> Prop) :=
  fun (q: states M) (p: states N) =>
       exists w: list A,
       ((initial M) == w ==> q) /\
       ((initial N) == w ==> p) /\
                 rel q p.

Lemma history_dependent_is_step_closed {A: Type} {M N: LTS A}
  (rel: states M -> states N -> Prop):
  step_closed_hd _ _ rel -> step_closed _ _ (history_dependent_subrel rel).
Proof.
  unfold step_closed_hd.
  unfold step_closed.
  intros StepClosed. intros.
  pose (Step := H0).
  unfold history_dependent_subrel in *.
  autodestruct.
  eapply StepClosed in Step; eauto.
  autodestruct.
  eexists; eauto.
  split; eauto.
  exists (x ++ [a]). autosplit.
  all: try eapply path_app; eauto.
  all: try apply gtrans_singleton; eauto.
Qed.

(** We use this in the following variation of simulation principle
 with stronger assumptions: **)
Lemma Build_PathSimulation {A: Type} (M N: LTS A)
  (rel: states M -> states N -> Prop):
  relates_initial _ _ rel ->
    step_closed_hd _ _ rel ->
    Simulation M N.
 Proof.
   intros rel_init path_step.
   pose (S := history_dependent_subrel rel).
   apply Build_Simulation with (rel := S).
   - exists nil. autosplit; auto.
   - eapply history_dependent_is_step_closed; eauto.
Qed.

Definition traces_state {A: Type} {M: LTS A} (q: states M) : list A -> Prop :=
  fun word => exists q' : states M, (q ==word==> q').

Definition traces {A: Type} (M: LTS A) : list A -> Prop :=
  traces_state (initial M).

Definition pred_inclusion {X: Type} (P1 P2: X -> Prop) := forall x: X, P1 x -> P2 x.

Theorem simulation_implies_trace_inclusion {A: Type} (M N: LTS A) :
  Simulation M N -> pred_inclusion (traces M) (traces N).
Proof.
  intros S w run.
  destruct run.
  apply (step_closed_sequence M N S) with (p := initial N) in H;
    try apply proj_sim_step;
    try apply proj_sim_initial;
    auto.
  destruct H as [p'].
  destruct H.
  exists p'.
  auto.
Qed.

Definition deterministic {A: Type} (related: A -> A -> Prop) (M: LTS A) :=
  forall (q q1 q2: states M) (a1 a2: A),
    (q --a1--> q1) -> (q --a2--> q2) -> (related a1 a2) ->
      a1 = a2 /\ q1 = q2.

Notation "M 'is' 'deterministic'" := (deterministic (fun x y => x = y) M) (at level 40) : type_scope.
Notation "M 'is' rel 'deterministic'" := (deterministic rel M) (at level 40) : type_scope.



(* Lift a relation between X and Y to lists over X and Y *)
Inductive list_rel_lift {X Y : Type} (rel: X -> Y -> Prop) :
  list X -> list Y -> Prop
  :=
  | list_rel_nil : list_rel_lift rel nil nil
  | list_rel_cons : forall (x: X) (y: Y) (lx: list X) (ly: list Y),
      rel x y -> list_rel_lift rel lx ly -> list_rel_lift rel (x::lx) (y::ly).

Definition idRel {A: Type} : A -> A -> Prop := fun a a' => a = a'.

Definition simulation_id {A: Type} (M: LTS A) :
  Simulation M M.
Proof.
  refine (Build_Simulation _ _ idRel _ _); unfold_goal.
  - simpl. unfold_goal. auto.
  - intros. destruct H. exists q'; split; auto. reflexivity.
Defined.

Lemma idRel_reflexive {A: Type} : reflexive A idRel.
Proof.
  intro a. cbv. auto.
Qed.

Lemma list_rel_lift_reflexive {A: Type} (rel: A -> A -> Prop):
  reflexive _ rel -> reflexive _ (list_rel_lift rel).
Proof.
  intro refl.
  intro w.
  induction w; auto; constructor; auto.
Qed.

Lemma list_rel_lift_id {A: Type} :
  same_relation _ (list_rel_lift (@idRel A)) idRel.
Proof.
  split.
  - intros ? ? R.
    induction R.
    constructor.
    cbv in H. cbv in IHR. subst.
    cbv. auto.
  - intros ? ? ?.
    cbv in H. subst.
    apply list_rel_lift_reflexive.
    apply idRel_reflexive.
Qed.

Lemma list_rel_lift_app {X Y: Type} (rel: X -> Y -> Prop)
  (lx1 lx2: list X) (ly1 ly2: list Y):
  list_rel_lift rel lx1 ly1 ->
  list_rel_lift rel lx2 ly2 ->
  list_rel_lift rel (lx1 ++ lx2) (ly1 ++ ly2).
Proof.
  revert ly1 ly2.
  induction lx1; intros.
  - inversion H. subst. assumption.
  - inversion H. subst.
    simpl.
    constructor. assumption.
    apply IHlx1. assumption.
    assumption.
Qed.

Lemma deterministic_sequence {A: Type} {rel: A -> A -> Prop} {M: LTS A} :
  M is rel deterministic ->
  forall (q q1 q2: states M) (w1 w2: list A),
    (q ==w1==> q1) -> (q ==w2==> q2) -> (list_rel_lift rel w1 w2) ->
      w1 = w2 /\ q1 = q2.
Proof.
  intros M_det ? ? ? ? ? ? ? ListRel.
  revert q q1 q2 H0 H.
  induction ListRel; intros.
  - inversion H. inversion H0. subst.
    split; auto.
  - inversion H0. inversion H1. subst.
    assert (x = y /\ q_a0 = q_a) as Hyp. {
        eapply M_det; eauto.
    }
    destruct Hyp. subst.
    assert (lx = ly /\ q1 = q2) as Hyp2. {
        eapply IHListRel; eauto.
    }
    destruct Hyp2. subst.
    split; try f_equal; auto.
Qed.

Definition converse {X Y: Type} (rel: X -> Y -> Prop) : (Y -> X -> Prop)
    := fun y x => rel x y.

Lemma deterministic_symmetric {A: Type} (rel_a: relation A) (M: LTS A) :
  M is rel_a deterministic <-> M is (converse rel_a) deterministic.
Proof.
  symmetric_cases.
  intro M_det.
  intro. intros.
  unfold converse in *.
  assert (a2 = a1 /\ q2 = q1). {
    eapply M_det; eauto.
  }
  autodestruct.
  split; auto.
Qed.

(** * Isomorphism **)

Definition left_unique {X Y: Type} (rel: X -> Y -> Prop) : Prop
    := forall (x: X) (y1 y2: Y), rel x y1 -> rel x y2 -> y1 = y2.
Definition right_unique {X Y: Type} (rel: X -> Y -> Prop) : Prop
    := left_unique (converse rel).

Inductive Isomorphism {A: Type} (M N : LTS A) : Type :=
  Build_Isomorphism: forall rel: states M -> states N -> Prop,
    relates_initial M N rel
    -> step_closed M N rel
    -> step_closed N M (converse rel)
    -> left_unique rel
    -> right_unique rel
    -> Isomorphism M N.

Inductive inhabited (A: Type) : Prop :=
  | witness_inhabited: forall (a: A), inhabited A.
Notation "M ≅ N" := (Isomorphism M N) (at level 40): type_scope.
Notation "M ⊑ N" := (inhabited (Simulation M N)) (at level 40): type_scope.


Definition proj_iso_rel {A: Type} (M N : LTS A)
    : Isomorphism M N -> (states M -> states N -> Prop).
Proof.
  intro Iso; destruct Iso. assumption.
Defined.

Coercion proj_iso_rel : Isomorphism >-> Funclass.

(** Like for Simulations, we have the following history-dependent variation
 of the isomorphism betweeen LTSs: **)
Theorem Build_PathIsomorphism {A: Type} (M N : LTS A) :
  forall rel: states M -> states N -> Prop,
    relates_initial M N rel
    -> step_closed_hd M N rel
    -> step_closed_hd N M (converse rel)
    -> left_unique (history_dependent_subrel rel)
    -> right_unique (history_dependent_subrel rel)
    -> Isomorphism M N.
Proof.
  intros rel init step_forward step_back l_uniq r_uniq.
  apply Build_Isomorphism with (rel := history_dependent_subrel rel).
  - exists nil. autosplit. assumption.
  - eapply history_dependent_is_step_closed; eauto.
  - assert (step_closed _ _ (history_dependent_subrel (converse rel)))
       as GoalFlipped. {
        eapply history_dependent_is_step_closed; eauto.
    }
    unfold converse in *.
    intros ?. intros.
    unfold history_dependent_subrel in *.
    autodestruct.
    eapply GoalFlipped in H0; eauto.
    autodestruct.
    eexists. autosplit; eauto.
  - auto.
  - auto.
Qed.

Lemma trace_inclusion_yields_step_closed {A: Type} (M N: LTS A) :
  N is deterministic ->
  pred_inclusion (traces M) (traces N) ->
  step_closed_hd M N (fun q p => True).
Proof.
  intros N_det TraceIncl.
  unfold_goal. intros.
  assert (traces_state (initial N) (w ++ [a])). {
    eapply TraceIncl.
    exists q'.
    eapply path_app; eauto.
    econstructor; eauto.
    constructor.
  }
  destruct H3 as [p' Run_wa].
  apply path_app_rev in Run_wa.
  destruct Run_wa as [p'' [? ?]].
  eapply gtrans_singleton in H4.
  assert (p'' = p). {
      eapply deterministic_sequence; eauto.
      apply list_rel_lift_id.
      reflexivity.
  }
  subst p''.
  exists p'. autosplit. auto.
Qed.

Theorem simulation_iff_trace_inclusion_for_deterministic {A: Type} (M N: LTS A) :
  N is deterministic -> (
  (M ⊑ N) <-> pred_inclusion (traces M) (traces N)).
Proof.
  intro N_det.
  split.
  * intro H. destruct H. eapply simulation_implies_trace_inclusion; eauto.
  * intros TraceIncl.
    constructor.
    (* Since we have identical path to the states, we can
    even use the full relation: *)
    pose (S := fun (q: states M) (p: states N) => True).
    apply Build_PathSimulation with (rel := S).
    - autosplit.
    - apply trace_inclusion_yields_step_closed; auto.
Qed.

(* The projeciton sends an isomorphism to its underyling relation *)
Definition proj_iso  {A: Type} {M N : LTS A} :
  Isomorphism M N -> (states M -> states N -> Prop).
Proof.
  intro iso.
  inversion iso.
  assumption.
Defined.

(** * Reachability  **)
(** Our notion of isomorphism implicitly restricts to the reachable subgraph
    of the LTSs involved.
**)
Definition reachable {A: Type} {M: LTS A} (q: states M): Prop
   := exists w: list A, (initial M ==w==> q).

Lemma reachable_closed {A: Type} {M: LTS A} {a: A} (q q': states M) :
  reachable q -> (q --a--> q') -> reachable q'.
Proof.
  intros.
  inversion H as [w Run].
  exists (w ++ [a]).
  revert Run H0 H.
  revert q.
  revert q'.
  generalize (initial M) as q0.
  induction w; intros; simpl; inversion Run; subst.
  - apply gtrans_singleton. assumption.
  - econstructor. eassumption.
    apply IHw with (q := q); assumption.
Qed.

Definition reachable_states {A: Type} (M: LTS A): Type
   := {q: states M | reachable q}.

Definition proj_reachable {A: Type} {M: LTS A}: reachable_states M -> states M.
Proof.
  apply proj1_sig.
Defined.

Lemma proj_reachable_injective {A: Type} {M: LTS A} (q q': reachable_states M):
  proj_reachable q = proj_reachable q' -> q = q'.
Proof.
  intros.
  destruct q as [q P].
  destruct q' as [q' P'].
  simpl in H. subst.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition reachable_part {A: Type} (M: LTS A) : LTS A.
Proof.
  apply new_LTS with (states := reachable_states M).
  - eapply (exist _ (initial M)).
    exists nil. constructor.
  - intros q a q'.
    exact (M |- proj_reachable q --a--> proj_reachable q').
Defined.

(** Our notion of isomorphism implicitly restricts LTSs to their reachable part: **)
Theorem reachable_isomorphic {A: Type} (M: LTS A) :
  M ≅ reachable_part M.
Proof.
  apply Build_Isomorphism with (rel := (fun q q' => q = proj_reachable q')).
  - cbv. auto.
  - intros ? ? ? ? ? ?.
    subst.
    unshelve eexists (exist _ q' _); simpl.
    * simpl. eapply reachable_closed; try eassumption.
      destruct p. simpl. assumption.
    * auto.
  - intros ? ? ? ? ? ?.
    exists (proj_reachable q').
    cbv in H.
    split.
    * destruct q. destruct q'.
      subst. auto.
    * cbv. auto.
  - intros ?. intros. subst.
    apply proj_reachable_injective; auto.
  - intros ? * ? ?.
    cbv in H.
    cbv in H0.
    subst. reflexivity.
Qed.

(** * Examples **)
(** An LTS with one state and no transitions: **)
Example SingletonLTS {A: Type} : LTS A :=
  {| states := unit;
     initial := tt;
     transition := fun (q: unit) (a: A) (q': unit) => False
  |}.

(** An LTS with an infinite chain of transitions labelled a:
   -> 0 --a--> 1 --a--> 2 --a--> ...
 **)
Example InfiniteChainLTS {A: Type} (a: A): LTS A :=
  {| states := nat;
     initial := 0;
     transition := fun (q: nat) (a': A) (q': nat) => S q = q' /\ a = a'
  |}.

Lemma InfiniteChainLTS_has_no_proper_loops {A: Type} {a: A}
  (q: states (InfiniteChainLTS a)) (w: list A):
  (q ==w==> q) -> w = [].
Proof.
  revert w.
  induction q; intros w Path.
  - destruct w using rev_ind. subst. auto.
    apply path_app_rev in Path.
    destruct Path as [p []].
    apply gtrans_singleton in H0.
    inversion H0.
    discriminate H1.
  - destruct w using rev_ind. auto.
    exfalso.
    apply path_app_rev in Path.
    destruct Path as [p []].
    apply gtrans_singleton in H0.
    inversion H0. injection H1 as H1.
    subst.
    assert ([x] ++ w = []). {
      apply IHq.
      eapply path_app.
      apply gtrans_singleton.
      eauto.
      eauto.
    }
    simpl in *.
    discriminate.
Qed.

Lemma InfiniteChainLTS_monotone {A: Type} {a: A}
  (q p: states (InfiniteChainLTS a)) (w: list A):
  (q ==w==> p) -> (q <= p).
Proof.
  revert q p.
  induction w using rev_ind; intros q p; intro Path.
  - inversion Path. subst. constructor.
  - apply path_app_rev in Path.
    destruct Path as [? [? ?]].
    apply gtrans_singleton in H0.
    inversion H0. subst.
    constructor.
    apply IHw.
    auto.
Qed.
