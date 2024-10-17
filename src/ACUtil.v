Require Import Lists.List.
Require Import Coq.Logic.Decidable.

Import ListNotations.

Ltac case_eq_subst term :=
  case_eq term;
  intros *;
  let Eq := fresh "CaseEq" in
  (intros Eq; try rewrite ->Eq; try rewrite ->Eq in *; simpl in *; try contradiction; try discriminate).

Ltac inv_clear hyp :=
  inversion hyp; try clear hyp.

Ltac unfold_goal  :=
  match goal with
  | |- ?term _ _ _ _ _ _ _ => unfold term; simpl
  | |- ?term _ _ _ _ _ _ => unfold term; simpl
  | |- ?term _ _ _ _ _ => unfold term; simpl
  | |- ?term _ _ _ _ => unfold term; simpl
  | |- ?term _ _ _ => unfold term; simpl
  | |- ?term _ _ => unfold term; simpl
  | |- ?term _ => unfold term; simpl
  | |- ?term => unfold term; simpl
  end.

Ltac necessarily_some option_value some_value :=
  let Eq := fresh "Eq_" some_value in
  destruct option_value as [some_value|] eqn: Eq;
    revgoals;
  [simpl in *;
   try (contradiction || discriminate)
  |].

Ltac autosplit :=
  (* if there are at least two constructors.. *)
  tryif (econstructor 2)
  then fail (*then fail*)
  else (*else, there is only one constructor, which we apply:
        we continue likewise in the subgoals: *)
    econstructor 1; try autosplit.

Ltac case_match :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:?
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:?
  end.

(** Tactic if the goal is of the shape
    [exists l : {x : A| P x}, Q l]
**)
Ltac sig_exists witness :=
  unshelve eexists (@exist _ _ witness _); simpl.

(** Turn a map into a relation: **)
Definition graph {X Y: Type} (f: X -> Y) : X -> Y -> Prop
  := fun x y => f x = y.

Lemma ex_elim {E: Type} (Pred: E -> Prop) (Cons: Prop) :
  ((exists x : E, Pred x) -> Cons)
  <-> (forall x: E, Pred x -> Cons).
Proof.
  split; intro H; intros.
  - apply H. econstructor; eassumption.
  - destruct H0. apply (H x). assumption.
Qed.

Lemma app_strip_common_prefix {A : Type} (pref l1 l2: list A) :
  pref ++ l1 = pref ++ l2 -> l1 = l2.
Proof.
  induction pref; intros H; simpl in H.
  - assumption.
  - apply IHpref.
    (* surprisingly, the inversion performs a rewrite in the goal: *)
    inversion H. auto.
Qed.

Lemma app_yields_prefix {A : Type} (pref l: list A) :
  pref = pref ++ l -> l = nil.
Proof.
  pose (H:= app_strip_common_prefix pref l nil).
  rewrite app_nil_r in H.
  auto.
Qed.

(** simplify implications in hypotheses **)
Ltac simpl_impl :=
  repeat
  match goal with
  | [ H : nil <> nil -> _ |- _ ] => clear H
  | [ H : ?x = ?x -> _ |- _ ] => apply (fun b f => f b) in H; try reflexivity
  | [ H : ?x <> ?x |- _ ] => exfalso; apply H; reflexivity
  | [ H : False |- _ ] => contradiction H
  | [ H : True |- _ ] => clear H
  | [ H : ((cons ?hd ?tl <> nil) -> ?thus) |- _ ] =>
      let tmp := fresh "Tmp" in
      apply (fun b f => f b) in H; try (intro tmp; discriminate tmp)
  end.

Ltac copy_hyp source target :=
  assert (target := source).

Definition isNonEmpty {A: Type} (l: list A) : Prop
  := match l with
     | nil => False
     | _ => True
     end.

Theorem list_empty_or_not {A: Type} (l: list A) :
  l = nil \/ isNonEmpty l.
Proof.
  destruct l; [left|right]; simpl; auto.
Qed.

Lemma app_cons_nonempty {A: Type} (l l': list A) (a: A) :
  isNonEmpty (l ++ [a] ++ l').
Proof.
  destruct (l ++ [a] ++ l') eqn: Eq.
  eapply app_cons_not_nil. eauto.
  simpl. auto.
Qed.


Theorem list_eq_nil_tnd {A: Type} (l: list A) :
  l = nil \/ l <> nil.
Proof.
  destruct l; [left|right]; auto.
  discriminate.
Qed.

Definition ne_list (A: Type)
  := { l: list A | isNonEmpty l }.

Definition proj_nonempty {A: Type} : ne_list A -> list A
  := fun l => proj1_sig l.

Lemma eq_ne_list {A: Type} (l1 l2: ne_list A):
  proj_nonempty l1 = proj_nonempty l2 -> l1 = l2.
Proof.
  intro H.
  destruct l1. destruct l2.
  simpl in H.
  subst.
  unfold isNonEmpty in *.
  destruct x0; simpl in *.
  - contradiction.
  - destruct i. destruct i0.
    reflexivity.
Qed.

Definition if_is_empty {A: Type} : (list A) -> option (ne_list A).
Proof.
  intro l.
  destruct l.
  - apply None.
  - apply Some.
    exists (cons a l).
    simpl. auto.
Qed.

Lemma exists_nonempty_list {A: Type} {P: list A -> Prop} :
  (exists l: ne_list A, P (proj_nonempty l))
  <-> exists a: A, exists u: list A, P (cons a u).
Proof.
  split; intro H; destruct H.
  - destruct x. simpl in H.
    destruct x as [|a u].
    simpl in *.
    contradiction.
    exists a. exists u. assumption.
  - destruct H.
    unshelve eexists (exist _ (x :: x0) _); simpl; auto.
Qed.


Lemma lazy_and {P Q: Prop} :
  (P /\ Q) <-> (P /\ (P -> Q)).
Proof.
  split; intro H; destruct H.
  * split; auto.
  * split; auto.
Qed.

Ltac rewrite_premise hyp :=
  apply (fun b f => f b) in hyp.

Ltac destruct_conjunctions :=
  repeat
  match goal with
  | [ H: _ /\ _ |- _ ] => destruct H
  end.

Lemma nonempty_iff_not_nil {A: Type} (l: list A) :
  isNonEmpty l <-> l <> nil.
Proof.
  split; destruct l; intros H; simpl in H; auto.
  - discriminate.
  - exfalso. auto.
  - simpl. auto.
Qed.

Lemma list_extract_last {A: Type} :
    forall l : list A, l = [] \/ exists p: list A, exists a: A, l = p ++ [a].
Proof.
  intro l.
  induction l.
  - left. reflexivity.
  - right.
    inversion IHl.
    * (* singleton list *)
      exists []. exists a.
      subst. simpl.
      reflexivity.
    * destruct H. destruct H.
      exists (a::x). exists x0.
      subst.
      reflexivity.
Qed.

(** a variation of app_eq_app where the two sides of the disjunction are disjoint. **)
Lemma app_eq_app_disjoint {A: Type} (x1 x2 y1 y2: list A) :
     x1++x2 = y1++y2 ->
    exists l, (l <> [] /\ x1 = y1++l /\ y2 = l++x2) \/ (y1 = x1++l /\ x2 = l++y2).
Proof.
  intro H.
  apply app_eq_app in H.
  destruct H as [l ?].
  exists l.
  destruct (list_empty_or_not l) as [Eq_mid|Eq_mid].
  - (* l=[] *)
    right. subst. simpl. simpl in *.
    repeat (progress (rewrite app_nil_r in *)).
    split; destruct H as [H'|H']; destruct H'; auto.
  - destruct H; [left|right].
    * split.
      apply nonempty_iff_not_nil. assumption.
      assumption.
    * assumption.
Qed.


Fixpoint FiniteExists {B: Type} (l: list B) (P: B -> Prop)
  : Prop :=
  match l with
  | [] => False
  | [hd] => P hd
  | (hd :: tl) => P hd \/ FiniteExists tl P
  end.

Fixpoint FiniteExists2 {B: Type} (l: list B) (P: B -> Prop)
  : Prop :=
  match l with
  | [] => False
  | (hd :: tl) => P hd \/ FiniteExists2 tl P
  end.

Lemma FiniteExists2_eq  {B: Type} (l: list B) (P: B -> Prop) :
  FiniteExists l P <-> FiniteExists2 l P.
Proof.
  induction l.
  * simpl. auto. split; auto.
  * split; intro Hyp; simpl in Hyp.
    - destruct l. simpl. auto.
      destruct Hyp.
      simpl. auto.
      apply IHl in H.
      simpl. right. apply H.
    - destruct Hyp.
      simpl. destruct l; auto.
      apply IHl in H.
      simpl. destruct l. inversion H.
      right. auto.
Qed.

Theorem FiniteExistsDecidable {B: Type} {P: B -> Prop} {l: list B}:
  (forall b: B, decidable (P b)) ->
  (forall b: B, List.In b l)  ->
  decidable (FiniteExists l P).
Proof.
  intros P_dec B_fin.
  replace l with ([] ++ l) in B_fin; revgoals. {
    auto.
  }
  pose (s := []: list B).
  replace [] with s in B_fin; auto.
  revert B_fin.
  generalize s.
  clear s.
  induction l as [|b ?]; intros.
  - right. intro X. inversion X.
  - destruct (P_dec b).
    + left. simpl. destruct l; auto.
    + assert (decidable (FiniteExists l P)) as dec_in_l. {
        apply (IHl (s ++ [b])).
        rewrite <- app_assoc. simpl. auto.
      }
      destruct dec_in_l.
      * left. simpl. destruct l.
        ** inversion H0.
        ** right. auto.
      * right.
        intro Contr.
        apply FiniteExists2_eq in Contr.
        simpl in Contr.
        destruct Contr.
        contradiction.
        apply FiniteExists2_eq in H1.
        contradiction.
Qed.

Fixpoint prop_app_eq_fixed_list {A: Type} (l1 l2 l12: list A) : Type :=
    match l12 with
    | [] => False
    | (hd::tl) =>
      { a : A | a = hd & inhabited
                { l1': list A
                | l1 = (a::l1') & inhabited (prop_app_eq_fixed_list l1' l2 tl)
                } }
    end +{l1 = [] /\ l2 = l12}.

Theorem app_eq_fixed_list {A: Type} (l1 l2 l12: list A) :
  l1 ++ l2 = l12 -> prop_app_eq_fixed_list l1 l2 l12.
Proof.
  revert l1.
  induction l12; intros.
  - unfold_goal. right. apply app_eq_nil in H. destruct H. auto.
  - simpl. destruct l1. simpl in H. right. split; auto.
    left.
    simpl in H. inversion H. subst.
    exists a. constructor. constructor. exists l1. auto.
    constructor. auto.
Qed.

Theorem ShowFiniteExists {B: Type} {P: B -> Prop} {l: list B}:
  (forall b: B, List.In b l) -> (exists b: B, P b) -> FiniteExists l P.
Proof.
  intros Fin Ex.
  destruct Ex.
  assert (List.In x l). {
    apply Fin.
  }
  clear Fin.
  induction l; intros.
  - inversion H0.
  - destruct l.
    * inversion H0. subst.
      simpl. auto.
      inversion H1.
    * inversion H0.
      subst. simpl. left. auto.
      simpl. right. apply IHl. auto.
Qed.

Theorem ViaFiniteExists {B: Type} {P: B -> Prop} {l: list B}:
  (FiniteExists l P) -> (exists b: B, P b).
Proof.
  intros H.
  induction l as [|b ?]; simpl in H.
  - contradiction.
  - destruct l.
    exists b. auto.
    destruct H.
    * exists b. auto.
    * apply IHl. auto.
Qed.

Ltac autodestruct_once :=
  match goal with
    | [H: inhabited _ |- _] => destruct H
    | [H: ex _ |- _] => destruct H
    | [H: sig _ |- _] => destruct H
    | [H: sigT _ |- _] => destruct H
    | [H: sig2 _ _ |- _] => destruct H
    | [H: _ /\ _ |- _] => destruct H
    | [H: Some _ = Some _ |- _] => injection H as H
    | [H: (?a::?l) = (?b::?k) |- _] => injection H as H
    | [H: ?l = ?l |- _] => clear H
    | [H: ?l = [] |- _] => subst l
    | [H: ?l = [?x] |- _] => subst l
  end; try contradiction; try discriminate.

Ltac autodestruct := repeat autodestruct_once.

Ltac destruct_sum :=
  match goal with
  | [H: sumor _ _ |- _] => destruct H
  end; try contradiction; try discriminate.


Lemma push_forall_into_conjunction {X: Type} {P Q: X -> Prop} :
      (forall x: X, P x) /\ (forall x: X, Q x)
      -> (forall x: X, P x /\ Q x).
Proof.
  intuition.
Qed.

(** Apply the principle of short circuiting known from
   && and || in imperative languages: **)
Lemma short_circuit_conjunction {P Q: Prop} :
  P ->
  (P -> Q) ->
  P /\ Q.
Proof.
  intuition.
Qed.

Ltac forall_into_conjuncts :=
  repeat unfold_goal;
  repeat match goal with
  | [ H: _ |- ?P /\ ?Q] =>
      revert H; apply push_forall_into_conjunction
  end.

Ltac symmetric_cases_old :=
  forall_into_conjuncts;
  let Hyp := fresh "FirstConjunct" in
  apply short_circuit_conjunction; [|intro Hyp; intros; eapply Hyp; eauto].

Ltac symmetric_cases_recursive :=
  match goal with
  | [ H: ?T |- ?P /\ ?Q ] =>
      revert H;
      apply push_forall_into_conjunction;
      symmetric_cases_recursive;
      intro H
  | |- ?P /\ ?Q =>
      apply short_circuit_conjunction; revgoals;
      [
        let Hyp := fresh "FirstConjunct" in
        intro Hyp
      |]
  end.

Ltac symmetric_cases :=
  repeat unfold_goal;
  symmetric_cases_recursive;
  [ try match goal with
    | [H: _ |- _] =>
        eapply H; eauto; fail
    end
  |].


(** The [assert_in_subtype] tactic shows that ident is contained
in the given sigmatype / subtype and every occurence of ident
in the context is replaced with the subtyped version of ident:
 **)
Ltac assert_in_subtype ident subtype :=
  let H := fresh "assert" in
  let sub := fresh ident in
  let eq_sub := fresh "eq_sub_" ident in
  eassert (exists sub: subtype, proj1_sig sub = ident) as H;
    [ unshelve eexists (exist _ ident _);
      [simpl|simpl;reflexivity]
    | simpl; auto;
      destruct H as [sub eq_sub];
      subst ident;
      rename sub into ident
    ].

(** A tactic that detects when an inhabitant of the [False]
 type was constructed somewhere: **)
Ltac inner_contradiction :=
    match goal with
    | [H: context [ False_rect ?T ?F ] |- _] =>
        exfalso; apply F
    | |- context [ False_rect ?T ?F ] =>
        exfalso; apply F
    end.
