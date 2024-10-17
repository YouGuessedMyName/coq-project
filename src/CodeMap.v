Require Import Relations.
Require Import Lists.List.
Require Import Coq.Logic.FinFun.
Require Import ACUtil.
Require Import Coq.Logic.Decidable.

Import ListNotations.

(** * Preliminary Definitions **)

(** The inductive definition that one list is the prefix of another: **)
Inductive prefix_of {A: Type}
  : list A -> list A -> Prop :=
  | prefix_of_nil : forall (x: list A), prefix_of nil x
  | prefix_of_cons : forall (a : A) (x: list A) (y: list A),
      prefix_of x y -> prefix_of (cons a x) (cons a y).

(** This is equivalent to the existence of a summand that transforms
 the one list in the other: **)

Lemma prefix_of_app {A: Type} (s l: list A) :
  prefix_of s l <-> exists u: list A, (s ++ u) = l.
Proof.
  split.
  - revert l.
    induction s; intros.
    * exists l. simpl. reflexivity.
    * destruct l; inversion H; subst.
      apply IHs in H1.
      destruct H1.
      exists x. simpl.
      f_equal.
      assumption.
  - apply ex_elim.
    revert l.
    induction s; intros.
    * constructor.
    * destruct l; simpl in H; inversion H; subst.
      constructor.
      eapply IHs.
      reflexivity.
Qed.

(** In particular, `prefix_of` is a reflexive relation: **)
Corollary prefix_of_reflexive {A: Type} (l: list A) :
  prefix_of l l.
Proof.
  eapply prefix_of_app.
  exists nil.
  rewrite ->app_nil_r.
  reflexivity.
Qed.

Corollary prefix_of_transitive {A: Type} (l1 l2 l3: list A) :
  prefix_of l1 l2 -> prefix_of l2 l3 -> prefix_of l1 l3.
Proof.
  intros P1 P2.
  apply prefix_of_app in P1. destruct P1 as [d1].
  apply prefix_of_app in P2. destruct P2 as [d2].
  eapply prefix_of_app.
  exists (d1 ++ d2).
  rewrite ->app_assoc.
  rewrite H. rewrite H0.
  reflexivity.
Qed.

Corollary prefix_of_antisymmetric {A: Type} (l1 l2: list A) :
  prefix_of l1 l2 -> prefix_of l2 l1 -> l1 = l2.
Proof.
  intros P1 P2.
  apply prefix_of_app in P1. destruct P1 as [d1].
  apply prefix_of_app in P2. destruct P2 as [d2].
  replace l2 with (l2 ++ nil) in H; try apply app_nil_r.
  rewrite <-H0 in H.
  rewrite <-app_assoc in H.
  apply app_strip_common_prefix in H.
  apply app_eq_nil in H.
  destruct H. subst.
  apply app_nil_r.
Qed.

Definition dec_eq (A: Type) : Prop := forall a1 a2: A, a1 = a2 \/ a1 <> a2.

Proposition prefix_of_decidable {A: Type} {s l: list A}:
  dec_eq A -> decidable (prefix_of s l).
Proof.
  intro eq_A.
  revert l.
  induction s; intro l.
  - left. constructor.
  - destruct l.
    * right. intros pref. inversion pref.
    * destruct (eq_A a a0).
      + subst a0. destruct (IHs l).
        ** left. constructor; auto.
        ** right. intro Contr. inversion Contr. subst.
           contradiction.
      + right. intro Contr. inversion Contr. subst.
        contradiction.
Qed.


(** Often, we want to talk about prefixes of option (list A) with the meaning
     that we have a `prefix_of` relation pair if both lists are defined
    and the one is a prefix of the other. **)

(* Lift a relation between X and Y to the 'Some' values of option X and option Y *)
Inductive option_rel_lift {X Y : Type} (rel: X -> Y -> Prop) :
  option X -> option Y -> Prop
  := option_rel_some : forall x : X, forall y : Y, rel x y ->
          option_rel_lift rel (Some x) (Some y).

(** The [some_lift_pred P x] predicate holds iff [x] is
 of the shape [x = Some v] and [P v] holds: **)

Definition some_lift_pred {A: Type} : (A -> Prop) -> option A -> Prop
    := fun pred maybe =>
       match maybe with
       | Some v => pred v
       | None => False
       end.

(** * Definition: Codes as Maps **)
(** A [CodeMap] is just the raw function without any properties: **)
Definition CodeMap (A: Type) (B: Type)
  := B -> option (list A).

Definition is_some {A: Type} (value: option A): Prop
  := match value with
     | Some _ => True
     | None => False
     end.

Definition code_has_run {A B: Type} (R: CodeMap A B) (u: list A): Prop
  := exists b: B, some_lift_pred (prefix_of u) (R b).

Definition in_dom {A: Type} {B: Type} (R: CodeMap A B) : B -> Prop
  := fun b => is_some (R b).

Definition dom {A: Type} {B: Type} (R: CodeMap A B) : Type
  := { b: B | is_some (R b) }.

Definition proj_dom {A: Type} {B: Type} {R: CodeMap A B} : dom R -> B
  := fun x => proj1_sig x.

Definition total_code {A: Type} {B: Type} (R: CodeMap A B) : dom R -> list A.
  intro b.
  destruct b.
  destruct (R x).
  - apply l.
  - contradiction.
Defined.

(** The following notion captures that a word is a proper
    prefix of an [option] value. **)
Definition below_code {A: Type} (w: list A) (maybe_longer: option (list A)) : Prop :=
             match maybe_longer with
             | Some v => w <> v /\ prefix_of w v
             | _ => False
             end.

Lemma below_code_app {A B: Type} (w: list A) (R: CodeMap A B) (b: B) :
  below_code w (R b)
    <->
  exists a : A, exists u : list A, Some (w ++ (a::u)) = R b.
Proof.
  split.
  - intro H.
    case_eq_subst (R b).
    destruct H.
    apply prefix_of_app in H0.
    destruct H0. subst.
    destruct x.
    * rewrite ->app_nil_r in H. contradiction.
    * exists a. exists x. reflexivity.
  - apply ex_elim. intro a.
    apply ex_elim. intro u.
    intro H.
    case_eq_subst (R b).
    inversion H.
    subst.
    split.
    * intro.
      assert (w ++ [] = w ++ a :: u).
      rewrite ->app_nil_r.
      assumption.
      apply app_strip_common_prefix in H1.
      discriminate.
    * apply prefix_of_app.
      exists (a::u).
      reflexivity.
Qed.

Lemma below_code_app_nonempty {A B: Type} (w: list A) (R: CodeMap A B) (b: B) :
  below_code w (R b)
    <->
  exists l: ne_list A, Some (w ++ proj_nonempty l) = R b.
Proof.
  pose (P := fun (l: list A) => Some (w ++ l) = R b).
  split; intro H.
  - apply (@exists_nonempty_list A P).
    apply below_code_app.
    assumption.
  - apply (@exists_nonempty_list A P) in H.
    apply below_code_app.
    assumption.
Qed.


(** The property of [prefix_free]ness is the central property of
    the code maps considered:
 **)

Definition prefix_free {A: Type} {B: Type}
  (code: CodeMap A B) : Prop
  := forall (b b' : B),
      (option_rel_lift prefix_of (code b) (code b')) -> (b = b').

(** The property that the code consists of only non-empty words; in the paper,
  this is directly encoded in the return type. Here, we have it as an extra
  property, because working with [list] is well-supported in Coq.
  **)
Definition code_ne_word {A: Type} {B: Type}
  (code: CodeMap A B) : Prop
  := forall (b : B), code b <> Some nil.

(** A [Code] is a [CodeMap] with the above to properties: **)
Inductive Code (A B: Type) : Type :=
  Build_Code : forall code : CodeMap A B,
      code_ne_word code -> (* every A-word in the code is non-empty *)
      prefix_free code ->
      Code A B.

Definition code_proj {A: Type} {B: Type} (R: Code A B) : B -> option (list A).
Proof.
  destruct R as [code].
  apply code.
Defined.

Definition proj_code_prefix_free {A B: Type} (R: Code A B) :
  prefix_free (code_proj R).
Proof. destruct R. simpl. auto. Qed.

Definition proj_code_ne_word {A B: Type} (R: Code A B) :
  code_ne_word (code_proj R).
Proof. destruct R. simpl. auto. Qed.

Coercion code_proj : Code >-> Funclass.

Lemma code_delta_empty {A B: Type} (R: Code A B) :
  forall (b b': B) (w v: list A),
    R b = Some w
    -> R b' = Some (w ++ v)
    -> v = [].
Proof.
  intros *.
  intros EqRb EqRb'.
  assert (b = b'). {
    eapply proj_code_prefix_free.
    rewrite EqRb.
    rewrite EqRb'.
    constructor.
    apply prefix_of_app.
    exists v.
    reflexivity.
  }
  subst.
  rewrite EqRb in EqRb'.
  inversion EqRb'.
  eapply app_strip_common_prefix.
  symmetry.
  rewrite app_nil_r.
  eassumption.
Qed.

(** The entirely undefined map is a code: **)
Example EmptyCode (A B: Type) : Code A B.
Proof.
  eapply (Build_Code _ _ (fun _ => None)).
  - intros ? ?. discriminate.
  - intros ? ? H. inversion H.
Defined.

(** * Kleisli extension **)

(** We define the Kleisli extension of a code map, and then will
    use that in the composition of codes. **)

Fixpoint kleisli_ext {A B: Type} (R: CodeMap A B) (b_list: list B)
     : option (list A)
  := match b_list with
     | nil => Some nil
     | b :: b_tail =>
         match R b with
         | None => None
         | Some a_list =>
             option_map (fun x => a_list ++ x) (kleisli_ext R b_tail)
         end
     end.

Notation "R ^*" := (kleisli_ext R) (at level 40, no associativity) : type_scope.

(** [option] as an applicative functor: **)
Definition option_fapp {A B: Type}: option (A -> B) -> option A -> option B
    := fun maybe_f maybe_a =>
         match (maybe_f, maybe_a) with
         | (Some f, Some a) => Some (f a)
         | _ => None
         end.

(** The following notation is borrowed from Haskell's notation of fapp: **)
Notation "f <*> g" := (option_fapp f g) (at level 40, left associativity).
(*
Notation "f <$> g" := (option_map f g) (at level 40, left associativity).
*)

(** In the following, we establish a series of results about [kleisli_ext],
    which are used for composed codes here and for results about code
    composition in other files. **)
Theorem kleisli_ext_app {A B: Type} (R: CodeMap A B) (l1 l2: list B):
  (kleisli_ext R (app l1 l2)) = Some (@app A) <*> (kleisli_ext R l1) <*> (kleisli_ext R l2).
Proof.
  induction l1 as [|b].
  - simpl. unfold option_fapp.
    simpl. destruct (R^* l2); auto.
  - simpl.
    rewrite ->IHl1.
    unfold option_map.
    destruct (R b) eqn: Hb; try auto.
    destruct (R^* l1) eqn: Hl1; auto.
    destruct (R^* l2) eqn: Hl2; auto.
    unfold option_fapp.
    rewrite <-app_assoc.
    reflexivity.
Qed.

(** This just checks that the kleisli extenion has the right type: **)
Definition theorem_kleisli_ext_is_a_codemap {A B: Type} (R: CodeMap A B)
  : CodeMap A (list B)
  := R^*.

(**
 In the following property, the abbreviated variable names have the following
 meaning:
 - ps = prefix of short list.
 - ss = suffix of short list.
 - pl = prefix of long list.
 - sl = suffix of long list.
 **)
Lemma prefix_of_prefixes {A : Type} (ps ss pl sl: list A) :
  prefix_of (ps ++ ss) (pl ++ sl) ->
  prefix_of ps pl \/ prefix_of pl ps.
Proof.
  (* make pl forall-quantified in the induction hyp. *)
  generalize pl. clear pl.
  induction ps.
  * left. constructor.
  * destruct pl.
    right. constructor.
    intro Pref.
    rewrite <-app_comm_cons in Pref.
    rewrite <-app_comm_cons in Pref.
    inversion Pref.
    apply  IHps in H0.
    destruct H0; eapply prefix_of_cons in H0; eauto.
Qed.

Lemma strip_common_prefix {A : Type} (pref l1 l2: list A) :
  prefix_of (pref ++ l1) (pref ++ l2) -> prefix_of l1 l2.
Proof.
  induction pref.
  - simpl. auto.
  - simpl. intro H. inversion H.
    apply IHpref.
    assumption.
Qed.


(** If R^*: list B -> option (list A) is the kleisli lift, then
   whenever (R^* bs1) `prefix_of` (R^* bs2) then bs1 `prefix_of` bs2.
  this also indicates that the kleisli extension of a prefix_free CodeMap
 is itself not necessarily prefix_free.
 **)
Lemma code_kleisli_ext_prefix_reflection {A B : Type} (R: CodeMap A B) :
  code_ne_word R ->
  prefix_free R -> forall bs1 bs2 : list B,
      option_rel_lift prefix_of (R^* bs1) (kleisli_ext R bs2)
      -> prefix_of bs1 bs2.
Proof.
  intro R_ne_word.
  intro R_prefix_free.
  induction bs1. (* keep bs2 forall-quantified in the induction hyp *)
  + simpl. constructor.
  + simpl. intros *. intro Pref.
    (* R^*(bs2) must also be defined *)
    case_eq_subst (kleisli_ext R bs1);
      case_eq_subst (R a);
      inversion Pref.
    subst x.
    rewrite <-H0 in Pref.
    destruct bs2.
    * (* The case `bs2 = nil` is contradictory *)
      simpl in H0.
      inversion H0.
      subst.
      inversion H1.
      exfalso.
      destruct l0.
      *** eapply R_ne_word. eassumption.
      *** rewrite <-app_comm_cons in Pref.
          inversion Pref.
          inversion H5.
    * (* bs2 -> b :: bs2 *)
      inversion Pref.
      simpl in H0.
      case_eq_subst (R b); try case_eq_subst (kleisli_ext R bs2).
      inversion H0. subst.
      apply prefix_of_prefixes in H3.
      replace b with a in *.
      - apply prefix_of_cons.
        apply IHbs1.
        rewrite ->CaseEq2.
        constructor.
        (* we now only need to strip the common prefixes *)
        rewrite ->CaseEq0 in CaseEq1. inversion CaseEq1. subst.
        apply strip_common_prefix in H1.
        assumption.
      - (* show that a = b *)
        destruct H3 ; [|symmetry].
          (* the two cases are symmetric, either (R a) is a prefix of (R b) *)
          (* or the other way round, so lets just swap a=b to b=a in one of *)
          (* the goals *)
        (* then in both cases we can do: *)
        all: apply R_prefix_free; rewrite ->CaseEq0; rewrite ->CaseEq1; constructor; assumption.
Qed.

Lemma kleisli_ext_preserves_nonempty {A B: Type} (R: Code A B) (l: list B) :
  isNonEmpty l -> forall R_l : list A, Some R_l = R^* l -> isNonEmpty R_l.
Proof.
  destruct l.
  - intros H; simpl in H; contradiction.
  - intros. simpl in H0.
    destruct (R b) eqn: HRb;
    destruct (R^* l) eqn: HRl; simpl in H0; try (discriminate H0).
    inversion H0.
    subst.
    destruct R as [R R_ne].
    destruct l0 eqn: Hl0.
    * exfalso. apply (R_ne b). assumption.
    * simpl. auto.
Qed.

Lemma kleisli_ext_preserves_neq_nil {A B: Type} (R: Code A B) (l: list B) :
  l <> nil -> forall R_l : list A, Some R_l = R^* l -> R_l <> nil.
Proof.
  intros P Rl Q.
  apply nonempty_iff_not_nil.
  eapply kleisli_ext_preserves_nonempty.
  eapply nonempty_iff_not_nil.
  eassumption.
  eassumption.
Qed.

Lemma kleisli_ext_reflects_empty {A B: Type} (R: Code A B) (l: list B) :
  ((R^*) l) = Some nil -> l = nil.
Proof.
  destruct (list_empty_or_not l).
  * auto.
  * intro EqRl.
    symmetry in EqRl.
    eassert (isNonEmpty nil). {
      eapply kleisli_ext_preserves_nonempty.
      eassumption.
      eassumption.
    }
    simpl in *.
    contradiction.
Qed.

Definition does_not_start_with_codeword {A B: Type} {R: Code A B} (l: list A) : Prop
    := (forall b: B, ~(option_rel_lift prefix_of (R b) (Some l))).

Example nil_does_not_start_with_codeword {A B: Type} (R: Code A B) :
  does_not_start_with_codeword (R:=R) nil.
Proof.
  intros b H.
  destruct R as [R NotEmpty ?].
  simpl in *.
  destruct (R b) eqn: EqRb; inversion H.
  subst.
  inversion H2. subst.
  eapply NotEmpty.
  eassumption.
Qed.

Lemma kleisli_ext_not_prefix {A B: Type} (R: Code A B) :
  forall (l: list B) (R_l suff: list A),
    (R^* l) = Some R_l
    -> does_not_start_with_codeword (R:=R) (R_l ++ suff)
    -> l = nil.
Proof.
  intros.
  destruct l; auto.
  (* the remaining case is contradictory: *)
  exfalso.
  apply H0 with (b:=b).
  simpl in H.
  destruct (R b) as [R_b|] eqn: HR_b; try discriminate.
  destruct (R^* l) as [Rstar_l|]; try discriminate.
  inversion H.
  constructor.
  rewrite <-app_assoc.
  apply prefix_of_app.
  eexists.
  auto.
Qed.

Lemma kleisli_ext_injective_with_suffix {A B: Type} (R: Code A B) :
  forall (l1 l2: list B) (Rl1 Rl2 suff1 suff2: list A),
    does_not_start_with_codeword (R:=R) suff1
    -> does_not_start_with_codeword (R:=R) suff2
    -> R^* l1 = Some Rl1
    -> R^* l2 = Some Rl2
    -> Rl1 ++ suff1 = Rl2 ++ suff2
       -> l1 = l2.
Proof.
  intros ? ? ? ? ? ? P_suff1 P_suff2.
  revert l1 l2 Rl1 Rl2.
  induction l1 as [|b1 tl1]; intros.
  - simpl in H0.
    simpl in H.
    inversion H. subst.
    simpl in H1.
    symmetry.
    eapply kleisli_ext_not_prefix.
    * eassumption.
    * rewrite <-H1. apply P_suff1.
  - destruct l2 as [|b2 tl2]. {
      (* first case is contradictory *)
      simpl in H0.
      inversion H0.
      subst.
      simpl in H1.
      eapply kleisli_ext_not_prefix.
      * eassumption.
      * rewrite ->H1. apply P_suff2.
    }
    simpl in H0.
    destruct (R b1) as [R_b1|] eqn: Eq_R_b1;
    destruct (R b2) as [R_b2|] eqn: Eq_R_b2;
      simpl in H;
      rewrite ->Eq_R_b1 in H;
      (* (R b1) and (R b2) can't be None: *)
      try discriminate.
    destruct (R^* tl1) as [R_tl1|] eqn: Eq_R_tl1; simpl in H; try discriminate.
    destruct (R^* tl2) as [R_tl2|] eqn: Eq_R_tl2; simpl in H0; try discriminate.
    inversion H.
    inversion H0.
    assert (b1 = b2). {
      subst.
      repeat (rewrite <-app_assoc in H1).
      apply app_eq_app in H1.
      destruct H1 as [l ?].
      destruct R as [R ? R_prefix_free].
      unfold prefix_free in R_prefix_free.
      destruct H1; [symmetry|]; apply R_prefix_free;
        simpl in Eq_R_b1;
        simpl in Eq_R_b2;
        rewrite ->Eq_R_b1;
        rewrite ->Eq_R_b2;
        constructor;
        apply prefix_of_app;
        exists l.
      +++ destruct H1. auto.
      +++ destruct H1. auto.
    }
    replace b2 with b1 in *.
    (* if b1=b2, then R_b1=R_b2: *)
    rewrite ->Eq_R_b1 in Eq_R_b2.
    inversion Eq_R_b2.
    replace R_b2 with R_b1 in *; auto.
    (* lets solve the goal: *)
    f_equal.
    eapply IHtl1.
    reflexivity.
    eassumption.
    rewrite <-H3 in H1.
    rewrite <-H4 in H1.
    repeat (rewrite <-app_assoc in H1).
    apply app_strip_common_prefix in H1.
    assumption.
Qed.

Corollary kleisli_ext_injective_on_dom {A B: Type} (R: Code A B) :
  forall l1 l2: list B, R^* l1 <> None ->
                 R^* l1 = R^* l2
                          -> l1 = l2.
Proof.
  intros.
  destruct (R^* l1) eqn: Eql1; try contradiction.
  destruct (R^* l2) eqn: Eql2; try contradiction.
  eapply kleisli_ext_injective_with_suffix with (suff1:=nil) (suff2:=nil) (R:=R).
  - apply nil_does_not_start_with_codeword.
  - apply nil_does_not_start_with_codeword.
  - eassumption.
  - eassumption.
  - inversion H0. auto.
Qed.

(** * Code composition **)
(** The code composition is the kleisli extension of code1 w.r.t. lists combined
 with the kleisli extension of code1 w.r.t. [option]. We didn't define the latter explicitly,
 so we verbosely write it as a match here: **)
Definition compose_codemap {A B C: Type} (code1: CodeMap A B) (code2: CodeMap B C) : CodeMap A C
  := fun c =>
    match (code2 c) with
    | None => None
    | Some bs => kleisli_ext code1 bs
    end.

Lemma composed_code_ne_word {A B C: Type} (R: CodeMap A B) (S: CodeMap B C) :
  code_ne_word R -> code_ne_word S -> code_ne_word (compose_codemap R S).
Proof.
  intro R_ne_word.
  intro S_ne_word.
  intro c.
  unfold compose_codemap.
  pose (H := S_ne_word c).
  generalize H.
  clear H.
  destruct (S c).
  - destruct l.
    + intro H. eauto.
    + intro H. simpl.
      pose (RbNE := R_ne_word b).
      generalize RbNE.
      clear RbNE.
      destruct (R b).
      destruct l0.
      * auto.
      * unfold option_map.
        destruct (kleisli_ext R l); auto; intros; discriminate.
      * simpl. auto.
  - intro. discriminate.
Qed.


Lemma composed_code_prefix_free {A B C: Type} (R: CodeMap A B) (S: CodeMap B C) :
  code_ne_word R ->
  prefix_free R -> prefix_free S -> prefix_free (compose_codemap R S).
Proof.
  intro R_ne_word.
  intro R_pref_free.
  intro S_pref_free.
  unfold prefix_free.
  intros c c'.
  unfold compose_codemap.
  case_eq_subst (S c); try case_eq_subst (S c'); intro Pref.
  - apply S_pref_free.
    rewrite ->CaseEq.
    rewrite ->CaseEq0.
    constructor.
    eapply code_kleisli_ext_prefix_reflection; eassumption.
  - inversion Pref.
  - inversion Pref.
  - inversion Pref.
Qed.

Theorem code_closed_under_composition
    {A B C: Type} (R: Code A B) (S: Code B C) :
  exists RS : Code A C, code_proj RS = compose_codemap R S.
Proof.
  pose (compose_codemap R S) as RS_map.
  unshelve epose (RS := _ : Code A C).
  apply (Build_Code A C RS_map).
  - apply composed_code_ne_word.
    destruct R; auto.
    destruct S; auto.
  - apply composed_code_prefix_free;
      destruct R; destruct S; auto.
  - exists RS. simpl. trivial.
Qed.

Definition compose_code {A B C: Type} (R: Code A B) (S: Code B C) : Code A C.
Proof.
  destruct R as [R_map].
  destruct S as [S_map].
  apply Build_Code with (code := compose_codemap R_map S_map).
  apply composed_code_ne_word; assumption.
  apply composed_code_prefix_free; assumption.
Defined.

Theorem compose_code_comm_proj {A B C: Type} (R: Code A B) (S: Code B C) :
  compose_codemap R S = compose_code R S.
Proof.
  unfold compose_code.
  destruct R.
  destruct S.
  simpl.
  reflexivity.
Qed.

