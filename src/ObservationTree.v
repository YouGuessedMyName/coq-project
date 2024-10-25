Require Import Mealy.
Require Import FunctionalSimulation.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Finite_sets_facts.

(* Definition 2.5 (Observation tree) *)
Definition tree (M : Mealy) : Prop
  := forall v : word I, del M (q0 M) v = Some v.

Definition access (M : Mealy) (v : word I) : word I := v.

Definition accessSet {M : Mealy} (U: Y -> Prop): (word I -> Prop)
  := U.

(* q' is the parent of q *)
Definition parent {M : Mealy} (q q' : Y) : Prop
  := exists i : I, del M q' (i :: nil) = Some q.

(* T is an observation tree for M *)
Definition observationTreeFor (T : Mealy) (M : Mealy) : Prop
  := exists f : (Y -> Y), funcSim T M f.

(* Definition 2.7 (Test suites) *)
(* v is a test case for S *)
Definition testCase (v : word I) (S : Mealy) := def (tra S (q0 S) v).

(* T is a test suite for S *)
Definition testSuite (T : word I -> Prop) (S : Mealy) := 
    Finite (word I) T /\ forall v : word I, T v -> testCase v S.

(* M passes test v for S *)
Definition passes1 (S M : Mealy) (v : word I) :=
  lam M (q0 S) v = lam M (q0 M) v.

(* M passes test suite T for S *)
Definition passes2 (S M : Mealy) (T : word I -> Prop) :=
  forall v : word I, T v -> passes1 S M v.

(* TT is a testing tree for test suite T and Mealy machine S *)
Definition testingTree (TT S : Mealy) (T : word I -> Prop) : Prop :=
tree TT /\
(* QT = {ϵ} ∪ Pref (T ) and qT0 = ϵ,*)
(forall A : word I -> Prop, Pref A T -> A = Q TT) /\
(* For all σ ∈ I∗ and i ∈ I with σi ∈ QT , δT (σ, i) = σi, *)
(forall v : word I, forall i : I, 
    del TT v (i :: nil) = Some (v ++ i :: nil)) /\
(* For all σ ∈ I∗ and i ∈ I with σi ∈ QT , λT (σ, i) = λS (δS (qS0 , σ), i).*)
(forall v : word I, forall q : Y, forall i : I,
    (del S (q0 S) v) = Some q ->
      lam TT v (i :: nil) = lam S q (i :: nil)
).

Lemma del_lam_tra :
forall M : Mealy,
forall q s : Y,
forall v : word I,
forall V : word O,
  del M q v = Some s /\ lam M q v = Some V
<->
  tra M q v = Some (s, V).
Proof.
intros.
split.
- intro H. destruct H as [H H'].
  destruct option_em with (prod Y (word O)) (tra M q v) as [J|J].
  * unfold del in H. rewrite J in H. discriminate H.
  * destruct J as [(s', V') J].
    unfold lam in H'. rewrite J in H'. injection H' as H'.
    unfold del in H. rewrite J in H. injection H as H.
  rewrite<- H. rewrite<- H'. apply J.
- intro H. unfold del. unfold lam. rewrite H. split. trivial. trivial.
Qed.

Lemma tra_trans_def_no_exi :
forall M : Mealy,
forall q s : Y,
forall i : I,
forall o : O,
  tra M q (i :: nil) = Some (s, o :: nil) 
 <-> 
    trans M q i = Some (s, o).
Proof.
intros.
split.
+ destruct option_em with (prod Y O) (trans M q i).
  - intro J. unfold tra in J. rewrite H in J. discriminate J.
  - intro J. destruct H as [(s', o')]. unfold tra in J. rewrite H in J.
    injection J as J. rewrite H. rewrite J. rewrite H0. trivial.
+ intro H. unfold tra. rewrite H. trivial.
Qed.

Search "lemma_a_1".

(* r = δ(q, i) *)
Lemma lemma_2_9 : 
forall S TT : Mealy, 
forall T : word I -> Prop,
forall f: Y -> Y,
        testingTree TT S T 
      -> 
        (forall r v : Y, 
          del TT (q0 TT) v = Some r -> del S (q0 S) v = Some (f r))
  ->
    funcSim TT S f.
Proof.
intros S TT T f Htt Hf.
unfold funcSim.
unfold testingTree in Htt. destruct Htt as [Htt Htt0]. 
destruct Htt0 as [Htt0 Htt1]. destruct Htt1 as [Htt1 Htt2].
unfold tree in Htt. 
split.
- specialize Hf with nil nil.
  specialize Htt with nil. injection Htt as Htt. rewrite Htt in Hf. 
  unfold del in Hf. unfold tra in Hf. rewrite Htt. symmetry. 
  injection Hf. trivial. trivial.
- intros q r i o H_qi_r.
  symmetry.
  rewrite<- tra_trans_def_no_exi.
  rewrite<- del_lam_tra.
  assert (H_qi_r2 := H_qi_r).
  rewrite <- tra_trans_def_no_exi in H_qi_r2. 
  rewrite<- del_lam_tra in H_qi_r2.
  destruct H_qi_r2 as [H_qi_del H_qi_lam].
  (* Step 1 *)
  assert (Htt1' := Htt1).
  specialize Htt1 with q i.
  assert (Hr_qi := H_qi_del).
  rewrite Htt1 in Hr_qi.
  injection Hr_qi as Hr_qi.
  (* Step 2 *)
  assert (Hf' := Hf).
  specialize Hf with r r. rewrite<- Hf. rewrite<- Hr_qi.
  (* Step 3 (Using Lemma) *)
    (* Case where tra S (q0 S) q undef *)
    destruct option_em with (prod Y (word O)) (tra S (q0 S) q) as [J|J].
    specialize Hf' with q q. specialize Htt with q. apply Hf' in Htt.
    unfold del in Htt. rewrite J in Htt. discriminate Htt.
  destruct J as [(fq, Q') J].
  destruct lemma_a_1 with S q (i :: nil) Q' (q0 S) (f q) as [Hl_del Hl_lam].
  + specialize Hf' with q q.
    assert (Htt' := Htt).
    specialize Htt with q.
    apply Hf' in Htt.
    unfold del in Htt.
    rewrite J in Htt.
    injection Htt as Htt.
    rewrite<- Htt.
    apply J.
  + rewrite<- Hl_del. split. 
    * trivial.
    * assert (Htt2' := Htt2).
      specialize Htt2 with q (f q) i.
      symmetry.
      rewrite<- Htt2.
      rewrite H_qi_lam.
      trivial.
      specialize Hf' with q q.
      specialize Htt with q.
      apply Hf' in Htt.
      apply Htt.
  + rewrite Htt. trivial.
Qed.
    

Lemma lemma_2_10 :
forall S M TT : Mealy,
forall T : word I -> Prop,
forall f : Y -> Y,
forall r v : Y, 
  testingTree TT S T
->
  del TT (q0 TT) v = Some r -> del S (q0 S) v = Some (f r)
->
  (funcSim TT M f
<->
  passes2 M TT T).
Proof.
intros.
split.
intro J.
unfold passes2.
unfold passes1.
intro u.
intro T_u.

Abort.
(* TODO definition of funcSim needs to be changed 
to only be relevant to actual states, not the whole type... *)
 
