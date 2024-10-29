(* Require Import Mealy.
Require Import FunctionalSimulation.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Finite_sets_facts.

(* Definition 2.5 (Observation tree) *)
Definition tree (M : Mealy) : Prop
  := forall v : word I, 
    Q M v->    
    del M (q0 M) v = Some v.

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
(Pref (Q TT) T) /\
(* For all σ ∈ I∗ and i ∈ I with σi ∈ QT , δT (σ, i) = σi, *)
(forall v : word I, forall i : I,
  Q TT (v ++ i :: nil) ->
    del TT v (i :: nil) = Some (v ++ i :: nil)) 
/\
(* For all σ ∈ I∗ and i ∈ I with σi ∈ QT , λT (σ, i) = λS (δS (qS0 , σ), i).*)
(forall v : word I, forall q : Y, forall i : I,
  Q TT (v ++ i :: nil) ->
    (del S (q0 S) v) = Some q ->
      lam TT v (i :: nil) = lam S q (i :: nil)
).



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
unfold testingTree in Htt. destruct Htt as [Htree Hstates]. 
destruct Hstates as [Hstates HtreeDelta]. destruct HtreeDelta as [HHtreeDelta HtreeLambda].
unfold tree in Htree. 
unfold funcSim.
split.
- specialize Hf with nil nil.
  specialize Htree with nil.
  admit.
(*    injection Htree as Htree. rewrite Htree in Hf. 
  unfold del in Hf. unfold tra in Hf. rewrite Htree. symmetry. 
  injection Hf. trivial. trivial. *)
- intros q r i o H_qInTree H_q_io_r.
  symmetry.
  rewrite<- tra_trans_def_no_exi.
  rewrite<- del_lam_tra.
  assert (H_q_io_r2 := H_q_io_r).
  rewrite <- tra_trans_def_no_exi in H_q_io_r2. 
  rewrite<- del_lam_tra in H_q_io_r2.
  destruct H_q_io_r2 as [H_q_io_del H_q_io_lam].
  (* Step 1 *)
  assert (HHtreeDelta_q_i := HHtreeDelta).
  specialize HHtreeDelta_q_i with q i.
  assert (H_r_is_qi := H_q_io_del).
  rewrite HHtreeDelta_q_i in H_r_is_qi.
  injection H_r_is_qi as H_r_is_qi.
  (* Step 2 *)
  assert (Hf_r_r := Hf).
  specialize Hf_r_r with r r. rewrite<- Hf_r_r. rewrite<- H_r_is_qi.
  (* Step 3 (Using Lemma) *)
    (* Case where tra S (q0 S) q undef *)
    destruct option_em with (prod Y (word O)) (tra S (q0 S) q) as [J|J].
    specialize Hf with q q. specialize Htree with q. apply Hf in Htree.
    unfold del in Htree. rewrite J in Htree. discriminate Htree.
    apply H_qInTree.
  destruct J as [(fq, Q') J].
  destruct lemma_a_1 with S q (i :: nil) Q' (q0 S) (f q) as [Hl_del Hl_lam].
  + assert (Hf_q_q := Hf).
    specialize Hf_q_q with q q.
    assert (Htree_q := Htree).
    specialize Htree_q with q.
    apply Hf_q_q in Htree_q.
    unfold del in Htree_q.
    rewrite J in Htree_q.
    injection Htree_q as Htree_q.
    rewrite<- Htree_q.
    apply J.
    apply H_qInTree.
  + rewrite<- Hl_del. split. 
    * trivial.
    *
      assert (HtreeLambda_q_fq_i := HtreeLambda).
      specialize HtreeLambda_q_fq_i with q (f q) i.
      rewrite<- HtreeLambda_q_fq_i.
      rewrite H_q_io_lam.
      trivial.
      ** unfold Q. exists (q ++ i :: nil). unfold del.
      destruct option_em with (prod Y (word O)) (tra TT (q0 TT) (q ++ i :: nil)).
      admit. (* TODO make a lemma for this *)
      **
      assert (Hf_q_q := Hf).
      specialize Hf_q_q with q q.
      assert (Htree_q := Htree).
      specialize Htree_q with q.
      apply Hf_q_q in Htree_q.
      apply Hf_q_q.
      rewrite Htree.
      trivial.
      apply H_qInTree.
      apply H_qInTree.
  + rewrite Htree. trivial. admit. (* TODO make a lemma for this *)
  + unfold Q. exists (q ++ i :: nil). rewrite Htree. trivial.
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
to only be relevant to actual states, not the whole type... *) *)
 
 *)