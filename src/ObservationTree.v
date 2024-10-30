Require Import Mealy.
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
  lam S (q0 S) v = lam M (q0 M) v.

(* M passes test suite T for S *)
Definition passes2 (S M : Mealy) (T : word I -> Prop) :=
  forall v : word I, T v -> passes1 S M v.

(* A is a prefix-closed set *)
Definition PrefClosed (A : word I -> Prop) : Prop :=
forall a b : word I, A a /\ pref b a -> A b.

(* TT is a testing tree for test suite T and Mealy machine S *)
Definition testingTree (TT S : Mealy) (T : word I -> Prop) : Prop :=
tree TT /\ 
(* QT = {ϵ} ∪ Pref (T ) and qT0 = ϵ,*)
(Q TT = T /\ PrefClosed T /\ q0 TT = nil) /\
(* For all σ ∈ I∗ and i ∈ I with σi ∈ QT , δT (σ, i) = σi, *)
(forall v : word I, forall i : I,
  Q TT v ->
    del TT v (i :: nil) <> None -> del TT v (i :: nil) = Some (v ++ i :: nil)) 
/\
(* For all σ ∈ I∗ and i ∈ I with σi ∈ QT , λT (σ, i) = λS (δS (qS0 , σ), i).*)
(forall v : word I, forall q : Y, forall w : word I,
  Q TT (v ++ w) ->
    (del S (q0 S) v) = Some q ->
      lam TT v w = lam S q w
).

Lemma next_state :
forall M : Mealy,
forall q r : Y,
forall i : I,
Q M q 
-> del M q (i :: nil) = Some r
-> Q M r.
Proof.
intros M q r i H J.
unfold Q in H. destruct H as [v H].
unfold Q. exists (v ++ i :: nil).
rewrite<- J.
apply lemma_a_1_delta. apply H.
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
- specialize Hf with (q0 TT) nil. unfold del in Hf. unfold tra in Hf.
  injection Hf as Hf'. symmetry in Hf'. apply Hf'. trivial.
- intros q r i o H_qInTree H_q_io_r.
  symmetry.
  rewrite<- tra_trans_def_known.
  rewrite<- del_lam_tra_def.
  assert (H_q_io_r2 := H_q_io_r).
  rewrite<- tra_trans_def_known in H_q_io_r2.
  rewrite<- del_lam_tra_def in H_q_io_r2.
  destruct H_q_io_r2 as [H_q_io_del H_q_io_lam].
  (* Step 1 *)
  assert (HHtreeDelta_q_i := HHtreeDelta).
  specialize HHtreeDelta_q_i with q i.
  assert (H_r_is_qi := H_q_io_del).
    destruct option_em with Y (del TT q (i :: nil)). rewrite H in H_q_io_del. discriminate H_q_io_del. 

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
    * assert (HtreeLambda_q_fq_i := HtreeLambda).
      specialize HtreeLambda_q_fq_i with q (f q) (i :: nil).
      rewrite<- HtreeLambda_q_fq_i.
      **  rewrite H_q_io_lam.
          trivial.
      **  rewrite H_r_is_qi. apply (next_state TT q r i). apply H_qInTree. apply H_q_io_del.
      **  assert (Hf_q_q := Hf).
          specialize Hf_q_q with q q.
          assert (Htree_q := Htree).
          specialize Htree_q with q.
          apply Hf_q_q in Htree_q.
          apply Hf_q_q.
          rewrite Htree.
          trivial.
          apply H_qInTree.
          apply H_qInTree.
  + rewrite Htree. 
    * trivial. 
    * apply (next_state TT q r i). apply H_qInTree. apply H_q_io_del.
  + apply H_qInTree.
  + destruct H as [q' H]. rewrite H. discriminate.
Qed.
    

Lemma r_is_qi :
forall TT : Mealy,
forall q r : Y,
forall i : I,
forall o : O,
Q TT q 
->
(forall (v : word I) (i : I),
              Q TT v ->
              del TT v (i :: nil) <> None ->
              del TT v (i :: nil) = Some (v ++ i :: nil))
->
(trans TT q i = Some (r, o))
->
(r = q ++ i :: nil).
Proof.
intros TT q r i o H_QTTq H_treeDelta H_q_io_r.
assert (temp := (H_treeDelta q i)).
assert (H_r_is_qi := H_QTTq).
apply temp in H_r_is_qi. clear temp.
+ unfold del in H_r_is_qi. unfold tra in H_r_is_qi. rewrite H_q_io_r in H_r_is_qi.
  injection H_r_is_qi. trivial.
+ unfold del. unfold tra. rewrite H_q_io_r. discriminate.
Qed.

Lemma list_tl_property :
forall A : Set,
forall o : A,
forall la lb : list A,
la <> nil ->
(tl la) ++ lb = tl (la ++ lb).
Proof.
intros.
induction la.
elim H. trivial.
simpl. trivial.
Qed.

Lemma lemma_q_1_lambda_part :
forall M : Mealy, 
forall v w : word I,
forall V W : word O,
forall q s : Y,
      tra M q v = Some (s, V)
  ->
        lam M q (v ++ w) = Some (V ++ W)
    ->
        lam M s w = Some W
.
Proof.
induction v.
- intros. unfold tra in H. injection H as H H'. rewrite<- H' in H0.
  simpl (nil ++ w) in H0. simpl (nil ++ W) in H0. rewrite H in H0. apply H0.
- intros.
  destruct option_em with (prod Y O) (trans M q a).
  unfold tra in H. rewrite H1 in H. discriminate H.
  destruct H1 as [(r, o) H1].

  destruct option_em with (prod Y (word O)) (tra M r v) as [J | J].
  unfold tra in H. rewrite H1 in H. 
  unfold tra in J. rewrite J in H. discriminate H.
  
  destruct J as [(t, tlV') J].
  
  specialize IHv with w (tl V) W r s.
  unfold tra in H. rewrite H1 in H.
  assert (J' := J).
  unfold tra in J. rewrite J in H.
  injection H as H H'.
  apply IHv.
  
  
  unfold tra.
  rewrite J.
  
  rewrite H.
  rewrite<- H'.
  simpl.
  trivial.

  simpl ((a :: v) ++ w) in H0.

  destruct option_em with (prod Y (word O)) (tra M r (v ++ w)).
  unfold lam in H0.
  unfold tra in H0.
  rewrite H1 in H0.

  assert (H2' := H2).
  unfold tra in H2.
  rewrite H2 in H0.
  discriminate H0.  

  destruct H2 as [(t', VW') H2].
  unfold lam in H0.
  unfold tra in H0.
  rewrite H1 in H0.
  assert (H2' := H2).
  unfold tra in H2.
  rewrite H2 in H0.
  
  injection H0 as H0.
  unfold lam.
  rewrite H2'.
  rewrite list_tl_property.
  rewrite<- H0.
  simpl. trivial.
  apply o.
  rewrite<- H'.
  discriminate.
Qed.

Lemma lemma_a_1_lambda :
forall M : Mealy, 
forall v w : word I,
forall V W : word O,
forall q s : Y,
      tra M q v = Some (s, V)
  ->
        (lam M s w = Some W
    <->
        (lam M q (v ++ w) = Some (V ++ W)))
.
Proof.
intros.
split.
intro J.
destruct (lemma_a_1 M v w V q s). apply H.
rewrite H1.
unfold ol_concat.
unfold lam. rewrite H.
destruct option_em with (prod Y (word O)) (tra M s w).
unfold lam in J. rewrite H2 in J. discriminate J. 
destruct H2 as [(q', W') H2].
rewrite H2.
assert (W = W').
unfold lam in J.
rewrite H2 in J.
injection J as J.
symmetry. apply J.
rewrite H3.
trivial.

intro J.
destruct em with (lam M s w = Some W).
apply H0.

apply (lemma_q_1_lambda_part M v w V W q s).
apply H.
apply J.
Qed.

Lemma lemma_2_10 :
forall S M TT : Mealy,
forall T : word I -> Prop,
forall f : Y -> Y,
  testingTree TT S T
->
  (forall r v : Y, 
  del TT (q0 TT) v = Some r -> del M (q0 M) v = Some (f r))
->
  (funcSim TT M f
<->
  passes2 M TT T).
Proof.
intros S M TT T f H_tt Hf.
(* Unfold testingTree *)
assert (H_tt' := H_tt).
unfold testingTree in H_tt.
destruct H_tt as [H_tree H_pref].
destruct H_pref as [H_pref H_treeDelta].
destruct H_treeDelta as [H_treeDelta H_treeLambda].
unfold tree in H_tree.
destruct H_pref as [H_tree_states H_pref].
destruct H_pref as [H_pref H_root].
symmetry. split.
- intro H_passes2. unfold funcSim. split.
  + (* 1. f (qT0 ) = f (ϵ) = δM(qM0 , ϵ) = qM0 . *)
  specialize Hf with (q0 TT) nil. unfold del in Hf. unfold tra in Hf.
  injection Hf as Hf'. symmetry in Hf'. apply Hf'. trivial.
  + intros q r i o H_QTTq H_q_io_r. symmetry. rewrite<- tra_trans_def_known. 
    (* Obtain qi = r using the lemma *)
    assert (r = q ++ i :: nil) as H_qi_is_r. 
      apply (r_is_qi TT q r i o). apply H_QTTq. apply H_treeDelta. apply H_q_io_r.
    (* Obtain the fact that q0 -q-> q*)
    
    (* Split the trans into delta and lambda, like in the paper *)
    rewrite <- del_lam_tra_def. split.
    * (* 2. Assume δT (σ, i)↓, for some σ ∈ QT and i ∈ I. Then by Lemma A.1:
      f (δT (σ, i)) =(D) f (σi) =(C) δM(qM0 , σi) =(B) δM(δM(qM0 , σ), i) =(A) δM(f(σ), i)*)
      (* A-B: rewrite δM(f(σ), i) to δM(qM0 , σi)*)
      symmetry.
      rewrite<- (lemma_a_1_delta M q (i :: nil) (q0 M) (f q)).
      --(* C rewrite δM(qM0 , σi) to f(σi) *)
        rewrite (Hf r (q ++ i :: nil)).
        ++  trivial.
        ++  rewrite H_tree. 
            **  rewrite H_qi_is_r. trivial.
            **  rewrite<- H_qi_is_r. apply (next_state TT q r i).
                --- apply H_QTTq.
                --- unfold del. unfold tra. rewrite H_q_io_r. trivial.
      --(* D rewrite f(σi) to (δT (σ, i)) *)
        rewrite (Hf q q).
        ++  trivial.
        ++  apply H_tree. apply H_QTTq.
    * (* 3. As M passes T , for all σ ∈ T , λM(qM0 , σ) = λS (qS0 , σ). 
      This implies that, for all σi ∈ Pref (T ), λM(qM0 , σi) = λS (qS0 , σi).*)
      assert (forall v : word I, Q TT v -> (lam M (q0 M) v = lam S (q0 S) v)) as H_M_S_same_output.
      ++  (* Follows easily from prefix and passes*)
          intros v H_QTTv. unfold passes2 in H_passes2. unfold passes1 in H_passes2.
          assert (T v) as H_Tv.
          ** rewrite<- H_tree_states. apply H_QTTv.
          ** rewrite (H_passes2 v).
              --- rewrite (H_treeLambda (q0 TT) (q0 S) v).
                  +++ trivial.
                  +++ rewrite H_root. simpl. apply H_QTTv.
                  +++ rewrite H_root. unfold del. unfold tra. trivial.  
              --- apply H_Tv.
      ++  (* Split H_q_io_r in order to rewrite later *)
          assert (temp := H_q_io_r). rewrite<- tra_trans_def_known in temp.
          rewrite<- del_lam_tra_def in temp. destruct temp as [H_q_i_r H_q_io].
          destruct option_em with (prod Y (word O)) (tra S (q0 S) q) as [J|J].
          *** (* Case where (tra S (q0 S) q) undef (proof by contradiction) *)
              exfalso.
              assert (lam S (q0 S) q = None) as J'.
              unfold lam. rewrite J. trivial.
              rewrite<- H_M_S_same_output in J'.
              assert (tra M (q0 M) q = None).
              destruct option_em with (prod Y (word O)) (tra M (q0 M) q).
              apply H.
              destruct H as [(mq, Qout)].
              unfold lam in J'. rewrite H in J'. discriminate J'.
              assert (Hf_q_q := Hf).
              specialize Hf_q_q with q q.
              assert (H_tree_q := H_tree).
              specialize H_tree_q with q.
              apply Hf_q_q in H_tree_q.
              unfold del in H_tree_q.
              rewrite H in H_tree_q.
              discriminate H_tree_q.
              apply H_QTTq.
              apply H_QTTq.
          *** destruct J as [(sq, Qout) J].
              rewrite (lemma_a_1_lambda M q (i :: nil) Qout (o :: nil) (q0 M) (f q)).
              ---- rewrite H_M_S_same_output.
                   ++++ rewrite<- (lemma_a_1_lambda S q (i :: nil) Qout (o :: nil) (q0 S) sq).
                        ****  rewrite<- (H_treeLambda q sq (i :: nil)).
                              apply H_q_io. rewrite<- H_qi_is_r. 
                              apply (next_state TT q r i).  apply H_QTTq. apply H_q_i_r.
                              unfold del. rewrite J. trivial.
                        **** apply J.
                   ++++ rewrite<- H_qi_is_r. apply (next_state TT q r i).  apply H_QTTq. apply H_q_i_r.
              ---- rewrite <- del_lam_tra_def.
                   split.
                   rewrite (Hf q q). trivial. apply H_tree. apply H_QTTq. 
                   rewrite H_M_S_same_output. unfold lam. rewrite J. trivial. apply H_QTTq.
- intro H_funcSim. unfold passes2. unfold passes1.
  intros q H_Qttq.
  rewrite<- H_tree_states in H_Qttq.
  (* Instantiate the output for TT *)
  destruct option_em with (prod Y (word O)) (tra TT (q0 TT) q) as [H_q0_io_q | H_q0_io_q].
  + (* Show the contradiction *)
    assert (contra := H_tree).
    specialize contra with q.
    unfold del in contra. rewrite H_q0_io_q in contra.
    discriminate contra. apply H_Qttq.
  + destruct H_q0_io_q as [(q', Qout) H_q0_io_q].
    (* Strengthen goal for Lemma *)
    assert (tra M (q0 M) q = Some (f q', Qout)) as H_strong.
    * (* Rewrite q0M to f(q0TT) *)
      assert (H_funcSimRoot := H_funcSim).
      unfold funcSim in H_funcSimRoot.
      destruct H_funcSimRoot as [H_funcSimRoot temp]. clear temp.
      rewrite<- H_funcSimRoot.
      (* Finally apply the Lemma *)
      apply (lemma_a_4 TT M f).
      apply H_funcSim.
      apply initial.
      apply H_q0_io_q.
    * (* Now apply what we just learned *)
      unfold lam.
      rewrite H_strong.
      rewrite H_q0_io_q.
      trivial.
Qed.