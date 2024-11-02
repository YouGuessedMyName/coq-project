Require Import Mealy.
Require Import Coq.Lists.List.


(* Definition 2.4 (Simulation) *)
(* f : M -> N is a funcitonal simulation from M to N
r = δ(q, i) *)
Definition funcSim (M N : Mealy) (f: Y -> Y) : Prop :=
  f(q0 M) = q0 N 
/\
  forall q r : Y, forall i : I, forall o : O,
      Q M q
    ->
      trans M q i = Some (r, o)
    ->
        Some (f(r), o) = trans N (f q) i
.

(* Lemma A.4. *)
Lemma lemma_a_4 : 
forall M N : Mealy,
forall f : Y -> Y, 
forall v : word I,
forall V : word O,
forall q q' : Y,
funcSim M N f 
-> Q M q
-> tra M q v = Some (q', V)
-> tra N (f q) v = Some ((f q'), V).
Proof.
induction v.
- intros V q q' H J P. simpl. unfold tra in P. 
  injection P as P P'. rewrite P. rewrite P'. trivial.
- intros V q q' H J P. assert (K := P). apply first_letter_exi in K.
  destruct K as [r K]. destruct K as [o K]. destruct K as [K K']. destruct K' as [K' K''].
  rewrite tra_trans_def_known in K''.
  specialize IHv with (tl V) r q'. assert (IH := H). apply IHv in IH. clear IHv.

  unfold funcSim in H. destruct H as [H H']. simpl.
  specialize H' with q r a o.
  assert (G := K'').
  
  apply H' in G.
  rewrite<- G.
  rewrite IH.
  rewrite K'.
  simpl.
  reflexivity.
  apply J.
  
  unfold Q in J.
  destruct J as [aq J].
    
  unfold Q.
  
  exists (aq ++ a :: nil).
    destruct option_em with (prod Y (word O)) (tra M (q0 M) aq) as [C | C].
    unfold del in J. rewrite C in J. discriminate J.
  destruct C as [(qq, AQ)]. 
  destruct lemma_a_1 with M aq (a :: nil) AQ (q0 M) q.
  unfold del in J. rewrite H0 in J. injection J as J. rewrite<- J. apply H0.
  rewrite H1. unfold del. unfold tra. rewrite K''. trivial.
  apply K.
Qed.