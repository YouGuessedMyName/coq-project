Require Import Mealy.
Require Import Coq.Lists.List.

(* Definition 2.4 (Simulation) *)
(* f : M -> N is a funcitonal simulation from M to N
r = δ(q, i) *)
Definition funcSim (M N : Mealy) (f: Y -> Y) : Prop :=
  f(q0 M) = q0 N 
/\
  forall q r : Y, forall i : I, forall o : O,
      trans M q i = Some (r, o)
    ->
        Some (f(r), o) = trans N (f q) i
.

(* Lemma A.4. *)
Lemma lemma_a4 : 
forall M N : Mealy,
forall f : Y -> Y, 
forall v : word I,
forall V : word O,
forall q q' : Y,
funcSim M N f 
-> tra M q v = Some (q', V)
-> tra N (f q) v = Some ((f q'), V).
Proof.
induction v.
- intros V q q' H J. simpl. unfold tra in J. 
  injection J as J J'. rewrite J. rewrite J'. trivial.
- intros V q q' H J. assert (K := J). apply first_letter_exi in K.
  destruct K as [r K]. destruct K as [o K]. destruct K as [K K']. destruct K' as [K' K''].
  specialize IHv with (tl V) r q'. assert (IH := H). apply IHv in IH. clear IHv.

  unfold funcSim in H. destruct H as [H H']. simpl.
  specialize H' with q r a o.
  assert (G := K).
  apply H' in G.
  rewrite<- G.
  rewrite IH.
  rewrite K''.
  simpl.
  reflexivity.
  apply K'.
Qed.