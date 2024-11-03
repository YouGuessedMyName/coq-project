Require Import Mealy.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Relations.Relation_Definitions.

Definition Bisimulation (M N : Mealy) (R : relation Y) : Prop
:= R (q0 M) (q0 N)
/\
forall q r : Y, Q M q -> Q N r -> forall i : I, R q r ->
  (def (tra M q (i :: nil)) <-> def (tra N r (i :: nil)))
/\
  forall q' r' : Y,
     Some q' = del M q (i :: nil)
  -> Some r' = del N r (i :: nil)
  -> R q' r'
    /\
      (lam M q (i :: nil)) = (lam N r (i :: nil)).

(* Definition 2.2 (Semantics and minimality) *)
Definition semantics (M : Mealy) (q : Y) :=
  lam M q.
Definition equiv (M N : Mealy) (q : Y) (r : Y) : Prop :=
  semantics M q = semantics N r.
Definition equivM (M N : Mealy) : Prop :=
  equiv M N (q0 M)(q0 N).
Definition minimalM (M : Mealy) : Prop :=
  forall q r : Y, Q M q -> Q M r -> (equiv M M q r) <-> q <> r.

Parameter function_em :
forall A B : Type, forall f g : A -> B,
f = g \/ exists a : A, f a <> g a.

Lemma semantics_lemma :
forall M N : Mealy, forall q r : Y,
  equiv M N q r
<->
  forall v : word I, lam M q v = lam N r v.
Proof.
intros.
split.
+ intro H_sem. unfold equiv in H_sem. intro v. unfold semantics in H_sem. rewrite H_sem. trivial.
+ intro H_same. unfold semantics. 
  destruct function_em with (word I) (option (word O)) (lam M q) (lam N r).
  apply H. destruct H as [v H]. rewrite H_same in H. elim H. trivial.
Qed.

Lemma del_tra :
forall M : Mealy,
forall q q' : Y,
forall v : word I,
  del M q v = Some q'
->
  exists V : word O,
    tra M q v = Some (q', V) /\ lam M q v = Some V.
Proof.
intros.
destruct option_em with (prod Y (word O)) (tra M q v) as [J|J].
- unfold del in H. rewrite J in H. discriminate H.
- destruct J as [(q'', V) J]. unfold del in H. rewrite J in H. 
  injection H as H. rewrite H in J. exists V. split.
  + apply J.
  + unfold lam. rewrite J. auto.
Qed.

Lemma del_tra_single_letter :
forall M : Mealy,
forall q q' : Y,
forall i : I,
  del M q (i :: nil) = Some q'
->
  exists o : O,
    tra M q (i :: nil) = Some (q', (o :: nil)) /\ lam M q (i :: nil) = Some (o :: nil).
Proof.
intros.
destruct option_em with (prod Y O) (trans M q i) as [J|J].
- unfold del in H. unfold tra in H. rewrite J in H. discriminate H.
- destruct J as [(q'', o) J]. unfold del in H. unfold tra in H. rewrite J in H. 
  injection H as H. rewrite H in J. exists o. unfold tra. rewrite J. split. 
  + auto.
  + unfold lam. unfold tra. rewrite J. auto.
Qed.

(* If q -u/U-> s, and s -w-> is undef, then q -uw/?-> is undef *)
Lemma second_half_undefined2 :
forall M : Mealy,
forall u w : word I,
forall q s : Y,
forall U : word O,
  tra M q u = Some (s, U)
->
  tra M s w = None
<->
  tra M q (u ++ w) = None.
Proof.
induction u.
(* Base case *)
- intros w q s U J. split. 
  + intro L. simpl. unfold tra in J. injection J as J J'. rewrite J. apply L.
  + intro L. simpl. unfold tra in J. injection J as J J'. rewrite<- J. 
    simpl (nil ++ w) in L. apply L.
- intros w q s U J. split. 
+ 
intro L. simpl.
destruct option_em with (prod Y O) (trans M q a) as [K | K].
rewrite K. reflexivity.
destruct K as [(r, o) K].
rewrite K.
specialize IHu with w r s (tl U).
apply (first_letter M q s r a u U o) in J.
rewrite IHu in L. rewrite L.
reflexivity.
apply J.
unfold tra. rewrite K. reflexivity.
+
intro L.
destruct option_em with (prod Y O) (trans M q a) as [K | K].
unfold tra in J. rewrite K in J. discriminate J.
destruct K as [(r, o) K].
specialize IHu with w r s (tl U).
apply (first_letter M q s r a u U o) in J.
rewrite IHu.
simpl ((a :: u) ++ w) in L.
destruct option_em with (prod Y (word O)) (tra M r (u ++ w)) as [G|G].
apply G.
destruct G as [(t, UV) G].
unfold tra in G.
unfold tra in L. rewrite K in L. rewrite G in L. discriminate L.
apply J.
unfold tra. rewrite K. reflexivity.
Qed.

Lemma lam_tra_undef :
forall M : Mealy,
forall q : Y,
forall v : word I,
tra M q v = None <-> lam M q v = None.
Proof.
intros.
split.
- intro H. unfold lam. rewrite H. auto.
- intro H. destruct option_em with (prod Y (word O)) (tra M q v).
  + apply H0.
  + destruct H0 as [(r, V) H0]. unfold lam in H. rewrite H0 in H. discriminate H.
Qed.

Lemma double_transition :
forall M N : Mealy,
forall q q' r r' : Y,
forall i : I,
(equiv M N q r)
-> Some q' = del M q (i :: nil)
-> Some r' = del N r (i :: nil)
-> exists o : O,
tra M q (i :: nil) = Some (q', o :: nil) /\ 
lam M q (i :: nil) = Some (o :: nil) /\
tra N r (i :: nil) = Some (r', o :: nil) /\
lam N r (i :: nil) = Some (o :: nil).
Proof.
intros M N q q' r r' i H_eq_qr HqDel2 HrDel2.
rewrite semantics_lemma in H_eq_qr.
symmetry in HqDel2. symmetry in HrDel2.
apply del_tra_single_letter in HqDel2.
apply del_tra_single_letter in HrDel2.
destruct HqDel2 as [o HqDel2]. destruct HrDel2 as [o' HrDel2].
destruct HqDel2 as [HqTra HqLam]. destruct HrDel2 as [HrTra HrLam].
assert (temp := HrLam).
rewrite<- H_eq_qr in temp.
rewrite HqLam in temp.
injection temp as temp.
rewrite<- temp in HrTra.
rewrite<- temp in HrLam.
clear temp o'.
exists o.
split. apply HqTra. split. apply HqLam. split. apply HrTra. apply HrLam.
Qed.

Lemma undef :
forall M N : Mealy,
forall q r : Y,
forall v : word I,
  (def (tra M q v)) <-> (def (tra N r v))
->
  (undef (tra M q v)) <-> (undef (tra N r v)).
Proof.
intros.
split.
destruct H as [H H'].
intro J.
destruct option_em with (prod Y (word O)) (tra N r v) as [K | K].
unfold undef. apply K.
unfold def in H'.
apply H' in K.
destruct K as [(q', V) K].
unfold undef in J. rewrite K in J.
discriminate J.

intro J.
destruct option_em with (prod Y (word O)) (tra M q v) as [K | K].
unfold undef. apply K.
unfold def in H.
apply H in K.
destruct K as [(q', V) K].
unfold undef in J. rewrite K in J.
discriminate J.
Qed.

Lemma reachability :
forall M : Mealy,
forall q q' : Y,
forall i : I,
Q M q 
-> del M q (i::nil) = Some q'
-> Q M q'.
Proof.
intros.
unfold Q in H.
destruct H as [v H].
unfold Q.
exists (v ++ i :: nil).
rewrite (lemma_a_1_delta M v (i::nil) (q0 M) q).
apply H0. apply H.
Qed.

Lemma lemma_a_3 :
forall M N : Mealy, equivM M N <-> exists R : relation Y, Bisimulation M N R.
Proof.
intros.
split.
intro H_eqMN.
- 
eexists. unfold Bisimulation. split.
+ eauto.
+ intros q r H_QMq H_QNr i H_eq_qr. split.
* split. 
--  
intro H_Mqi_def. rewrite semantics_lemma in H_eq_qr.
destruct option_em with (prod Y (word O)) (tra N r (i :: nil)) as [J|J].
++ 
specialize H_eq_qr with (i :: nil). unfold lam in H_eq_qr. rewrite J in H_eq_qr.
unfold def in H_Mqi_def. destruct H_Mqi_def as [(q', o) H_Mqi_def].
rewrite H_Mqi_def in H_eq_qr. discriminate H_eq_qr.
++ unfold def. apply J.
--  
intro H_Nri_def. rewrite semantics_lemma in H_eq_qr.
destruct option_em with (prod Y (word O)) (tra M q (i :: nil)) as [J|J].
++ 
specialize H_eq_qr with (i :: nil). unfold lam in H_eq_qr. rewrite J in H_eq_qr.
unfold def in H_Nri_def. destruct H_Nri_def as [(q', o) H_Nri_def].
rewrite H_Nri_def in H_eq_qr. discriminate H_eq_qr.
++ unfold def. apply J.
* intros q' r' HqDel HrDel. split.
(* Obtain the output letter o *)
destruct double_transition with M N q q' r r' i as [o temp].
apply H_eq_qr. apply HqDel. apply HrDel.
destruct temp as [HqTra temp]. destruct temp as [HqLam temp]. destruct temp as [HrTra HrLam].
++
rewrite semantics_lemma. rewrite semantics_lemma in H_eq_qr.
intro v. 

(* Obtain output word V *)
destruct option_em with (prod Y (word O)) (tra M q' v) as [J|J].
**
assert (tra M q (i::nil ++ v) = None) as H.
---
apply (second_half_undefined M (i::nil) v q q' (o :: nil)).
+++ apply HqTra.
+++ apply J.
---
assert (H0 := H).
rewrite (lam_tra_undef M q (i::nil ++ v)) in H.
rewrite H_eq_qr in H.
rewrite<- lam_tra_undef in H.
apply (second_half_undefined2 N (i :: nil) v r r' (o :: nil)) in H.
+++
unfold lam. rewrite J. rewrite H. reflexivity.
+++ apply HrTra.
**
destruct J as [(q'', V) J].
assert (H_q'Tra := J).
rewrite<- del_lam_tra_def in J.
destruct J as [H_q'Del H_q'Lam].
assert (H_l := H_q'Lam).
rewrite (lemma_a_1_lambda M (i::nil) v (o ::nil) V q q') in H_l.
---
rewrite H_eq_qr in H_l.
rewrite<- (lemma_a_1_lambda N (i::nil) v (o ::nil) V r r') in H_l.
+++ rewrite H_l. rewrite H_q'Lam. auto.
+++ apply HrTra.
--- apply HqTra.
++
rewrite semantics_lemma in H_eq_qr. rewrite H_eq_qr. trivial.
(* - intro temp. destruct temp as [H_rTraDef H_bisim].
destruct option_em with (prod Y (word O)) (tra M q (i :: nil)) as [J|J].
-- (* Case where tra M q (i :: nil) undef *)
  rewrite semantics_lemma in H_eq_qr.
  rewrite lam_tra_undef in J. rewrite H_eq_qr in J. rewrite<- lam_tra_undef in J.
  unfold def in H_rTraDef. destruct H_rTraDef as [(q', O) H_rTraDef].
  rewrite H_rTraDef in J. discriminate J.
-- unfold def. apply J. *)
- intro H_bis. destruct H_bis as [R H_bis].
unfold Bisimulation in H_bis. destruct H_bis as [H_Rq0 H_bis].
unfold equivM. rewrite semantics_lemma.
assert (forall v : word I, forall q r : Y,
R q r -> Q M q -> Q N r ->  lam M q v = lam N r v) as HH. {
  induction v as [IHv | i].
  - intros q r H_QMq H_QNr. unfold lam. unfold tra. auto.

  - intros q r H_Rqr H_QMq H_QNr.
assert (((tra M q (i :: nil) ↓) <-> (tra N r (i :: nil) ↓)) /\
forall q' r' : Y,
         Some q' = del M q (i :: nil) ->
         Some r' = del N r (i :: nil) -> R q' r' 
        /\ lam M q (i :: nil) = lam N r (i :: nil)) as H_bis2.
apply H_bis. apply H_QMq. apply H_QNr. apply H_Rqr.
destruct H_bis2 as [H_bisDef H_bisEq]. (* TODO lemma undef *)
  destruct option_em with (prod Y (word O)) (tra M q (i :: nil)) as [K | K].
* destruct option_em with (prod Y (word O)) (tra N r (i :: nil)) as [G | G].
-- unfold lam. rewrite tra_trans_undef in K. unfold tra. rewrite K.
   rewrite tra_trans_undef in G. rewrite G. auto.
-- destruct H_bisDef as [H_bisDef1 H_bisDef2]. unfold def in H_bisDef2. 
apply H_bisDef2 in G. destruct G as [(q', o) G]. rewrite K in G. discriminate G.
* destruct option_em with (prod Y (word O)) (tra N r (i :: nil)) as [G | G].
-- destruct H_bisDef as [H_bisDef1 H_bisDef2]. unfold def in H_bisDef1. 
apply H_bisDef1 in K. destruct K as [(q', o) K]. rewrite K in G. discriminate G.
-- destruct K as [(q', A) K]. destruct G as [(r', A') G].

assert (R q' r' /\ lam M q (i :: nil) = lam N r (i :: nil)) as L. {
  apply H_bisEq.
  unfold del. rewrite K. auto.
  unfold del. rewrite G. auto.
}
destruct option_em with (prod Y (word O)) (tra N r' v) as [Z|Z].
+ apply undef in H_bisDef. assert (tra N r (i :: v) = None). {
Check second_half_undefined2.
rewrite<- (second_half_undefined2 N (i::nil) v r r' A).
apply Z. 
destruct L as [L L']. unfold lam in L'. rewrite K in L'. rewrite G in L'. injection L' as L'.
rewrite L'. apply G.
}
assert (tra M q' v = None) as H0. {
assert (Z' := Z).
rewrite<- (del_lam_tra_undef N r' v) in Z'.
destruct Z' as [temp Z']. clear temp.
rewrite<- (IHv q' r') in Z'.
destruct option_em with (prod Y (word O)) (tra M q' v). apply H0.
destruct H0 as [(t, V) H0].
unfold lam in Z'. rewrite H0 in Z'. discriminate Z'.
apply L.
apply (reachability M q q' i H_QMq). unfold del. rewrite K. auto.
apply (reachability N r r' i H_QNr). unfold del. rewrite G. auto.
apply A.
}
Check second_half_undefined2.
rewrite (second_half_undefined2 M (i::nil) v q q' A) in H0.
simpl ((i :: nil) ++ v) in H0.
unfold lam. rewrite H. rewrite H0. auto.
apply K.
+ destruct Z as [(r'', V) Z].
rewrite<- del_lam_tra_def in Z.
destruct Z as [Z0 Z].
assert (Z' := Z).
rewrite<- (IHv q' r') in Z.
rewrite (lemma_a_1_lambda M (i::nil) v A V q q') in Z. simpl ((i :: nil) ++ v) in Z.
rewrite (lemma_a_1_lambda N (i::nil) v A V r r') in Z'. simpl ((i :: nil) ++ v) in Z'.
rewrite Z. rewrite Z'. auto.
destruct L as [L L'].
rewrite<- del_lam_tra_def.
split.
unfold del. rewrite G. auto.
rewrite<- L'. unfold lam. rewrite K. auto.
apply K.
apply L.
apply (reachability M q q' i H_QMq). unfold del. rewrite K. auto.
apply (reachability N r r' i H_QNr). unfold del. rewrite G. auto.
}
intro v. specialize HH with v (q0 M) (q0 N). apply HH. apply H_Rq0. apply initial. apply initial.
Qed.

