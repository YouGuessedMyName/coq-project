Require Import Mealy.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Relations.Relation_Definitions.

Definition Bisimulation (M N : Mealy) (R : relation Y) : Prop
:= R (q0 M) (q0 N)
/\
forall q r : Y, Q M q -> Q N r -> forall i : I, R q r ->
  def (tra M q (i :: nil)) <-> def (tra N r (i :: nil))
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

Parameter

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
* intro H_Mqi_def. split.
--  
rewrite semantics_lemma in H_eq_qr.
destruct option_em with (prod Y (word O)) (tra N r (i :: nil)) as [J|J].
++ 
specialize H_eq_qr with (i :: nil). unfold lam in H_eq_qr. rewrite J in H_eq_qr.
unfold def in H_Mqi_def. destruct H_Mqi_def as [(q', o) H_Mqi_def].
rewrite H_Mqi_def in H_eq_qr. discriminate H_eq_qr.
++ unfold def. apply J.
-- intros q' r' HqDel HrDel. split.
++ 
rewrite semantics_lemma. rewrite semantics_lemma in H_eq_qr.
intro v. 
(* Obtain the output letter o *)
assert (HqDel2 := HqDel). assert (HrDel2 := HrDel).
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
rewrite<- del_lam_tra_undef in H.
destruct H as [H H'].
rewrite H_eq_qr in H'.
assert (i :: nil ++ v = (i :: nil) ++ v) as Hlist. simpl. auto. 
rewrite Hlist in H0.
apply<- (second_half_undefined2 N (i::nil) v r r' (o::nil)) in H0.
rewrite (lemma_a_1_lambda M ) in H'.

rewrite J. rewrite H_eq_qr.
