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
  -> Some r' = del M r (i :: nil)
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
-- intros q' r' H_M_q_i_q' H_N_r_i_r'. split.
++ 
rewrite semantics_lemma. rewrite semantics_lemma in H_eq_qr.
intro v.
(* Instantiate the output i/o *)
destruct option_em with (prod Y (word O)) (tra M q (i :: nil)) as [J|J].
unfold del in H_M_q_i_q'. rewrite J in H_M_q_i_q'. discriminate H_M_q_i_q'.
destruct J as [(q'', o) J].
assert (temp := H_M_q_i_q').
unfold del in temp. rewrite J in temp. injection temp as temp. rewrite<- temp in J. clear temp.


