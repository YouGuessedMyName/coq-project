Require Import Coq.Lists.List.
Require Import Coq.Sets.Finite_sets_facts.

(* Enable classical logic *)
(* Sorry Freek, I know you love propositional logic*)
Parameter em: forall p:Prop, p \/ ~p.

(* TODO, ask how to prove this (if it is even possible...*)
Parameter option_em :
forall A : Type, forall o : option A,
  o = None \/ exists a : A, o = Some a.


Definition ol_concat {A} (o o' : option (list A)) : option (list A) :=
  match o with
    | None => None
    | Some la =>
    match o' with
      | None => None
      | Some la' => Some (la ++ la')
    end
end.
Notation "o +++ o'" := (ol_concat o o') (at level 303, no associativity) : type_scope.

(* Keep the final state from the second argument, but concatenate the output words *)
Definition ol_concat2 {A B} (o o' : option (prod A (list B))) : option (prod A (list B)) :=
  match o with
    | None => None
    | Some (_, V) =>
    match o' with
      | None => None
      | Some (r, W) => Some (r, V ++ W)
    end
end.

Definition ol_2nd_tolist {A B} (o : option (prod A B)) : option (prod A (list B)) :=
match o with
  | None => None
  | Some (q, b) => Some (q, b :: nil) 
end.

Notation "o ++2 o'" := (ol_concat o o') (at level 303, no associativity) : type_scope.

Definition def {A} (o : option A) : Prop := exists a : A, o = Some a.
Definition undef {A} (o : option A) : Prop := o = None.

(* Partial functions *)
Notation "f ↑" := (undef f) (at level 303, no associativity) : type_scope.
Notation "f ↓" := (def f) (at level 303, no associativity) : type_scope.

(* We fix an input and an output set *)
Inductive I : Set.
Inductive O : Set.

Definition word := list.

(* Definition 2.1 (Mealy machine) *)
(* Here, we deviate a bit from the paper. 
Instead of having two transitions functions (delta, lambda), we combine them into one *)
Definition Y := word I.
Structure Mealy : Type := {
  q0 : Y;
  trans : Y -> I -> option (Y * O);
  Q : Ensemble Y;
}.

(* The intial state is always in the states, obtained from domain knowledge. *)
Parameter initial : forall M : Mealy, Q M (q0 M).

Fixpoint tra (M : Mealy) (q: Y) (v : word I) : (option ((Y) * word O)) :=
match v with
  | nil => Some (q, nil)
  | cons i v' => 
    match (trans M q i) with
     | Some (r, o) => 
        match (tra M r v') with
          | None => None
          | Some (r', w) => Some (r', o :: w)
        end
     | None => None
    end
end.

Definition del (M : Mealy) (q: Y) (v : word I) : (option (Y)) := 
match (tra M q v) with
  | None => None
  | Some (r, _) => Some r
end.
Definition lam (M : Mealy) (q: Y) (v : word I) : (option (word O)) := 
match (tra M q v) with
  | None => None
  | Some (_, w) => Some w
end.

(* Lemmas about transitions. *)
(* A transition with a single letter behaves the same as the basic transition function *)
Lemma tra_trans_undef :
forall M : Mealy,
forall q : Y,
forall a : I,
  tra M q (a :: nil) = None 
<-> 
  trans M q a = None.
Proof.
intros.
split.
 - destruct option_em with (prod Y O) (trans M q a) as [J | J].
  + intro H.
    unfold tra in H.
    apply J.
  + destruct J as [(r, A) J].
    intro H.
    unfold tra in H.
    rewrite J in H.
    discriminate H.
- intro H.
  unfold tra.
  rewrite H.
  trivial.
Qed.

(* Conversion between tra with a word of one letter and trans with one letter, 
where you give the WORD (singleton word) as a parameter *)
Lemma tra_trans_def2 :
forall M : Mealy,
forall q s : Y,
forall i : I,
forall A : list O,
  tra M q (i :: nil) = Some (s, A) 
 <-> 
    exists o : O, (A = o :: nil) /\ trans M q i = Some (s, o).
Proof.
intros.
split.
* intro H.
  destruct option_em with (prod Y O) (trans M q i) as [J | J].
  - apply tra_trans_undef in J.
    rewrite J in H.
    discriminate H.
  - destruct J as [(s', o) J].
    exists o.
    assert (G := H).
    unfold tra in G.
    rewrite J in G.
    injection G as G K.
    split.
    + rewrite<- K.
      reflexivity.
    + rewrite J.
      rewrite G.
      reflexivity.
* intro H.
  destruct H as [o' H].
  destruct H as [H J].
  rewrite H.
  unfold tra.
  rewrite J.
  reflexivity.
Qed.

Lemma tra_insert_letter :
forall M : Mealy,
forall q r s : Y,
forall v : word I, 
forall a : I,
forall V : word O,
forall a' : O,
  tra M q (a :: v) = Some (s, V)
->
  tra M q (a :: nil) = Some (r, a' :: nil)
->
  tra M r v = Some (s, tl V) 
  /\ V = a' :: (tl V) 
  /\ trans M q a = Some (r, a').
Proof.
intros M q r s v a V a' H J.
(* Apply tra_trans_def *)
rewrite (tra_trans_def2 M q r a (a' :: nil)) in J.
destruct J as [x J]. destruct J as [J J'].
injection J as J.
  (* Case where tra M r v undef *)
  destruct option_em with (prod Y (word O)) (tra M r v) as [L | L].
  unfold tra in H. rewrite J' in H. unfold tra in L. 
  rewrite L in H. discriminate H.

unfold tra in H. rewrite J' in H.
destruct L as [(s', V') L].
assert (G := L).
unfold tra in L. rewrite L in H.
rewrite G.
injection H as H H'. rewrite H. simpl.
split.
- rewrite<- H'. simpl. reflexivity.
- split. 
  + rewrite<- H'. simpl. rewrite J. reflexivity.
  + rewrite J'. rewrite<- J. reflexivity.
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
->
  tra M q (u ++ w) = None.
induction u.
(* Base case *)
- intros w q s U J L. simpl. unfold tra in J.
  injection J as J J'. rewrite J. apply L.
- intros w q s U J L. simpl.
  destruct option_em with (prod Y O) (trans M q a) as [K | K].
  rewrite K. reflexivity.
destruct K as [(r, a') K].
rewrite K.
specialize IHu with w r s (tl U).
apply (tra_insert_letter M q r s u a U a') in J.
rewrite IHu.
reflexivity.
apply J.
apply L.
apply tra_trans_def2.
exists a'.
split.
reflexivity.
apply K.
Qed.

Lemma transition_consistency :
forall M : Mealy,
forall v w : word I,
forall V : word O,
forall q s : Y,
  tra M q v = Some (s, V)
-> 
  tra M q (v ++ w) = ol_concat2 (tra M q v) (tra M s w).
Proof.
induction v.
(* Base case *)
- intros. inversion H. simpl.
  destruct option_em with (prod Y (word O)) (tra M s w).
  * rewrite H0. trivial.
  * destruct H0 as [(a, b)]. rewrite H0. trivial.
(* Inductive case *)
(* q -a/A-> r -> v/V-> s -> w/W -> t*)
- intros.
    (* Case where tra(s, w) is undef *)
    destruct option_em with (prod Y (word O)) (tra M s w) as [G | G].
    rewrite G. rewrite H. unfold ol_concat2. rewrite second_half_undefined2 with M (a :: v) w q s V.
    trivial. apply H. apply G.
  destruct G as [(t, W) P].
    (* Case where tra(q a) is undef *)
    destruct option_em with (prod Y (word O)) (tra M q (a :: nil)) as [Q | Q].
    simpl. apply (tra_trans_undef M q a) in Q.
    rewrite Q. unfold ol_concat2. trivial.
  destruct Q as [(r, A) R].
  (* Obtain a', where a' :: nil = A *)
  assert (R' := R).
  apply (tra_trans_def2 M q r a A) in R'.
  destruct R' as [a' R'].
  destruct R' as [R' R''].
  (* Specialize the IH *)
    (* from: forall w' V' q' s': q' -v/V-> s', THEN q' -vw/VW-> t' , where s' -w/W-> t' 
    to: r -vw/VW -> t, where s -w/W-> t *)
    specialize IHv with w (tl V) r s.
    assert (K := H).
    apply (tra_insert_letter M q r s v a V a') in K.
    (* apply (tra_insert_letter M q r s v a V A) in K. *)
    destruct K as [K L]. 
    assert (IH := K).
    apply IHv in IH. clear IHv.
  destruct L as [L L'].
  simpl.
  rewrite L'.
  rewrite IH.
  rewrite K.
  rewrite P.
  rewrite L.
  simpl.
  reflexivity.
  rewrite R.
  rewrite R'.
  reflexivity.
Qed.

(* Lemma A.1. Let M be a Mealy machine, q ∈ Q, i ∈ I and σ ∈ I∗. Then
δ(q, σi) = δ(δ(q, σ), i) and λ(q, σi) = λ(q, σ) · λ(δ(q, σ), i). 

Here is a slightly more general version because i is replaced by w, 
which can be any word (not just a single letter). Also, s = δ(δ(q, σ)

The proof is basically an application of lemma transition_consistency *)
Lemma lemma_a_1 : 
forall M : Mealy, 
    forall v w : word I,
      forall V : word O,
        forall q s : Y,
          tra M q v = Some (s, V) 
      ->
            (del M q (v ++ w)) = (del M s w)
        /\
            (lam M q (v ++ w) = ol_concat (lam M q v) (lam M s w))
.
Proof.
intros.
inversion H.
apply (transition_consistency M v (w) V q s) in H.
destruct option_em with (prod Y (word O)) (tra M s (w)).
(* Case where lam(s, w) is undef *)
- rewrite H0 in H.
  rewrite H1 in H.
  unfold ol_concat2 in H.
  split.
  + unfold del.
    rewrite H.
    rewrite H0.
    trivial.
  + unfold lam.
    rewrite H.
    rewrite H0.
    rewrite H1.
    simpl.
    reflexivity.
(* Case where lam(s, w) is def *)
- destruct H0 as [(t, O)].
  rewrite H0 in H.
  rewrite H1 in H.
  unfold ol_concat2 in H.
  split.
  + unfold del.
    rewrite H.
    rewrite H0.
    reflexivity.
  + unfold lam. 
    rewrite H.
    rewrite H0.
    rewrite H1.
    simpl.
    reflexivity.
Qed.

