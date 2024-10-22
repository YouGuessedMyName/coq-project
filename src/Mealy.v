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

Notation "o ++2 o'" := (ol_concat o o') (at level 303, no associativity) : type_scope.

Definition def {A} (o : option A) : Prop := exists a : A, o = Some a.
Definition undef {A} (o : option A) : Prop := o = None.

(* Partial functions *)
Notation "f ↑" := (undef f) (at level 303, no associativity) : type_scope.
Notation "f ↓" := (def f) (at level 303, no associativity) : type_scope.

(* We fix an input and an output set *)
Inductive I := ia | ib.
Inductive O := oa | ob.

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

(* The intial state is always in the states *)
Parameter initial : forall M : Mealy, Q M (q0 M).

Fixpoint tra (M : Mealy) (q: Y) (v : word I) : (option ((Y) * word O)) :=
match v with
  | nil => Some (q, nil)
  | cons i v' => 
    match (trans M q i) with
     | Some (r, o) => 
        match (tra M r v') with
          | None => None
          | Some (r', w) => Some (r', w)
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


(* IHv : tra M r v = Some (s, V) -> tra M r (v ++ w) = ol_concat2 (tra M r v) (tra M s w)
q : Y
H : tra M q (a :: v) = Some (s, V)*)
Parameter temp :
forall M : Mealy,
forall q r s : Y,
forall a : I,
forall v : word I,
forall V : word O,
  tra M q (a :: v) = Some (s, V)
->
  tra M r v = Some (s, V).

(* trans M q a *) (* tra M q (a :: nil) = Some (r, A) *)
Parameter temp2 : 
forall M : Mealy,
forall q r s : Y,
forall a : I,
forall A : word O,
  tra M q (a :: nil) = Some (r, A)
->
  (exists b : O, A = b :: nil /\ trans M q a = Some (r, b)).


Lemma transition_consistency2 :
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
  destruct option_em with (prod Y (word O)) (tra M s w).
  rewrite H0. rewrite H. unfold ol_concat2. admit.
  destruct H0 as [(t, W)].

  destruct option_em with (prod Y (word O)) (tra M q (a :: nil)).
  admit.

  destruct H1 as [(r, A)].
  (* IH forall w' V' q' s': q' -v/V-> s', THEN q' -vw/VW-> t' , where s' -w/W-> t' *)
  specialize IHv with w V r s.
  assert (K := H).
  apply (temp M q r s a v V) in K.
  assert (IH := K).
  apply IHv in IH. clear IHv.
assert (G := H1).
apply (temp2 M q r s a A) in G.
destruct G as [a' G].
destruct G.
simpl.
rewrite H3.
rewrite IH.
rewrite K.
destruct option_em with (prod Y (word O)) (ol_concat2 (Some (s, V)) (tra M s w)).
rewrite H4.
trivial.
destruct H4 as [(t', W')].
rewrite H4.

unfold ol_concat2.
simpl.
reflexivity.
Qed.


inversion H1.
rewrite H3.

unfold tra in H1.
  
destruct H0 as [()]
simpl.
specialize IHv with w V r s.
simpl.
rewrite H0.
simpl.
Parameter transition_consistency :
forall M : Mealy,
forall v w : word I,
forall V : word O,
forall q s : Y,
  tra M q v = Some (s, V)
-> 
  tra M q (v ++ w) = ol_concat2 (tra M q v) (tra M s w).

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

