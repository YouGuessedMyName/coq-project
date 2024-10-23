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

(* Lemmas about partially defined transitions. *)

(* A transition with a single letter behaves the same as the basic transition function *)
(* replaces temp4 *)
Parameter tra_trans_undef :
forall M : Mealy,
forall q : Y,
forall a : I,
  tra M q (a :: nil) = None 
<-> 
  trans M q a = None.

(* As of yet unused, might come in handy *)
(* Conversion between tra with a word of one letter and trans with one letter, 
where you give the LETTER as a parameter *)
Parameter tra_trans_def1 :
forall M : Mealy,
forall q s : Y,
forall a : I,
forall a' : O,
  tra M q (a :: nil) = Some (s, a' :: nil) 
<-> 
  trans M q a = Some (s, a').

(* Conversion between tra with a word of one letter and trans with one letter, 
where you give the WORD (singleton word) as a parameter *)
Parameter tra_trans_def2 :
forall M : Mealy,
forall q s : Y,
forall v : word I,
forall a : I,
forall A : list O,
  tra M q (a :: v) = Some (s, A) 
 <-> 
    exists a' : O, (A = a' :: nil) /\ trans M q a = Some (s, a').

(* q -av/AV-> s, and q -a/A-> r, then r -v/V -> s *)
(* replaces temp *)
Lemma tra_insert_letter :
forall M : Mealy,
forall q r s : Y,
forall v : word I, forall a : I,
forall V : word O,
forall A : word O,
  tra M q (a :: v) = Some (s, V)
->
  tra M q (a :: nil) = Some (r, A)
->
  tra M r v = Some (s, tl V) /\ 
    exists a' : O, V = a' :: (tl V) /\ a' :: nil = A /\ trans M q a = Some (r, a').
Proof.
intros.
rewrite (tra_trans_def2 M q r nil a A) in H0.
destruct option_em with (prod Y (word O)) (tra M r v).
unfold tra in H.
destruct H0.
destruct H0.
rewrite H2 in H.
unfold tra in H1.
rewrite H1 in H.
discriminate H.
destruct H0.
destruct H0.
destruct H1 as [(s', V')].
unfold tra in H.
rewrite H2 in H.
assert (G := H1).
unfold tra in H1.
rewrite H1 in H.
rewrite G.
injection H as H.
symmetry in H2.
rewrite H.
simpl.
split.
rewrite<- H3.
simpl.
reflexivity.
exists x.
simpl.
split.
rewrite<- H3.
simpl.
reflexivity.
rewrite H0.
split.
reflexivity.
rewrite H2.
reflexivity.
Qed.

(* If q -u/U-> s, and s -w-> is undef, then q -uw/?-> is undef *)
Parameter second_half_undefined :
forall M : Mealy,
forall q s : Y,
forall u w : word I,
forall U : word O,
  tra M q u = Some (s, U)
->
  tra M s w = None
->
  tra M q (u ++ w) = None.

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
    (* Case where tra(s, w) is undef *)
    destruct option_em with (prod Y (word O)) (tra M s w) as [G | G].
    rewrite G. rewrite H. unfold ol_concat2. rewrite second_half_undefined with M q s (a :: v) w V.
    trivial. apply H. apply G.
  destruct G as [(t, W) P].
    (* Case where tra(q a) is undef *)
    destruct option_em with (prod Y (word O)) (tra M q (a :: nil)) as [Q | Q].
    simpl. apply (tra_trans_undef M q a) in Q.
    rewrite Q. unfold ol_concat2. trivial.
  destruct Q as [(r, A) R].
  (* Specialize the IH *)
    (* from: forall w' V' q' s': q' -v/V-> s', THEN q' -vw/VW-> t' , where s' -w/W-> t' 
    to: r -vw/VW -> t, where s -w/W-> t *)
    specialize IHv with w (tl V) r s.
    assert (K := H).    
    apply (tra_insert_letter M q r s v a V A) in K.
    destruct K as [K L]. 
    assert (IH := K).
    apply IHv in IH. clear IHv.
  (* Obtain a' *)
  destruct L as [a' U].
  simpl.
  destruct U as [U U'].
  destruct U' as [U' U''].
  rewrite U''.
  rewrite IH.
  rewrite K.
  rewrite P.
  rewrite U.
  simpl.
  reflexivity.
  apply R.
Qed.

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
apply (transition_consistency2 M v (w) V q s) in H.
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

