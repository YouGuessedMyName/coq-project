Require Import Mealy.
Require Import ObservationTree.
Require Import FunctionalSimulation.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Finite_sets_facts.


(* Definition 2.2 (Semantics and minimality) *)
Definition semantics (M : Mealy) (q : Y) :=
  lam M q.
Definition equiv (M N : Mealy) (q : Y) (r : Y) : Prop :=
  semantics M q = semantics N r.
Definition equivM (M N : Mealy) : Prop :=
  equiv M N (q0 M)(q0 N).


Definition UComplete : Prop :=
forall T : word I -> Prop,
forall M S : Mealy,
passes2 S M T -> equivM M S.

Definition Um : Prop := True. (*TODO*)

Definition UkA : (word I -> Prop) -> Mealy -> Prop :=
fun A M => (
forall q : Y, Q M q -> (
  exists v : word I, exists w : word I,
  A v /\ del M (q0 M) (v ++ w) = Some q 
)).

Definition Ua : (word I -> Prop) -> Mealy -> Prop :=
fun A M => (
exists v : word I, exists w : word I,
forall q r : Y,
del M (q0 M) v = Some q
-> del M (q0 M) w = Some r
-> v <> w /\ equiv M M q r
).