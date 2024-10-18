Require Import Coq.Sets.Constructive_sets.
(* Conformance Testing Reconsidered *)

(* Enable classical logic *)
(* Sorry Freek, I know you love propositional logic*)
Parameter em: forall p:Prop, p \/ ~p.

(* Partial functions *)
Definition def {A : Type} (o : option A) : Prop :=
  match o with
  | Some a => True
  | None => False
  end.
Notation "f ↑" := (~ def f) (at level 303, no associativity) : type_scope.
Notation "f ↓" := (def f) (at level 303, no associativity) : type_scope.

(* We fix an input and an output set *)
Inductive I := ia | ib.
Inductive O := oa | ob.
Definition word := list.

(* Definition 2.1 (Mealy machine) *)
Structure Mealy : Type := {
  Q : Set;
  q0 : Q;
  delta : Q -> I -> option Q;
  lambda : Q -> I -> option O;
}.
(* This follows from domain knowledge, delta is defined iff lambda is defined *)
Parameter lambda_delta1: forall M : Mealy, forall i : I, forall q : Q M, 
  (delta M q i ↓) <-> (lambda M q i ↓).
Parameter lambda_delta2: forall M : Mealy, forall i : I, forall q : Q M, 
  (delta M q i ↑) <-> (lambda M q i ↑).

Definition complete {M : Mealy} (q : Q M) :=
  forall i : I, ((delta M q i) ↓).
Definition completeSet {M : Mealy} (W : Q M -> Prop) :=
  forall q : Q M,
    W q -> complete q.
(* Lift delta and lambda to sequences *)
Fixpoint deltaS {M : Mealy} (q: Q M) (v : word I) : option (Q M) :=
match v with
  | nil => Some q
  | cons i v' => 
    match (delta M q i) with
     | Some r => 
        match (deltaS r v') with
          | None => None
          | Some r' => Some r'
        end
     | None => None
    end
end.
Fixpoint lambdaS {M : Mealy} (q: Q M) (v : word I) : option (word O) :=
match v with
  | nil => Some nil
  | cons i v' => 
    match (delta M q i) with
     | Some r =>
        match (lambdaS r v') with
          | None => None
          | Some w => 
            match (lambda M q i) with
              | None => None
              | Some i => Some (cons i w)
            end
          end
     | None => None
    end
end.
Notation "q - v w -> r" := (lambdaS q v = w /\ deltaS q v = r) (at level 303, no associativity) : type_scope.
Notation "q = v w => r" := (q - v w -> r /\ length v > 0) (at level 303, no associativity) : type_scope.

Definition stateCover (M : Mealy) (A: (word I) -> Prop) : Prop 
  := forall q : Q M, exists v : (word I), A v /\ deltaS (q0 M) v = Some q.
Definition minimal (M : Mealy) (A: (word I) -> Prop) : Prop
  := forall q : Q M, ~ (exists v w : (word I), A v /\ A w /\ v <> w /\ deltaS (q0 M) v = Some q /\ deltaS (q0 M) w = Some q).
Definition initiallyConnected (M : Mealy) : Prop
  := exists A : ((word I) -> Prop), stateCover M A.
(* 'We will only consider Mealy machines that are initially connected.' *)
Parameter allInitiallyConnected : forall M : Mealy, initiallyConnected M.


Definition SI : (I*O) -> (I*O) -> Prop
   := fun '(i1,_) '(i2,_) => i1 = i2.

Definition SO : (I*O) -> (I*O) -> Prop
   := fun '(_,o1) '(_,o2) => o1 = o2.

Fixpoint first (lio : list (I * O)) : list I :=
match lio with
  | nil => nil
  | cons (i, o) lio' => cons i (first lio')
end.

Fixpoint second (lio : list (I * O)) : list O :=
match lio with
  | nil => nil
  | cons (i, o) lio' => cons o (second lio')
end.

Definition SI_star : list (I * O) -> list (I * O) -> Prop := 
  fun l1 l2 => first l1 = first l2.

Definition SO_star : list (I * O) -> list (I * O) -> Prop := 
  fun l1 l2 => second l1 = second l2.

Definition Mealy := LTS (I*O).

(*Definition Example (M N : MealyMachine) (q r : states M) (q' : states N) :=
exists sigma : I_star,
  transition M q (ia, o0) r.*)
Definition Apart (M N : Mealy) (q : states M) (r : states N) (v : list I) :=
exists io io': list (I * O),
  exists q' : states M, exists r' : states N,
    (q == io ==> q') /\ (r == io' ==> r')
  /\
    v = first io /\ v = first io' /\ ~ (first io = first io').

Notation "v ? q # r" := (Apart _ _ q r v) (at level 303, no associativity) : type_scope.
Notation "q # r" := (exists v : list I, (Apart _ _ q r v)) (at level 303, no associativity) : type_scope.
Notation "x ↓↓ a"  := (exists y : _ , (gtrans _ x a y)) (at level 303, no associativity) : type_scope.

Lemma A6_WeakCoTransitivity : 
forall M : Mealy, forall r r' q : states M, forall io : list (I*O),
  ((first io) ? r # r') /\ (q ↓↓ io)
->
  (r # q) \/ (r' # q).
Proof.
intros.
destruct H.
elim em with (r # q).
intro x.
left.
apply x.

intro x.
right.
unfold Apart in H.
unfold Apart.
exists (first io).
exists io.


Qed.