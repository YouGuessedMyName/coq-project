(* Require Import Coq.Sets.Constructive_sets. *)
(* Conformance Testing Reconsidered *)

Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Lists.List.

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

(* v is a prefix of w *)
Definition pref (v w : word I) : Prop := exists v' : word I, v ++ v' = w.
(* A is the set of prefixes of set B *)
Definition Pref (A B : word I -> Prop) := 
forall a b : word I, A a /\ B b <-> pref a b.


(* Definition 2.1 (Mealy machine) *)
(* Here, we deviate a bit from the paper. Instead of having two transitions functions, we combine them into one *)
Definition Y := word I.
Structure Mealy : Type := {
  q0 : Y;
  trans : Y -> I -> option (Y * O);
  Q : Y -> Prop;
}.

(* The intial state is always in the states *)
Parameter initial : forall M : Mealy, Q M (q0 M).

Definition delta (M : Mealy) (q : Y) (i : I) : option (Y) :=
match (trans M q i) with
  | None => None
  | Some (r, _) => Some r
end.
Definition lambda (M : Mealy) (q : Y) (i : I) : option O :=
match (trans M q i) with
  | None => None
  | Some (_, o) => Some o
end.
(* This follows from domain knowledge, delta is defined iff lambda is defined *)
(* Parameter lambda_delta1: forall M : Mealy, forall i : I, forall q : Q M, 
  (delta M q i ↓) <-> (lambda M q i ↓).
Parameter lambda_delta2: forall M : Mealy, forall i : I, forall q : Q M, 
  (delta M q i ↑) <-> (lambda M q i ↑). *)

Definition complete (M : Mealy) (q : Y) :=
  forall i : I, ((trans M q i) ↓).
Definition completeSet {M : Mealy} (W : Y -> Prop) :=
  forall q : Y, Q M q ->
    W q -> complete M q.
Definition completeM (M : Mealy) : Prop
  := forall q : Y, Q M q -> complete M q.
(* Lift delta and lambda to sequences *)
Fixpoint transS (M : Mealy) (q: Y) (v : word I) : (option ((Y) * word O)) :=
match v with
  | nil => Some (q, nil)
  | cons i v' => 
    match (trans M q i) with
     | Some (r, o) => 
        match (transS M r v') with
          | None => None
          | Some (r', w) => Some (r', w)
        end
     | None => None
    end
end.
Definition deltaS (M : Mealy) (q: Y) (v : word I) : (option (Y)) := 
match (transS M q v) with
  | Some (r, w) => Some r
  | None => None
end.
Definition lambdaS (M : Mealy) (q: Y) (v : word I) : (option (word O)) := 
match (transS M q v) with
  | Some (r, w) => Some w
  | None => None
end.

Notation "q - v w -> r" := (transS q v = (r, w)) (at level 303, no associativity) : type_scope.
Notation "q = v w => r" := (q - v w -> (r, w) /\ length v > 0) (at level 303, no associativity) : type_scope.

Definition stateCover (M : Mealy) (A: (word I) -> Prop) : Prop 
  := forall q : Y, Q M q -> exists v : (word I), A v /\ deltaS M (q0 M) v = Some q.
Definition minimalStateCover (M : Mealy) (A: (word I) -> Prop) : Prop
  := stateCover M A /\ forall q : Y, Q M q -> ~ (exists v w : (word I), A v /\ A w /\ v <> w /\ deltaS M (q0 M) v = Some q /\ deltaS M (q0 M) w = Some q).
Definition initiallyConnected (M : Mealy) : Prop
  := exists A : ((word I) -> Prop), stateCover M A.
(* 'We will only consider Mealy machines that are initially connected.' *)
Parameter allInitiallyConnected : forall M : Mealy, initiallyConnected M.

(* Definition 2.2 (Semantics and minimality) *)
Definition semantics (M : Mealy) (q : Y) :=
  lambdaS M q.
Notation "[ q ]" := (semantics q) (at level 303, no associativity) : type_scope. 
Definition equiv (M N : Mealy) (q : Y) (r : Y) : Prop :=
  semantics M q = semantics M r.
Notation "q ≈ r" := (equiv q r) (at level 303, no associativity) : type_scope. 
Definition equivM (M N : Mealy) : Prop :=
  equiv M N (q0 M)(q0 N).
Definition minimalM (M : Mealy) : Prop :=
  forall q r : Y, Q M q -> Q M r -> (equiv M M q r) <-> q <> r.

(* Definition 2.4 (Simulation) *)
(* f : M -> N is a funcitonal simulation from M to N *)
Definition funcSim (M N : Mealy) (f: Y -> Y) : Prop :=
  f(q0 M) = q0 N 
/\
  forall q : Y, Q M q -> forall i : I, 
      match (trans M q i) with
        | None => True
        | Some (r, o) => 
          match (trans N (f q) i) with
            | None => False
            | Some (r', o') => (f r = r') /\ o = o'
          end
      end
.

(* Definition 2.5 (Observation tree) *)
Definition tree (M : Mealy) : Prop
  := forall v : word I, deltaS M (q0 M) v = Some v.

Definition access (M : Mealy) (v : word I) : word I := v.

Definition accessSet {M : Mealy} (U: Y -> Prop): (word I -> Prop)
  := U.

(* q' is the parent of q *)
Definition parent {M : Mealy} (q q' : Y) : Prop
  := exists i : I, delta M q' i = Some q.

(* T is an observation tree for M *)
Definition observationTreeFor (T : Mealy) (M : Mealy) : Prop
  := exists f : (Y -> Y), funcSim T M f.

(* Definition 2.7 (Test suites) *)
(* v is a test case for S *)
Definition testCase (v : word I) (S : Mealy) := def (transS S (q0 S) v).

(* T is a test suite for S *)
Definition testSuite (T : word I -> Prop) (S : Mealy) := 
    Finite (word I) T /\ forall v : word I, T v -> testCase v S.

(* M passes test v for S *)
Definition passes1 (S M : Mealy) (v : word I) :=
  lambdaS M (q0 S) v = lambdaS M (q0 M) v.

(* M passes test suite T for S *)
Definition passes2 (S M : Mealy) (T : word I -> Prop) :=
  forall v : word I, T v -> passes1 S M v.

Check Union.
Check Same_set.
Print Same_set.
Check Finite.
Check Ensemble.
(* Union _ T T = Union _ T T. *)
(* Same_set _ T T *)

(* TT is a testing tree for test suite T and Mealy machine S *)
Definition testingTree (TT S : Mealy) (T : word I -> Prop) : Prop :=
tree TT /\
(* QT = {ϵ} ∪ Pref (T ) and qT0 = ϵ,*)
(forall A : word I -> Prop, Pref A T -> A = Q TT) /\
(* For all σ ∈ I∗ and i ∈ I with σi ∈ QT , δT (σ, i) = σi, *)
(forall v : word I, forall i : I, 
  Q TT (v ++ cons i nil) ->
    delta TT v i = Some (v ++ cons i nil)) /\
(* For all σ ∈ I∗ and i ∈ I with σi ∈ QT , λT (σ, i) = λS (δS (qS0 , σ), i).*)
(forall v : word I, forall i : I,
  Q TT (v ++ cons i nil) ->
    match (deltaS S (q0 S) v) with
      | None => True
      | Some w => lambda TT v i = lambda S w i
    end
).

(* For every Tree, the root state is nil. *)
Lemma treeRoot : forall TT : Mealy, tree TT -> q0 TT = nil.
Proof.
intros.
unfold tree in H.
specialize (H nil).
unfold deltaS in H.
unfold transS in H.
injection H as H.
apply H.
Qed.

Lemma lemma_2_9 : forall S TT : Mealy, forall T : word I -> Prop, forall f: Y -> Y,
        (testingTree TT S T 
      /\ 
        (forall v : Y, Q TT v ->
          match (deltaS S (q0 S) v) with
            | None => False
            | Some r => f v = r
          end))
  ->
    funcSim TT S f.
Proof.
intros.
destruct H.
unfold funcSim.
split.
  - specialize (H0 (q0 TT)).
    rewrite treeRoot in H0.
    unfold deltaS in H0.
    unfold transS in H0.
    rewrite treeRoot.
    apply H0.
    rewrite <-treeRoot with TT.
    apply initial.
    apply H. apply H. apply H.

  - intros.
    unfold deltaS in H0.
    unfold testingTree in H.
    
    
    apply H0.

(* lambda TT v i = lambda S (deltaS S (q0 S) v) i) *)
Definitino testingTree2 (TT M : Mealy) (T : word I -> Prop) :=


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