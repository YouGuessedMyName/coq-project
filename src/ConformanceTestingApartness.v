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
Fixpoint deltaS (M : Mealy) (q: Y) (v : word I) : (option (Y)) := 
match v with
  | nil => Some q
  | i :: v' =>
    match (delta M q i) with
      | None => None
      | Some r => deltaS M r v'
    end
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

Parameter trans_em :
forall M : Mealy, 
  forall q : Y, 
    forall i : I,
  trans M q i = None \/ exists r : Y, exists o : O, trans M q i = Some (r, o).

Parameter transS_em : 
forall M : Mealy, 
  forall q : Y, 
    forall v : word I,
  transS M q v = None \/ exists r : Y, exists w : word O, transS M q v = Some (r, w).

Parameter option_em :
forall A : Type, forall o : option A,
  o = None \/ exists a : A, o = Some a.

Lemma delta_em :
forall M : Mealy, 
  forall q : Y, 
    forall i : I,
      delta M q i = None \/ exists r : Y, delta M q i = Some r.
Proof.
intros.
destruct option_em with Y (delta M q i).


Parameter deltaS_em :
forall M : Mealy, 
  forall q : Y, 
    forall v : word I,
      deltaS M q v = None \/ exists r : Y, deltaS M q v = Some r.

(* delta(q, av) = s, and delta(q, a) = r, and delta(r, v) = s' => s = s' *)
Lemma delta_property1 : 
forall M : Mealy, 
  forall a : I,
    forall v : word I,
      forall q r s s' : Y,
          deltaS M q (a :: v) = Some s
        ->
            delta M q a = Some r
          ->
            deltaS M r v = Some s'
              -> s = s'
.
Proof.
intros.
unfold deltaS in H.
rewrite H0 in H.
unfold deltaS in H1.
destruct em with (Some s = Some s').
injection H2 as H2.
apply H2.
elim H2.
rewrite<- H.
rewrite<- H1.
reflexivity.
Qed.

Lemma delta_undefined_property : 
forall M : Mealy, 
  forall q r : Y,
    forall v : word I,
      forall a : I,
        delta M q a = Some r ->
        deltaS M r v = None -> deltaS M q (a :: v) = None.
Proof.
intros.
unfold deltaS in H0.
unfold deltaS.
rewrite H.
apply H0.
Qed.

Lemma delta_undefined_contradiction :
forall M : Mealy, 
  forall q r : Y,
    forall v : word I,
      forall a : I,
        
        delta M q a = Some r ->
        deltaS M r v = None -> (exists s : Y, (deltaS M q (a :: v) = Some s)) -> False.
Proof.
intros.
destruct H1 as [s].
destruct em with (deltaS M q (a :: v) = None).
rewrite H2 in H1.
discriminate H1.
destruct (delta_undefined_property M q r v a).
apply H.
apply H0.
unfold not in H2.
apply H2.
reflexivity.
Qed.

Lemma helper1 : 
forall M : Mealy, 
  forall q r : Y,
    forall i : I,
      transS M r (i :: nil) = None -> trans M r i = None.
Proof.
(* transS M q (v ++ i :: nil) = None *)
intros.
inversion H.
destruct trans_em with M r i.
apply H0.
destruct H0. destruct H0.
rewrite H0 in H1.
discriminate H1.
Qed. 

Lemma lemma_a_1A : 
forall M : Mealy, 
    forall i : I, 
      forall v : word I,
        forall t : Y,
        match (deltaS M t v) with
          | None => True
          | Some r => (deltaS M t (v ++ i :: nil)) = (deltaS M r (i :: nil))
        end
.
Proof.
induction v.
(* Base case *)
intro q.
simpl.
reflexivity.

(* Inductive case *)
intro q.

destruct deltaS_em with M q (a :: v).
rewrite H.
trivial.
(* q -a/b-> r -> v/w-> s -> i/o -> t*)
destruct H as [s].

rewrite H.
simpl.

destruct delta_em with M q a.
exfalso.
unfold deltaS in H.
rewrite H0 in H.
discriminate H.
destruct H0 as [r].

rewrite H0.
specialize IHv with r.

destruct deltaS_em with M r v.
  exfalso.
  apply delta_undefined_contradiction with M q r v a.
  apply H0.
  apply H1.
  exists s.
  apply H.

destruct H1 as [s'].

rewrite H1 in IHv.
rewrite IHv.
simpl.
destruct em with (s = s').
rewrite H2.
reflexivity.
elim H2.
apply (delta_property1 M a v q r s s').
apply H.
apply H0.
apply H1.
Qed.

rewrite IHv.
clear IHv.
simpl.

destruct delta_em with M s i.
admit.
destruct H1 as [t].
rewrite H1.


destruct deltaS_em with M r (v ++ i :: nil)..
admit.
destruct H2 as [t].
rewrite H2 in IHv.
rewrite H2.
destruct trans_em with M s i.
admit.
destruct H3 as [t']. destruct H3 as [o'].
rewrite IHv.
clear IHv.
simpl.
destruct em with (s = s').
rewrite H4.
reflexivity.
exfalso.
clear IHv.

admit.
unfold transS in H1.


destruct H0 as [s_a]. 
specialize IHv with r.
rewrite H.
unfold deltaS.
destruct transS_em with M q ((a :: v) ++ i :: nil).
admit.
destruct H0 as [s]. destruct H0 as [o'].
rewrite H0.
simpl.
destruct trans_em with M q a.
admit.
destruct H0 as []


specialize IHv with r.
destruct transS_em with M r v.
admit.
destruct H0 as [s]. destruct H0 as [i'].
rewrite H0 in IHv.
(* q -v/w-> r -i-> s *)
(* delta(r, vi) = delta(s, i) *)
(* TP: delta(q, avi) = delta(r, vi) =(IH)= delta(s, i) *)
destruct transS_em with M q (a ::v).
admit.
destruct H1 as [r']. destruct H1 as

(* intros.
destruct transS_em with M q v.
- rewrite H0. trivial.
- destruct H0. destruct H0.
  rewrite H0.
  unfold deltaS.
  destruct transS_em with M x (i :: nil).
  * rewrite H1.
    destruct transS_em with M q (v ++ i :: nil).
    rewrite H2.
    trivial.
    destruct H2. destruct H2.
    exfalso.
    admit.
  * destruct H1. destruct H1.
    destruct transS_em with M q (v ++ i :: nil).
    + exfalso.
      admit.
    + destruct H2. destruct H2.
      induction v.
      simpl.
      unfold transS in H0.
      injection H0 as H0.
      rewrite H0.
      tauto.
      
      clear IHv.
      destruct trans_em with M q a.
      simpl.
      unfold transS in H0.
      rewrite H3 in H0.
      discriminate H0.

      destruct H3. destruct H3.
      simpl.
      rewrite H3. *)
       
          



Lemma helper2 : 
forall M : Mealy, 
  forall q r : Y,
    forall i : I,
      forall v : word I,
      transS M r (i :: nil) = None -> transS M q (v ++ i :: nil)= None.
Proof.
(* transS M q (v ++ i :: nil) = None *)
intros.
destruct trans_em with M r i.
destruct transS_em with M q (v ++ i :: nil).
apply H1.
destruct H0. destruct H1. destruct H0.
rewrite H0.
exfalso.

(* admit. *)
unfold transS.
destruct H0. destruct H0.
unfold transS in H.
rewrite H0 in H.
discriminate H.
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