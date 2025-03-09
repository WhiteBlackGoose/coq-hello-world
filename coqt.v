Require Import Bool.

Theorem False_cannot_be_proven: ~ False.
Proof.
    unfold not.
    intros false.
    case false.
Qed.

Theorem not_eqb_true_false: ~(Is_true (eqb true false)).
Proof.
  simpl.
  exact False_cannot_be_proven.
Qed.

Theorem true_is_True: Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem absurd2 : forall A C : Prop, A -> ~ A -> C.
Proof.
  intros A C.
  intros proof_of_A proof_that_A_cannot_be_proven.
  unfold not in proof_that_A_cannot_be_proven.
  pose (proof_of_False := proof_that_A_cannot_be_proven proof_of_A).
  case proof_of_False.
Qed.

Theorem vacuous_truth : forall A : Prop, False -> A.
Proof.
    intros A.
    pose (a := fun (a:False) => match a with end : A).
    exact a.
Qed.


Theorem or_is_weaker_than_and : (forall A B : Prop, A /\ B -> A \/ B).
Proof.
    intros A B.
    intros pAandB.
    destruct pAandB as (pA & pB).
    pose (a_or_b_proof := or_introl (A := A) (B := B) pA).
    exact (a_or_b_proof).
Qed.

Theorem backward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
    intros A B C.
    intros pA pAiB pAiBiC.
    refine (pAiBiC _ _).
        exact pA.
        exact (pAiB pA).
Qed.

Theorem bool_reflexivity: (forall a: bool, Is_true (eqb a a)).
Proof.
    intros a.
    case a.
        (* a is true *)
        simpl.
        exact I.
        (* a is false *)
        simpl.
        exact I.
Qed.

Theorem and_implies_or: (forall A B: Prop, forall proof_of_and: A /\ B, A \/ B).
Proof.
    intros A B proof_of_and.
    case proof_of_and.
    intros pA pB.
    exact (or_introl pA).
Qed.

Theorem thm_eqb_a_t: (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
    intros a.
    case a.
        simpl.
        intros i.
        exact i.

        simpl.
        intros f.
        case f.
Qed.

Inductive triple_or (A B C : Prop) :=
    | c1 : A -> triple_or A B C
    | c2 : B -> triple_or A B C
    | c3 : C -> triple_or A B C.

Theorem one_of_3_holds: (forall A B C : Prop, triple_or A B C -> A \/ B \/ C).
Proof.
    intros A B C.
    intros o.
    case o.
        intros a.
        exact (or_introl a).
        intros b.
        pose (b_or_c := or_introl b : B \/ C).
        exact (or_intror b_or_c).
        intros c.
        pose (b_or_c := or_intror c : B \/ C).
        exact (or_intror b_or_c).
Qed.

Theorem right_or : (forall A B : Prop, B -> A \/ B).
Proof.
    intros A B.
    intros proof_of_B.
    refine (or_intror _).
        exact proof_of_B.
Qed.

Theorem or_commutes : (forall A B, A \/ B -> B \/ A).
Proof.
    intros A B.
    intros proof_of_A_or_B.
    pose (b_or_a := B \/ A).
    case proof_of_A_or_B.
        intros a.
        exact (or_intror a).
        intros b.
        exact (or_introl b).
Qed.

Theorem and_commutes : (forall A B, A /\ B -> B /\ A).
Proof.
    intros A B.
    intros pAB.
    case pAB.
    intros pA pB.
    refine (conj _ _).
        exact pB.
        exact pA.
Qed.

Theorem and_commutes_2 : (forall A B, A /\ B -> B /\ A).
Proof.
    intros A B.
    intros pAandB.
    destruct pAandB as [pA pB].
    exact (conj pB pA).
Qed.

Lemma True_implied : (forall A : Prop, A -> True).
Proof.
  intros A a.
  exact I.
Qed.

Lemma prop_implies_iff : (forall A : Prop, A -> True <-> A).
Proof.
  intros A a.
  constructor.
+ intros _.
  exact a.
+ exact (True_implied _).
Qed.

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.

  case a. {
    simpl.
    exact (prop_implies_iff _ (or_introl I)).
  }

  case b. {
    simpl.
    exact (prop_implies_iff _ (or_intror I)).
  }

  simpl.
  constructor.

  + intros F.
    case F.

  + intros F.
    case F.
    intros F0.
    exact F0.
    intros F1.
    exact F1.
Qed.

