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

Theorem andb_is_and : (forall a b, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
  intros a b.
  constructor.
    intros H.
    case a, b.
      simpl.
      exact (conj I I).
      simpl in H.
      case H.
      simpl in H.
      case H.
      simpl in H.
      case H.
    intros H.
    destruct H as [ga gb].
    case a, b.
    simpl.
    exact I.
    simpl.
    simpl in gb.
    exact gb.
    simpl.
    simpl in ga.
    exact ga.
    simpl.
    simpl in ga.
    exact ga.
Qed.

Lemma not_false : (~ False).
Proof.
  intros a.
  exact a.
Qed.

Theorem negb_is_not : (forall a, Is_true (negb a) <-> (~(Is_true a))).
Proof.
  intros a.
  case a.
  constructor.
  + simpl.
    intros f.
    case f.
  + simpl.
    intros nn.
    exact (nn I).
  + simpl.
    exact (prop_implies_iff _ not_false).
Qed.

Definition basic_predicate
:=
  (fun a => Is_true (andb a true))
.

Theorem thm_exists_basics : (exists a, Is_true (andb a true)).
Proof.
  pose (witness := true).
  refine (ex_intro _ witness _).
    simpl.
    exact I.
Qed.

Theorem thm_forall_exists : (forall b, (exists a, Is_true(eqb a b))).
Proof.
  intros b.
  case b.
  + pose (w := true).
    refine (ex_intro _ w _).
      simpl.
      exact I.
  + pose (w := false).
    refine (ex_intro _ w _).
      simpl.
      exact I.
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
    simpl.
    exact I.
    simpl.
    exact I.
Qed.

Theorem thm_forall_exists__again : (forall b, (exists a, Is_true(eqb a b))).
Proof.
  intros b.
  refine (ex_intro _ b _).
  exact (eqb_a_a b).
Qed.

Theorem forall_exists : (forall P : Set->Prop,
    (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  intros P G.
  intros C.
  destruct C as [x_wit x_proof].
  pose (inst := G x_wit).
  exact (inst x_proof).
Qed.

Inductive and3 (A B C : Prop) : Prop :=
  conj3  : A -> B -> C -> and3 A B C.

Theorem and3_impl_and : (forall A B C : Prop, and3 A B C -> and A B /\ and B C).
Proof.
  intros A B C.
  constructor.
  destruct H as [a b c].
  exact (conj a b).
  destruct H as [a b c].
  exact (conj b c).
Qed.

Inductive list (A : Prop) : Prop :=
  | empty : list A
  | add   : A -> list A.

Definition empty_list (A : Prop) (l : list A) : bool :=
  match l with
  | empty A => false
  | add _ => true
end.

Theorem not_empty_impl : (forall A : Prop, forall l : list A, not (empty_list A l) -> A).
Proof.
  intros A l.
  intros hyp.
  simpl in hyp.
+ pose (rr := eq l (empty A)).
  pose (rr := eq l (empty A)).
  simpl.
  case hyp.
