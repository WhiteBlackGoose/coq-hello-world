Require Import Bool.
Require Import List.

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

Theorem equiv_is_eq : (forall A B : Prop, (A = B) -> (A <-> B)).
Proof.
  intros A B.
  constructor.
  destruct H as [a].
  trivial.
  destruct H as [a].
  trivial.
Qed.

Theorem thm_eq_sym : (forall x y : Set, x = y -> y = x).
Proof.
  intros x y.
  intros x_y.
  destruct x_y as [].
  exact (eq_refl x).
Qed.

Theorem thm_eq_trans__again : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
  intros x y z.
  intros x_y y_z.
  rewrite x_y.
  rewrite <- y_z.
  exact (eq_refl y).
Qed.

Theorem neq_nega: (forall a, a <> (negb a)).
Proof.
  intros a.
  unfold not.
  case a.
    intros a_eq_neg_a.
    simpl in a_eq_neg_a.
    discriminate a_eq_neg_a.

    intros a_eq_neg_a.
    simpl in a_eq_neg_a.
    discriminate a_eq_neg_a.
Qed.


Theorem plus_n_O : (forall n, n + O = n).
Proof.
  intros n.
  elim n.
  + simpl.
    exact (eq_refl 0).
  + intros n0 f.
    simpl.
    rewrite f.
    exact (eq_refl (S n0)).
Qed.

Theorem plus_sym: (forall n m, n + m = m + n).
Proof.
  intros n m.
  elim n.
    elim m.
      exact (eq_refl (O + O)).
      intros m'.
      intros inductive_hyp_m.
      simpl.
      rewrite <- inductive_hyp_m.
      simpl.
      exact (eq_refl (S m')).

    intros n' ind_hyp_n.
    simpl.
    rewrite ind_hyp_n.
    elim m.
      simpl.
      exact (eq_refl (S n')).
      intros m'.
      intros inductive_hyp_m.
      simpl.
      rewrite inductive_hyp_m.
      simpl.
      exact (eq_refl (S (m' + S n'))).
Qed.

Theorem plus_sym_my: (forall n m, n + m = m + n).
Proof.
  intros n m.
  elim n.
  + simpl.
    exact (eq_sym (plus_n_O _)).
  + intros n' ind.
    simpl.
    rewrite ind.
    elim m.
    - simpl.
      exact (eq_refl (S n')).
    - intros m' ind2.
      simpl.
      rewrite ind2.
      exact (eq_refl (S (m' + S n'))).
Qed.

Theorem cons_adds_one_to_length :
   (forall A:Type,
   (forall (x : A) (lst : list A),
   length (x :: lst) = (S (length lst)))).
Proof.
  intros A x lst.
  simpl.
  exact (eq_refl (S (length lst))).
Qed.

Inductive idk (A:Type) :=
  | nuhuh : idk A
  | nocap : A -> idk A.

Definition xd (A:Type) (lst:list A) : idk A :=
  match lst with
  | nil => nuhuh _
  | smh :: _ => nocap _ smh
  end.
  

Fixpoint sum (lst : list nat) : nat :=
  match lst with
  | hd :: rst => hd + sum rst
  | nil => 0
  end.

Compute sum (1 :: 2 :: 3 :: nil).

Definition hd_error (A : Type) (l : list A)
:=
  match l with
    | nil => None
    | x :: _ => Some x
  end.

Theorem correctness_of_hd_error :
   (forall A:Type,
   (forall (x : A) (lst : list A),
   (hd_error A nil) = None /\ (hd_error A (x :: lst)) = Some x)).
Proof.
  intros A x lst.
  constructor.
  + simpl.
    exact (eq_refl (None)).
  + simpl.
    exact (eq_refl (Some x)).
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

Definition empty_list (A : Type) (l : list A) : bool :=
  match l with
  | nil => true
  | _ => false
end.

Theorem not_empty_impl :
    (forall A : Type,
    forall l : list A,
    not (Is_true (empty_list A l)) -> A).
Proof.
  intros A lst.
  unfold not.
  intros premise.
  induction lst.
  + simpl in premise.
    case (premise I).
  + simpl in premise.
    exact a.
Qed.

Section MyMergesort.

Require Import Nat.

Fixpoint sorted (lst:list nat): bool :=
  match lst with
  | nil => true
  | _ :: nil => true
  | hd1 :: ((hd2 :: rst) as tl) => (hd1 <=? hd2) && sorted tl
  end.

Fixpoint merge (l1:list nat) (l2:list nat) :=
  match l1, l2 with
  | nil, rst | rst, nil => rst
  | (h1 :: r1), (h2 :: r2) =>
    if h1 <=? h2 then
      h1 :: h2 :: merge r1 r2
    else
      h2 :: h1 :: merge r1 r2
  end.

Lemma sublist_sorted : (forall a l, Is_true (sorted (a :: l)) -> Is_true (sorted l)).
Proof.
  intros a l.
  intros prem.
  induction l.
  + trivial.
  + simpl in prem.
    assert (prem' := andb_prop_elim _ _ prem).
    destruct prem' as [_ sorted_l].
    exact sorted_l.
Qed.

Lemma merge_nil_stays : (forall l, merge l nil = l).
Proof.
  intros l.
  induction l.
  + simpl.
    exact (eq_refl nil).
  + simpl.
    exact (eq_refl (a :: l)).
Qed.

Lemma sorted_merge_sublist :
    (forall a l1 l2,
      Is_true (sorted l1)
      -> Is_true (sorted l2)
      -> Is_true (sorted (merge l1 (a :: l2)))
      -> Is_true (sorted (merge l1 l2))).
Proof.
  intros a l1 l2.
  admit.
Admitted.

Theorem merge_returns_sorted :
    (forall l1 l2 : list nat,
    Is_true (sorted l1) /\ Is_true (sorted l2)
    -> Is_true (sorted (merge l1 l2))).
Proof.
  intros l1 l2.
  elim l1.
  elim l2.
  + simpl.
    trivial.
  + simpl.
    intros a l' prem.
    intros prem'.
    destruct prem' as [_ i].
    exact i.
  + intros a l' step prem.
    destruct prem as [sorted_a_l' sorted_l2].
    assert (sorted_l'_l2 : Is_true (sorted (merge l' l2))).
    {
      exact (step (conj (sublist_sorted a l' sorted_a_l') sorted_l2)).
    }
    clear step.
    destruct l2 as [ | a' l2'].
    - rewrite (merge_nil_stays (a :: l')).
      exact sorted_a_l'.
    - simpl.
      destruct (a <=? a') eqn:f.
      * simpl.
        rewrite f.
        assert (sorted_l'_l2' : Is_true (sorted (merge l' l2'))).
        {
          exact (sorted_merge_sublist )
        }
        simpl.
        rewrite (Is_true_eq_true )
