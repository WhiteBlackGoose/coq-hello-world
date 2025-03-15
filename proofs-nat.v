Load MyAlgebra.

Instance nat_add_magma : magma nat :=
  { op a b := a + b; }.

#[refine]
Instance nat_add_assoc : associative nat := {}.
Proof.
  intros a b c.
  simpl.
  elim a.
  elim b.
  elim c.
  + simpl.
    exact (eq_refl 0).
  + intros n.
    simpl.
    intros _.
    exact (eq_refl (S n)).
  + intros n.
    simpl.
    intros _.
    exact (eq_refl (S (n + c))).
  + intros n.
    intros prem.
    simpl.
    rewrite prem.
    exact (eq_refl (S (n + b + c))).
Qed.

Lemma plus_0 : (forall n : nat, n + 0 = n).
Proof.
  intros n.
  induction n.
  + simpl.
    exact (eq_refl 0).
  + simpl.
    rewrite IHn.
    exact (eq_refl (S n)).
Qed.

#[refine]
Instance nat_add_identity : has_identity nat := {
  id := 0;
}.
Proof.
+ intros a.
  constructor.
  - simpl.
    exact (eq_refl a).
  - simpl.
    exact (plus_0 a).
Qed.

#[refine]
Instance nat_add_comm : @commutative nat nat_add_magma := {}.
Proof.
  intros a b.
  simpl.
  exact (Nat.add_comm a b).
Qed.

Theorem addition_not_divisible_by_subtraction : (~ (divisibility nat add sub)).
Proof.
  unfold not.
  intros prop.
  unfold divisibility in prop.
  assert (f := prop 1 4).
  simpl in f.
  destruct f as [_ inv].
  simplify_eq inv.
Qed.


Instance nat_mul_magma : magma nat :=
  { op a b := a * b; }.


#[refine]
Instance nat_mul_assoc : @associative nat (nat_mul_magma) := {}.
Proof.
  unfold associativity.
  intros a b c.
  simpl.
  exact (Nat.mul_assoc a b c).
Qed.

#[refine]
Instance nat_mul_identity : @has_identity nat (nat_mul_magma) := {
  id := 1;
}.
Proof.
  unfold identity.
  intros a.
  constructor.
  + simpl.
    exact (Nat.mul_1_l a).
  + simpl.
    exact (Nat.mul_1_r a).
Qed.

#[refine]
Instance nat_mul_comm : @commutative nat nat_mul_magma := {}.
Proof.
  intros a b.
  simpl.
  exact (Nat.mul_comm a b).
Qed.

