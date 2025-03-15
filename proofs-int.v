Load MyAlgebra.

Require Import ZArith.
Require Import ZArith.Int.

Open Scope Z_scope.

Instance int_add_magma : magma Z := {
  op a b := a + b;
}.

Instance int_add_ass : @associative Z int_add_magma := {
  assoc := Z.add_assoc;
}.

Instance int_add_comm : @commutative Z int_add_magma := {
  comm := Z.add_comm;
}.

#[refine]
Instance int_add_id : @has_identity Z int_add_magma := {
  id := 0;
}.
Proof.
  unfold identity.
  intros a.
  simpl.
  constructor.
  + exact (eq_refl a).
  + rewrite Zplus_0_r.
    exact (eq_refl a).
Qed.

#[refine]
Instance int_add_inv : @divisible Z int_add_magma := {
  op_inv a b := a - b;
}.
Proof.
  unfold divisibility.
  intros a b.
  constructor.
  - simpl.
    unfold Zminus.
    rewrite (Zplus_assoc_reverse a (-b) b).
    rewrite (Zplus_comm (-b) b).
    rewrite Zplus_opp_r.
    rewrite Zplus_0_r.
    exact (eq_refl a).
  - simpl.
    unfold Zminus.
    rewrite Zplus_comm.
    rewrite <- Zplus_assoc.
    rewrite (Zplus_comm (-b) b).
    rewrite Zplus_opp_r.
    rewrite Zplus_0_r.
    exact (eq_refl a).
Qed.

Instance int_add_group : group Z := {}.

Instance int_add_abelian_group : abelian_group Z := {}.

Instance int_mul_magma : magma Z := {
  op := Zmult;
}.

#[refine]
Instance int_mul_ass : @associative Z int_mul_magma := {}.
Proof.
  unfold associativity.
  simpl.
  exact Zmult_assoc.
Qed.

#[refine]
Instance int_mul_id : @has_identity Z int_mul_magma := {
  id := 1;
}.
Proof.
  unfold identity.
  intros a.
  exact (conj (Zmult_1_l a) (Zmult_1_r a)).
Qed.

#[refine]
Instance int_mul_comm : @commutative Z int_mul_magma := {}.
Proof.
  simpl.
  exact Zmult_comm.
Qed.

Instance int_mul_monoid : @monoid Z int_mul_magma int_mul_ass int_mul_id := {}.

#[refine]
Instance int_distr : distributive Z (@op Z int_add_magma) (@op Z int_mul_magma) := {}.
Proof.
  unfold distributivity.
  simpl.
  exact Zmult_plus_distr_r.
Qed.

Instance int_ring : ring Z int_add_magma int_mul_magma := {}.
