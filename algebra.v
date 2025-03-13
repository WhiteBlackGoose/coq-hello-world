Require Import Bool.
Require Import Nat.

(*

https://en.wikipedia.org/wiki/Magma_(algebra)#Types_of_magma

*)

Definition associativity (A : Type) (op : A -> A -> A) :=
  forall a b c : A, op a (op b c) = op (op a b) c.

Definition divisibility (A : Type) (op : A -> A -> A) (op_inv : A -> A -> A) :=
  forall a b : A, op (op_inv a b) b = a /\ op b (op_inv a b) = a.

Definition identity (A : Type) (id : A) (op : A -> A -> A) :=
  forall a : A, op id a = a /\ op a id = a.

Definition commutativity (A : Type) (op : A -> A -> A) :=
  forall a b : A, op a b = op b a.

Class magma (A : Type) :=
  { op : A -> A -> A }.

Class associative (A : Type) {m : magma A} :=
  { assoc : associativity A op }.

Class divisible (A : Type) {m : magma A} :=
  { op_inv : A -> A -> A;
    div : divisibility A op op_inv }.

Class has_identity (A : Type) {m : magma A} :=
  { id : A;
    id_holds : identity A id op }.

Class commutative (A : Type) {m : magma A} :=
  { comm : forall a b : A, op a b = op b a }.

Class semigroup (A : Type)
  {q1 : magma A}
  {q2 : associative A} := {}.
Class unital_magma (A : Type)
  {q1 : magma A}
  {q2 : has_identity A} := {}.
Class quasigroup (A : Type)
  {q1 : magma A}
  {q2 : divisible A} := {}.
Class associative_quasigroup (A : Type)
  {q1 : magma A}
  {q2 : divisible A}
  {q3 : associative A} := {}.
Class loop (A : Type)
  {q1 : magma A}
  {q2 : divisible A}
  {q3 : has_identity A} := {}.
Class monoid (A : Type)
  {q1 : magma A}
  {q2 : associative A}
  {q3 : has_identity A} := {}.
Class group (A : Type)
  {q1 : magma A}
  {q2 : associative A}
  {q3 : divisible A}
  {q4 : has_identity A} := {}.
Class abelian_group (A : Type)
  `{q : group A}
  {c : commutative A}
  := {}.



Definition divisibility_except (A : Type) (hole : A) (inv : A -> A -> A) {m : magma A} :=
  forall a b : A, b <> hole -> op (inv a b) b = a /\ op b (inv a b) = a.

Class field (A : Type)
  {g_add : magma A}
  {g_add_id : has_identity A}
  `{g_add_g : abelian_group A}
  {g_mul : magma A}
  `{g_mul_comm : commutative A}
  := {
    inv : A -> A -> A;
    div_non_zero : divisibility_except A (@id A g_add g_add_id) inv;
    distrib :
      let add a b := @op A g_add a b in
      let mul a b := @op A g_mul a b in
      forall a b c : A, mul a (add b c) = add (mul a b) (mul a c);
  }.


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


