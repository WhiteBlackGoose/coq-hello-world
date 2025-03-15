Require Import Bool.
Require Import Nat.

Require Import Arith.
Require Import Arith.PeanoNat.

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

Definition distributivity (A : Type) (add : A -> A -> A) (mul : A -> A -> A) :=
    forall a b c : A, mul a (add b c) = add (mul a b) (mul a c).

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

Class distributive (A : Type) (add : A -> A -> A) (mul : A -> A -> A) :=
  { distrib : distributivity A add mul }.

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


Class ring (A : Type)
  (g_add : magma A)
  `{g_add_g : abelian_group A }
  (g_mul : magma A)
  {g_mul_ass : @associative A g_mul }
  {g_mul_id : @has_identity A g_mul }
  `{g_mul_mon : @monoid A g_mul g_mul_ass g_mul_id }
  `{g_mul_comm : @commutative A g_mul }
  {g_distr : distributive A (@op A g_add) (@op A g_mul)}
  := {}.

Definition divisibility_except (A : Type) (hole : A) (inv : A -> A -> A) {m : magma A} :=
  forall a b : A, b <> hole -> op (inv a b) b = a /\ op b (inv a b) = a.

Class field (A : Type)
  {g_add : magma A}
  {g_add_id : has_identity A}
  `{g_add_g : abelian_group A}
  {g_mul : magma A}
  `{g_mul_comm : commutative A}
  {g_distr : distributive A (@op A g_add) (@op A g_mul)}
  := {
    inv : A -> A -> A;
    div_non_zero : divisibility_except A (@id A g_add g_add_id) inv;
  }.


