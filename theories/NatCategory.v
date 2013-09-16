Require Export Category DiscreteCategory IndiscreteCategory.
Require Import Common.

Set Universe Polymorphism.

Fixpoint CardinalityRepresentative (n : nat) : Set :=
  match n with
    | 0 => Empty
    | 1 => Unit
    | S n' => (CardinalityRepresentative n' + Unit)%type
  end.

Coercion CardinalityRepresentative : nat >-> Sortclass.

Instance trunc_CardinalityRepresentative (n : nat)
: IsHSet (CardinalityRepresentative n).
Proof.
  induction n; [ typeclasses eauto |].
  induction n; [ typeclasses eauto |].
  intros [x|x] [y|y];
  typeclasses eauto.
Qed.

Definition NatCategory (n : nat) :=
  match n with
    | 0 => IndiscreteCategory 0
    | 1 => IndiscreteCategory 1
    | S (S n') => DiscreteCategory (S (S n'))
  end.

Coercion NatCategory : nat >-> PreCategory.

Notation "1" := (NatCategory 1) : category_scope.

Typeclasses Transparent NatCategory.
Hint Unfold NatCategory.
Arguments NatCategory / .
