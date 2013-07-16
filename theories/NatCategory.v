Require Export Category DiscreteCategory.
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

Definition NatCategory (n : nat) := DiscreteCategory n.

Coercion NatCategory : nat >-> PreCategory.

Typeclasses Transparent NatCategory.
Hint Unfold NatCategory.
Arguments NatCategory / .
