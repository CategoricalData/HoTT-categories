Require Export Category.Core Category.Morphisms Category.StrictCategory.
Require Import Common Notations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Class IsCategory (C : PreCategory) :=
  category_is_category : forall s d : C, IsEquiv (@idtoiso C s d).

Notation isotoid C s d := (@equiv_inv _ _ _ (@category_is_category C _ s d)).

Hint Unfold IsCategory : typeclass_instances.

Instance trunc_category `{IsCategory C} : IsTrunc 1 C | 10000.
Proof.
  intros ? ?.
  eapply trunc_equiv';
  [ apply symmetry;
    esplit;
    apply_hyp
  | ].
  typeclasses eauto.
Qed.
