Require Export Category.Core.
Require Import Common Notations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Class IsStrictCategory (C : PreCategory) :=
  Strict_category_is_strict : IsHSet (Object C).

(*Existing Instance Strict_category_is_strict.*)

Hint Unfold IsStrictCategory : typeclass_instances.

Record StrictCategory :=
  {
    StrictPreCategory :> PreCategory;
    StrictCategory_IsStrict :> IsStrictCategory StrictPreCategory
  }.

Existing Instance StrictCategory_IsStrict.
