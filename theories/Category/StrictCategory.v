Require Export Category.Core.
Require Import Common Notations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Notation IsStrictCategory C := (IsHSet (Object C)).

Record StrictCategory :=
  {
    StrictPreCategory :> PreCategory;
    StrictCategory_IsStrict :> IsStrictCategory StrictPreCategory
  }.

Existing Instance StrictCategory_IsStrict.
