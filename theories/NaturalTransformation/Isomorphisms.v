Require Export FunctorCategory Category.Morphisms.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Universe Polymorphism.

Definition FunctorCategoryOf `{Funext} {C} {D} (F : Functor C D) := [C, D]%category.
Arguments FunctorCategoryOf / .
Notation "F ≅ G" := (Isomorphic F%functor G%functor) : functor_scope.
Notation "F ≅ G" := (Isomorphic (C := FunctorCategoryOf F) F%functor G%functor) : functor_scope.
