Require Export Category Functor NaturalTransformation.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section FunctorPreCategory.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  (** There is a category Fun(C, D) of functors from [C] to [D]. *)

  Definition FunctorPreCategory : PreCategory.
    refine (@Build_PreCategory (Functor C D)
                               (NaturalTransformation (C := C) (D := D))
                               (IdentityNaturalTransformation (C := C) (D := D))
                               (NTComposeT (C := C) (D := D))
                               _
                               _
                               _
                               _);
    abstract (nt_eq; auto with morphism).
  Defined.
End FunctorPreCategory.

Notation "C ^ D" := (FunctorPreCategory D C) : category_scope.
