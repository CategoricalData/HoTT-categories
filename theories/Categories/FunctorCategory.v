Require Export Category Functor NaturalTransformation.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section FunctorCategory.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  (** There is a category Fun(C, D) of functors from [C] to [D]. *)

  Definition FunctorCategory : PreCategory.
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
End FunctorCategory.

Notation "C ^ D" := (FunctorCategory D C) : category_scope.
Notation "[ C , D ]" := (FunctorCategory C D) : category_scope.

Lemma IsStrict_FunctorCategory `{Funext} C `{IsStrictCategory D}
: IsStrictCategory [C, D].
Proof.
  typeclasses eauto.
Defined.
