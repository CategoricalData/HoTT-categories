Require Export Functor.Product FunctorCategory.
Require Import Common NaturalTransformation.Equality.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope natural_transformation_scope.

Section FunctorProduct_Functor.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable D' : PreCategory.

  Definition FunctorProduct_MorphismOf
             s d
             (m : Morphism ([C, D] * [C, D']) s d)
  : Morphism [_, _] (fst s * snd s)%functor (fst d * snd d)%functor
    := FunctorProductFunctorial (fst m) (snd m).

  Definition FunctorProduct_FCompositionOf
             s d d'
             (m1 : Morphism ([C, D] * [C, D']) s d)
             (m2 : Morphism ([C, D] * [C, D']) d d')
  : FunctorProduct_MorphismOf (m2 ∘ m1)
    = FunctorProduct_MorphismOf m2 ∘ FunctorProduct_MorphismOf m1.
  Proof.
    abstract (nt_eq; reflexivity).
  Qed.

  Definition FunctorProduct_FIdentityOf
             (x : Object ([C, D] * [C, D']))
  : FunctorProduct_MorphismOf (Identity x) = Identity _.
  Proof.
    abstract (nt_eq; reflexivity).
  Qed.

  Definition FunctorProduct_Functor
  : Object [[C, D] * [C, D'], [C, D * D']]
    := Build_Functor
          ([C, D] * [C, D']) [C, D * D']
          _
          FunctorProduct_MorphismOf
          FunctorProduct_FCompositionOf
          FunctorProduct_FIdentityOf.
End FunctorProduct_Functor.
