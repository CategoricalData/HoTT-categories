Require Export FunctorCategory Category.Product NaturalTransformation.Composition.Functorial ExponentialLaws.Law4.Functors.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section FunctorialComposition.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Local Open Scope natural_transformation_scope.

  Definition FunctorialComposition_MorphismOf
             s d (m : Morphism [C, D] s d)
  : Morphism [[D, E], [C, E]]
             (NTWhiskerR_Functorial _ s)
             (NTWhiskerR_Functorial _ d)
    := Build_NaturalTransformation
         (NTWhiskerR_Functorial E s)
         (NTWhiskerR_Functorial E d)
         (fun x => NTWhiskerL x m)
         (fun _ _ _ => NTWhiskerExchange _ _).

  Definition FunctorialComposition : Object [[C, D], [[D, E], [C, E]]].
  Proof.
    refine (Build_Functor
              [C, D] [[D, E], [C, E]]
              (@NTWhiskerR_Functorial _ _ _ _)
              FunctorialComposition_MorphismOf
              _
              _);
    abstract (
        nt_eq;
        rewrite ?FCompositionOf, ?FIdentityOf;
        reflexivity
      ).
  Defined.

  Definition FunctorialComposition_uncurried : Object [[C, D] * [D, E], [C, E]]
    := ExponentialLaw4Functor _ _ _ FunctorialComposition.
End FunctorialComposition.
