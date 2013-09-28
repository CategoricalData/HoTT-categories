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
             s d (m : Morphism [D, E] s d)
  : Morphism [[C, D], [C, E]]
             (NTWhiskerL_Functorial _ s)
             (NTWhiskerL_Functorial _ d)
    := Build_NaturalTransformation
         (NTWhiskerL_Functorial C s)
         (NTWhiskerL_Functorial C d)
         (fun x => NTWhiskerR m x)
         (fun _ _ _ => inverse (NTWhiskerExchange _ _)).

  Definition FunctorialComposition : Object [[D, E], [[C, D], [C, E]]].
  Proof.
    refine (Build_Functor
              [D, E] [[C, D], [C, E]]
              (@NTWhiskerL_Functorial _ _ _ _)
              FunctorialComposition_MorphismOf
              _
              _);
    abstract (nt_eq; reflexivity).
  Defined.

  Definition FunctorialComposition_uncurried : Object [[D, E] * [C, D], [C, E]]
    := ExponentialLaw4Functor _ _ _ FunctorialComposition.
End FunctorialComposition.
