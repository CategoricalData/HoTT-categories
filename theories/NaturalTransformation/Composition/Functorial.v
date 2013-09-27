Require Export FunctorCategory NaturalTransformation.Composition.
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

  Definition NTWhiskerL_Functorial (F : [D, E]%category)
  : [[C, D], [C, E]]%category
    := Build_Functor
         [C, D] [C, E]
         (fun G => F ∘ G)
         (fun _ _ T => F ∘ T)
         (fun _ _ _ _ _ => NTWhiskerL_CompositionOf _ _ _)
         (fun _ => RightIdentityNaturalTransformationWhisker _ _).

  Definition NTWhiskerR_Functorial (G : [C, D]%category)
  : [[D, E], [C, E]]%category
    := Build_Functor
         [C, D] [C, E]
         (fun F => F ∘ G)
         (fun _ _ T => T ∘ G)
         (fun _ _ _ _ _ => inverse (NTWhiskerR_CompositionOf _ _ _))
         (fun _ => LeftIdentityNaturalTransformationWhisker _ _).

 Definition FunctorialComposition : Object [[D, E] * [C, D], [C, E]].
  Proof.
    assert (forall s d (m : Morphism ([D, E] * [C, D])
    refine (Build_Functor
              ([D, E] * [C, D]) [C, E]
              (fun fg => fst fg ∘ snd fg)
              (fun _ _ tu => NTComposeF (fst tu) (snd tu))
          _
          _
        )
    end;
    abstract (
      intros;
        destruct_hypotheses;
        auto with category;
          nt_eq;
          repeat rewrite FIdentityOf;
            auto with category
    ).
  Defined.
End FunctorialComposition.
