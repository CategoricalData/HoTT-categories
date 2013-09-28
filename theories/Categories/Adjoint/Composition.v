Require Export Adjoint.UnitCounit.
Require Import Common Category.Morphisms.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope natural_transformation_scope.

Section compose.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Variable F : Functor C D.
  Variable F' : Functor D E.
  Variable G : Functor D C.
  Variable G' : Functor E D.

  Variable A' : F' ⊣ G'.
  Variable A : F ⊣ G.

  Section morphisms.
    Let ComposeAdjunctionsUnitMorphism'
    : NaturalTransformation (IdentityFunctor C)
                            ((G ∘ G') ∘ (F' ∘ F)).
    Proof.
      pose (Adjunction_Unit A) as η.
      pose (Adjunction_Unit A') as η'.
      refine ((fun (T : NaturalTransformation _ _) (U : NaturalTransformation _ _)
               => NTComposeT T ((G ∘ η' ∘ F) ∘ (U ∘ η))) _ _);
        nt_solve_associator.
    Defined.

    Definition ComposeAdjunctionsUnitMorphism
      := Eval cbv beta iota zeta delta [ComposeAdjunctionsUnitMorphism' NTC_Composable_term]
        in ComposeAdjunctionsUnitMorphism'.

    Let ComposeAdjunctionsCounitMorphism'
    : NaturalTransformation ((F' ∘ F) ∘ (G ∘ G'))
                            (IdentityFunctor E).
    Proof.
      pose (Adjunction_Counit A) as ε.
      pose (Adjunction_Counit A') as ε'.
      refine ((fun (T : NaturalTransformation _ _) (U : NaturalTransformation _ _)
               => NTComposeT ε' (NTComposeT U (NTComposeT (F' ∘ ε ∘ G') T))) _ _);
        nt_solve_associator.
    Defined.

    Definition ComposeAdjunctionsCounitMorphism
      := Eval cbv beta iota zeta delta [ComposeAdjunctionsCounitMorphism' NTC_Composable_term]
        in ComposeAdjunctionsCounitMorphism'.
  End morphisms.

  (* TODO(jgross): speed this up, automate it more *)
  Definition ComposeAdjunctions : F' ∘ F ⊣ G ∘ G'.
  Proof.
    exists ComposeAdjunctionsUnitMorphism
           ComposeAdjunctionsCounitMorphism;
    clear;
    simpl;
    abstract (
        repeat match goal with
                 | _ => intro
                 | _ => reflexivity
                 | _ => progress rewrite ?FIdentityOf, ?LeftIdentity, ?RightIdentity
                 | _ => rewrite <- ?FCompositionOf, Adjunction_UnitCounitEquation1
                 | _ => rewrite <- ?FCompositionOf, Adjunction_UnitCounitEquation2
                 | [ A : _ ⊣ _ |- _ = 1%morphism ]
                   => (etransitivity; [ | apply (Adjunction_UnitCounitEquation1 A) ];
                       instantiate; try_associativity ltac:(f_ap))
                 | [ A : _ ⊣ _ |- _ = 1%morphism ]
                   => (etransitivity; [ | apply (Adjunction_UnitCounitEquation2 A) ];
                       instantiate; try_associativity ltac:(f_ap))
                 | _ => repeat try_associativity_quick ltac:(rewrite <- !FCompositionOf);
                 progress repeat apply ap;
                 rewrite ?FCompositionOf
                 | [ |- appcontext[ComponentsOf ?T] ]
                   => simpl_do_clear try_associativity_quick_rewrite_rev (Commutes T);
                 try_associativity ltac:(apply concat_RightIdentity || apply concat_LeftIdentity)
                 | [ |- appcontext[ComponentsOf ?T] ]
                   => simpl_do_clear try_associativity_quick_rewrite (Commutes T);
                 try_associativity ltac:(apply concat_RightIdentity || apply concat_LeftIdentity)
               end
      ).
  Defined.
End compose.

Infix "o" := ComposeAdjunctions : adjunction_scope.
Infix "∘" := ComposeAdjunctions : adjunction_scope.
