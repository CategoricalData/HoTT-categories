Require Export Category Functor.Core Functor.Composition Functor.Identity.
Require Import Common Functor.Equality.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section IdentityFunctorLemmas.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Context `{Funext}.

  Local Open Scope functor_scope.

  Local Transparent ComposeFunctors_FIdentityOf.
  Local Transparent ComposeFunctors_FCompositionOf.

  Lemma LeftIdentityFunctor (F : Functor D C) : IdentityFunctor _ ∘ F = F.
  Proof.
    functor_eq.
  Defined.

  Lemma RightIdentityFunctor (F : Functor C D) : F ∘ IdentityFunctor _ = F.
  Proof.
    functor_eq.
  Defined.

  Definition LeftIdentityFunctor_fst F : ap ObjectOf (LeftIdentityFunctor F) = idpath
    := @Functor_eq'_sig_fst _ _ _ (IdentityFunctor C ∘ F) F 1%path 1%path.

  Definition RightIdentityFunctor_fst F : ap ObjectOf (RightIdentityFunctor F) = idpath
    := @Functor_eq'_sig_fst _ _ _ (F ∘ IdentityFunctor C) F 1%path 1%path.
End IdentityFunctorLemmas.

Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : category.
Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : functor.
Hint Immediate @LeftIdentityFunctor @RightIdentityFunctor : category functor.

Section FunctorCompositionLemmas.
  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Context `{H0 : Funext}.

  Local Open Scope functor_scope.

  Local Transparent ComposeFunctors_FCompositionOf.
  Local Transparent ComposeFunctors_FIdentityOf.

  Lemma ComposeFunctorsAssociativity (F : Functor B C) (G : Functor C D) (H : Functor D E)
  : (H ∘ G) ∘ F = H ∘ (G ∘ F).
  Proof.
    functor_eq.
  Defined.

  Definition ComposeFunctorsAssociativity_fst F G H
  : ap ObjectOf (ComposeFunctorsAssociativity F G H) = idpath
    := @Functor_eq'_sig_fst _ _ _ (H ∘ G ∘ F) (H ∘ (G ∘ F)) 1%path 1%path.
End FunctorCompositionLemmas.

Hint Resolve @ComposeFunctorsAssociativity : category functor.

Opaque ComposeFunctorsAssociativity LeftIdentityFunctor RightIdentityFunctor.
