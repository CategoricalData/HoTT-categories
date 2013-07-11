Require Export Category Functor.Core Functor.Composition Functor.Identity.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Ltac functor_t :=
  destruct_head Functor; expand; f_ap;
  repeat (apply path_forall; intro);
  try refine (center _).

Section IdentityFunctorLemmas.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Context `{Funext}.

  Local Open Scope functor_scope.

  Local Transparent ComposeFunctors_FIdentityOf.
  Local Transparent ComposeFunctors_FCompositionOf.

  Lemma LeftIdentityFunctor (F : Functor D C) : IdentityFunctor _ ∘ F = F.
    functor_t.
  Qed.

  Lemma RightIdentityFunctor (F : Functor C D) : F ∘ IdentityFunctor _ = F.
    functor_t.
  Qed.
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
    functor_t.
  Qed.
End FunctorCompositionLemmas.

Hint Resolve @ComposeFunctorsAssociativity : category functor.
