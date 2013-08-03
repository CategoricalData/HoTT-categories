Require Export CommaCategory Category.Product Functor.Product.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.
Local Open Scope category_scope.

Section CommaCategory.
  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable S : Functor A C.
  Variable T : Functor B C.

  Definition CommaCategoryProjection : Functor (S ↓ T) (A * B)
    := Build_Functor (S ↓ T) (A * B)
                     (fun abf => (CCO_a abf, CCO_b abf)%core)
                     (fun _ _ m => (CCM_g m, CCM_h m)%core)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End CommaCategory.

Section SliceCategory.
  Variable A : PreCategory.

  Local Arguments ComposeFunctors / .
  Local Arguments ComposeFunctors_FCompositionOf / .
  Local Arguments ComposeFunctors_FIdentityOf / .
  Local Arguments path_prod / .
  Local Arguments path_prod' / .
  Local Arguments path_prod_uncurried / .
  Local Transparent ComposeFunctors_FCompositionOf.
  Local Transparent ComposeFunctors_FIdentityOf.

  Definition ArrowCategoryProjection : Functor (ArrowCategory A) A
    := Eval simpl in fst_Functor ∘ CommaCategoryProjection _ (IdentityFunctor A).

  Definition SliceCategoryOverProjection (a : A) : Functor (A / a) A
    := Eval simpl in fst_Functor ∘ CommaCategoryProjection (IdentityFunctor A) _.

  Definition CosliceCategoryOverProjection (a : A) : Functor (a \ A) A
    := Eval simpl in snd_Functor ∘ CommaCategoryProjection _ (IdentityFunctor A).

  Section Slice_Coslice.
    Variable C : PreCategory.
    Variable a : C.
    Variable S : Functor A C.

    Definition SliceCategoryProjection : Functor (S ↓ a) A
      := Eval simpl in fst_Functor ∘ CommaCategoryProjection S (FunctorFromTerminal C a).

    Definition CosliceCategoryProjection : Functor (a ↓ S) A
      := Eval simpl in snd_Functor ∘ CommaCategoryProjection (FunctorFromTerminal C a) S.
  End Slice_Coslice.
End SliceCategory.
