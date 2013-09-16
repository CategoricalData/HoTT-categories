Require Export Category.Sum Functor.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section SumCategoryFunctors.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition inl_Functor : Functor C (C + D)
    := Build_Functor C (C + D)
                     (@inl _ _)
                     (fun _ _ m => m)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition inr_Functor : Functor D (C + D)
    := Build_Functor D (C + D)
                     (@inr _ _)
                     (fun _ _ m => m)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End SumCategoryFunctors.
