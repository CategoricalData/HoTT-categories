Require Export FunctorCategory Category.Product.
Require Import Common Functor.Product Functor.Product.ProductFunctor.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.

Section Law3.
  Context `{Funext}.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Definition ExponentialLaw3Functor
  : Functor [D, C1 * C2] ([D, C1] * [D, C2])
    := Build_Functor
         [D, C1 * C2] ([D, C1] * [D, C2])
         (fun H => (fst_Functor ∘ H, snd_Functor ∘ H))
         (fun s d m =>
            (NTWhiskerL fst_Functor m,
             NTWhiskerL snd_Functor m))
         (fun _ _ _ _ _ => path_prod' (NTWhiskerL_CompositionOf _ _ _)
                                      (NTWhiskerL_CompositionOf _ _ _))
         (fun _ => path_prod' (RightIdentityNaturalTransformationWhisker _ _)
                              (RightIdentityNaturalTransformationWhisker _ _)).

  Definition ExponentialLaw3Functor_Inverse
  : Functor ([D, C1] * [D, C2]) [D, C1 * C2]
    := FunctorProduct_Functor _ _ _.
End Law3.
