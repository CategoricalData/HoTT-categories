Require Export FunctorCategory Category.Sum Category.Product.
Require Import Common Functor.Pointwise Functor.Product Functor.Sum NaturalTransformation.Sum.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.

Section Law2.
  Context `{Funext}.
  Variable D : PreCategory.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.

  Definition ExponentialLaw2Functor
  : Functor [C1 + C2, D] ([C1, D] * [C2, D])
    := PointwiseFunctor (inl_Functor C1 C2) (IdentityFunctor D)
       * PointwiseFunctor (inr_Functor C1 C2) (IdentityFunctor D).

  Definition ExponentialLaw2Functor_Inverse
  : Functor ([C1, D] * [C2, D]) [C1 + C2, D].
  Proof.
    let C := match goal with |- Functor ?C ?D => constr:(C) end in
    let D := match goal with |- Functor ?C ?D => constr:(D) end in
    refine (Build_Functor
              C D
              (fun FG => sum_Functor (fst FG) (snd FG))
              (fun _ _ m => sum_Functor_Functorial (fst m) (snd m))
              _
              _);
    simpl in *;
    abstract (
        repeat (intros [?|?] || intros [? ?]);
        simpl in *;
          apply NaturalTransformation_eq; intros [?|?];
        reflexivity
      ).
  Defined.
End Law2.
