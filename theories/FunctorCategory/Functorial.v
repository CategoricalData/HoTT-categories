Require Export FunctorCategory Functor.Pointwise Functor.Pointwise.Properties Category.Duals Category.Product.
Require Import Common Cat.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

Section FunctorCategoryFunctor.
  Context `{fs1 : Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Let Cat : PreCategory := SubPreCat P.

  Hypothesis HasFunctorCategories : forall C D : Cat, P [C.1, D.1].

  Definition FunctorCategoryFunctor_uncurried `{fs2 : Funext}
  : Object (@FunctorCategory fs2 (Cat^op * Cat) Cat)
    := Build_Functor
         (Cat^op * Cat) Cat
         (fun CD => ([(fst CD).1, (snd CD).1]; HasFunctorCategories _ _))
         (fun CD C'D' FG => [fst FG, snd FG]%functor)
         (fun _ _ _ _ _ => FunctorCompositionPointwise _ _ _ _)
         (fun _ => IdentityFunctorPointwise _ _).

  (* Definition FunctorCategoryFunctor : ((Cat ^ Cat) ^ (OppositeCategory Cat))%category
    := ExponentialLaw4Functor_Inverse _ _ _ FunctorCategoryUncurriedFunctor. *)
End FunctorCategoryFunctor.
