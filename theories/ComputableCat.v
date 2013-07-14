Require Export Category Functor.
Require Import Common.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section ComputableCat.
  Context `{Funext}.

  Variable I : Type.
  Variable Index2Cat : I -> PreCategory.

  Local Coercion Index2Cat : I >-> PreCategory.

  Context `{forall C D : I, IsHSet (Functor C D)}.

  Definition ComputableCat : PreCategory
    := @Build_PreCategory I
                          (fun C D : I => Functor C D)
                          (fun x : I => IdentityFunctor x)
                          (fun C D E : I => ComposeFunctors (C := C) (D := D) (E := E))
                          (fun _ _ _ _ _ _ _ => ComposeFunctorsAssociativity _ _ _)
                          (fun _ _ _ => LeftIdentityFunctor _)
                          (fun _ _ _ => RightIdentityFunctor _)
                          _.
End ComputableCat.
