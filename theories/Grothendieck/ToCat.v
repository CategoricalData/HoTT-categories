Require Export Category Functor Cat Grothendieck.PseudofunctorToCat.
Require Import Common Pseudofunctor Pseudofunctor.FromFunctor.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section GrothendieckCat.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (SubPreCat P).

  (** Quoting Wikipedia:

      The Grothendieck construction is an auxiliary construction used
      in the mathematical field of category theory.

      Let

      [F : C -> Set]

      be a functor from any small category to the category of sets.
      The Grothendieck construct for [F] is the category [Γ F] whose
      objects are pairs [(c, x)], where [c : C] is an object and [x :
      F c] is an element, and for which the set [Hom (Γ F) (c1, x1)
      (c2, x2)] is the set of morphisms [f : c1 -> c2] in [C] such
      that [F.(MorphismOf) f x1 = x2].  *)

  Variable C : PreCategory.
  Variable F : Functor C Cat.

  Definition CategoryOfElementsOfFunctor : PreCategory
    := CategoryOfElements (PseudofunctorOfFunctor F).

  Definition GrothendieckCatFunctorOfFunctor : Functor CategoryOfElementsOfFunctor C
    := GrothendieckCatFunctor (PseudofunctorOfFunctor F).
End GrothendieckCat.
