Require Export Grothendieck.ToCat CategoryOfSections.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.

Section dependent_product.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (SubPreCat P).

  Variable F : Functor C Cat.

  (** Quoting http://mathoverflow.net/questions/137689/explicit-description-of-the-oplax-limit-of-a-functor-to-cat:

      The oplax limit is the category of sections for the functor from
      the Grothendieck construction to the base category.

      The strong limit is the category of cartesian sections
      (every arrow in the base category gets mapped to a cartesian
      one).

      Notice how this goes along very well with the interpretation as
      dependent product and as $∀$: The set theoretic product is just
      the set of sections into the disjoint union.

      Given a strong functor [F : X → Cat] we denote the Grothendieck
      construction by [Gr F].

      There is a canonical functor [π : Gr F → X]. Sections of this
      functor are functors [s : X → Gr F] such that [s ∘ π = id]. *)

  Definition DependentProduct : PreCategory
    := CategoryOfSections (GrothendieckCatFunctorOfFunctor F).
End dependent_product.

Notation Pi := DependentProduct.
