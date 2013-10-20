Require Export Category Functor.
Require Import Common SetCategory.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section Grothendieck.
  Context `{Funext}.

  (**
     Quoting Wikipedia:

     The Grothendieck construction is an auxiliary construction used
     in the mathematical field of category theory.

     Let

     [F : C -> Set]

     be a functor from any small category to the category of sets.
     The Grothendieck construct for [F] is the category [Γ F] whose
     objects are pairs [(c, x)], where [c : C] is an object and [x : F
     c] is an element, and for which the set [Hom (Γ F) (c1, x1) (c2,
     x2)] is the set of morphisms [f : c1 -> c2] in [C] such that
     [F.(MorphismOf) f x1 = x2].  *)

  Variable C : PreCategory.
  Variable F : Functor C SetCat.

  Record GrothendieckPair :=
    {
      GrothendieckC : C;
      GrothendieckX : (F GrothendieckC : hSet)
    }.

  Local Notation GrothendieckMorphism s d :=
    { f : Morphism C (GrothendieckC s) (GrothendieckC d)
    | MorphismOf F f (GrothendieckX s) = GrothendieckX d }.

  Definition GrothendieckCompose_H s d d'
             (m1 : GrothendieckMorphism d d')
             (m2 : GrothendieckMorphism s d)
  : (F ₁ (m1 .1 ∘ m2 .1)) (GrothendieckX s) = GrothendieckX d'.
  Proof.
    etransitivity; [ | exact (m1.2) ].
    etransitivity; [ | apply ap; exact (m2.2) ].
    match goal with
      | [ |- ?f ?x = ?g (?h ?x) ] => change (f x = (g ∘ h) x)
    end.
    match goal with
      | [ |- ?f ?x = ?g ?x ] => apply (@apD10 _ _ f g)
    end.
    apply (FCompositionOf F).
  Defined.

  Definition GrothendieckCompose s d d'
             (m1 : GrothendieckMorphism d d')
             (m2 : GrothendieckMorphism s d)
  : GrothendieckMorphism s d'.
  Proof.
    exists (m1.1 ∘ m2.1).
    apply GrothendieckCompose_H.
  Defined.

  Definition GrothendieckIdentity_H x
    := apD10 (FIdentityOf F (GrothendieckC x)) (GrothendieckX x).

  Definition GrothendieckIdentity x : GrothendieckMorphism x x.
  Proof.
    exists (Identity (GrothendieckC x)).
    apply GrothendieckIdentity_H.
  Defined.

  Global Arguments GrothendieckCompose_H / .
  Global Opaque GrothendieckCompose_H.

  Global Arguments GrothendieckIdentity_H / .
  Global Opaque GrothendieckIdentity_H.

  Global Arguments GrothendieckIdentity _ / .
  Global Arguments GrothendieckCompose _ _ _ _ _ / .

  Definition CategoryOfElements : PreCategory.
  Proof.
    refine (@Build_PreCategory
              GrothendieckPair
              (fun s d => GrothendieckMorphism s d)
              GrothendieckIdentity
              GrothendieckCompose
              _
              _
              _
              _);
    abstract (
        repeat intro;
        apply path_sigma_uncurried; simpl;
        ((exists (Associativity _ _ _ _ _ _ _ _))
           || (exists (LeftIdentity _ _ _ _))
           || (exists (RightIdentity _ _ _ _)));
        exact (center _)
      ).
  Defined.

  Definition GrothendieckFunctor : Functor CategoryOfElements C
    := Build_Functor CategoryOfElements C
                     GrothendieckC
                     (fun s d => @projT1 _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End Grothendieck.
