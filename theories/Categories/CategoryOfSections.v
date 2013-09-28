Require Export Category Functor NaturalTransformation.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope equiv_scope.
Local Open Scope functor_scope.

Section FunctorSectionCategory.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable R : Functor C D.

  (** There is a category [Sect(R)] of sections of [R]. *)

  Record SectionOfFunctor :=
    {
      SectionOfFunctor_Morphism :> Functor D C;
      SectionOfFunctor_IsSection : R ∘ SectionOfFunctor_Morphism = IdentityFunctor _
    }.

  Local Notation SectionOfFunctor_sigT :=
    { SectionOfFunctor_Morphism : Functor D C
    | R ∘ SectionOfFunctor_Morphism = IdentityFunctor _ }.

  Lemma SectionOfFunctor_sig
  : SectionOfFunctor_sigT <~> SectionOfFunctor.
  Proof.
    issig Build_SectionOfFunctor
          SectionOfFunctor_Morphism
          SectionOfFunctor_IsSection.
  Defined.

  Definition CategoryOfSections : PreCategory.
  Proof.
    refine (@Build_PreCategory
              SectionOfFunctor
              (fun F G => NaturalTransformation F G)
              (fun F => IdentityNaturalTransformation F)
              (fun _ _ _ T U => NTComposeT T U)
              _
              _
              _
              _);
    abstract (nt_eq; auto with morphism).
  Defined.
End FunctorSectionCategory.

Lemma IsStrict_FunctorCategory `{Funext}
      `{IsStrictCategory C, IsStrictCategory D}
      (F : Functor C D)
: IsStrictCategory (CategoryOfSections F).
Proof.
  eapply trunc_equiv; [ | apply SectionOfFunctor_sig ].
  typeclasses eauto.
Qed.
