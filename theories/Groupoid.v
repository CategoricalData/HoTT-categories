Require Export Category.
Require Import Common.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope equiv_scope.
Local Open Scope category_scope.

Section Groupoid.
  Variable X : Type.
  Context `{IsTrunc 1 X}.

  Local Notation Groupoid_Morphism := (@paths X).

  Definition Groupoid_Compose s d d' (m : Groupoid_Morphism d d') (m' : Groupoid_Morphism s d)
  : Groupoid_Morphism s d'
    := transitivity s d d' m' m.

  Definition Groupoid_Identity x : Groupoid_Morphism x x
    := reflexivity _.

  Global Arguments Groupoid_Compose [s d d'] m m' / .
  Global Arguments Groupoid_Identity x / .

  Definition Groupoid : PreCategory.
    refine (@Build_PreCategory X
                               Groupoid_Morphism
                               Groupoid_Identity
                               Groupoid_Compose
                               _
                               _
                               _
                               _);
    simpl; intros; path_induction; reflexivity.
  Defined.

  Definition Groupoid_isotoid (s d : Groupoid)
  : s ≅ d -> s = d
    := fun f => IsomorphicMorphism.

  Global Instance GroupoidIsCategory : IsCategory Groupoid.
  Proof.
    repeat intro.
    apply (isequiv_adjointify (@idtoiso Groupoid _ _)
                              (@Groupoid_isotoid _ _));
      repeat intro;
      destruct_head @Isomorphic;
      destruct_head @IsIsomorphism;
      compute in *;
      super_path_induction.
  Qed.
End Groupoid.

Arguments Groupoid _ {_}.

Lemma GroupoidIsStrict X `{IsHSet X}
: IsStrictCategory (Groupoid X).
Proof.
  typeclasses eauto.
Defined.
