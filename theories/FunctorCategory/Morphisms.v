Require Export FunctorCategory Category.Morphisms.
Require Import Common NaturalTransformation.Composition.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Definition NaturalIsomorphism `{Funext} (C D : PreCategory) F G := @Isomorphic [C, D] F G.

Arguments NaturalIsomorphism {_} [C D] F G / .

Coercion NaturalIsomorphismNT `{Funext} C D F G (T : @NaturalIsomorphism _ C D F G)
: NaturalTransformation F G
  := T : Morphism _ _ _.

Infix "≅" := NaturalIsomorphism : natural_transformation_scope.

Global Instance NTC_NI_R `{Funext} A (a : A)
       `(T : @NaturalIsomorphism _ C D F G)
       `{@NTC_Composable _ _ a (T : Morphism _ _ _) T' term}
: @NTC_Composable A _ a T T' term | 0.

Global Instance NTC_NI_L `{Funext} A (a : A)
       `(T : @NaturalIsomorphism _ C D F G)
       `{@NTC_Composable _ _ (T : Morphism _ _ _) a T' term}
: @NTC_Composable _ _ T a T' term | 0.

Definition iso_NaturalTransformation0 `{Funext} `{@IsIsomorphism [C, D] F G T} x
: IsIsomorphism (T x).
Proof.
  exists (T^-1 x).
  - exact (apD10 (ap ComponentsOf LeftInverse) x).
  - exact (apD10 (ap ComponentsOf RightInverse) x).
Defined.

Definition iso_NaturalTransformation1_NT `{Funext}
           C D (F G : Functor C D) (T : NaturalTransformation F G)
           `{forall x, IsIsomorphism (T x)}
: NaturalTransformation G F.
Proof.
  exists (fun x => (T x)^-1);
  abstract (
      intros;
      iso_move_inverse;
      first [ apply Commutes
            | symmetry; apply Commutes ]
    ).
Defined.

Definition iso_NaturalTransformation1 `{Funext}
           C D F G (T : NaturalTransformation F G)
           `{forall x, IsIsomorphism (T x)}
: @IsIsomorphism [C, D] F G T.
Proof.
  exists (iso_NaturalTransformation1_NT _);
  abstract (
      nt_eq;
      first [ apply LeftInverse
            | apply RightInverse ]
    ).
Defined.

Hint Immediate iso_NaturalTransformation0 iso_NaturalTransformation1 : typeclass_instances.
