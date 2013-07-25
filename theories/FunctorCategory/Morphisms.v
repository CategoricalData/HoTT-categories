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

Hint Immediate iso_NaturalTransformation0 : typeclass_instances.

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

Section idtoiso.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition idtoiso_FunctorCategory_NT
             (F G : Object [C, D])
             (T : F = G)
  : NaturalTransformation F G.
  Proof.
    refine (Build_NaturalTransformation
              F G
              (fun x => idtoiso _ (ap10 (ap ObjectOf T) x))
              _).
    intros; case T; simpl.
    etransitivity; [ | symmetry ];
    first [ apply LeftIdentity
          | apply RightIdentity ].
  Defined.

  Definition idtoiso_FunctorCategory
             (F G : Object [C, D])
             (T : F = G)
  : F ≅ G.
  Proof.
    exists (idtoiso_FunctorCategory_NT T).
    exists (idtoiso_FunctorCategory_NT (inverse T));
      abstract (nt_eq; case T; simpl; auto with morphism).
  Defined.

  Lemma eta_idtoiso_FunctorCategory
        (F G : Object [C, D])
        (T : F = G)
  : idtoiso _ T = idtoiso_FunctorCategory T.
  Proof.
    case T.
    expand; f_ap.
    exact (center _).
  Qed.
End idtoiso.

Hint Immediate iso_NaturalTransformation0 iso_NaturalTransformation1 : typeclass_instances.
