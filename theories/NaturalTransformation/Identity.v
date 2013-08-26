Require Export Functor.Core NaturalTransformation.Core NaturalTransformation.Equality.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section IdentityNaturalTransformation.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Ltac id_fin_t :=
    intros;
    etransitivity;
    [ apply LeftIdentity
    | apply symmetry; apply RightIdentity ].

  (** There is an identity natrual transformation.  We create a number
      of variants, for various uses. *)
  Section Generalized.
    Variables F G : Functor C D.
    Hypothesis HO : ObjectOf F = ObjectOf G.
    Hypothesis HM : match HO in _ = GO return forall s d, Morphism C s d -> Morphism D (GO s) (GO d) with
                      | idpath => MorphismOf F
                    end = MorphismOf G.

    Notation CO c := match HO in _ = GO return Morphism D (F c) (GO c) with
                       | idpath => Identity (F c)
                     end.

    Definition GeneralizedIdentityNaturalTransformation_Commutes
               s d (m : Morphism C s d)
    : CO d ∘ MorphismOf F m
      = MorphismOf G m ∘ CO s.
    Proof.
      subst_body; simpl;
      case HM; case HO;
      id_fin_t.
    Defined.

    Definition GeneralizedIdentityNaturalTransformation
    : NaturalTransformation F G
      := Build_NaturalTransformation F G
                                     (fun c => CO c)
                                     GeneralizedIdentityNaturalTransformation_Commutes.
  End Generalized.

  Global Arguments GeneralizedIdentityNaturalTransformation_Commutes / .
  Global Arguments GeneralizedIdentityNaturalTransformation F G !HO !HM / .

  Section Generalized'.
    Variables F G : Functor C D.
    Hypothesis H : F = G.

    Definition GeneralizedIdentityNaturalTransformation' : NaturalTransformation F G.
      apply (GeneralizedIdentityNaturalTransformation F G (ap (@ObjectOf C D) H)).
      case H.
      reflexivity.
    Defined.
  End Generalized'.

  Definition IdentityNaturalTransformation (F : Functor C D) : NaturalTransformation F F
    := Eval simpl in @GeneralizedIdentityNaturalTransformation F F idpath idpath.

  Global Arguments GeneralizedIdentityNaturalTransformation' F G !H / .
End IdentityNaturalTransformation.

Global Opaque GeneralizedIdentityNaturalTransformation_Commutes.
