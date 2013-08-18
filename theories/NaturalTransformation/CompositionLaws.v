Require Export Functor NaturalTransformation.Core NaturalTransformation.Identity NaturalTransformation.Composition NaturalTransformation.Equality.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section IdentityNaturalTransformation.
  Context `{fs : Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Lemma LeftIdentityNaturalTransformation (F F' : Functor C D) (T : NaturalTransformation F' F)
  : IdentityNaturalTransformation F ∘ T = T.
  Proof.
    nt_eq; auto with morphism.
  Qed.

  Lemma RightIdentityNaturalTransformation (F F' : Functor C D) (T : NaturalTransformation F F')
  : T ∘ IdentityNaturalTransformation F = T.
  Proof.
    nt_eq; auto with morphism.
  Qed.

  Local Transparent NTWhiskerR_Commutes NTWhiskerL_Commutes.

  Definition LeftIdentityNaturalTransformationWhisker E (G : Functor D E) (F : Functor C D)
  : IdentityNaturalTransformation G ∘ F = IdentityNaturalTransformation _
    := idpath.

  Definition RightIdentityNaturalTransformationWhisker E (G : Functor D E) (F : Functor C D)
  : G ∘ IdentityNaturalTransformation F = IdentityNaturalTransformation _.
  Proof.
    nt_eq; auto with functor.
  Qed.
End IdentityNaturalTransformation.

Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : category.
Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : natural_transformation.

Section NTComposeF.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variables G G' : Functor D E.
  Variables F F' : Functor C D.
  Variable T' : NaturalTransformation G G'.
  Variable T : NaturalTransformation F F'.

  Lemma NTWhiskerExchange
  : (G' ∘ T) ∘ (T' ∘ F) = (T' ∘ F') ∘ (G ∘ T).
  Proof.
    nt_eq; simpl.
    symmetry.
    apply Commutes.
  Qed.
End NTComposeF.

Section Associativity.
  Context `{fs : Funext}.

  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variable F : Functor D E.
  Variable G : Functor C D.
  Variable H : Functor B C.

  Notation F0 := ((F ∘ G) ∘ H)%functor.
  Notation F1 := (F ∘ (G ∘ H))%functor.

  Definition ComposeFunctorsAssociator1 : NaturalTransformation F0 F1
    := Eval simpl in GeneralizedIdentityNaturalTransformation F0 F1 idpath idpath.

  Definition ComposeFunctorsAssociator2 : NaturalTransformation F1 F0
    := Eval simpl in GeneralizedIdentityNaturalTransformation F1 F0 idpath idpath.
End Associativity.

Section IdentityFunctor.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Ltac nt_id_t := split; nt_eq; autorewrite with morphism; reflexivity.

  Section left.
    Variable F : Functor D C.

    Definition LeftIdentityFunctorNaturalTransformation1 : NaturalTransformation (IdentityFunctor _ ∘ F) F
      := Eval simpl in GeneralizedIdentityNaturalTransformation (IdentityFunctor _ ∘ F) F idpath idpath.
    Definition LeftIdentityFunctorNaturalTransformation2 : NaturalTransformation F (IdentityFunctor _ ∘ F)
      := Eval simpl in GeneralizedIdentityNaturalTransformation F (IdentityFunctor _ ∘ F) idpath idpath.

    Theorem LeftIdentityFunctorNT_Isomorphism
    : LeftIdentityFunctorNaturalTransformation1 ∘ LeftIdentityFunctorNaturalTransformation2 = IdentityNaturalTransformation _
      /\ LeftIdentityFunctorNaturalTransformation2 ∘ LeftIdentityFunctorNaturalTransformation1 = IdentityNaturalTransformation _.
    Proof.
      nt_id_t.
    Qed.
  End left.

  Section right.
    Variable F : Functor C D.

    Definition RightIdentityFunctorNaturalTransformation1 : NaturalTransformation (F ∘ IdentityFunctor _) F
      := Eval simpl in GeneralizedIdentityNaturalTransformation (F ∘ IdentityFunctor _) F idpath idpath.
    Definition RightIdentityFunctorNaturalTransformation2 : NaturalTransformation F (F ∘ IdentityFunctor _)
      := Eval simpl in GeneralizedIdentityNaturalTransformation F (F ∘ IdentityFunctor _) idpath idpath.

    Theorem RightIdentityFunctorNT_Isomorphism
    : RightIdentityFunctorNaturalTransformation1 ∘ RightIdentityFunctorNaturalTransformation2 = IdentityNaturalTransformation _
      /\ RightIdentityFunctorNaturalTransformation2 ∘ RightIdentityFunctorNaturalTransformation1 = IdentityNaturalTransformation _.
    Proof.
      nt_id_t.
    Qed.
  End right.
End IdentityFunctor.

Ltac nt_solve_associator' :=
  repeat match goal with
           | _ => exact (ComposeFunctorsAssociator1 _ _ _)
           | _ => exact (ComposeFunctorsAssociator2 _ _ _)
           | [ |- NaturalTransformation (?F ∘ _) (?F ∘ _) ] =>
             refine (NTWhiskerL F _)
           | [ |- NaturalTransformation (_ ∘ ?F) (_ ∘ ?F) ] =>
             refine (NTWhiskerR _ F)
         end.
Ltac nt_solve_associator :=
  repeat match goal with
           | _ => refine (NTComposeT (ComposeFunctorsAssociator1 _ _ _) _); progress nt_solve_associator'
           | _ => refine (NTComposeT _ (ComposeFunctorsAssociator1 _ _ _)); progress nt_solve_associator'
           | _ => refine (NTComposeT (ComposeFunctorsAssociator2 _ _ _) _); progress nt_solve_associator'
           | _ => refine (NTComposeT _ (ComposeFunctorsAssociator2 _ _ _)); progress nt_solve_associator'
           | _ => progress nt_solve_associator'
         end.
