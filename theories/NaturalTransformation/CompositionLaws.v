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
  : IdentityNaturalTransformation F ∘₁ T = T.
  Proof.
    nt_eq; auto with morphism.
  Qed.

  Lemma RightIdentityNaturalTransformation (F F' : Functor C D) (T : NaturalTransformation F F')
  : T ∘₁ IdentityNaturalTransformation F = T.
  Proof.
    nt_eq; auto with morphism.
  Qed.
End IdentityNaturalTransformation.

Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : category.
Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : natural_transformation.

Section IdentityNaturalTransformationF.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variable G : Functor D E.
  Variable F : Functor C D.

  Lemma NTComposeFIdentityNaturalTransformation :
    IdentityNaturalTransformation G ∘₀ IdentityNaturalTransformation F = IdentityNaturalTransformation (G ∘ F).
  Proof.
    nt_eq.
    rewrite !FIdentityOf.
    auto with morphism.
  Qed.
End IdentityNaturalTransformationF.

Hint Rewrite @NTComposeFIdentityNaturalTransformation : category.
Hint Rewrite @NTComposeFIdentityNaturalTransformation : natural_transformation.

(*Local Arguments GeneralizedIdentityNaturalTransformation / .*)

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
    : LeftIdentityFunctorNaturalTransformation1 ∘₁ LeftIdentityFunctorNaturalTransformation2 = IdentityNaturalTransformation _
      /\ LeftIdentityFunctorNaturalTransformation2 ∘₁ LeftIdentityFunctorNaturalTransformation1 = IdentityNaturalTransformation _.
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
    : RightIdentityFunctorNaturalTransformation1 ∘₁ RightIdentityFunctorNaturalTransformation2 = IdentityNaturalTransformation _
      /\ RightIdentityFunctorNaturalTransformation2 ∘₁ RightIdentityFunctorNaturalTransformation1 = IdentityNaturalTransformation _.
    Proof.
      nt_id_t.
    Qed.
  End right.
End IdentityFunctor.

Section NaturalTransformationExchangeLaw.
  Context `{fs : Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Variables F G H : Functor C D.
  Variables F' G' H' : Functor D E.

  Variable T : NaturalTransformation F G.
  Variable U : NaturalTransformation G H.

  Variable T' : NaturalTransformation F' G'.
  Variable U' : NaturalTransformation G' H'.

  Local Ltac t_progress := progress repeat
    match goal with
      | _ => progress f_ap
      | _ => apply Commutes
      | _ => apply symmetry; apply Commutes
    end.

  Local Ltac t_exch := repeat
    match goal with
      | _ => rewrite ?FCompositionOf, ?Associativity;
        t_progress
      | _ => rewrite <- ?FCompositionOf, <- ?Associativity;
        t_progress
    end.

  Theorem NaturalTransformationExchangeLaw
  : (U' ∘₁ T') ∘₀ (U ∘₁ T)
    = (U' ∘₀ U) ∘₁ (T' ∘₀ T).
  Proof.
    abstract (nt_eq; t_exch).
  Qed.
End NaturalTransformationExchangeLaw.

Hint Resolve @NaturalTransformationExchangeLaw : category.
Hint Resolve @NaturalTransformationExchangeLaw : natural_transformation.

Ltac nt_solve_associator' :=
  repeat match goal with
           | _ => exact (ComposeFunctorsAssociator1 _ _ _)
           | _ => exact (ComposeFunctorsAssociator2 _ _ _)
           | [ |- NaturalTransformation (?F ∘ _) (?F ∘ _) ] =>
             refine (IdentityNaturalTransformation F ∘₀ _)%natural_transformation
           | [ |- NaturalTransformation (_ ∘ ?F) (_ ∘ ?F) ] =>
             refine (_ ∘₀ IdentityNaturalTransformation F)
         end.
Ltac nt_solve_associator :=
  repeat match goal with
           | _ => refine (ComposeFunctorsAssociator1 _ _ _ ∘₁ _); progress nt_solve_associator'
           | _ => refine (_ ∘₁ ComposeFunctorsAssociator1 _ _ _); progress nt_solve_associator'
           | _ => refine (ComposeFunctorsAssociator2 _ _ _ ∘₁ _); progress nt_solve_associator'
           | _ => refine (_ ∘₁ ComposeFunctorsAssociator2 _ _ _); progress nt_solve_associator'
           | _ => progress nt_solve_associator'
         end.
