Require Export Category Functor.Core Category.Product NaturalTransformation.Core.
Require Import Common Functor.Equality.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section ProductCategoryFunctors.
  Context {C : PreCategory}.
  Context {D : PreCategory}.

  Definition fst_Functor : Functor (C * D) C
    := Build_Functor (C * D) C
                     (@fst _ _)
                     (fun _ _ => @fst _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition snd_Functor : Functor (C * D) D
    := Build_Functor (C * D) D
                     (@snd _ _)
                     (fun _ _ => @snd _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End ProductCategoryFunctors.

Section FunctorProduct.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable D' : PreCategory.

  Definition FunctorProduct (F : Functor C D) (F' : Functor C D')
  : Functor C (D * D')
    := Build_Functor
         C (D * D')
         (fun c => (F c, F' c))
         (fun s d m => (MorphismOf F m, MorphismOf F' m))
         (fun _ _ _ _ _ => path_prod' (FCompositionOf F _ _ _ _ _)
                                      (FCompositionOf F' _ _ _ _ _))
         (fun _ => path_prod' (FIdentityOf F _) (FIdentityOf F' _)).

  Local Infix "*" := FunctorProduct : functor_scope.

  Definition FunctorProductFunctorial
             (F G : Functor C D)
             (F' G' : Functor C D')
             (T : NaturalTransformation F G)
             (T' : NaturalTransformation F' G')
  : NaturalTransformation (F * F') (G * G')
    := Build_NaturalTransformation
         (F * F') (G * G')
         (fun x => (T x, T' x))
         (fun _ _ _ => path_prod' (Commutes T _ _ _) (Commutes T' _ _ _)).
End FunctorProduct.

Infix "*" := FunctorProduct : functor_scope.

Section FunctorProduct'.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable C' : PreCategory.
  Variable D' : PreCategory.
  Variable F : Functor C D.
  Variable F' : Functor C' D'.

  Local Open Scope functor_scope.

  Definition FunctorProduct' : Functor  (C * C') (D * D')
    := (F ∘ fst_Functor) * (F' ∘ snd_Functor).
End FunctorProduct'.

Section FunctorProductUniversal.
  Context `{Funext}.

  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.

  Variable a : Functor C A.
  Variable b : Functor C B.

  Local Open Scope functor_scope.

  Local Transparent ComposeFunctors_FCompositionOf ComposeFunctors_FIdentityOf.

  Lemma FunctorProduct_Commutes_fst : fst_Functor ∘ (a * b) = a.
  Proof.
    functor_eq; trivial.
  Defined.

  Lemma FunctorProduct_Commutes_snd : snd_Functor ∘ (a * b) = b.
  Proof.
    functor_eq; trivial.
  Defined.

  (*Global Instance FunctorProduct_contr
  : Contr { F : Functor C (A * B)
          | fst_Functor ∘ F = a
            /\ snd_Functor ∘ F = b }
    := {| center := (a * b;
                     (FunctorProduct_Commutes_fst,
                      FunctorProduct_Commutes_snd)) |}.
  Proof.
    SearchAbout IsTrunc Functor.
    intros.
*)
End FunctorProductUniversal.

Section ProductInducedFunctors.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Variable F : Functor (C * D) E.

  Local Ltac t :=
    simpl; intros; rewrite <- ?FCompositionOf, <- ?FIdentityOf; simpl;
    rewrite ?LeftIdentity, ?RightIdentity;
    trivial.

  (** Note: This is just the currying exponential law *)
  Definition InducedProductFstFunctor (d : D) : Functor C E.
  Proof.
    refine (Build_Functor C E
                          (fun c => F (c, d))
                          (fun _ _ m => MorphismOf F (s := (_, _)) (d := (_, _)) (m, Identity d))
                          _
                          _);
    abstract t.
  Defined.

  Definition InducedProductSndFunctor (c : C) : Functor D E.
  Proof.
    refine (Build_Functor D E
                          (fun d => F (c, d))
                          (fun _ _ m => MorphismOf F (s := (_, _)) (d := (_, _)) (Identity c, m))
                          _
                          _);
    abstract t.
  Defined.
End ProductInducedFunctors.

Notation "F ⟨ c , - ⟩" := (InducedProductSndFunctor F c) : functor_scope.
Notation "F ⟨ - , d ⟩" := (InducedProductFstFunctor F d) : functor_scope.
