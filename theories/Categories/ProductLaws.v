Require Export InitialTerminalCategory Category.Product Functor.Product.
Require Import Common Functor.Equality.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.
Local Open Scope functor_scope.

Section swap.
  Definition SwapFunctor (C D : PreCategory)
  : Functor (C * D) (D * C)
    := Build_Functor (C * D) (D * C)
                     (fun cd => (snd cd, fst cd))
                     (fun _ _ m => (snd m, fst m))
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Lemma ProductLawSwap `{Funext} (C D : PreCategory)
  : SwapFunctor C D ∘ SwapFunctor D C = 1.
  Proof.
    functor_eq.
    exists (path_forall _ _ (fun x => @eta_prod D C x)).
    repeat (apply path_forall; intro).
    rewrite !transport_forall_constant.
    destruct_head_hnf @prod.
    match goal with
      | [ |- appcontext[transport (fun x2 => (?K (fst (x2 ?x)) (fst (x2 ?x0))
                                              * ?K' (snd (x2 ?x)) (snd (x2 ?x0)))%type)
                                  (@path_forall ?H ?A ?B ?f ?g ?e)
                                  ?Px] ]
        => rewrite (@path_forall_2_beta H A B x x0 (fun x2x x2x0 => (K (fst x2x) (fst x2x0) * K' (snd x2x) (snd x2x0))%type) f g e Px)
    end.
    reflexivity.
  Qed.
End swap.

Section Law0.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Local Notation "0" := zero : category_scope.

  Variable C : PreCategory.

  Global Instance IsInitialCategory_Product
  : IsInitialCategory (C * 0)
    := fun P c => initial_category_rect P (snd c).

  Global Instance IsInitialCategory_Product'
  : IsInitialCategory (0 * C)
    := fun P c => initial_category_rect P (fst c).

  Definition ProductLaw0Functor : Functor (C * 0) 0 := FunctorFromInitial _.
  Definition ProductLaw0'Functor : Functor (0 * C) 0 := FunctorFromInitial _.
  Definition ProductLaw0Functor_Inverse : Functor 0 (C * 0) := FunctorFromInitial _.
  Definition ProductLaw0'Functor_Inverse : Functor 0 (0 * C) := FunctorFromInitial _.

  Definition ProductLaw0
  : ProductLaw0Functor ∘ ProductLaw0Functor_Inverse = 1
    /\ ProductLaw0Functor_Inverse ∘ ProductLaw0Functor = 1
    := center _.

  Definition ProductLaw0'
  : ProductLaw0'Functor ∘ ProductLaw0'Functor_Inverse = 1
    /\ ProductLaw0'Functor_Inverse ∘ ProductLaw0'Functor = 1
    := center _.
End Law0.

Section Law1.
  Context `{Funext}.
  Context `{IsTerminalCategory one}.
  Local Notation "1" := one : category_scope.
  Variable C : Category.

  Definition ProductLaw1Functor : Functor (C * 1) C
    := @fst_Functor C 1.

  Definition ProductLaw1'Functor : Functor (1 * C) C
    := @snd_Functor 1 C.

  Definition ProductLaw1Functor_Inverse : Functor C (C * 1)
    := IdentityFunctor C * FunctorToTerminal _.

  Definition ProductLaw1'Functor_Inverse : Functor C (1 * C)
    := FunctorToTerminal _ * IdentityFunctor C.

  (** We could throw this in a [repeat match goal with ... end], but
      we know the order, so we hard-code the order to speed it up by a
      factor of about 10. *)

  Local Ltac t_prod :=
    split;
    try first [ exact (FunctorProduct_Commutes_fst _ _)
              | exact (FunctorProduct_Commutes_snd _ _) ];
    [];
    apply path_prod_functor;
    rewrite <- !ComposeFunctorsAssociativity by assumption;
    (rewrite ?FunctorProduct_Commutes_fst, ?FunctorProduct_Commutes_snd,
     ?LeftIdentityFunctor, ?RightIdentityFunctor
      by assumption);
    try (reflexivity || exact (center _)).

  Lemma ProductLaw1
  : ProductLaw1Functor ∘ ProductLaw1Functor_Inverse = 1
    /\ ProductLaw1Functor_Inverse ∘ ProductLaw1Functor = 1.
  Proof.
    unfold ProductLaw1Functor, ProductLaw1Functor_Inverse.
    abstract t_prod.
  Qed.

  Lemma ProductLaw1'
  : ProductLaw1'Functor ∘ ProductLaw1'Functor_Inverse = 1
    /\ ProductLaw1'Functor_Inverse ∘ ProductLaw1'Functor = 1.
  Proof.
    unfold ProductLaw1'Functor, ProductLaw1'Functor_Inverse.
    abstract t_prod.
  Qed.
End Law1.
