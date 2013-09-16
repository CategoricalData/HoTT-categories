Require Export Functor.Pointwise.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.
Local Open Scope functor_scope.

Section FunctorCategoryParts.
  Context `{Funext}.

  Let transport_idmap_ap A (P : A -> Type) x y (p : x = y) (u : P x)
  : transport idmap (ap P p) u = transport P p u
  := inverse (transport_compose idmap _ _ _).

  (** We could do this all in a big [repeat match], but we split it
      up, to shave off about two seconds per proof. *)
  Local Ltac functor_pointwise_t helper_lem_match helper_lem :=
    repeat (apply path_forall; intro);
    rewrite !transport_forall_constant, !path_forall_2_beta, !transport_path_prod'_beta;
    nt_eq;
    repeat match goal with
             | [ |- appcontext[ComponentsOf (transport ?P ?p ?z)] ]
               => rewrite (@ap_transport _ P _ _ _ p (fun _ => ComponentsOf) z)
           end;
    rewrite !transport_forall_constant;
    repeat match goal with
             | [ |- appcontext[transport ?P ?p ?u] ]
               => progress (rewrite <- (transport_idmap_ap P p u); simpl)
           end;
    repeat match goal with
             | [ x : _ |- appcontext[ap (fun x3 : ?T => ?f (ObjectOf x3 ?z))] ]
               => rewrite (@ap_compose' _ _ _ (fun x3 : T => ObjectOf x3) (fun Ox3 => f (Ox3 x)))
             | [ x : _ |- appcontext[ap (fun x3 : ?T => ?f (ObjectOf x3 ?z) ?w)] ]
               => rewrite (@ap_compose' _ _ _ (fun x3 : T => ObjectOf x3) (fun Ox3 => f (Ox3 x) w))
           end;
    repeat match goal with
             | _ => done
             | [ |- appcontext[fun F => @ObjectOf ?C ?D F] ]
               => progress change (fun F => @ObjectOf C D F) with (@ObjectOf C D)
             | [ |- appcontext[helper_lem_match ?x] ]
               => rewrite (helper_lem x)
           end.

  Section FIdentityOf.
    Variable C : PreCategory.
    Variable D : PreCategory.

    Local Transparent ComposeFunctors_FIdentityOf ComposeFunctors_FCompositionOf.

    Lemma IdentityFunctorPointwise_helper_helper (x : Functor C D)
    : 1 ∘ x ∘ 1 = x.
    Proof.
      functor_eq.
    Defined.

    Definition IdentityFunctorPointwise_helper_helper_ObjectOf x
    : ap ObjectOf (IdentityFunctorPointwise_helper_helper x) = idpath
      := Functor_eq'_sig_fst _ _ _.

    Lemma IdentityFunctorPointwise_helper
    : (fun x : Functor C D => 1 ∘ x ∘ 1) = idmap.
    Proof.
      apply path_forall; intro x.
      apply IdentityFunctorPointwise_helper_helper.
    Defined.

    Lemma IdentityFunctorPointwise
    : [IdentityFunctor C, IdentityFunctor D] = IdentityFunctor _.
    Proof.
      functor_eq.
      exists IdentityFunctorPointwise_helper.
      unfold IdentityFunctorPointwise_helper.
      functor_pointwise_t
        IdentityFunctorPointwise_helper_helper
        IdentityFunctorPointwise_helper_helper_ObjectOf.
    Qed.
  End FIdentityOf.

  Section FCompositionOf.
    Variable C : Category.
    Variable D : Category.
    Variable C' : Category.
    Variable D' : Category.
    Variable C'' : Category.
    Variable D'' : Category.

    Variable F' : Functor C' C''.
    Variable G : Functor D D'.
    Variable F : Functor C C'.
    Variable G' : Functor D' D''.

    Lemma FunctorCompositionPointwise_helper_helper (x : Functor C'' D)
    : G' ∘ G ∘ x ∘ (F' ∘ F) = G' ∘ (G ∘ x ∘ F') ∘ F.
    Proof.
      functor_eq.
    Defined.

    Definition FunctorCompositionPointwise_helper_helper_ObjectOf x
    : ap ObjectOf (FunctorCompositionPointwise_helper_helper x) = idpath
      := Functor_eq'_sig_fst _ _ _.

    Lemma FunctorCompositionPointwise_helper
    : (fun x => G' ∘ G ∘ x ∘ (F' ∘ F)) = (fun x => G' ∘ (G ∘ x ∘ F') ∘ F).
    Proof.
      apply path_forall; intro x.
      apply FunctorCompositionPointwise_helper_helper.
    Defined.

    Lemma FunctorCompositionPointwise
    : [F' ∘ F, G' ∘ G] = [F, G'] ∘ [F', G].
    Proof.
      functor_eq.
      exists FunctorCompositionPointwise_helper.
      unfold FunctorCompositionPointwise_helper.
      functor_pointwise_t
        FunctorCompositionPointwise_helper_helper
        FunctorCompositionPointwise_helper_helper_ObjectOf.
    Qed.
  End FCompositionOf.
End FunctorCategoryParts.
