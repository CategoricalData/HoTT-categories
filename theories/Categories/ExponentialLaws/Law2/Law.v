Require Export ExponentialLaws.Law2.Functors.
Require Import Common Functor.Pointwise Functor.Product Functor.Sum NaturalTransformation.Sum.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.

Section Law2.
  Context `{Funext}.
  Variable D : PreCategory.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.

  Lemma ExponentialLaw2_helper1 (c : Functor C1 D * Functor C2 D)
  : (1 ∘ (fst c + snd c) ∘ inl_Functor C1 C2,
     1 ∘ (fst c + snd c) ∘ inr_Functor C1 C2) = c.
  Proof.
    apply path_prod; simpl;
    functor_eq.
  Defined.

  Lemma ExponentialLaw2_helper2_helper (c : Functor (C1 + C2) D) x
  : (1 ∘ c ∘ inl_Functor C1 C2 + 1 ∘ c ∘ inr_Functor C1 C2) x = c x.
  Proof.
    destruct x; reflexivity.
  Defined.

  Lemma ExponentialLaw2_helper2 (c : Functor (C1 + C2) D)
  : 1 ∘ c ∘ inl_Functor C1 C2 + 1 ∘ c ∘ inr_Functor C1 C2 = c.
  Proof.
    functor_eq.
    exists (path_forall _ _ (@ExponentialLaw2_helper2_helper c)).
    repeat (apply (@path_forall _); intro).
    (*Set Printing Implicit.
    Set Printing Coercions.
    Unset Printing Notations.
    repeat match goal with
             | _ => reflexivity
             | _ => progress simpl
             | [ H : Object 1 |- _ ] => destruct (contr H)
             | [ H : Morphism 1 _ _ |- _ ] => destruct (contr H)
             | _ => rewrite !transport_forall_constant
             | [ |- appcontext[@MorphismOf ?C ?D (transport ?P ?p ?z)] ]
               => rewrite (@ap_transport _ P _ _ _ p (fun _ => @MorphismOf C D) z)
           end.
    Set Printing Implicit.
    rewrite !transport_forall_constant.
lazymatch goal with
    | [ |- appcontext[@MorphismOf ?C ?D (transport ?P ?p ?z)] ]
      => pose (@ap_transport _ P _ _ _ p (fun _ => @MorphismOf C D) z)
    end.
    apply path_forall.

    rewrite !transport_forall_constant.*)
    admit.
  Defined.

  Lemma ExponentialLaw2
  : ExponentialLaw2Functor D C1 C2 ∘ ExponentialLaw2Functor_Inverse D C1 C2 = 1
    /\ ExponentialLaw2Functor_Inverse D C1 C2 ∘ ExponentialLaw2Functor D C1 C2 = 1.
  Proof.
    split;
    functor_eq;
    [ (exists (path_forall _ _ ExponentialLaw2_helper1))
    | (exists (path_forall _ _ ExponentialLaw2_helper2)) ]. (*
    repeat (apply (@path_forall _) || apply path_prod || intro || functor_eq || nt_eq);
    repeat match goal with
             | _ => reflexivity
             | _ => progress simpl
             | [ H : Object 1 |- _ ] => destruct (contr H)
             | [ H : Morphism 1 _ _ |- _ ] => destruct (contr H)
             | _ => rewrite !transport_forall_constant
             | [ |- appcontext[ComponentsOf (transport ?P ?p ?z)] ]
               => rewrite (@ap_transport _ P _ _ _ p (fun _ => ComponentsOf) z)
           end;
    transport_path_forall_hammer.
    destruct_head_hnf @prod;
    unfold ExponentialLaw2_helper1, ExponentialLaw2_helper2;
    rewrite !transport_path_prod;
    rewrite !transport_prod.
    Opaque Functor_eq'_sig.
    repeat match goal with
             | _ => reflexivity
             | _ => progress simpl
             | [ H : Object 1 |- _ ] => destruct (contr H)
             | [ H : Morphism 1 _ _ |- _ ] => destruct (contr H)
             | _ => rewrite !transport_forall_constant
             | [ |- appcontext[ComponentsOf (transport ?P ?p ?z)] ]
               => rewrite (@ap_transport _ P _ _ _ p (fun _ => ComponentsOf) z)
           end.
    Set Printing Coercions.
    repeat match goal with
             | [ |- appcontext[transport (fun y => ?f (@ObjectOf ?C ?D y ?x))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x)) (@ObjectOf C D))
             | [ |- appcontext[transport (fun y => ?f (@ObjectOf ?C ?D y ?x) ?z)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x) z) (@ObjectOf C D))
           end.
    Set Printing Implicit.
    simpl.
    Check @Functor_eq'_sig_fst.
    match goal with
      | [ |- appcontext[ap (@ObjectOf ?C ?D) (@Functor_eq'_sig ?H ?C ?D ?F ?G (?HO; ?HM))] ]
        => pose (@Functor_eq'_sig_fst H C D F G HO HM)
    end.
    rewrite p.
    rewrite !Functor_eq'_sig_fst.
    transport_path_forall_hammer.
    assert (idpath = contr (center 1%category)) by exact (center _).
    path_induction.
    reflexivity.




 (* Lemma ExponentialLaw2
  : ExponentialLaw2Functor ∘ ExponentialLaw2Functor_Inverse = 1
    /\ ExponentialLaw2Functor_Inverse ∘ ExponentialLaw2Functor = 1.
  Proof.
    split.
    functor_eq.
    simpl.
    abstract (repeat
                match goal with
                  | _ => reflexivity
                  | _ => split
                  | _ => progress (simpl in *; intros; trivial)
                  | _ => progress repeat subst
                  | _ => progress destruct_head_hnf @Empty_set
                  | _ => progress simpl_eq
                  | _ => progress apply Functor_eq
                  | _ => progress nt_eq
                  | _ => progress rsimplify_morphisms
                  | _ => progress destruct_head_hnf @sum
                  | _ => progress rewrite FIdentityOf
                end).
  Qed.*)*)
  Admitted.
End Law2.
