Require Export ExponentialLaws.Law4.Functors.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.

Section Law4.
  Context `{Funext}.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Lemma ExponentialLaw4_helper1 c
  : ExponentialLaw4Functor C1 C2 D (ExponentialLaw4Functor_Inverse C1 C2 D c) = c.
  Proof.
    functor_eq.
    exists (path_forall _ _ (fun c1c2 => ap (ObjectOf c) (eta_prod c1c2))).
    abstract (
        repeat (apply path_forall || intro);
        rewrite !transport_forall_constant;
        transport_path_forall_hammer;
        destruct_head prod;
        rewrite <- FCompositionOf;
        simpl;
        autorewrite with morphism;
        reflexivity
      ).
  Defined.

  Lemma ExponentialLaw4_helper2_helper c x
  : ExponentialLaw4Functor_Inverse C1 C2 D (ExponentialLaw4Functor C1 C2 D c) x = c x.
  Proof.
    functor_eq.
    abstract (
        repeat (apply path_forall || intro);
        rewrite !transport_forall_constant;
        simpl;
        rewrite FIdentityOf; simpl;
          by autorewrite with morphism
      ).
  Defined.

  Local Ltac exp_t :=
    repeat match goal with
             | _ => progress simpl in *
             | _ => reflexivity
             | _ => rewrite !FIdentityOf
             | _ => progress autorewrite with morphism
             | [ |- appcontext[fst (transport ?P ?p ?z)] ]
               => simpl_do_clear do_rewrite (@ap_transport _ P _ _ _ p (fun _ => @fst _ _) z)
             | [ |- appcontext[snd (transport ?P ?p ?z)] ]
               => simpl_do_clear do_rewrite (@ap_transport _ P _ _ _ p (fun _ => @snd _ _) z)
             | [ |- appcontext[ComponentsOf (transport ?P ?p ?z)] ]
               => simpl_do_clear do_rewrite (@ap_transport _ P _ _ _ p (fun _ => ComponentsOf) z)
             | _ => rewrite !transport_path_prod
             | _ => rewrite !transport_const
             | _ => rewrite !transport_forall_constant
             | [ |- appcontext[transport (fun y => ?f (@ObjectOf ?C ?D y ?x))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x)) (@ObjectOf C D))
             | [ |- appcontext[transport (fun y => ?f (@ObjectOf ?C ?D y ?x) ?z)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x) z) (@ObjectOf C D))
             | [ |- appcontext[transport (fun y => ?f (?g (@ObjectOf ?C ?D y ?x)))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (y x))) (@ObjectOf C D))
             | [ |- appcontext[transport (fun y => ?f (?g (@ObjectOf ?C ?D y ?x)) ?z)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (y x)) z) (@ObjectOf C D))
             | [ |- appcontext[transport (fun y => ?f (?g (@ObjectOf ?C ?D y ?x) ?k))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (y x) k)) (@ObjectOf C D))
             | [ |- appcontext[transport (fun y => ?f (?g (@ObjectOf ?C ?D y ?x) ?k) ?z)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (y x) k) z) (@ObjectOf C D))
             | [ |- appcontext[ap (@ObjectOf ?C ?D) (@Functor_eq'_sig ?H ?C ?D ?F ?G (?HO; ?HM))] ]
               => simpl_do_clear do_rewrite (@Functor_eq'_sig_fst H C D F G HO HM)
             | _ => transport_path_forall_hammer
           end.

  Lemma ExponentialLaw4_helper2 c
  : ExponentialLaw4Functor_Inverse C1 C2 D (ExponentialLaw4Functor C1 C2 D c) = c.
  Proof.
    functor_eq.
    exists (path_forall _ _ (ExponentialLaw4_helper2_helper c)).
    abstract (
        repeat (apply path_forall || intro || nt_eq);
        rewrite !transport_forall_constant;
        simpl;
        rewrite path_forall_2_beta, transport_path_prod';
        unfold ExponentialLaw4_helper2_helper;
        simpl;
        exp_t
      ).
  Defined.

  Lemma ExponentialLaw4
  : ExponentialLaw4Functor C1 C2 D ∘ ExponentialLaw4Functor_Inverse C1 C2 D = 1
    /\
     ExponentialLaw4Functor_Inverse C1 C2 D ∘ ExponentialLaw4Functor C1 C2 D = 1.
  Proof.
    split;
    functor_eq;
    [ (exists (path_forall _ _ ExponentialLaw4_helper1))
    | (exists (path_forall _ _ ExponentialLaw4_helper2)) ];
    repeat (apply path_forall || intro || nt_eq);
    rewrite !transport_forall_constant;
    unfold ExponentialLaw4_helper1, ExponentialLaw4_helper2, ExponentialLaw4_helper2_helper;
    destruct_head prod.
    - exp_t.
    - exp_t.
  Qed.
End Law4.
