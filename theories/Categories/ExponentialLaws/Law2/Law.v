Require Export ExponentialLaws.Law2.Functors.
Require Import Common Functor.Pointwise Functor.Product Functor.Sum NaturalTransformation.Sum Functor.Equality.

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
    (exists (path_forall _ _ (@ExponentialLaw2_helper2_helper c))).
    abstract (
        repeat (apply (@path_forall _); intro);
        repeat match goal with
                 | [ H : Empty |- _ ] => by destruct H
                 | _ => reflexivity
                 | [ H : (_ + _)%type |- _ ] => destruct H
                 | [ |- appcontext[transport (fun x : ?A => forall y : ?B, @?C x y) ?p ?f ?k] ]
                   => simpl_do_clear do_rewrite (@transport_forall_constant A B C _ _ p f k)
                 | _ => progress transport_path_forall_hammer
               end
      ).
  Defined.

  Lemma ExponentialLaw2
  : ExponentialLaw2Functor D C1 C2 ∘ ExponentialLaw2Functor_Inverse D C1 C2 = 1
    /\ ExponentialLaw2Functor_Inverse D C1 C2 ∘ ExponentialLaw2Functor D C1 C2 = 1.
  Proof.
    split;
    functor_eq;
    [ (exists (path_forall _ _ ExponentialLaw2_helper1))
    | (exists (path_forall _ _ ExponentialLaw2_helper2)) ];
    repeat (apply (@path_forall _) || apply path_prod || intro || functor_eq || nt_eq);
    destruct_head prod;
    rewrite !transport_forall_constant;
    [ transport_path_forall_hammer
    | transport_path_forall_hammer
    | rewrite path_forall_2_beta, transport_path_prod' ];
    unfold ExponentialLaw2_helper1, ExponentialLaw2_helper2;
    repeat match goal with
             | _ => progress simpl in *
             | _ => reflexivity
             | [ H : (_ + _)%type |- _ ] => destruct H
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
             | [ |- appcontext[ap (@ObjectOf ?C ?D) (@Functor_eq'_sig ?H ?C ?D ?F ?G (?HO; ?HM))] ]
               => simpl_do_clear do_rewrite (@Functor_eq'_sig_fst H C D F G HO HM)
             | _ => transport_path_forall_hammer
           end.
  Qed.
End Law2.
