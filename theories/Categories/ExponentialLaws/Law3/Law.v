Require Export ExponentialLaws.Law3.Functors.
Require Import Common Functor.Product Functor.Product.ProductFunctor Functor.Equality.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.

Section Law3.
  Context `{Funext}.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Lemma ExponentialLaw3_helper (c : Functor D C1 * Functor D C2)
  : (fst_Functor ∘ (fst c * snd c), snd_Functor ∘ (fst c * snd c)) = c.
  Proof.
    apply path_prod;
    [ apply FunctorProduct_Commutes_fst
    | apply FunctorProduct_Commutes_snd ].
  Defined.

  Lemma ExponentialLaw3
  : ExponentialLaw3Functor C1 C2 D ∘ ExponentialLaw3Functor_Inverse C1 C2 D = 1
    /\ ExponentialLaw3Functor_Inverse C1 C2 D ∘ ExponentialLaw3Functor C1 C2 D = 1.
  Proof.
    split; functor_eq;
    [ (exists (path_forall _ _ ExponentialLaw3_helper));
      repeat (apply path_forall || intros [? ?])
    | (exists (path_forall _ _ (fun _ => FunctorProduct_unique idpath idpath)));
      repeat (apply path_forall || intro) ];
    rewrite !transport_forall_constant;
    [ transport_path_forall_hammer;
      apply path_prod; simpl; nt_eq
    | rewrite path_forall_2_beta, transport_path_prod';
      nt_eq; apply path_prod; simpl ];
    unfold ExponentialLaw3_helper, FunctorProduct_Commutes_fst, FunctorProduct_Commutes_snd, FunctorProduct_unique, FunctorProduct_unique_helper;
    repeat match goal with
             | _ => progress simpl in *
             | _ => reflexivity
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
             | [ |- appcontext[ap (@ObjectOf ?C ?D) (@Functor_eq'_sig ?H ?C ?D ?F ?G (?HO; ?HM))] ]
               => simpl_do_clear do_rewrite (@Functor_eq'_sig_fst H C D F G HO HM)
             | _ => transport_path_forall_hammer
           end;
    repeat match goal with
             | [ |- appcontext[ComponentsOf ?T ?x] ] => generalize (T x)
             | [ |- appcontext[ObjectOf ?T ?x] ] => generalize (T x)
             | _ => by repeat (intros [] || intro)
           end.
  Qed.
End Law3.
