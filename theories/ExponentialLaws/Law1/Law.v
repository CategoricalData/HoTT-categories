Require Export ExponentialLaws.Law1.Functors.
Require Import Common InitialTerminalCategory.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.

Section Law1.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  Definition ExponentialLaw1_helper (c : Functor 1 C)
  : FunctorFromTerminal C (c (center _)) = c.
  Proof.
    functor_eq.
    exists (path_forall _ _ (fun x => ap (ObjectOf c) (contr _))).
    abstract (
        repeat (apply path_forall; intro);
        rewrite !transport_forall_constant;
        simpl;
        transport_path_forall_hammer;
        repeat match goal with
                 | [ H : Object 1 |- _ ] => destruct (contr H)
                 | [ H : Morphism 1 _ _ |- _ ] => destruct (contr H)
               end;
        simpl;
        rewrite <- FIdentityOf;
        f_ap;
        apply symmetry;
        apply contr
      ).
  Defined.

  Lemma ExponentialLaw1
  : ExponentialLaw1Functor C ∘ ExponentialLaw1Functor_Inverse C = 1
    /\ ExponentialLaw1Functor_Inverse C ∘ ExponentialLaw1Functor C = 1.
  Proof.
    split;
    functor_eq.
    exists (path_forall _ _ ExponentialLaw1_helper).
    repeat (apply (@path_forall _) || intro || functor_eq || nt_eq).
    repeat match goal with
             | _ => reflexivity
             | _ => progress simpl
             | [ H : Object 1 |- _ ] => destruct (contr H)
             | [ H : Morphism 1 _ _ |- _ ] => destruct (contr H)
             | _ => rewrite !transport_forall_constant
             | [ |- appcontext[ComponentsOf (transport ?P ?p ?z)] ]
               => rewrite (@ap_transport _ P _ _ _ p (fun _ => ComponentsOf) z)
           end.
    transport_path_forall_hammer.
    unfold ExponentialLaw1_helper.
    repeat match goal with
             | [ |- appcontext[transport (fun y => ?f (@ObjectOf ?C ?D y ?x))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x)) (@ObjectOf C D))
             | [ |- appcontext[transport (fun y => ?f (@ObjectOf ?C ?D y ?x) ?z)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x) z) (@ObjectOf C D))
           end.
    rewrite !Functor_eq'_sig_fst.
    transport_path_forall_hammer.
    assert (idpath = contr (center 1%category)) by exact (center _).
    path_induction.
    reflexivity.
  Qed.
End Law1.
