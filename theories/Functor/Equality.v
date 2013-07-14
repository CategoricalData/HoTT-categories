Require Export Functor.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

Section Functors_Equal.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Open Scope equiv_scope.

  Lemma Functor_eq' (F G : Functor C D)
  : forall HO : ObjectOf F = ObjectOf G,
      transport (fun GO => forall s d, Morphism C s d -> Morphism D (GO s) (GO d)) HO (MorphismOf F) = MorphismOf G
      -> F = G.
  Proof.
    intros.
    destruct F, G; simpl in *.
    path_induction; simpl.
    f_ap;
      abstract refine (center _).
  Defined.

  Lemma Functor_eq (F G : Functor C D)
  : forall HO : ObjectOf F == ObjectOf G,
      (forall s d m,
         transport (fun GO => forall s d, Morphism C s d -> Morphism D (GO s) (GO d))
                   (path_forall _ _ HO)
                   (MorphismOf F)
                   s d m
         = MorphismOf G m)
      -> F = G.
  Proof.
    intros.
    eapply (Functor_eq' F G (path_forall _ _ HO)).
    repeat (apply path_forall; intro); apply_hyp.
  Qed.

  Local Notation Functor_eq'_T F G := { HO : ObjectOf F = ObjectOf G
                                      | transport (fun GO => forall s d, Morphism C s d -> Morphism D (GO s) (GO d))
                                                  HO
                                                  (MorphismOf F)
                                        = MorphismOf G }.

  Definition Functor_eq'_sig (F G : Functor C D) : Functor_eq'_T F G -> F = G.
    intros [? ?].
    eapply Functor_eq'.
    eassumption.
  Defined.

  Definition Functor_eq'_sig_inv (F G : Functor C D) : F = G -> Functor_eq'_T F G
    := fun H0 => match H0 with idpath => (idpath; idpath) end.

  Local Ltac t :=
    repeat match goal with
             | _ => reflexivity
             | _ => intro
             | _ => progress path_induction
             | _ => progress destruct_head Functor
             | _ => progress simpl in *
             | _ => progress destruct_eq_in_match
             | _ => progress destruct_head sigT
             | _ => progress clear_contr_eq_in_match
           end.

  Lemma Functor_eq'_sig_equiv (F G : Functor C D)
  : Functor_eq'_T F G <~> F = G.
  Proof.
    apply (equiv_adjointify (@Functor_eq'_sig F G)
                            (@Functor_eq'_sig_inv F G));
    t.
  Defined.

  (*Lemma Functor_sig
  : { OO : C -> D
    & { MO : forall s d, Morphism C s d -> Morphism D (OO s) (OO d)
      & { FCO : forall s d d' (m1 : Morphism C s d) (m2 : Morphism C d d'),
                  MO _ _ (m2 ∘ m1) = MO d d' m2 ∘ MO s d m1
        & forall x,
            MO x x (Identity x) = Identity (OO x) } } }
      <~> Functor C D.
  Proof.
    issig (@Build_Functor C D) (@ObjectOf C D) (@MorphismOf C D) (@FCompositionOf C D) (@FIdentityOf C D).
  Defined.*)

  Global Instance Functor_IsTrunc `{IsTrunc n D} `{forall s d, IsTrunc n (Morphism D s d)}
  : IsTrunc n (Functor C D).
  Proof.
    induction n;
    simpl; intros;
    [ refine {| center := (Build_Functor C D
                                         (fun _ => center D)
                                         (fun _ _ _ => Identity _)
                                         (fun _ _ _ _ _ => symmetry _ _ (LeftIdentity D _ _ _))
                                         (fun _ => idpath)) |};
      intros;
      match goal with
        | [ |- ?F = ?G ] => apply (Functor_eq F G (fun _ => contr _))
      end;
      simpl; intros;
      refine (center _)
    | eapply trunc_equiv';
      [ exact (Functor_eq'_sig_equiv _ _)
      | typeclasses eauto ]
    ].
  Defined.
End Functors_Equal.

Ltac functor_eq :=
  repeat match goal with
           | _ => intro
           | _ => apply Functor_eq'_sig; simpl
           | _ => (exists idpath)
         end.
