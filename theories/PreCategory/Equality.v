Require Export PreCategory.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section PreCategories_Equal.
  Context `{Funext}.

  Local Open Scope equiv_scope.

  Local Notation HCT C D HO HM :=
    (transport (fun morD => forall s d d' : Object D, morD d d' -> morD s d -> morD s d')
               HM
               (transportD
                  (fun objD : Type => objD -> objD -> Type)
                  (fun objC morC => forall s d d' : objC, morC d d' -> morC s d -> morC s d')
                  HO
                  (Morphism C)
                  (Compose (C := C)))
     = Compose (C := D)).
  Local Notation PreCategory_eq'_sig_T C D :=
    ({ HO : Object C = Object D
     | { HM : transport (fun objD => objD -> objD -> Type) HO (Morphism C)
              = Morphism D
       | HCT C D HO HM }}).

  Lemma PreCategory_eq'_sig (C D : PreCategory)
  : PreCategory_eq'_sig_T C D -> C = D.
  Proof.
    intros.
    destruct_head sigT.
    pose (Identity (C := C)) as IdC.
    pose (Identity (C := D)) as IdD.
    pose proof (IdentityUnique C) as X.
    destruct C, D; simpl in *.
    path_induction; simpl in *.
    assert (IdC = IdD)
      by (subst_body; apply path_forall; apply_hyp);
      subst_body.
    path_induction.
    clear X.
    f_ap;
      repeat (apply path_forall; intro);
      abstract refine (center _).
  Defined.

  Lemma PreCategory_eq' (C D : PreCategory)
  : forall (HO : Object C = Object D)
           (HM : transport (fun objD => objD -> objD -> Type) HO (Morphism C)
                 = Morphism D),
      HCT C D HO HM
      -> C = D.
  Proof.
    intros.
    apply PreCategory_eq'_sig;
      repeat esplit.
    eassumption.
  Qed.

  Lemma PreCategory_eq (C D : PreCategory)
  : forall (HO : Object C = Object D)
           (HM : forall s d,
                   transport (fun objD => objD -> objD -> Type) HO (Morphism C) s d
                   = Morphism D s d),
      HCT C D HO (path_forall _ _ (fun s => path_forall _ _ (HM s)))
      -> C = D.
  Proof.
    intros.
    eapply PreCategory_eq'.
    eassumption.
  Qed.

  Definition PreCategory_eq'_sig_inv (C D : PreCategory) : C = D -> PreCategory_eq'_sig_T C D
    := fun H0 => match H0 with idpath => (idpath; (idpath; idpath)) end.

  Local Ltac t :=
    repeat match goal with
             | _ => reflexivity
             | _ => intro
             | _ => progress path_induction
             | _ => progress destruct_head PreCategory
             | _ => progress simpl in *
             | _ => progress destruct_eq_in_match
             | _ => progress destruct_head sigT
             | _ => progress clear_contr_eq_in_match
             | [ |- appcontext[path_forall ?x ?y (IdentityUnique ?a ?b ?c ?d ?e)] ]
               => let H := fresh in
                  set (H := path_forall x y (IdentityUnique a b c d e));
                    simpl in *;
                    try clearbody H;
                    try destruct H
             | _ => progress replace_contr_idpath
           end.

  Lemma PreCategory_eq'_sig_equiv_eisretr (C D : PreCategory)
  : Sect (PreCategory_eq'_sig C D) (@PreCategory_eq'_sig_inv C D).
  Proof.
    t.
  Defined.

  Lemma PreCategory_eq'_sig_equiv_eissect (C D : PreCategory)
  : Sect (@PreCategory_eq'_sig_inv C D) (PreCategory_eq'_sig C D).
  Proof.
    t.
  Defined.

  Lemma PreCategory_eq'_sig_equiv_eisadj (C D : PreCategory)
  : forall x, @PreCategory_eq'_sig_equiv_eisretr C D (@PreCategory_eq'_sig_inv C D x)
              = ap (@PreCategory_eq'_sig_inv C D) (PreCategory_eq'_sig_equiv_eissect x).
  Proof.
    Time t. (* 61.882 secs *)
  Defined.

  Lemma PreCategory_eq'_sig_equiv (C D : PreCategory)
  : C = D <~> PreCategory_eq'_sig_T C D.
    econstructor; econstructor; exact (@PreCategory_eq'_sig_equiv_eisadj C D).
  Defined.

  (*Lemma PreCategory_sig
  : { OO : C -> D
    & { MO : forall s d, Morphism C s d -> Morphism D (OO s) (OO d)
      & { FCO : forall s d d' (m1 : Morphism C s d) (m2 : Morphism C d d'),
                  MO _ _ (m2 ∘ m1) = MO d d' m2 ∘ MO s d m1
        & forall x,
            MO x x (Identity x) = Identity (OO x) } } }
      <~> PreCategory C D.
  Proof.
    issig (@Build_PreCategory C D) (@ObjectOf C D) (@MorphismOf C D) (@FCompositionOf C D) (@FIdentityOf C D).
  Defined.*)

(*  Global Instance PreCategory_IsTrunc (C D : PreCategory)
         `{IsTrunc (trunc_S n) (Object C)} `{forall s d, IsTrunc (trunc_S n) (Morphism C s d)}
         `{IsTrunc (trunc_S n) (Object D)} `{forall s d, IsTrunc (trunc_S n) (Morphism D s d)}
  : IsTrunc n (C = D).
  Proof.
    induction n;
    simpl; intros.
    simpl in *.
    [ refine {| center := (Build_PreCategory C D
                                         (fun _ => center D)
                                         (fun _ _ _ => Identity _)
                                         (fun _ _ _ _ _ => symmetry _ _ (LeftIdentity D _ _ _))
                                         (fun _ => idpath)) |};
      intros;
      match goal with
        | [ |- ?F = ?G ] => apply (PreCategory_eq F G (fun _ => contr _))
      end;
      simpl; intros;
      refine (center _)
    | eapply trunc_equiv';
      [ apply symmetry;
        exact (PreCategory_eq'_sig_equiv _ _)
      | typeclasses eauto ]
    ].
  Defined.*)
End PreCategories_Equal.

Ltac category_eq :=
  repeat match goal with
           | [ |- _ == _ ] => intro; simpl
           | [ |- _ = _ :> PreCategory _ _ ] => eapply PreCategory_eq
         end.
