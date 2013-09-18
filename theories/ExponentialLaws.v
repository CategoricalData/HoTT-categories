Require Export FunctorCategory Category.Sum Category.Product Functor.
Require Import Common NatCategory InitialTerminalCategory Functor.Pointwise Functor.Product Functor.Sum NatCategory Functor.Pointwise.Properties NaturalTransformation.Sum NaturalTransformation.CompositionLaws Functor.Product.ProductFunctor.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.

Section Law0.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  Global Instance IsTerminalCategory_FunctorsFromInitial
  : IsTerminalCategory [0, C].

  Definition ExponentialLaw0Functor : Functor [0, C] 1
    := center _.

  Definition ExponentialLaw0Functor_Inverse : Functor 1 [0, C]
    := center _.

  Definition ExponentialLaw0
  : ExponentialLaw0Functor ∘ ExponentialLaw0Functor_Inverse = 1
    /\ ExponentialLaw0Functor_Inverse ∘ ExponentialLaw0Functor = 1
    := center _.
End Law0.

Section Law0'.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.
  Variable c : C.

  Local Instance IsInitialCategory_FunctorsToInitialFromInhabited
  : IsInitialCategory [C, 0]
    := fun P F => @ToInitialCategoryFunctor_empty C _ _ F P c.

  Definition ExponentialLaw0'Functor : Functor [C, 0] 0
    := center _.

  Definition ExponentialLaw0'Functor_Inverse : Functor 0 [C, 0]
    := center _.

  Definition ExponentialLaw0'
  : ExponentialLaw0'Functor ∘ ExponentialLaw0'Functor_Inverse = 1
    /\ ExponentialLaw0'Functor_Inverse ∘ ExponentialLaw0'Functor = 1
    := center _.
End Law0'.

Section Law1.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  Definition ExponentialLaw1Functor : Functor [1, C] C
    := Build_Functor [1, C] C
                     (fun F => F (center _))
                     (fun s d m => m (center _))
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition ExponentialLaw1Functor_Inverse_MorphismOf
             s d (m : Morphism C s d)
  : Morphism [1, C]
             (FunctorFromTerminal _ s)
             (FunctorFromTerminal _ d).
  Proof.
    refine (Build_NaturalTransformation
              (FunctorFromTerminal _ s)
              (FunctorFromTerminal _ d)
              (fun _ => m)
              _).
    simpl; intros.
    etransitivity;
      [ apply RightIdentity
      | apply symmetry; apply LeftIdentity ].
  Defined.

  Global Arguments ExponentialLaw1Functor_Inverse_MorphismOf / _ _ _.

  Definition ExponentialLaw1Functor_Inverse : Functor C [1, C].
  Proof.
    refine (Build_Functor
              C [1, C]
              (@FunctorFromTerminal _ _ _ _ _)
              ExponentialLaw1Functor_Inverse_MorphismOf
              _
              _
           );
    abstract (nt_eq; trivial).
  Defined.

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
  : ExponentialLaw1Functor ∘ ExponentialLaw1Functor_Inverse = 1
    /\ ExponentialLaw1Functor_Inverse ∘ ExponentialLaw1Functor = 1.
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

Section Law1'.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  Global Instance: IsTerminalCategory [C, 1].

  Definition ExponentialLaw1'Functor : Functor [C, 1] 1
    := FunctorToTerminal _.

  Definition ExponentialLaw1'Functor_Inverse : Functor 1 [C, 1]
    := FunctorToTerminal _.

  Definition ExponentialLaw1'
  : ExponentialLaw1'Functor ∘ ExponentialLaw1'Functor_Inverse = 1
    /\ ExponentialLaw1'Functor_Inverse ∘ ExponentialLaw1'Functor = 1
    := center _.
End Law1'.

Section LawEval.
  (** Insert evaluation functor C * [C, D] -> D *)
End LawEval.

Section Law2.
  Context `{Funext}.
  Variable D : PreCategory.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.

  Definition ExponentialLaw2Functor
  : Functor [C1 + C2, D] ([C1, D] * [C2, D])
    := PointwiseFunctor (inl_Functor C1 C2) (IdentityFunctor D)
       * PointwiseFunctor (inr_Functor C1 C2) (IdentityFunctor D).

  Definition ExponentialLaw2Functor_Inverse
  : Functor ([C1, D] * [C2, D]) [C1 + C2, D].
  Proof.
    let C := match goal with |- Functor ?C ?D => constr:(C) end in
    let D := match goal with |- Functor ?C ?D => constr:(D) end in
    refine (Build_Functor
              C D
              (fun FG => sum_Functor (fst FG) (snd FG))
              (fun _ _ m => sum_Functor_Functorial (fst m) (snd m))
              _
              _);
    simpl in *;
    abstract (
        repeat (intros [?|?] || intros [? ?]);
        simpl in *;
          apply NaturalTransformation_eq; intros [?|?];
        reflexivity
      ).
  Defined.


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
  Qed.*)
End Law2.

Section Law3.
  Context `{Funext}.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Definition ExponentialLaw3Functor
  : Functor [D, C1 * C2] ([D, C1] * [D, C2])
    := Build_Functor
         [D, C1 * C2] ([D, C1] * [D, C2])
         (fun H => (fst_Functor ∘ H, snd_Functor ∘ H))
         (fun s d m =>
            (NTWhiskerL fst_Functor m,
             NTWhiskerL snd_Functor m))
         (fun _ _ _ _ _ => path_prod' (NTWhiskerL_CompositionOf _ _ _)
                                      (NTWhiskerL_CompositionOf _ _ _))
         (fun _ => path_prod' (RightIdentityNaturalTransformationWhisker _ _)
                              (RightIdentityNaturalTransformationWhisker _ _)).

  Definition ExponentialLaw3Functor_Inverse
  : Functor ([D, C1] * [D, C2]) [D, C1 * C2]
    := FunctorProduct_Functor _ _ _.
(*
  Lemma ExponentialLaw3
  : ExponentialLaw3Functor ∘ ExponentialLaw3Functor_Inverse = 1
    /\ ExponentialLaw3Functor_Inverse ∘ ExponentialLaw3Functor = 1.
  Proof.
    split; functor_eq; simpl.
    abstract (
        repeat
          match goal with
            | _ => reflexivity
            | _ => split
            | _ => progress (simpl; intros; trivial)
            | _ => progress repeat subst
            | _ => progress JMeq_eq
            | _ => progress simpl_eq
            | _ => progress apply Functor_eq
            | _ => progress apply NaturalTransformation_JMeq
            | _ => rsimplify_morphisms
          end
      ).
  Qed.*)
End Law3.

Section Law4.
  Context `{Funext}.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Local Open Scope morphism_scope.

  Local Ltac do_exponential4_helper rew_comp :=
    intros; simpl;
    repeat (simpl;
            match goal with
              | _ => reflexivity
              | _ => progress rew_comp
              | _ => rewrite !FIdentityOf
              | _ => rewrite !LeftIdentity
              | _ => rewrite !RightIdentity
              | _ => try_associativity_quick ltac:(f_ap)
              | _ => rewrite !Commutes
              | _ => try_associativity_quick ltac:(rewrite !Commutes)
            end).

  Section functor.
    Local Ltac do_exponential4
      := do_exponential4_helper ltac:(rewrite !FCompositionOf).

    Definition ExponentialLaw4Functor_ObjectOf
    : [C1, [C2, D]]%category -> [C1 * C2, D]%category.
    Proof.
      intro F; hnf in F |- *.
      refine (Build_Functor
                (C1 * C2) D
                (fun c1c2 => F (fst c1c2) (snd c1c2))
                (fun s d m => F (fst d) ₁ (snd m) ∘ (F ₁ (fst m)) (snd s))
                _
                _);
        abstract do_exponential4.
    Defined.

    Definition ExponentialLaw4Functor_MorphismOf
               s d (m : Morphism [C1, [C2, D]] s d)
    : Morphism [C1 * C2, D]
               (ExponentialLaw4Functor_ObjectOf s)
               (ExponentialLaw4Functor_ObjectOf d).
    Proof.
      simpl.
      refine (Build_NaturalTransformation
                (ExponentialLaw4Functor_ObjectOf s)
                (ExponentialLaw4Functor_ObjectOf d)
                (fun c => m (fst c) (snd c))
                _);
        abstract (
            repeat match goal with
                     | [ |- appcontext[ComponentsOf ?T ?x ∘ ComponentsOf ?U ?x] ] =>
                       change (T x ∘ U x) with ((Compose (C := [_, _]) T U) x)
                     | _ => f_ap
                     | _ => rewrite !Commutes
                     | _ => do_exponential4
                   end
          ).
    Defined.

    Definition ExponentialLaw4Functor
    : Functor [C1, [C2, D]] [C1 * C2, D].
    Proof.
      refine (Build_Functor
                [C1, [C2, D]] [C1 * C2, D]
                ExponentialLaw4Functor_ObjectOf
                ExponentialLaw4Functor_MorphismOf
                _
                _);
      abstract by nt_eq.
    Defined.
  End functor.

  Section inverse.
    Local Ltac do_exponential4_inverse
      := do_exponential4_helper ltac:(rewrite <- !FCompositionOf).

    Section ObjectOf.
      Variable F : Functor (C1 * C2) D.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf
      : C1 -> [C2, D]%category.
      Proof.
        intro c1.
        refine (Build_Functor
                  C2 D
                  (fun c2 => F (c1, c2))
                  (fun s2 d2 m2 => F.(MorphismOf) (s := (c1, s2)) (d := (c1, d2)) (Identity c1, m2))
                  _
                  _);
          abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf_MorphismOf
                 s d (m : Morphism C1 s d)
      : Morphism [C2, D]
                 (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf s)
                 (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf d).
      Proof.
        refine (Build_NaturalTransformation
                  (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf s)
                  (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf d)
                  (fun c => F.(MorphismOf) (s := (s, c)) (d := (d, c)) (m, Identity c))
                  _);
        abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf
      : [C1, [C2, D]]%category.
      Proof.
        refine (Build_Functor
                  C1 [C2, D]
                  ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf
                  ExponentialLaw4Functor_Inverse_ObjectOf_MorphismOf
                  _
                  _);
        abstract (nt_eq; do_exponential4_inverse).
      Defined.
    End ObjectOf.

    Section MorphismOf.
      Definition ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf
                 s d (m : Morphism [C1 * C2, D] s d)
      : forall c, Morphism [C2, D]
                           ((ExponentialLaw4Functor_Inverse_ObjectOf s) c)
                           ((ExponentialLaw4Functor_Inverse_ObjectOf d) c).
      Proof.
        intro c.
        refine (Build_NaturalTransformation
                  ((ExponentialLaw4Functor_Inverse_ObjectOf s) c)
                  ((ExponentialLaw4Functor_Inverse_ObjectOf d) c)
                  (fun c' => m (c, c'))
                  _).
        abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_MorphismOf
                 s d (m : Morphism [C1 * C2, D] s d)
      : Morphism [C1, [C2, D]]
                 (ExponentialLaw4Functor_Inverse_ObjectOf s)
                 (ExponentialLaw4Functor_Inverse_ObjectOf d).
      Proof.
        refine (Build_NaturalTransformation
                  (ExponentialLaw4Functor_Inverse_ObjectOf s)
                  (ExponentialLaw4Functor_Inverse_ObjectOf d)
                  (ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf m)
                  _).
        abstract (nt_eq; do_exponential4_inverse).
      Defined.
    End MorphismOf.

    Arguments ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf / _ _ _ _ .

    Definition ExponentialLaw4Functor_Inverse
    : Functor [C1 * C2, D] [C1, [C2, D]].
    Proof.
      refine (Build_Functor
                [C1 * C2, D] [C1, [C2, D]]
                ExponentialLaw4Functor_Inverse_ObjectOf
                ExponentialLaw4Functor_Inverse_MorphismOf
                _
                _);
      abstract by nt_eq.
    Defined.
  End inverse.

(*  Lemma ExponentialLaw4
  : ExponentialLaw4Functor ExponentialLaw4Functor_Inverse
    = 1 /\
    ExponentialLaw4Functor_Inverse ExponentialLaw4Functor
    = 1.
  Proof.
    abstract (repeat match goal with
                       | _ => reflexivity
                       | _ => split
                       | _ => intro
                       | _ => progress (simpl in *; intros; subst; trivial)
                       | _ => apply eq_JMeq
                       | _ => apply Functor_eq
                       | _ => apply NaturalTransformation_eq
                       | _ => apply NaturalTransformation_JMeq
                       | _ => progress destruct_head prod

                       | _ => rewrite <- !FCompositionOf
                       | _ => rewrite !FIdentityOf
                       | _ => rewrite !LeftIdentity
                       | _ => rewrite !RightIdentity
                     end).
  Qed.*)
End Law4.
