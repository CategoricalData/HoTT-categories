Require Export Functor.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section NaturalTransformation.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of functors is known as a natural transformation. Namely,
     given two functors [F : C -> D], [G : C -> D], a natural
     transformation [T: F -> G] is a collection of maps [T A : F A ->
     G A], one for each object [A] of [C], such that [(T B) ∘ (F m) =
     (G m) ∘ (T A)] for every map [m : A -> B] of [C]; that is, the
     following diagram is commutative:

<<
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    G m     V
     G A --------> G B
>>
     **)

  Record NaturalTransformation :=
    {
      ComponentsOf :> forall c, D.(Morphism) (F c) (G c);
      Commutes : forall s d (m : C.(Morphism) s d),
                   ComponentsOf d ∘ F.(MorphismOf) m = G.(MorphismOf) m ∘ ComponentsOf s
    }.
End NaturalTransformation.

Bind Scope natural_transformation_scope with NaturalTransformation.

Create HintDb natural_transformation discriminated.

Arguments ComponentsOf {C%category D%category F%functor G%functor} T%natural_transformation c%object : rename, simpl nomatch.
Arguments Commutes [C D F G] T _ _ _ : rename.

Hint Resolve @Commutes : category natural_transformation.

Section NaturalTransformations_Equal.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.

  Local Open Scope equiv_scope.

  Lemma NaturalTransformation_sig
  : { CO : forall x, Morphism D (F x) (G x) & forall s d (m : Morphism C s d),
                                                CO d ∘ F ₁ m = G ₁ m ∘ CO s }
      <~> NaturalTransformation F G.
  Proof.
    issig (@Build_NaturalTransformation _ _ F G) (@ComponentsOf _ _ F G) (@Commutes _ _ F G).
  Defined.

  Global Instance NaturalTransformation_IsHSet : IsHSet (NaturalTransformation F G).
    eapply trunc_equiv'; [ exact NaturalTransformation_sig | ].
    typeclasses eauto.
  Qed.

  Lemma NaturalTransformation_eq' (T U : NaturalTransformation F G)
  : ComponentsOf T = ComponentsOf U
    -> T = U.
  Proof.
    intros.
    destruct T, U; simpl in *.
    path_induction.
    f_ap.
    refine (center _).
  Qed.

  Lemma NaturalTransformation_eq (T U : NaturalTransformation F G)
  : ComponentsOf T == ComponentsOf U
    -> T = U.
  Proof.
    intros.
    apply NaturalTransformation_eq'.
    apply path_forall; assumption.
  Qed.

  Let eq_inv (T U : NaturalTransformation F G) : T = U -> ComponentsOf T == ComponentsOf U
    := (fun H _ => match H with idpath => idpath end).

  Lemma NaturalTransformation_eq_equiv_eisretr (T U : NaturalTransformation F G)
  : Sect (NaturalTransformation_eq T U) (@eq_inv T U).
    repeat intro.
    refine (center _).
  Qed.

  Lemma NaturalTransformation_eq_equiv_eissect (T U : NaturalTransformation F G)
  : Sect (@eq_inv T U) (NaturalTransformation_eq T U).
    repeat intro.
    refine (center _).
  Qed.

  Lemma NaturalTransformation_eq_equiv_eisadj (T U : NaturalTransformation F G)
  : forall x, @NaturalTransformation_eq_equiv_eisretr T U (@eq_inv T U x)
              = ap (@eq_inv T U) (NaturalTransformation_eq_equiv_eissect x).
    repeat intro.
    refine (center _).
  Qed.

  Lemma NaturalTransformation_eq_equiv (T U : NaturalTransformation F G)
  : T = U <~> (ComponentsOf T == ComponentsOf U).
    econstructor; econstructor; exact (@NaturalTransformation_eq_equiv_eisadj T U).
  Defined.
End NaturalTransformations_Equal.

Ltac nt_eq :=
  repeat match goal with
           | [ |- _ == _ ] => intro; simpl
           | [ |- _ = _ :> NaturalTransformation _ _ ] => apply NaturalTransformation_eq
         end.

Section NaturalTransformationComposition.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variables F F' F'' : Functor C D.
  Variables G G' : Functor D E.

  (*
     We have the diagram
<<
          F
     C -------> D
          |
          |
          | T
          |
          V
     C -------> D
          F'
          |
          | T'
          |
          V
     C ------> D
          F''
>>

     And we want the commutative diagram
<<
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    F' m    V
     F' A -------> F' B
      |            |
      |            |
      | T' A       | T' B
      |            |
      V    F'' m   V
     F'' A ------> F'' B
>>
  *)

  Section NTComposeT.
    Variable T' : NaturalTransformation F' F''.
    Variable T : NaturalTransformation F F'.

    Let CO := fun c => T' c ∘ T c.

    Local Ltac t_fin :=
      match goal with
        | _ => apply Associativity
        | _ => apply symmetry; apply Associativity
      end.

    Local Ltac t :=
      match goal with
        | _ => t_fin
        | [ T : _, m : _ |- _ ] => case (Commutes T _ _ m); t_fin
        | [ T : _, m : _ |- _ ] => case (symmetry _ _ (Commutes T _ _ m)); t_fin
      end.

    Definition NTComposeT_Commutes s d (m : Morphism C s d)
    : CO d ∘ MorphismOf F m = MorphismOf F'' m ∘ CO s.
      transitivity (T' _ ∘ (MorphismOf F' m ∘ T _));
      [
      | transitivity ((T' _ ∘ MorphismOf F' m) ∘ T _);
        [
        | ]];
      t.
    Defined.

    Global Arguments NTComposeT_Commutes / .
    Global Opaque NTComposeT_Commutes.

    Definition NTComposeT
    : NaturalTransformation F F''
      := Build_NaturalTransformation F F''
                                     (fun c => T' c ∘ T c)
                                     NTComposeT_Commutes.
  End NTComposeT.

  (*
     We have the diagram

<<
          F          G
     C -------> D -------> E
          |          |
          |          |
          | T        | U
          |          |
          V          V
     C -------> D -------> E
          F'         G'
>>

     And we want the commutative diagram

<<
             G (F m)
     G (F A) -------> G (F B)
        |                |
        |                |
        | U (T A)        | U (T B)
        |                |
        V     G' (F' m)  V
     G' (F' A) -----> G' (F' B)
>>
  *)

  Section NTComposeF.
    Variable U : NaturalTransformation G G'.
    Variable T : NaturalTransformation F F'.

    Notation CO := (fun c => G'.(MorphismOf) (T c) ∘ U (F c)).

    Definition NTComposeF_Commutes s d (m : Morphism C s d)
    : CO d ∘ (MorphismOf G (MorphismOf F m))
      = MorphismOf G' (MorphismOf F' m) ∘ CO s.
    Proof.
      simpl.
      repeat try_associativity ltac:(rewrite <- ?Commutes; rewrite <- ?FCompositionOf).
      reflexivity.
    Defined.

    Global Arguments NTComposeF_Commutes / .
    Global Opaque NTComposeF_Commutes.

    Definition NTComposeF
    : NaturalTransformation (G ∘ F) (G' ∘ F')
      := Build_NaturalTransformation (G ∘ F) (G' ∘ F')
                                     CO
                                     NTComposeF_Commutes.
  End NTComposeF.
End NaturalTransformationComposition.

(** As per Wikipedia (http://en.wikipedia.org/wiki/2-category), we use
    [∘₀] to denote composition along 0-cells (functors), and [∘₁] to
    denote composition along 1-cells (natural transformations). *)

Infix "'o0'" := NTComposeF : natural_transformation_scope.
Infix "'o1'" := NTComposeT : natural_transformation_scope.
Infix "∘₀" := NTComposeF : natural_transformation_scope.
Infix "∘₁" := NTComposeT : natural_transformation_scope.

Section IdentityNaturalTransformation.
  Context `{fs : Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Ltac id_fin_t :=
    intros;
    etransitivity;
    [ apply LeftIdentity
    | apply symmetry; apply RightIdentity ].

  (** There is an identity natrual transformation.  We create a number
      of variants, for various uses. *)
  Section Generalized.
    Variables F G : Functor C D.
    Hypothesis HO : ObjectOf F = ObjectOf G.
    Hypothesis HM : match HO in _ = GO return forall s d, Morphism C s d -> Morphism D (GO s) (GO d) with
                      | idpath => MorphismOf F
                    end = MorphismOf G.

    Notation CO c := match HO in _ = GO return Morphism D (F c) (GO c) with
                       | idpath => Identity (F c)
                     end.

    Definition GeneralizedIdentityNaturalTransformation_Commutes
               s d (m : Morphism C s d)
    : CO d ∘ MorphismOf F m
      = MorphismOf G m ∘ CO s.
    Proof.
      subst_body; simpl;
      case HM; case HO;
      id_fin_t.
    Defined.

    Global Arguments GeneralizedIdentityNaturalTransformation_Commutes / .
    Global Opaque GeneralizedIdentityNaturalTransformation_Commutes.

    Definition GeneralizedIdentityNaturalTransformation
    : NaturalTransformation F G
      := Build_NaturalTransformation F G
                                     (fun c => CO c)
                                     GeneralizedIdentityNaturalTransformation_Commutes.
  End Generalized.

  Local Arguments GeneralizedIdentityNaturalTransformation / .

  Section Generalized'.
    Variables F G : Functor C D.
    Hypothesis H : F = G.

    Definition GeneralizedIdentityNaturalTransformation' : NaturalTransformation F G.
      apply (GeneralizedIdentityNaturalTransformation F G (ap (@ObjectOf C D) H)).
      case H.
      reflexivity.
    Defined.
  End Generalized'.

  Definition IdentityNaturalTransformation (F : Functor C D) : NaturalTransformation F F
    := Eval simpl in @GeneralizedIdentityNaturalTransformation F F idpath idpath.

  Local Transparent NTComposeT_Commutes GeneralizedIdentityNaturalTransformation_Commutes.
  Local Arguments GeneralizedIdentityNaturalTransformation_Commutes / .
  Local Arguments NTComposeT_Commutes / .

  Lemma LeftIdentityNaturalTransformation (F F' : Functor C D) (T : NaturalTransformation F' F)
  : IdentityNaturalTransformation F ∘₁ T = T.
    nt_eq; auto with morphism.
  Qed.

  Lemma RightIdentityNaturalTransformation (F F' : Functor C D) (T : NaturalTransformation F F')
  : T ∘₁ IdentityNaturalTransformation F = T.
    nt_eq; auto with morphism.
  Qed.
End IdentityNaturalTransformation.

Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : category.
Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : natural_transformation.

Section IdentityNaturalTransformationF.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variable G : Functor D E.
  Variable F : Functor C D.

  Lemma NTComposeFIdentityNaturalTransformation :
    IdentityNaturalTransformation G ∘₀ IdentityNaturalTransformation F = IdentityNaturalTransformation (G ∘ F).
  Proof.
    nt_eq.
    rewrite !FIdentityOf.
    auto with morphism.
  Qed.
End IdentityNaturalTransformationF.

Hint Rewrite @NTComposeFIdentityNaturalTransformation : category.
Hint Rewrite @NTComposeFIdentityNaturalTransformation : natural_transformation.

Local Arguments GeneralizedIdentityNaturalTransformation / .

Section Associativity.
  Context `{fs : Funext}.

  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variable F : Functor D E.
  Variable G : Functor C D.
  Variable H : Functor B C.

  Notation F0 := ((F ∘ G) ∘ H)%functor.
  Notation F1 := (F ∘ (G ∘ H))%functor.

  Definition ComposeFunctorsAssociator1 : NaturalTransformation F0 F1
    := Eval simpl in GeneralizedIdentityNaturalTransformation F0 F1 idpath idpath.

  Definition ComposeFunctorsAssociator2 : NaturalTransformation F1 F0
    := Eval simpl in GeneralizedIdentityNaturalTransformation F1 F0 idpath idpath.
End Associativity.

Section IdentityFunctor.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Ltac nt_id_t := split; nt_eq; autorewrite with morphism; reflexivity.

  Section left.
    Variable F : Functor D C.

    Definition LeftIdentityFunctorNaturalTransformation1 : NaturalTransformation (IdentityFunctor _ ∘ F) F
      := Eval simpl in GeneralizedIdentityNaturalTransformation (IdentityFunctor _ ∘ F) F idpath idpath.
    Definition LeftIdentityFunctorNaturalTransformation2 : NaturalTransformation F (IdentityFunctor _ ∘ F)
      := Eval simpl in GeneralizedIdentityNaturalTransformation F (IdentityFunctor _ ∘ F) idpath idpath.

    Theorem LeftIdentityFunctorNT_Isomorphism
    : LeftIdentityFunctorNaturalTransformation1 ∘₁ LeftIdentityFunctorNaturalTransformation2 = IdentityNaturalTransformation _
      /\ LeftIdentityFunctorNaturalTransformation2 ∘₁ LeftIdentityFunctorNaturalTransformation1 = IdentityNaturalTransformation _.
    Proof.
      nt_id_t.
    Qed.
  End left.

  Section right.
    Variable F : Functor C D.

    Definition RightIdentityFunctorNaturalTransformation1 : NaturalTransformation (F ∘ IdentityFunctor _) F
      := Eval simpl in GeneralizedIdentityNaturalTransformation (F ∘ IdentityFunctor _) F idpath idpath.
    Definition RightIdentityFunctorNaturalTransformation2 : NaturalTransformation F (F ∘ IdentityFunctor _)
      := Eval simpl in GeneralizedIdentityNaturalTransformation F (F ∘ IdentityFunctor _) idpath idpath.

    Theorem RightIdentityFunctorNT_Isomorphism
    : RightIdentityFunctorNaturalTransformation1 ∘₁ RightIdentityFunctorNaturalTransformation2 = IdentityNaturalTransformation _
      /\ RightIdentityFunctorNaturalTransformation2 ∘₁ RightIdentityFunctorNaturalTransformation1 = IdentityNaturalTransformation _.
    Proof.
      nt_id_t.
    Qed.
  End right.
End IdentityFunctor.

Section NaturalTransformationExchangeLaw.
  Context `{fs : Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Variables F G H : Functor C D.
  Variables F' G' H' : Functor D E.

  Variable T : NaturalTransformation F G.
  Variable U : NaturalTransformation G H.

  Variable T' : NaturalTransformation F' G'.
  Variable U' : NaturalTransformation G' H'.

  Local Ltac t_progress := progress repeat
    match goal with
      | _ => progress f_ap
      | _ => apply Commutes
      | _ => apply symmetry; apply Commutes
    end.

  Local Ltac t_exch := repeat
    match goal with
      | _ => rewrite ?FCompositionOf, ?Associativity;
        t_progress
      | _ => rewrite <- ?FCompositionOf, <- ?Associativity;
        t_progress
    end.

  Theorem NaturalTransformationExchangeLaw
  : (U' ∘₁ T') ∘₀ (U ∘₁ T)
    = (U' ∘₀ U) ∘₁ (T' ∘₀ T).
  Proof.
    abstract (nt_eq; t_exch).
  Qed.
End NaturalTransformationExchangeLaw.

Hint Resolve @NaturalTransformationExchangeLaw : category.
Hint Resolve @NaturalTransformationExchangeLaw : natural_transformation.

Ltac nt_solve_associator' :=
  repeat match goal with
           | _ => exact (ComposeFunctorsAssociator1 _ _ _)
           | _ => exact (ComposeFunctorsAssociator2 _ _ _)
           | [ |- NaturalTransformation (?F ∘ _) (?F ∘ _) ] =>
             refine (IdentityNaturalTransformation F ∘₀ _)%natural_transformation
           | [ |- NaturalTransformation (_ ∘ ?F) (_ ∘ ?F) ] =>
             refine (_ ∘₀ IdentityNaturalTransformation F)
         end.
Ltac nt_solve_associator :=
  repeat match goal with
           | _ => refine (ComposeFunctorsAssociator1 _ _ _ ∘₁ _); progress nt_solve_associator'
           | _ => refine (_ ∘₁ ComposeFunctorsAssociator1 _ _ _); progress nt_solve_associator'
           | _ => refine (ComposeFunctorsAssociator2 _ _ _ ∘₁ _); progress nt_solve_associator'
           | _ => refine (_ ∘₁ ComposeFunctorsAssociator2 _ _ _); progress nt_solve_associator'
           | _ => progress nt_solve_associator'
         end.
