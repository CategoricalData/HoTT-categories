Require Export CommaCategory Category Functor InitialTerminalCategory Cat NaturalTransformation.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

Section LaxCommaCategory.
  Context `{Funext}.

  (** Quoting David Spivak:
     David: ok
       so an object of [FC ⇓ D] is a pair [(X, G)], where [X] is a
       finite category (or a small category or whatever you wanted)
       and [G : X --> D] is a functor.
       a morphism in [FC ⇓ D] is a ``natural transformation diagram''
       (as opposed to a commutative diagram, in which the natural
       transformation would be ``identity'')
       so a map in [FC ⇓ D] from [(X, G)] to [(X', G')] is a pair
       [(F, α)] where [F : X --> X'] is a functor and
       [α : G --> G' ∘ F] is a natural transformation
       and the punchline is that there is a functor
       [colim : FC ⇓ D --> D]
     David: consider for yourself the case where [F : X --> X'] is
       identity ([X = X']) and (separately) the case where
       [α : G --> G ∘ F] is identity.
       the point is, you've already done the work to get this colim
       functor.
       because every map in [FC ⇓ D] can be written as a composition
       of two maps, one where the [F]-part is identity and one where
       the [α]-part is identity.
       and you've worked both of those cases out already.
       *)

  Variable A : PreCategory.
  Variable B : PreCategory.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (SubPreCat P).
  Local Notation C := Cat.

  Variable S : Functor A C.
  Variable T : Functor B C.

  Local Notation LaxCommaCategory_Object := (CommaCategory_Object S T).
  Local Notation LCCO_a := (@CCO_a _ _ _ S T).
  Local Notation LCCO_b := (@CCO_b _ _ _ S T).
  Local Notation LCCO_f := (@CCO_f _ _ _ S T).

  Record LaxCommaCategory_Morphism (abf a'b'f' : LaxCommaCategory_Object) :=
    {
      LCCM_g : Morphism A (LCCO_a abf) (LCCO_a a'b'f');
      LCCM_h : Morphism B (LCCO_b abf) (LCCO_b a'b'f');
      LCCM_p : NaturalTransformation
                 (MorphismOf T LCCM_h ∘ LCCO_f abf)
                 (LCCO_f a'b'f' ∘ MorphismOf S LCCM_g)
    }.

  Local Notation LaxCommaCategory_Morphism_sig_T abf a'b'f' :=
    ({ LCCM_g : Morphism A (LCCO_a abf) (LCCO_a a'b'f')
     | { LCCM_h : Morphism B (LCCO_b abf) (LCCO_b a'b'f')
       | NaturalTransformation (MorphismOf T LCCM_h ∘ LCCO_f abf)
                               (LCCO_f a'b'f' ∘ MorphismOf S LCCM_g) }}).

  Lemma LaxCommaCategory_Morphism_sig_equiv abf a'b'f'
  : (LaxCommaCategory_Morphism_sig_T abf a'b'f')
      <~> LaxCommaCategory_Morphism abf a'b'f'.
  Proof.
    issig (@Build_LaxCommaCategory_Morphism abf a'b'f')
          (@LCCM_g abf a'b'f')
          (@LCCM_h abf a'b'f')
          (@LCCM_p abf a'b'f'). (* 5 s *)
  Defined.

  Global Instance trunc_LaxCommaCategory_Morphism abf a'b'f'
         `{IsTrunc n (Morphism A (LCCO_a abf) (LCCO_a a'b'f'))}
         `{IsTrunc n (Morphism B (LCCO_b abf) (LCCO_b a'b'f'))}
         `{forall m1 m2,
             IsTrunc n (NaturalTransformation (T ₁ m2 ∘ LCCO_f abf) (LCCO_f a'b'f' ∘ S ₁ m1))}
  : IsTrunc n (LaxCommaCategory_Morphism abf a'b'f').
  Proof.
    eapply trunc_equiv';
    [ exact (LaxCommaCategory_Morphism_sig_equiv _ _) | ].
    typeclasses eauto.
  Qed.

  Lemma LaxCommaCategory_Morphism_eq abf a'b'f'
        (gh g'h' : LaxCommaCategory_Morphism abf a'b'f')
  : forall (Hg : LCCM_g gh = LCCM_g g'h')
           (Hh : LCCM_h gh = LCCM_h g'h'),
      transport
        (fun m => NaturalTransformation (T ₁ (LCCM_h g'h') ∘ LCCO_f abf) (LCCO_f a'b'f' ∘ S ₁ m))
        Hg
        (transport
           (fun m => NaturalTransformation (T ₁ m ∘ LCCO_f abf) (LCCO_f a'b'f' ∘ S ₁ (LCCM_g gh)))
           Hh
           (LCCM_p gh))
      = LCCM_p g'h'
      -> gh = g'h'.
  Proof.
    destruct gh, g'h'; simpl.
    intros; path_induction; simpl.
    reflexivity.
  Qed.

  Section sigT_eq.
    Let curry_2_2_3_1__2_2_1_1 C D E F
        (f : forall (c : C) (d : D) (e : E c d), F)
    : { c : C | { d : D | E c d } } -> F
      := fun cde => f cde.1 cde.2.1 cde.2.2.

    Definition LaxCommaCategory_Morphism_sigT_eq abf a'b'f' gh g'h'
      := Eval cbv beta iota zeta delta[curry_2_2_3_1__2_2_1_1] in
          @curry_2_2_3_1__2_2_1_1 _ _ _ _ (@LaxCommaCategory_Morphism_eq abf a'b'f' gh g'h').
  End sigT_eq.

  Definition LaxCommaCategory_Compose s d d'
             (gh : LaxCommaCategory_Morphism d d') (g'h' : LaxCommaCategory_Morphism s d)
  : LaxCommaCategory_Morphism s d'.
  Proof.
    exists (LCCM_g gh ∘ LCCM_g g'h') (LCCM_h gh ∘ LCCM_h g'h').
    rewrite <- (inverse (FCompositionOf T _ _ _ _ _)).
    rewrite <- (inverse (FCompositionOf S _ _ _ _ _)).
    destruct g'h'.
    simpl in *.

    abstract (
        destruct_head LaxCommaCategory_Morphism;
        repeat rewrite FCompositionOf;
        repeat try_associativity ltac:(t_rev_with t')
      ).
  Defined.

  Global Arguments LaxCommaCategory_Compose _ _ _ _ _ / .

  Definition LaxCommaCategory_Identity x : LaxCommaCategory_Morphism x x.
    exists (Identity (LCCO_a x)) (Identity (LCCO_b x)).
    abstract (
        simpl; autorewrite with category; reflexivity
      ).
  Defined.

  Global Arguments LaxCommaCategory_Identity _ / .

  Local Ltac comma_eq_t :=
    intros;
    apply LaxCommaCategory_Morphism_eq;
    simpl;
    autorewrite with category;
    reflexivity.

  Definition LaxCommaCategory : PreCategory.
    refine (@Build_PreCategory
              LaxCommaCategory_Object
              LaxCommaCategory_Morphism
              LaxCommaCategory_Identity
              LaxCommaCategory_Compose
              _
              _
              _
              _
           );
    abstract comma_eq_t.
  Defined.

  Section strict.
    Global Instance LaxCommaCategory_IsStrict `{IsStrictCategory A, IsStrictCategory B}
    : IsStrictCategory LaxCommaCategory.
    Proof.
      typeclasses eauto.
    Qed.
  End strict.

(*  Section category.
    Context `{IsCategory A, IsCategory B}.
    (*Context `{Funext}. *)

    Definition LaxCommaCategory_isotoid (x y : LaxCommaCategory)
    : x ≅ y -> x = y.
    Proof.
      intro i.
      destruct i as [i [i' ? ?]].
      hnf in *.
      destruct i, i'.
      simpl in *.


    Global Instance LaxCommaCategory_IsCategory `{IsCategory A, IsCategory B}
    : IsCategory LaxCommaCategory.
    Proof.
      hnf.
      unfold IsStrictCategory in *.
      typeclasses eauto.
    Qed.
  End category.
*)
End LaxCommaCategory.

Hint Unfold LaxCommaCategory_Compose LaxCommaCategory_Identity : category.
Hint Constructors LaxCommaCategory_Morphism LaxCommaCategory_Object : category.

Section SliceCategory.
  Variable A : PreCategory.
  Variable C : PreCategory.
  Variable a : C.
  Variable S : Functor A C.

  Definition SliceCategory := LaxCommaCategory S (FunctorFromTerminal C a).
  Definition CosliceCategory := LaxCommaCategory (FunctorFromTerminal C a) S.

  (** [x ↓ F] is a coslice category; [F ↓ x] is a slice category; [x ↓ F] deals with morphisms [x -> F y]; [F ↓ x] has morphisms [F y -> x] *)
End SliceCategory.

Section SliceCategoryOver.
  Variable C : PreCategory.
  Variable a : C.

  Definition SliceCategoryOver := SliceCategory a (IdentityFunctor C).
  Definition CosliceCategoryOver := CosliceCategory a (IdentityFunctor C).
End SliceCategoryOver.

Section ArrowCategory.
  Variable C : PreCategory.

  Definition ArrowCategory := LaxCommaCategory (IdentityFunctor C) (IdentityFunctor C).
End ArrowCategory.

Notation "C / a" := (@SliceCategoryOver C a) : category_scope.
Notation "a \ C" := (@CosliceCategoryOver C a) : category_scope.

Definition CC_Functor' (C : PreCategory) (D : PreCategory) := Functor C D.
Coercion CC_FunctorFromTerminal' (C : PreCategory) (x : C) : CC_Functor' TerminalCategory C := FunctorFromTerminal C x.
Arguments CC_Functor' / .
Arguments CC_FunctorFromTerminal' / .

(* ASCII notations *)
(* Set some notations for printing *)
Notation "x |v| F" := (CosliceCategory x F) : category_scope.
Notation "F |v| x" := (SliceCategory x F) : category_scope.
Notation "S |v| T" := (LaxCommaCategory S T) : category_scope.
(* set the notation for parsing *)
Notation "S |v| T" := (LaxCommaCategory (S : CC_Functor' _ _)
                                     (T : CC_Functor' _ _)) : category_scope.

(* Unicode Notations *)
(* Set some notations for printing *)
Notation "x ↓ F" := (CosliceCategory x F) : category_scope.
Notation "F ↓ x" := (SliceCategory x F) : category_scope.
Notation "S ↓ T" := (LaxCommaCategory S T) : category_scope.
(* set the notation for parsing *)
Notation "S ↓ T" := (LaxCommaCategory (S : CC_Functor' _ _)
                                   (T : CC_Functor' _ _)) : category_scope.
(*Set Printing All.
Check (fun (C : Category)(D : Category)(E : Category)(S : Functor C D) (T : Functor E D) => (S ↓ T)%category).
Check (fun (D : Category)(E : Category)(S : Functor E D) (x : D) => (x ↓ S)%category).*)
