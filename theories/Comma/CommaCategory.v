Require Export Category Functor InitialTerminalCategory.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

Section CommaCategory.
  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable S : Functor A C.
  Variable T : Functor B C.

  (** Quoting Wikipedia:

      Suppose that [A], [B], and [C] are categories, and [S] and [T]
      are functors

      [S : A -> C <- B : T]

      We can form the comma category [(S ↓ T)] as follows:

      (o) The objects are all triples [(α, β, f)] with [α] an object
          in [A], [β] an object in [B], and [f : S α -> T β] a
          morphism in [C].

      (o) The morphisms from [(α, β, f)] to [(α', β', f')] are all
          pairs [(g, h)] where [g : α -> α'] and [h : β -> β'] are
          morphisms in [A] and [B] respectively, such that the
          following diagram commutes:

<<
               S g
          S α -----> S α'
           |          |
         f |          | f'
           |          |
           V          V
          T β -----> T β'
               T h
>>

     Morphisms are composed by taking [(g, h) ∘ (g', h')] to be [(g ∘
     g', h ∘ h')], whenever the latter expression is defined.  The
     identity morphism on an object [(α, β, f)] is [(Identity α,
     Identity β)].  *)

  Record CommaCategory_Object :=
    {
      CCO_a : A;
      CCO_b : B;
      CCO_f : Morphism C (S CCO_a) (T CCO_b)
    }.

  Local Notation CommaCategory_Object_sig_T :=
    ({ CCO_a : A
     | { CCO_b : B
       | Morphism C (S CCO_a) (T CCO_b) }}).

  Lemma CommaCategory_Object_sig_equiv
  : CommaCategory_Object_sig_T <~> CommaCategory_Object.
  Proof.
    issig (@Build_CommaCategory_Object)
          (@CCO_a)
          (@CCO_b)
          (@CCO_f).
  Defined.

  Global Instance trunc_CommaCategory_Object `{IsTrunc n A, IsTrunc n B}
         `{forall s d, IsTrunc n (Morphism C s d)}
  : IsTrunc n CommaCategory_Object.
  Proof.
    eapply trunc_equiv';
    [ exact CommaCategory_Object_sig_equiv | ].
    typeclasses eauto.
  Qed.

  Lemma CommaCategory_Object_eq' (x y : CommaCategory_Object)
  : forall (Hα : CCO_a x = CCO_a y)
           (Hβ : CCO_b x = CCO_b y),
      match Hα in _ = X, Hβ in _ = Y return Morphism C (S X) (T Y) with
        | idpath, idpath => CCO_f x
      end = CCO_f y
      -> x = y.
  Proof.
    destruct x, y; simpl.
    intros; path_induction; reflexivity.
  Defined.

  Record CommaCategory_Morphism (abf a'b'f' : CommaCategory_Object) :=
    {
      CCM_g : Morphism A (CCO_a abf) (CCO_a a'b'f');
      CCM_h : Morphism B (CCO_b abf) (CCO_b a'b'f');
      CCM_p : MorphismOf T CCM_h ∘ CCO_f abf = CCO_f a'b'f' ∘ MorphismOf S CCM_g
    }.

  Local Notation CommaCategory_Morphism_sig_T abf a'b'f' :=
    ({ CCM_g : Morphism A (CCO_a abf) (CCO_a a'b'f')
     | { CCM_h : Morphism B (CCO_b abf) (CCO_b a'b'f')
       | MorphismOf T CCM_h ∘ CCO_f abf = CCO_f a'b'f' ∘ MorphismOf S CCM_g }}).

  Lemma CommaCategory_Morphism_sig_equiv abf a'b'f'
  : (CommaCategory_Morphism_sig_T abf a'b'f')
      <~> CommaCategory_Morphism abf a'b'f'.
  Proof.
    issig (@Build_CommaCategory_Morphism abf a'b'f')
          (@CCM_g abf a'b'f')
          (@CCM_h abf a'b'f')
          (@CCM_p abf a'b'f').
  Defined.

  Global Instance trunc_CommaCategory_Morphism abf a'b'f'
         `{IsTrunc n (Morphism A (CCO_a abf) (CCO_a a'b'f'))}
         `{IsTrunc n (Morphism B (CCO_b abf) (CCO_b a'b'f'))}
         `{forall m1 m2,
             IsTrunc n (T ₁ m2 ∘ CCO_f abf = CCO_f a'b'f' ∘ S ₁ m1)}
  : IsTrunc n (CommaCategory_Morphism abf a'b'f').
  Proof.
    eapply trunc_equiv';
    [ exact (CommaCategory_Morphism_sig_equiv _ _) | ].
    typeclasses eauto.
  Qed.

  Lemma CommaCategory_Morphism_eq abf a'b'f'
        (gh g'h' : CommaCategory_Morphism abf a'b'f')
  : CCM_g gh = CCM_g g'h'
    -> CCM_h gh = CCM_h g'h'
    -> gh = g'h'.
  Proof.
    destruct gh, g'h'; simpl.
    intros; path_induction.
    f_ap.
    exact (center _).
  Qed.

  Definition CommaCategory_Compose s d d'
             (gh : CommaCategory_Morphism d d') (g'h' : CommaCategory_Morphism s d)
  : CommaCategory_Morphism s d'.
  Proof.
    exists (CCM_g gh ∘ CCM_g g'h') (CCM_h gh ∘ CCM_h g'h').
    hnf in *; simpl in *.
    abstract (
        destruct_head CommaCategory_Morphism;
        repeat rewrite FCompositionOf;
        repeat try_associativity ltac:(t_rev_with t')
      ).
  Defined.

  Global Arguments CommaCategory_Compose _ _ _ _ _ / .

  Definition CommaCategory_Identity x : CommaCategory_Morphism x x.
    exists (Identity (CCO_a x)) (Identity (CCO_b x)).
    abstract (
        simpl; autorewrite with category; reflexivity
      ).
  Defined.

  Global Arguments CommaCategory_Identity _ / .

  Local Ltac comma_eq_t :=
    intros;
    apply CommaCategory_Morphism_eq;
    simpl;
    autorewrite with category;
    reflexivity.

  Definition CommaCategory : PreCategory.
    refine (@Build_PreCategory
              CommaCategory_Object
              CommaCategory_Morphism
              CommaCategory_Identity
              CommaCategory_Compose
              _
              _
              _
              _
           );
    abstract comma_eq_t.
  Defined.

  Section strict.
    Global Instance CommaCategory_IsStrict `{IsStrictCategory A, IsStrictCategory B}
    : IsStrictCategory CommaCategory.
    Proof.
      typeclasses eauto.
    Qed.
  End strict.

(*  Section category.
    Context `{IsCategory A, IsCategory B}.
    (*Context `{Funext}. *)

    Definition CommaCategory_isotoid (x y : CommaCategory)
    : x ≅ y -> x = y.
    Proof.
      intro i.
      destruct i as [i [i' ? ?]].
      hnf in *.
      destruct i, i'.
      simpl in *.


    Global Instance CommaCategory_IsCategory `{IsCategory A, IsCategory B}
    : IsCategory CommaCategory.
    Proof.
      hnf.
      unfold IsStrictCategory in *.
      typeclasses eauto.
    Qed.
  End category.
*)
End CommaCategory.

Hint Unfold CommaCategory_Compose CommaCategory_Identity : category.
Hint Constructors CommaCategory_Morphism CommaCategory_Object : category.

Section SliceCategory.
  Variable A : PreCategory.
  Variable C : PreCategory.
  Variable a : C.
  Variable S : Functor A C.

  Definition SliceCategory := CommaCategory S (FunctorFromTerminal C a).
  Definition CosliceCategory := CommaCategory (FunctorFromTerminal C a) S.

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

  Definition ArrowCategory := CommaCategory (IdentityFunctor C) (IdentityFunctor C).
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
Notation "S |v| T" := (CommaCategory S T) : category_scope.
(* set the notation for parsing *)
Notation "S |v| T" := (CommaCategory (S : CC_Functor' _ _)
                                     (T : CC_Functor' _ _)) : category_scope.

(* Unicode Notations *)
(* Set some notations for printing *)
Notation "x ↓ F" := (CosliceCategory x F) : category_scope.
Notation "F ↓ x" := (SliceCategory x F) : category_scope.
Notation "S ↓ T" := (CommaCategory S T) : category_scope.
(* set the notation for parsing *)
Notation "S ↓ T" := (CommaCategory (S : CC_Functor' _ _)
                                   (T : CC_Functor' _ _)) : category_scope.
(*Set Printing All.
Check (fun (C : Category)(D : Category)(E : Category)(S : Functor C D) (T : Functor E D) => (S ↓ T)%category).
Check (fun (D : Category)(E : Category)(S : Functor E D) (x : D) => (x ↓ S)%category).*)
