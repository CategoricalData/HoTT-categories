Require Export Category Functor NaturalTransformation.
Require Import Common Notations NatCategory.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Notation InitialCategory := (NatCategory 0) (only parsing).
Notation TerminalCategory := (NatCategory 1) (only parsing).

Class IsTerminalCategory (C : PreCategory)
      `{Contr (Object C)}
      `{forall s d, Contr (Morphism C s d)}.

Class IsInitialCategory (C : PreCategory)
  := initial_category_rect : forall P : Type, C -> P.

Instance trunc_initial_category `{IsInitialCategory C}
: IsHProp C
  := fun x y => initial_category_rect _ x.
Instance trunc_initial_category_mor `{IsInitialCategory C} x y
: Contr (Morphism C x y)
  := initial_category_rect _ x.

Instance is_initial_category_0 : IsInitialCategory 0 := Empty_rect.
Instance: IsTerminalCategory 1 | 0.
Instance: Contr (Object 1) | 0 := _.
Instance: Contr (Morphism 1 x y) | 0 := fun x y => _.
Instance default_terminal C {H H1} : @IsTerminalCategory C H H1 | 10.

Arguments initial_category_rect / .
Arguments is_initial_category_0 / .

Section Functors.
  Variable C : PreCategory.

  Definition FunctorToTerminal `{@IsTerminalCategory one Hone Hone'}
  : Functor C one
    := Build_Functor
         C one
         (fun _ => center _)
         (fun _ _ _ => center _)
         (fun _ _ _ _ _ => contr _)
         (fun _ => contr _).

  Definition FunctorFromTerminal `{@IsTerminalCategory one Hone Hone'} (c : C)
  : Functor one C
    := Build_Functor
         one C
         (fun _ => c)
         (fun _ _ _ => Identity c)
         (fun _ _ _ _ _ => symmetry _ _ (@IdentityIdentity _ _))
         (fun _ => idpath).

  Definition FunctorFromInitial `{@IsInitialCategory zero}
  : Functor zero C
    := Build_Functor
         zero C
         (fun x => initial_category_rect _ x)
         (fun x _ _ => initial_category_rect _ x)
         (fun x _ _ _ _ => initial_category_rect _ x)
         (fun x => initial_category_rect _ x).
End Functors.

Arguments FunctorToTerminal / .
Arguments FunctorFromTerminal / .
Arguments FunctorFromInitial / .

Definition FunctorTo1 C : Functor C 1
  := Eval simpl in FunctorToTerminal C.
Definition FunctorFrom1 C c : Functor 1 C
  := Eval simpl in FunctorFromTerminal C c.
Definition FunctorFrom0 C : Functor 0 C
  := Eval simpl in FunctorFromInitial C.

Notation "! x" := (FunctorFromTerminal _ x) : functor_scope.

Section FunctorsUnique.
  Context `{Funext}.

  Global Instance trunc_InitialCategoryFunction
         `{@IsInitialCategory zero} T
  : Contr (zero -> T) :=
    let x := {| center x := initial_category_rect _ x |} in x.
  Proof.
    intro y.
    apply path_forall; intro x.
    apply (initial_category_rect _ x).
  Defined.

  Variable C : PreCategory.

  Global Instance trunc_InitialCategoryFunctor
         `{@IsInitialCategory zero}
  : Contr (Functor zero C)
    := let x := {| center := FunctorFromInitial C |} in x.
  Proof.
    abstract (
        intros; apply Functor_eq'_sig;
        (exists (center _));
        apply path_forall; intro x;
        apply (initial_category_rect _ x)
      ).
  Defined.

  Global Instance trunc_ToInitialCategoryFunctor
         `{@IsInitialCategory zero}
  : IsHProp (Functor C zero).
  Proof.
    typeclasses eauto.
  Qed.

  Definition ToInitialCategoryFunctor_empty
             `{@IsInitialCategory zero}
             (F : Functor C zero)
  : IsInitialCategory C
    := fun P x => initial_category_rect P (F x).

  Global Instance trunc_TerminalCategoryFunctor
         `{@IsTerminalCategory one H0 H1}
  : Contr (Functor C one)
    := let x := {| center := FunctorToTerminal C |} in x.
  Proof.
    intros.
    exact (center _).
  Defined.
End FunctorsUnique.

Section NaturalTransformations.
  Variable C : PreCategory.

  Definition FromInitialCategoryNaturalTransformation
             `{@IsInitialCategory zero} (F G : Functor zero C)
  : NaturalTransformation F G
    := Build_NaturalTransformation
         F G
         (fun x => initial_category_rect _ x)
         (fun x _ _ => initial_category_rect _ x).

  Global Instance trunc_FromInitialCategoryNaturalTransformation
         `{Funext}
         `{@IsInitialCategory zero} (F G : Functor zero C)
  : Contr (NaturalTransformation F G)
    := let x := {| center := FromInitialCategoryNaturalTransformation F G |}
       in x.
  Proof.
    abstract (
        intros;
        apply NaturalTransformation_eq;
        intro x;
        exact (initial_category_rect _ x)
      ).
  Defined.

  Local Existing Instance ToInitialCategoryFunctor_empty.

  Global Instance trunc_ToInitialCategoryNaturalTransformation
         `{Funext}
         `{@IsInitialCategory zero}
         (F G : Functor zero C)
  : Contr (NaturalTransformation F G)
    := trunc_FromInitialCategoryNaturalTransformation F G.

  Definition TerminalCategoryNaturalTransformation
             `{@IsTerminalCategory one H0 H1} (F G : Functor C one)
  : NaturalTransformation F G
    := Build_NaturalTransformation
         F G
         (fun x => center _)
         (fun _ _ _ => path_contr _ _).

  Global Instance trunc_TerminalCategoryNaturalTransformation
         `{Funext}
         `{@IsTerminalCategory one H0 H1} (F G : Functor C one)
  : Contr (NaturalTransformation F G)
    := let x := {| center := TerminalCategoryNaturalTransformation F G |} in x.
  Proof.
    abstract (nt_eq; exact (contr _)).
  Defined.
End NaturalTransformations.
