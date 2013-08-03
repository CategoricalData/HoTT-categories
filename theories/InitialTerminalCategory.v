Require Export Category Functor.
Require Import Common Notations NatCategory.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section InitialTerminal.
   Definition InitialCategory : PreCategory := 0.
   Definition TerminalCategory : PreCategory := 1.
End InitialTerminal.

Section Functors.
  Variable C : PreCategory.

  Definition FunctorTo1 : Functor C 1
    := Build_Functor C 1 (fun _ => tt) (fun _ _ _ => tt) (fun _ _ _ _ _ => idpath) (fun _ => idpath).
  Definition FunctorToTerminal : Functor C TerminalCategory := FunctorTo1.

  Definition FunctorFrom1 (c : C) : Functor 1 C
    := Build_Functor 1 C (fun _ => c) (fun _ _ _ => Identity c) (fun _ _ _ _ _ => symmetry _ _ (@RightIdentity _ _ _ _)) (fun _ => idpath).
  Definition FunctorFromTerminal (c : C) : Functor TerminalCategory C := FunctorFrom1 c.

  Definition FunctorFrom0 : Functor 0 C
    := Build_Functor 0 C (fun x => match x with end) (fun x _ _ => match x with end) (fun x _ _ _ _ => match x with end) (fun x => match x with end).
  Definition FunctorFromInitial : Functor InitialCategory C := FunctorFrom0.
End Functors.

Notation "! x" := (FunctorFromTerminal _ x) : functor_scope.

Section FunctorsUnique.
  Context `{Funext}.

  Variable C : PreCategory.

  Global Instance trunc_InitialCategoryFunctor
  : Contr (Functor InitialCategory C)
    := let x := {| center := FunctorFromInitial C |} in x.
  Proof.
    abstract (
        intros; apply Functor_eq'_sig;
        (exists (center _));
        apply path_forall; intros []
      ).
  Defined.

  Global Instance trunc_ToInitialCategoryFunctor
  : IsHProp (Functor C InitialCategory).
  Proof.
    typeclasses eauto.
  Qed.

  Global Instance trunc_TerminalCategoryFunctor
  : Contr (Functor C TerminalCategory)
    := let x := {| center := FunctorToTerminal C |} in x.
  Proof.
    intros.
    exact (center _).
  Defined.
End FunctorsUnique.
