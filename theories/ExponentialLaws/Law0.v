Require Export FunctorCategory.
Require Import Common InitialTerminalCategory.

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

Section Law00.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsInitialCategory zero'}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "00" := zero' : category_scope.
  Local Notation "1" := one : category_scope.

  Local Instance IsTerminalCategory_FunctorsToInitialFromInitial
  : IsTerminalCategory [0, 00]
    := _.

  Definition ExponentialLaw00Functor : Functor [0, 0] 1
    := center _.

  Definition ExponentialLaw00Functor_Inverse : Functor 1 [0, 0]
    := center _.

  Definition ExponentialLaw00
  : ExponentialLaw00Functor ∘ ExponentialLaw00Functor_Inverse = 1
    /\ ExponentialLaw00Functor_Inverse ∘ ExponentialLaw00Functor = 1
    := center _.
End Law00.
