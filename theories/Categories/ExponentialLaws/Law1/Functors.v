Require Export FunctorCategory.
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
