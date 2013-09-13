Require Export Subcategory.SigmaMorphisms.
Require Import Common Functor.Equality.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section sigT_mor_hProp.
  Variable A : PreCategory.
  Variable Pmor : forall s d, Morphism A s d -> Type.

  Local Notation mor s d := (sigT (Pmor s d)).
  Context `(HPmor : forall s d m, IsHProp (Pmor s d m)).

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 ∘ m2).

  Local Notation identity x := (@Identity A x; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 ∘ m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Local Ltac t ex_tac :=
    intros;
    simpl;
    apply path_sigma_uncurried;
    simpl;
    ex_tac;
    apply allpath_hprop.

  Let P_Associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).
  Proof.
    abstract t ltac:(exists (Associativity _ _ _ _ _ _ _ _)).
  Qed.

  Let P_LeftIdentity
  : forall a b (f : mor a b),
      compose (identity b) f = f.
  Proof.
    subst_body.
    abstract t ltac:(exists (LeftIdentity _ _ _ _)).
  Defined.

  Let P_RightIdentity
  : forall a b (f : mor a b),
      compose f (identity a) = f.
  Proof.
    subst_body.
    abstract t ltac:(exists (RightIdentity _ _ _ _)).
  Defined.

  Definition Category_sig_mor : PreCategory
    := Eval cbv delta [P_Associativity P_LeftIdentity P_RightIdentity]
      in @Category_sigT_mor A Pmor _ Pidentity Pcompose P_Associativity P_LeftIdentity P_RightIdentity.

  Definition proj1_sig_mor_functor : Functor Category_sig_mor A
    := projT1_mor_functor.
End sigT_mor_hProp.

Arguments proj1_sig_mor_functor {A Pmor HPmor Pidentity Pcompose}.

Notation WideSubcategory := Category_sig_mor.
