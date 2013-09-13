Require Export Category.Core Functor.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section sigT_obj_mor.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Local Notation obj := (sigT Pobj).

  Variable Pmor : forall s d : obj, Morphism A s.1 d.1 -> Type.

  Local Notation mor s d := (sigT (Pmor s d)).
  Context `(HPmor : forall s d, IsHSet (mor s d)).

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 ∘ m2).

  Local Notation identity x := (@Identity A x.1; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 ∘ m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_Associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).

  Hypothesis P_LeftIdentity
  : forall a b (f : mor a b),
      compose (identity b) f = f.

  Hypothesis P_RightIdentity
  : forall a b (f : mor a b),
      compose f (identity a) = f.

  Definition Category_sigT : PreCategory.
  Proof.
    refine (@Build_PreCategory
              obj
              (fun s d => mor s d)
              (fun x => identity x)
              (fun s d d' m1 m2 => compose m1 m2)
              _
              _
              _
              _);
    assumption.
  Defined.

  Definition projT1_functor : Functor Category_sigT A
    := Build_Functor
         Category_sigT A
         (@projT1 _ _)
         (fun _ _ => @projT1 _ _)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).
End sigT_obj_mor.

Arguments projT1_functor {A Pobj Pmor HPmor Pidentity Pcompose P_Associativity P_LeftIdentity P_RightIdentity}.

Section sigT_obj_mor_hProp.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Local Notation obj := (sigT Pobj).

  Variable Pmor : forall s d : obj, Morphism A s.1 d.1 -> Type.

  Local Notation mor s d := (sigT (Pmor s d)).
  Context `(HPmor : forall s d m, IsHProp (Pmor s d m)).

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 ∘ m2).

  Local Notation identity x := (@Identity A x.1; @Pidentity x).
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

  Definition Category_sig : PreCategory
    := Eval cbv delta [P_Associativity P_LeftIdentity P_RightIdentity]
      in @Category_sigT A Pobj Pmor _ Pidentity Pcompose P_Associativity P_LeftIdentity P_RightIdentity.

  Definition proj1_sig_functor : Functor Category_sig A
    := projT1_functor.
End sigT_obj_mor_hProp.

Arguments proj1_sig_functor {A Pobj Pmor HPmor Pidentity Pcompose}.

Notation Subcategory := Category_sig.
