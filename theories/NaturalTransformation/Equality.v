Require Export Functor NaturalTransformation.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

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
