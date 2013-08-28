Require Export Adjoint.UnitCounit NaturalTransformation.Equality.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section Adjunctions_Equal.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Local Open Scope equiv_scope.

  Notation Adjunction_sigT :=
    { η : NaturalTransformation ─ (G ∘ F)
    | { ε : NaturalTransformation (F ∘ G) ─
      | { equ1 : forall Y : C, (ε (F Y) ∘ F ₁ (η Y))%morphism = ─
        | forall X : D, (G ₁ (ε X) ∘ η (G X))%morphism = ─ }}}.

  Lemma Adjunction_sig
  : Adjunction_sigT <~> (F ⊣ G).
  Proof.
    issig (@Build_AdjunctionUnitCounit _ _ F G)
          (@Adjunction_Unit _ _ F G)
          (@Adjunction_Counit _ _ F G)
          (@Adjunction_UnitCounitEquation1 _ _ F G)
          (@Adjunction_UnitCounitEquation2 _ _ F G).
  Defined.

  Global Instance trunc_adjunction : IsHSet (F ⊣ G).
  Proof.
    eapply trunc_equiv'; [ exact Adjunction_sig | ].
    typeclasses eauto.
  Qed.

  Lemma Adjunction_eq' (A A' : F ⊣ G)
  : Adjunction_Unit A = Adjunction_Unit A'
    -> Adjunction_Counit A = Adjunction_Counit A'
    -> A = A'.
  Proof.
    intros.
    destruct A, A'; simpl in *.
    path_induction.
    f_ap;
      exact (center _).
  Qed.

  Lemma Adjunction_eq (A A' : F ⊣ G)
  : ComponentsOf (Adjunction_Unit A) == ComponentsOf (Adjunction_Unit A')
    -> ComponentsOf (Adjunction_Counit A) == ComponentsOf (Adjunction_Counit A')
    -> A = A'.
  Proof.
    intros.
    apply Adjunction_eq';
    apply NaturalTransformation_eq;
    assumption.
  Qed.

  (** In fact, it suffices to show that either the units are equal, or
      the counits are euqal, by the UMP of the (co)unit.  And if we
      are working in a [Category], rather than a [PreCategory], then
      [Adjunction] is, in fact, an hProp, because the (co)unit is
      unique up to unique isomorphism.

      TODO: Formalize this. *)
End Adjunctions_Equal.

Ltac adjunction_eq :=
  repeat match goal with
           | _ => intro
           | _ => apply Adjunction_eq; simpl
         end.
