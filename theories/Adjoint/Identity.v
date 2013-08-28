Require Export Adjoint.UnitCounit Functor.Identity.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section IdentityAdjunction.
  (** There is an identity adjunction.  It does the obvious thing. *)
  Definition IdentityAdjunction C : IdentityFunctor C ⊣ IdentityFunctor C
    := @Build_AdjunctionUnitCounit
         C C ─ ─
         (IdentityNaturalTransformation _)
         (IdentityNaturalTransformation _)
         (fun _ => LeftIdentity _ _ _ _)
         (fun _ => RightIdentity _ _ _ _).
End IdentityAdjunction.

(* I'm not sure how much I like this notation... *)
Notation "─" := (IdentityAdjunction _) : adjunction_scope.
