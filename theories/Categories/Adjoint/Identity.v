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
         C C 1 1
         (IdentityNaturalTransformation _)
         (IdentityNaturalTransformation _)
         (fun _ => IdentityIdentity _ _)
         (fun _ => IdentityIdentity _ _).
End IdentityAdjunction.

Notation "1" := (IdentityAdjunction _) : adjunction_scope.
