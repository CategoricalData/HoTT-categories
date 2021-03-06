Require Export Category.Core Functor.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section IdentityFunctor.
  (** There is an identity functor.  It does the obvious thing. *)
  Definition IdentityFunctor C : Functor C C
    := Build_Functor C C
                     (fun x => x)
                     (fun _ _ x => x)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End IdentityFunctor.

Notation "1" := (IdentityFunctor _) : functor_scope.
