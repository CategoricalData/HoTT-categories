Require Export Category.Duals NatCategory Category.Equality.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

(** The categories [0] and [1] are judgementally self-dual. *)
Definition SelfDual_Initial : 0^op = 0 := idpath.
Definition SelfDual_Terminal : 1^op = 1 := idpath.

(** The nat categories are propositionally self-dual. *)
(** We need [CardinalityRepresentative] to be [Opaque] so that we pick
    up the truncation rule for it. *)
Local Opaque CardinalityRepresentative.

Local Ltac dual_t :=
  repeat match goal with
           | _ => reflexivity
           | [ |- @sigT ?A ?P ] => let t := fresh in
                                   assert (t : A);
                                     [
                                     | exists t ]
           | _ => progress (repeat (apply path_forall; intro); simpl)
           | _ => apply (path_universe (symmetry _ _))
           | _ => exact (center _)
           | _ => progress category_eq; simpl
         end.

Lemma SelfDual_NatCategory `{Funext} `{Univalence} (n : nat) : n^op = n.
Proof.
  destruct n as [|[|]];
  dual_t.
Qed.
