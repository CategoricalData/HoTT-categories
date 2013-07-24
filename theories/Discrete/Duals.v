Require Export Category.Duals DiscreteCategory Category.Equality.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

(** The discrete categories are propositionally self-dual. *)

Local Ltac dual_t :=
  repeat match goal with
           | _ => reflexivity
           | _ => progress (repeat (apply path_forall; intro); simpl)
           | _ => apply (path_universe (symmetry _ _))
           | [ |- @sigT ?A ?P ] => cut A;
                                  [ let t := fresh in
                                    intro t; exists t
                                  | ]
           | _ => exact (center _)
           | _ => progress category_eq; simpl
         end.

Lemma SelfDual_Discrete `{Funext} `{Univalence} `{IsHSet X}
: (DiscreteCategory X)^op = DiscreteCategory X.
Proof.
  dual_t.
Qed.
