Require Export Category.Duals Groupoid Category.Equality.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

(** The groupoid categories are propositionally self-dual. *)

Local Ltac dual_t :=
  repeat match goal with
           | _ => reflexivity
           | _ => progress (repeat (apply path_forall; intro); simpl)
           | _ => apply (path_universe (symmetry _ _))
           | _ => exact (center _)
           | _ => progress category_eq; simpl
         end.

Lemma paths_sym `{Funext} `{Univalence} `{IsTrunc 1 X}
: (fun s d : X => d = s) = paths.
Proof.
  repeat (apply path_arrow; intro).
  exact (path_universe (symmetry _ _)).
Defined.

Lemma paths_refl_sym `{Funext} `{Univalence} `{IsTrunc 1 X}
: (fun x : X => x = x) = (fun x => x = x).
Proof.
  repeat (apply path_arrow; intro).
  exact (path_universe (symmetry _ _)).
Defined.

Lemma SelfDual_Groupoid `{Funext} `{Univalence} `{IsTrunc 1 X} : (Groupoid X)^op = Groupoid X.
Proof.
  dual_t.
  exists paths_sym.
  unfold Groupoid_Compose, transitivity, transitive_paths;
    repeat (apply path_forall; intro);
    repeat rewrite transport_forall_constant; simpl;
    path_induction; simpl;
    unfold paths_sym, path_arrow;
    transport_path_forall_hammer;
    rewrite !transport_arrow, !transport_path_universe, !transport_inverse, !transport_path_universe_fun_inv;
    reflexivity.
Qed.
