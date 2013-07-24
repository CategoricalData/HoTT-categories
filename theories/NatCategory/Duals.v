Require Export Category.Duals NatCategory Discrete.Duals.
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
Lemma SelfDual_NatCategory `{Funext} `{Univalence} (n : nat) : n^op = n.
Proof.
  destruct n as [|[|]]; try reflexivity;
  apply SelfDual_Discrete.
Qed.
