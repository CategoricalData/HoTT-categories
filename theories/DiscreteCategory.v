Require Export Category Groupoid.
Require Import Common.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope equiv_scope.
Local Open Scope category_scope.

Definition DiscreteCategory X `{IsHSet X} := Groupoid X.

Arguments DiscreteCategory X {_} / .
