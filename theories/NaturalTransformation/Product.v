Require Export Category.Product Functor.Product NaturalTransformation.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section ProductNaturalTransformation.
  Context {A : PreCategory}.
  Context {B : PreCategory}.
  Context {C : PreCategory}.
  Variables F F' : Functor A B.
  Variables G G' : Functor A C.
  Variable T : NaturalTransformation F F'.
  Variable U : NaturalTransformation G G'.

  Definition ProductNaturalTransformation
  : NaturalTransformation (F * G) (F' * G')
    := Build_NaturalTransformation
         (F * G) (F' * G')
         (fun x : A => (T x, U x))
         (fun _ _ _ => path_prod' (Commutes T _ _ _) (Commutes U _ _ _)).
End ProductNaturalTransformation.

Infix "*" := ProductNaturalTransformation : natural_transformation_scope.
