Require Export Category.Product Functor.Product NaturalTransformation.Core.
Require Import Common InitialTerminalCategory.

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

Section ProductInducedNaturalTransformations.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Variable F : Functor (C * D) E.

  Local Ltac t :=
    simpl; intros;
    rewrite <- !FCompositionOf;
    simpl;
    rewrite ?LeftIdentity, ?RightIdentity;
    reflexivity.

  Definition InducedProductFstNaturalTransformation s d (m : Morphism C s d)
  : NaturalTransformation (F ⟨ s, 1 ⟩) (F ⟨ d, 1 ⟩).
  Proof.
    let F0 := match goal with |- NaturalTransformation ?F0 ?G0 => constr:(F0) end in
    let G0 := match goal with |- NaturalTransformation ?F0 ?G0 => constr:(G0) end in
    refine (Build_NaturalTransformation
              F0 G0
              (fun d => MorphismOf F (s := (_, _)) (d := (_, _)) (m, Identity (C := D) d))
              _).
    abstract t.
  Defined.

  Definition InducedProductSndNaturalTransformation s d (m : Morphism D s d)
  : NaturalTransformation (F ⟨ 1, s ⟩) (F ⟨ 1 , d ⟩).
  Proof.
    let F0 := match goal with |- NaturalTransformation ?F0 ?G0 => constr:(F0) end in
    let G0 := match goal with |- NaturalTransformation ?F0 ?G0 => constr:(G0) end in
    refine (Build_NaturalTransformation
              F0 G0
              (fun c => MorphismOf F (s := (_, _)) (d := (_, _)) (Identity (C := C) c, m))
              _).
    abstract t.
  Defined.
End ProductInducedNaturalTransformations.

(*Notation "F ⟨ f , - ⟩" := (InducedProductSndNaturalTransformation F f) : natural_transformation_scope.
Notation "F ⟨ - , f ⟩" := (InducedProductFstNaturalTransformation F f) : natural_transformation_scope.*)
