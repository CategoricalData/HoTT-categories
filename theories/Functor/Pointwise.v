Require Export FunctorCategory.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.

Section PointwiseFunctor.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable C' : PreCategory.
  Variable D' : PreCategory.

  Variable F : Functor C' C.
  Variable G : Functor D D'.

  Local Notation PointwiseFunctor_ObjectOf H := (G ∘ H ∘ F : Object [C', D']).
(*  Definition PointwiseFunctor_ObjectOf : [C, D] -> [C', D']
    := fun H => G ∘ H ∘ F.*)

  Definition PointwiseFunctor_MorphismOf s d (m : Morphism [C, D] s d)
  : Morphism [C', D']
             (PointwiseFunctor_ObjectOf s)
             (PointwiseFunctor_ObjectOf d)
      := Eval simpl in (G ∘ m ∘ F)%natural_transformation.

  Global Arguments PointwiseFunctor_MorphismOf _ _ _ / .

  Definition PointwiseFunctor : Functor [C, D] [C', D'].
    refine (Build_Functor
              [C, D] [C', D']
              (fun x => PointwiseFunctor_ObjectOf x)
              PointwiseFunctor_MorphismOf
              _
              _);
    abstract (intros; simpl; nt_eq; auto with functor).
  Defined.
End PointwiseFunctor.

Notation "G ^ F" := (PointwiseFunctor F G) : functor_scope.
Notation "[ F , G ]" := (PointwiseFunctor F G) : functor_scope.
