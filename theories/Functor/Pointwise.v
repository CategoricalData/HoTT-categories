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
  Variable C' : PreCategory.
  Variable F : Functor C' C.

  Variable D : PreCategory.
  Variable D' : PreCategory.
  Variable G : Functor D D'.

  Local Notation PointwiseFunctor_ObjectOf H := (G ∘ H ∘ F : Object [C', D']).
  Local Notation PointwiseFunctorWhiskerL_ObjectOf H := (G ∘ H : Object [C, D']).
  Local Notation PointwiseFunctorWhiskerR_ObjectOf H := (H ∘ F : Object [C', D]).
(*  Definition PointwiseFunctor_ObjectOf : [C, D] -> [C', D']
    := fun H => G ∘ H ∘ F.*)

  Definition PointwiseFunctor_MorphismOf s d (m : Morphism [C, D] s d)
  : Morphism [C', D']
             (PointwiseFunctor_ObjectOf s)
             (PointwiseFunctor_ObjectOf d)
      := Eval simpl in (G ∘ m ∘ F)%natural_transformation.

  Definition PointwiseFunctorWhiskerL_MorphismOf s d (m : Morphism [C, D] s d)
  : Morphism [C, D']
             (PointwiseFunctorWhiskerL_ObjectOf s)
             (PointwiseFunctorWhiskerL_ObjectOf d)
      := Eval simpl in (G ∘ m)%natural_transformation.

  Definition PointwiseFunctorWhiskerR_MorphismOf s d (m : Morphism [C, D] s d)
  : Morphism [C', D]
             (PointwiseFunctorWhiskerR_ObjectOf s)
             (PointwiseFunctorWhiskerR_ObjectOf d)
      := Eval simpl in (m ∘ F)%natural_transformation.

  Global Arguments PointwiseFunctor_MorphismOf _ _ _ / .
  Global Arguments PointwiseFunctorWhiskerL_MorphismOf _ _ _ / .
  Global Arguments PointwiseFunctorWhiskerR_MorphismOf _ _ _ / .

  Definition PointwiseFunctor : Functor [C, D] [C', D'].
  Proof.
    refine (Build_Functor
              [C, D] [C', D']
              (fun x => PointwiseFunctor_ObjectOf x)
              PointwiseFunctor_MorphismOf
              _
              _);
    abstract (intros; simpl; nt_eq; auto with functor).
  Defined.

  Definition PointwiseFunctorWhiskerL : Functor [C, D] [C, D'].
  Proof.
    refine (Build_Functor
              [C, D] [C, D']
              (fun x => PointwiseFunctorWhiskerL_ObjectOf x)
              PointwiseFunctorWhiskerL_MorphismOf
              _
              _);
    abstract (intros; simpl; nt_eq; auto with functor).
  Defined.

  Definition PointwiseFunctorWhiskerR : Functor [C, D] [C', D].
  Proof.
    refine (Build_Functor
              [C, D] [C', D]
              (fun x => PointwiseFunctorWhiskerR_ObjectOf x)
              PointwiseFunctorWhiskerR_MorphismOf
              _
              _);
    abstract (intros; simpl; nt_eq; auto with functor).
  Defined.
End PointwiseFunctor.


Section notations.
  (** We do some black magic with typeclasses to make notations play
      well.  The cost is extra verbosity, but it will all disappear
      with [simpl]. *)

  Global Class PointwiseFunctor_Typable `{Funext} A B (a : A) (b : B) (T : Type) (term : T) := {}.

  Definition PointwiseFunctor_Typable_term `{@PointwiseFunctor_Typable H A B a b T term} := term.
  Global Arguments PointwiseFunctor_Typable_term / .

  Global Instance PointwiseFunctor_FunctorFunctor `{Funext} C C' D D' (F : Functor C C') (G : Functor D D')
  : PointwiseFunctor_Typable F G (PointwiseFunctor F G) | 1000.

  Global Instance PointwiseFunctor_CategoryFunctor `{Funext} C D D' (G : Functor D D')
  : PointwiseFunctor_Typable C G (PointwiseFunctorWhiskerL C G) | 100.

  Global Instance PointwiseFunctor_FunctorCategory `{Funext} C C' (F : Functor C C') D
  : PointwiseFunctor_Typable F D (PointwiseFunctorWhiskerR F D) | 100.

  Global Instance PointwiseFunctor_CategoryCategory `{Funext} C D
  : PointwiseFunctor_Typable C D (FunctorCategory C D) | 10.
End notations.

Hint Unfold PointwiseFunctor_Typable_term : typeclass_instances.

(* Set some notations for printing *)
Notation "G ^ F" := (PointwiseFunctor F G) : functor_scope.
Notation "D ^ F" := (PointwiseFunctorWhiskerR F D) : functor_scope.
Notation "G ^ C" := (PointwiseFunctorWhiskerL C G) : functor_scope.
Notation "D ^ C" := (FunctorCategory C D) : functor_scope.
Notation "[ F , G ]" := (PointwiseFunctor F G) : functor_scope.
Notation "[ F , D ]" := (PointwiseFunctorWhiskerR F D) : functor_scope.
Notation "[ C , G ]" := (PointwiseFunctorWhiskerL C G) : functor_scope.
Notation "[ C , D ]" := (FunctorCategory C D) : functor_scope.

(* Notation for parsing *)
Notation "G ^ F"
  := (@PointwiseFunctor_Typable_term _ _ _ F%functor G%functor _ _ _) : functor_scope.
Notation "[ F , G ]"
  := (@PointwiseFunctor_Typable_term _ _ _ F%functor G%functor _ _ _) : functor_scope.
