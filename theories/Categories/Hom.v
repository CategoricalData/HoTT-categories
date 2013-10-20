Require Export Category Functor Category.Duals Category.Product Functor.Product SetCategory.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope category_scope.

(*
   We could do covariant and contravariant as


  Section covariant_contravariant.
    Local Arguments InducedProductSndFunctor / .
    Local Arguments InducedProductFstFunctor / .
    Definition CovariantHomFunctor (A : Object C^op)
      := Eval simpl in (HomFunctor ⟨ A , - ⟩)%functor.
    Definition ContravariantHomFunctor (A : C)
      := Eval simpl in (HomFunctor ⟨ - , A ⟩)%functor.
  End covariant_contravariant.
*)

Section HomFunctor.
  Context `{Funext}.
  Variable C : PreCategory.

  Local Notation objOf c'c :=
    (BuildhSet
       (Morphism C (fst (c'c : Object (C^op * C))) (snd (c'c : Object (C^op * C))))
       _).

  Definition HomFunctor_MorphismOf s's d'd (hf : Morphism (C^op * C) s's d'd)
  : Morphism SetCat (objOf s's) (objOf d'd)
    := fun g => snd hf ∘ g ∘ fst hf.

  Definition HomFunctor : Functor (C^op * C) SetCat.
    refine (Build_Functor (C^op * C) SetCat
                          (fun c'c => objOf c'c)
                          HomFunctor_MorphismOf
                          _
                          _);
    abstract (
        repeat (apply path_forall || intros [] || intro);
        simpl in *;
          unfold HomFunctor_MorphismOf, compose; simpl;
        rewrite <- ?Associativity, ?LeftIdentity, ?RightIdentity;
        reflexivity
      ).
  Defined.
End HomFunctor.
