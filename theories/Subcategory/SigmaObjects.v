Require Export Subcategory.Sigma Functor.Composition Functor.Identity.
Require Import Common Functor.Equality.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section sigT_obj.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Definition Category_sigT_obj : PreCategory.
  Proof.
    refine (@Build_PreCategory
              (sigT Pobj)
              (fun s d => A.(Morphism) (projT1 s) (projT1 d))
              (fun x => Identity (C := A) (projT1 x))
              (fun s d d' m1 m2 => Compose (C := A) m1 m2)
              _
              _
              _
              _
           );
    simpl; intros; auto with category.
  Defined.

  Definition projT1_obj_functor : Functor Category_sigT_obj A
    := Build_Functor
         Category_sigT_obj A
         (@projT1 _ _)
         (fun s d m => m)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition Category_sigT_obj_as_sigT : PreCategory
    := @Category_sig A Pobj (fun _ _ _ => Unit) _ (fun _ => tt) (fun _ _ _ _ _ _ _ => tt).

  Definition sigT_functor_obj : Functor Category_sigT_obj_as_sigT Category_sigT_obj
    := Build_Functor Category_sigT_obj_as_sigT Category_sigT_obj
                     (fun x => x)
                     (fun _ _ => @projT1 _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition sigT_functor_obj_inv : Functor Category_sigT_obj Category_sigT_obj_as_sigT
    := Build_Functor Category_sigT_obj Category_sigT_obj_as_sigT
                     (fun x => x)
                     (fun _ _ m => existT _ m tt)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Local Open Scope functor_scope.

  Lemma sigT_obj_eq `{Funext}
  : sigT_functor_obj ∘ sigT_functor_obj_inv = IdentityFunctor _
    /\ sigT_functor_obj_inv ∘ sigT_functor_obj = IdentityFunctor _.
  Proof.
    split; functor_eq.
    repeat (apply path_forall; intro).
    destruct_head_hnf @sigT.
    destruct_head_hnf Unit.
    reflexivity.
  Qed.

  Definition sigT_obj_compat : projT1_obj_functor ∘ sigT_functor_obj = projT1_functor
    := idpath.
End sigT_obj.

Arguments projT1_obj_functor {A Pobj}.
