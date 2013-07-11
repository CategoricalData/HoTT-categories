Require Export Category Functor.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section ProductCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Definition ProductPreCategory : PreCategory.
    refine (@Build_PreCategory (C * D)%type
                               (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type)
                               (fun x => (Identity (fst x), Identity (snd x)))
                               (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd m2) (snd m1)))
                               _
                               _
                               _
                               _);
    abstract (
        intros; destruct_head prod; simpl;
        try f_ap; auto with morphism;
        typeclasses eauto
      ).
  Defined.
End ProductCategory.

Infix "*" := ProductPreCategory : category_scope.

Section ProductCategoryFunctors.
  Context {C : PreCategory}.
  Context {D : PreCategory}.

  Definition fst_Functor : Functor (C * D) C
    := Build_Functor (C * D) C
                     (@fst _ _)
                     (fun _ _ => @fst _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition snd_Functor : Functor (C * D) D
    := Build_Functor (C * D) D
                     (@snd _ _)
                     (fun _ _ => @snd _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End ProductCategoryFunctors.
