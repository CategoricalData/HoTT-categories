Require Export Category.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Section ProductCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition ProductCategory : PreCategory.
    refine (@Build_PreCategory (C * D)%type
                               (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type)
                               (fun x => (Identity (fst x), Identity (snd x)))
                               (fun s d d' m2 m1 => (fst m2 ∘ fst m1, snd m2 ∘ snd m1))
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

Infix "*" := ProductCategory : category_scope.

Global Instance IsStrict_Product `{IsStrictCategory C, IsStrictCategory D}
: IsStrictCategory (C * D).
Proof.
  typeclasses eauto.
Qed.
