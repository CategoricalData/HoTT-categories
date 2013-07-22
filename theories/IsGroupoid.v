Require Export Category Category.Morphisms CommaCategory SetCategory.
Require Import Common.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Notation IsGroupoid C := (forall s d (m : Morphism C s d), IsIsomorphism m).

Definition GroupoidJ `{Funext} (C : PreCategory)
: forall (C0 : Functor (ArrowCategory C) SetCat),
    (forall x : C, C0 (Build_CommaCategory_Object (IdentityFunctor C) (IdentityFunctor C)
                                                  x x (Identity x))
                   : HSet)
    -> forall M N (P : Morphism C M N),
         C0 (Build_CommaCategory_Object (IdentityFunctor C) (IdentityFunctor C)
                                        M N P)
         : HSet.
Proof.
  intros F H' M N P.
  specialize (H' M).
  pose (Build_CommaCategory_Morphism
          (Build_CommaCategory_Object (IdentityFunctor C) (IdentityFunctor C)
                                      M M (Identity M))
          (Build_CommaCategory_Object (IdentityFunctor C) (IdentityFunctor C)
                                      M N P)
          (Identity M)
          P
          idpath)
    as m; simpl in *.
  pose (MorphismOf F m) as m'.
  exact (m' H').
Defined.
