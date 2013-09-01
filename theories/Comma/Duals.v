Require Export CommaCategory Category.Morphisms Category.Duals Functor.Duals.
Require Import Common.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

Section CommaDuals.
  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.

  Local Ltac t :=
    simpl; intros; repeat apply ap;
    exact (center _).

  Section op.
    Variable S : Functor A C.
    Variable T : Functor B C.

    Local Notation objOf x
     := (Build_CommaCategory_Object (T^op) (S^op) _ _ (CCO_f x)).
    Local Notation objOf_inv x
      := (Build_CommaCategory_Object S T _ _ (CCO_f x)).

    Definition CommaDualFunctor : Functor (S ↓ T) ((T^op ↓ S^op)^op).
    Proof.
      refine (Build_Functor (S ↓ T) ((T^op ↓ S^op)^op)
                            (fun x => objOf x)
                            (fun s d m => Build_CommaCategory_Morphism
                                            (objOf d) (objOf s)
                                            (CCM_h m)
                                            (CCM_g m)
                                            (symmetry _ _ (CCM_p m)))
                            _
                            _);
      abstract t.
    Defined.

    Definition CommaDualFunctor_inv : Functor ((T^op ↓ S^op)^op) (S ↓ T).
    Proof.
      refine (Build_Functor ((T^op ↓ S^op)^op) (S ↓ T)
                            (fun x => objOf_inv x)
                            (fun s d m => Build_CommaCategory_Morphism
                                            (objOf_inv s) (objOf_inv d)
                                            (CCM_h m)
                                            (CCM_g m)
                                            (symmetry _ _ (CCM_p m)))
                            _
                            _);
      abstract t.
    Defined.
  End op.

  Section op'.
    Variable S : Functor A^op C^op.
    Variable T : Functor B^op C^op.

    Local Notation objOf x
     := (Build_CommaCategory_Object (T^op') (S^op') _ _ (CCO_f x)).
    Local Notation objOf_inv x
      := (Build_CommaCategory_Object S T _ _ (CCO_f x)).

    Definition CommaDualFunctor' : Functor (S ↓ T) ((T^op' ↓ S^op')^op).
    Proof.
      refine (Build_Functor (S ↓ T) ((T^op' ↓ S^op')^op)
                            (fun x => objOf x)
                            (fun s d m => Build_CommaCategory_Morphism
                                            (objOf d) (objOf s)
                                            (CCM_h m)
                                            (CCM_g m)
                                            (symmetry _ _ (CCM_p m)))
                            _
                            _);
      abstract t.
    Defined.

    Definition CommaDualFunctor_inv' : Functor ((T^op' ↓ S^op')^op) (S ↓ T).
    Proof.
      refine (Build_Functor ((T^op' ↓ S^op')^op) (S ↓ T)
                            (fun x => objOf_inv x)
                            (fun s d m => Build_CommaCategory_Morphism
                                            (objOf_inv s) (objOf_inv d)
                                            (CCM_h m)
                                            (CCM_g m)
                                            (symmetry _ _ (CCM_p m)))
                            _
                            _);
      abstract t.
    Defined.
  End op'.
End CommaDuals.
