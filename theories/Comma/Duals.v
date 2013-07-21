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
  Variable S : Functor A C.
  Variable T : Functor B C.

  Local Notation objOf x := (Build_CommaCategory_Object S T _ _ (CCO_f x)).
  Local Notation objOf_inv x := (Build_CommaCategory_Object (T ^op) (S ^op) _ _ (CCO_f x)).

  Definition CommaDualFunctor : Functor ((T ^op ↓ S ^op) ^op) (S ↓ T).
    refine (Build_Functor ((T ^op ↓ S ^op) ^op) (S ↓ T)
                          (fun x => objOf x)
                          (fun s d m => Build_CommaCategory_Morphism
                                          (objOf s) (objOf d)
                                          (CCM_h m)
                                          (CCM_g m)
                                          (symmetry _ _ (CCM_p m)))
                          _
                          _);
    abstract (
        simpl; intros; repeat apply ap;
        exact (center _)
      ).
  Defined.

  Definition CommaDualFunctor_inv : Functor (S ↓ T) ((T ^op ↓ S ^op) ^op).
    refine (Build_Functor (S ↓ T) ((T ^op ↓ S ^op) ^op)
                          (fun x => objOf_inv x)
                          (fun s d m => Build_CommaCategory_Morphism
                                          (objOf_inv d) (objOf_inv s)
                                          (CCM_h m)
                                          (CCM_g m)
                                          (symmetry _ _ (CCM_p m)))
                          _
                          _);
    abstract (
        simpl; intros; repeat apply ap;
        exact (center _)
      ).
  Defined.
End CommaDuals.
