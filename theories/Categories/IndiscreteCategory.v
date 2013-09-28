Require Export Category Functor.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section IndiscreteCategory.
  (** The indiscrete category has exactly one morphism between any two
      objects. *)
  Variable X : Type.

  (** We define the symmetrized version of associaitivity differently
      so that the dual of an indiscrete category is convertible with
      the indiscrete category. *)

  Definition IndiscreteCategory : PreCategory
    := @Build_PreCategory' X
                           (fun _ _ => Unit)
                           (fun _ => tt)
                           (fun _ _ _ _ _ => tt)
                           (fun _ _ _ _ _ _ _ => idpath)
                           (fun _ _ _ _ _ _ _ => idpath)
                           (fun _ _ f => match f with tt => idpath end)
                           (fun _ _ f => match f with tt => idpath end)
                           (fun _ => idpath)
                           _.
End IndiscreteCategory.

Definition IsStrict_Indiscrete `{H : IsHSet X}
: IsStrictCategory (IndiscreteCategory X)
  := H.

Instance IsCategory_Indiscrete `{H : IsHProp X}
: IsCategory (IndiscreteCategory X).
Proof.
  intros.
  eapply (isequiv_adjointify (idtoiso (IndiscreteCategory X) (x := s) (y := d))
                             (fun _ => center _));
    abstract (
        repeat intro;
        destruct_head_hnf @Isomorphic;
        destruct_head_hnf @IsIsomorphism;
        destruct_head_hnf @Unit;
        path_induction_hammer
      ).
Defined.

Section FunctorToIndiscrete.
  Variable X : Type.
  Variable C : PreCategory.
  Variable objOf : C -> X.

  Definition FunctorToIndiscrete : Functor C (IndiscreteCategory X)
    := Build_Functor C (IndiscreteCategory X)
                     objOf
                     (fun _ _ _ => tt)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End FunctorToIndiscrete.
