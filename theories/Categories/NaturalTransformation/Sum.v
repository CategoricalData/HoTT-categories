Require Export Functor.Sum NaturalTransformation.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section sum_functor_nt.
  Definition sum_Functor_Functorial
             C C' D F G F' G'
             (T : @NaturalTransformation C D F G)
             (T' : @NaturalTransformation C' D F' G')
  : NaturalTransformation (F + F') (G + G').
  Proof.
    refine (Build_NaturalTransformation
              (F + F') (G + G')
              (fun x => match x with
                          | inl c => T c
                          | inr c' => T' c'
                        end)
              _).
    abstract (
        repeat (intros [] || intro); simpl;
        auto with natural_transformation
      ).
  Defined.
End sum_functor_nt.

Notation "T + U" := (sum_Functor_Functorial T U) : natural_transformation_scope.
