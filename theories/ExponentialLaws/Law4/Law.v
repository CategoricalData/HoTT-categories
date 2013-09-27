Require Export ExponentialLaws.Law4.Functors.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.

Section Law4.
  Context `{Funext}.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Lemma ExponentialLaw4
  : ExponentialLaw4Functor C1 C2 D ∘ ExponentialLaw4Functor_Inverse C1 C2 D = 1
    /\
     ExponentialLaw4Functor_Inverse C1 C2 D ∘ ExponentialLaw4Functor C1 C2 D = 1.
  Proof.
    (*abstract (repeat match goal with
                       | _ => reflexivity
                       | _ => split
                       | _ => intro
                       | _ => progress (simpl in *; intros; subst; trivial)
                       | _ => apply eq_JMeq
                       | _ => apply Functor_eq
                       | _ => apply NaturalTransformation_eq
                       | _ => apply NaturalTransformation_JMeq
                       | _ => progress destruct_head prod

                       | _ => rewrite <- !FCompositionOf
                       | _ => rewrite !FIdentityOf
                       | _ => rewrite !LeftIdentity
                       | _ => rewrite !RightIdentity
                     end).*)
  Admitted.
End Law4.
