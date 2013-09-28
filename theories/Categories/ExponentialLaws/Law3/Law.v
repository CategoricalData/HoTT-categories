Require Export ExponentialLaws.Law3.Functors.
Require Import Common Functor.Product Functor.Product.ProductFunctor.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.

Section Law3.
  Context `{Funext}.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Lemma ExponentialLaw3
  : ExponentialLaw3Functor C1 C2 D ∘ ExponentialLaw3Functor_Inverse C1 C2 D = 1
    /\ ExponentialLaw3Functor_Inverse C1 C2 D ∘ ExponentialLaw3Functor C1 C2 D = 1.
  Proof.
    (*split; functor_eq; simpl.
    abstract (
        repeat
          match goal with
            | _ => reflexivity
            | _ => split
            | _ => progress (simpl; intros; trivial)
            | _ => progress repeat subst
            | _ => progress JMeq_eq
            | _ => progress simpl_eq
            | _ => progress apply Functor_eq
            | _ => progress apply NaturalTransformation_JMeq
            | _ => rsimplify_morphisms
          end
      ).*)
  Admitted.
End Law3.
