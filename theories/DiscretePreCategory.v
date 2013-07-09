Require Export PreCategory.
Require Import Common StrictCategory.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section DiscretePreCategory.
  Variable X : Type.
  Context `{IsTrunc 1 X}.

  Local Notation DiscreteCategory_Morphism := (@paths X).

  Definition DiscreteCategory_Compose s d d' (m : DiscreteCategory_Morphism d d') (m' : DiscreteCategory_Morphism s d)
  : DiscreteCategory_Morphism s d'
    := transitivity s d d' m' m.

  Definition DiscreteCategory_Identity x : DiscreteCategory_Morphism x x
    := reflexivity _.

  Global Arguments DiscreteCategory_Compose [s d d'] m m' / .
  Global Arguments DiscreteCategory_Identity x / .

  Definition DiscretePreCategory : PreCategory.
    refine (@Build_PreCategory X
                               DiscreteCategory_Morphism
                               DiscreteCategory_Identity
                               DiscreteCategory_Compose
                               _
                               _
                               _
                               _);
    abstract (simpl; intros; path_induction; reflexivity).
  Defined.
End DiscretePreCategory.

Arguments DiscretePreCategory _ {_}.

Instance DiscretePreCategoryIsStrict X `{IsHSet X}
: IsStrictCategory (DiscretePreCategory X).
Proof.
  typeclasses eauto.
Defined.
