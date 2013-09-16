Require Export Category.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section SumCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition SumCategory_Morphism (s d : C + D) : Type
    := match (s, d) with
         | (inl s, inl d) => C.(Morphism) s d
         | (inr s, inr d) => D.(Morphism) s d
         | _ => Empty
       end.

  Global Arguments SumCategory_Morphism _ _ / .

  Definition SumCategory_Identity (x : C + D) : SumCategory_Morphism x x
    := match x with
         | inl x => Identity x
         | inr x => Identity x
       end.

  Global Arguments SumCategory_Identity _ / .

  Definition SumCategory_Compose (s d d' : C + D) (m1 : SumCategory_Morphism d d') (m2 : SumCategory_Morphism s d)
  : SumCategory_Morphism s d'.
  Proof.
    (* XXX NOTE: try to use typeclasses and work up to existance of morphisms here *)
    case s, d, d'; simpl in *; try destruct_to_empty_set;
    eapply Compose; eassumption.
  Defined.

  Global Arguments SumCategory_Compose [_ _ _] _ _ / .

  Definition SumCategory : PreCategory.
  Proof.
    refine (@Build_PreCategory
              (C + D)%type
              SumCategory_Morphism
              SumCategory_Identity
              SumCategory_Compose
              _
              _
              _
              _);
    abstract (
        repeat (intros [] || intro);
        simpl in *;
          auto with morphism;
        typeclasses eauto
      ).
  Defined.
End SumCategory.

Infix "+" := SumCategory : category_scope.
