Require Export Category Functor.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section SumPreCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition SumPreCategory_Morphism (s d : C + D) : Type
    := match (s, d) with
         | (inl s, inl d) => C.(Morphism) s d
         | (inr s, inr d) => D.(Morphism) s d
         | _ => Empty
       end.

  Global Arguments SumPreCategory_Morphism _ _ / .

  Definition SumPreCategory_Identity (x : C + D) : SumPreCategory_Morphism x x
    := match x with
         | inl x => Identity x
         | inr x => Identity x
       end.

  Global Arguments SumPreCategory_Identity _ / .

  Definition SumPreCategory_Compose (s d d' : C + D) (m1 : SumPreCategory_Morphism d d') (m2 : SumPreCategory_Morphism s d)
  : SumPreCategory_Morphism s d'.
    (* XXX NOTE: try to use typeclasses and work up to existance of morphisms here *)
    case s, d, d'; simpl in *; try destruct_to_empty_set;
    eapply Compose; eassumption.
  Defined.

  Global Arguments SumPreCategory_Compose [_ _ _] _ _ / .

  Definition SumPreCategory : PreCategory.
    refine (@Build_PreCategory
              (C + D)%type
              SumPreCategory_Morphism
              SumPreCategory_Identity
              SumPreCategory_Compose
              _
              _
              _
              _);
    abstract (
        repeat match goal with
                 | [ H : Empty |- _ ] => case H
                 | _ => let H := fresh in intro H; try (case H; clear H); simpl in *
               end;
        eauto with morphism;
        typeclasses eauto
      ).
  Defined.
End SumPreCategory.

Infix "+" := SumPreCategory : category_scope.

Section SumPreCategoryFunctors.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition inl_Functor : Functor C (C + D)
    := Build_Functor C (C + D)
                     (@inl _ _)
                     (fun _ _ m => m)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition inr_Functor : Functor D (C + D)
    := Build_Functor D (C + D)
                     (@inr _ _)
                     (fun _ _ m => m)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End SumPreCategoryFunctors.
