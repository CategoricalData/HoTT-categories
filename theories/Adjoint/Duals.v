Require Export Category.Duals Functor.Duals NaturalTransformation.Duals Adjoint.UnitCounit.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

Section OppositeAdjunction.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition OppositeAdjunction
             (F : Functor C D)
             (G : Functor D C)
             (A : F ⊣ G)
  : G^op ⊣ F^op
    := @Build_AdjunctionUnitCounit
         _ _ (G^op) (F^op)
         ((Adjunction_Counit A)^op)
         ((Adjunction_Unit A)^op)
         (Adjunction_UnitCounitEquation2 A)
         (Adjunction_UnitCounitEquation1 A).

  Definition OppositeAdjunction_inv
             (F : Functor C D)
             (G : Functor D C)
             (A : F^op ⊣ G^op)
  : G ⊣ F
    := @Build_AdjunctionUnitCounit
         _ _ G F
         (@OppositeNaturalTransformation_Tinv _ _ 1 (F ∘ G) (Adjunction_Counit A))
         (@OppositeNaturalTransformation_Tinv _ _ (G ∘ F) 1 (Adjunction_Unit A))
         (Adjunction_UnitCounitEquation2 A)
         (Adjunction_UnitCounitEquation1 A).

  Definition OppositeAdjunction'R
             (F : Functor C^op D^op)
             (G : Functor D C)
             (A : F ⊣ G^op)
  : G ⊣ F^op'
    := @Build_AdjunctionUnitCounit
         _ _ G (F^op')
         ((Adjunction_Counit A)^op')
         ((Adjunction_Unit A)^op')
         (Adjunction_UnitCounitEquation2 A)
         (Adjunction_UnitCounitEquation1 A).

  Definition OppositeAdjunction'L
             (F : Functor C D)
             (G : Functor D^op C^op)
             (A : F^op ⊣ G)
  : G^op' ⊣ F
    := @Build_AdjunctionUnitCounit
         _ _ (G^op') F
         ((Adjunction_Counit A)^op')
         ((Adjunction_Unit A)^op')
         (Adjunction_UnitCounitEquation2 A)
         (Adjunction_UnitCounitEquation1 A).
End OppositeAdjunction.

Notation "A ^op" := (OppositeAdjunction A) : adjunction_scope.
Notation "A ^op'" := (OppositeAdjunction_inv A) : adjunction_scope.
Notation "A ^op'L" := (OppositeAdjunction'L A) : adjunction_scope.
Notation "A ^op'R" := (OppositeAdjunction'R A) : adjunction_scope.

(* This notation should be [only parsing] for now, because otherwise
   copy/paste doesn't work, because the parser doesn't recognize the
   unicode characters [ᵒᵖ].  So, really, this notation is just a
   reminder to do something when Coq's parser is better. *)

Notation "A ᵒᵖ" := (OppositeAdjunction A) (only parsing) : adjunction_scope.
Notation "A ᵒᵖ'" := (OppositeAdjunction_inv A) (only parsing) : adjunction_scope.
Notation "A ᵒᵖ'ᴸ" := (OppositeAdjunction'L A) (only parsing) : adjunction_scope.
Notation "A ᵒᵖ'ᴿ" := (OppositeAdjunction'R A) (only parsing) : adjunction_scope.

Section OppositeAdjunction_Id.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.
  Variable A : F ⊣ G.

  Lemma op_op_functor_id
  : match
      op_op_functor_id F as Fop in (_ = F), op_op_functor_id G as Gop in (_ = G)
      return
      F ⊣ G
    with
      | idpath, idpath
        => match
          op_op_id C as Cop in (_ = C), op_op_id D as Dop in (_ = D)
          return
          (match Cop in (_ = C), Dop in (_ = D) return Functor C D with
             | idpath, idpath => (F^op)^op
           end
             ⊣
             match Dop in (_ = D), Cop in (_ = C) return Functor D C with
               | idpath, idpath => (G^op)^op
             end)
        with
          | idpath, idpath
            => ((A^op)^op)%adjunction
        end
    end = A.
  Proof.
    destruct A as [[] [] ? ?], F, G, C, D.
    (** WTF? [reflexivity] fails here *)
    Fail reflexivity.
    exact idpath.
  Defined.
End OppositeAdjunction_Id.
