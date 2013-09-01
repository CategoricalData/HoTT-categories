Require Export Category.Duals Functor.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

Section OppositeFunctor.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition OppositeFunctor (F : Functor C D) : Functor C^op D^op
    := Build_Functor (C^op) (D^op)
                     (ObjectOf F)
                     (fun s d => MorphismOf F (s := d) (d := s))
                     (fun d' d s m1 m2 => FCompositionOf F s d d' m2 m1)
                     (FIdentityOf F).

  (** I wish Coq had η conversion for records, so we wouldn't need this
      nonsense. *)
  Definition OppositeFunctor_inv (F : Functor C^op D^op) : Functor C D
    := Build_Functor C D
                     (ObjectOf F)
                     (fun s d => MorphismOf F (s := d) (d := s))
                     (fun d' d s m1 m2 => FCompositionOf F s d d' m2 m1)
                     (FIdentityOf F).
End OppositeFunctor.

Notation "F ^op" := (OppositeFunctor F) : functor_scope.
Notation "F ^op'" := (OppositeFunctor_inv F) : functor_scope.

(* This notation should be [only parsing] for now, because otherwise
   copy/paste doesn't work, because the parser doesn't recognize the
   unicode characters [ᵒᵖ].  So, really, this notation is just a
   reminder to do something when Coq's parser is better. *)

Notation "F ᵒᵖ" := (OppositeFunctor F) (only parsing) : functor_scope.
Notation "F ᵒᵖ'" := (OppositeFunctor_inv F) (only parsing) : functor_scope.

Section OppositeFunctor_Id.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.

  Lemma op_op_functor_id
  : match op_op_id C in (_ = C), op_op_id D in (_ = D) return Functor C D with
      | idpath, idpath => ((F^op)^op)%functor
    end = F.
  Proof.
    destruct F, C, D; reflexivity.
  Defined.
End OppositeFunctor_Id.
