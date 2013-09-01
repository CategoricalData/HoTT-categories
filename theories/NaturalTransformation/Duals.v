Require Export Functor.Duals NaturalTransformation.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

Section OppositeNaturalTransformation.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition OppositeNaturalTransformation
             (F G : Functor C D)
             (T : NaturalTransformation F G)
  : NaturalTransformation G^op F^op
    := Build_NaturalTransformation' (G^op) (F^op)
                                    (ComponentsOf T)
                                    (fun s d => Commutes_sym T d s)
                                    (fun s d => Commutes T d s).

  Definition OppositeNaturalTransformation'
             (F G : Functor C^op D^op)
             (T : NaturalTransformation F G)
  : NaturalTransformation G^op' F^op'
    := Build_NaturalTransformation' (G^op') (F^op')
                                    (ComponentsOf T)
                                    (fun s d => Commutes_sym T d s)
                                    (fun s d => Commutes T d s).

  Definition OppositeNaturalTransformation_Finv
             (F G : Functor C^op D^op)
             (T : NaturalTransformation G^op' F^op')
  : NaturalTransformation F G
    := Build_NaturalTransformation' F G
                                    (ComponentsOf T)
                                    (fun s d => Commutes_sym T d s)
                                    (fun s d => Commutes T d s).

  Definition OppositeNaturalTransformation_Tinv
             (F G : Functor C D)
             (T : NaturalTransformation G^op F^op)
  : NaturalTransformation F G
    := Build_NaturalTransformation' F G
                                    (ComponentsOf T)
                                    (fun s d => Commutes_sym T d s)
                                    (fun s d => Commutes T d s).
End OppositeNaturalTransformation.

Notation "T ^op" := (OppositeNaturalTransformation T) : natural_transformation_scope.
Notation "T ^op'" := (OppositeNaturalTransformation' T) : natural_transformation_scope.
Notation "T ^op''" := (OppositeNaturalTransformation_Finv T) : natural_transformation_scope.
Notation "T ^op'''" := (OppositeNaturalTransformation_Finv T) : natural_transformation_scope.


(* This notation should be [only parsing] for now, because otherwise
   copy/paste doesn't work, because the parser doesn't recognize the
   unicode characters [ᵒᵖ].  So, really, this notation is just a
   reminder to do something when Coq's parser is better. *)

Notation "T ᵒᵖ" := (OppositeNaturalTransformation T) (only parsing) : natural_transformation_scope.
Notation "T ᵒᵖ'" := (OppositeNaturalTransformation' T) (only parsing) : natural_transformation_scope.
Notation "T ᵒᵖ''" := (OppositeNaturalTransformation_Finv T) (only parsing) : natural_transformation_scope.
Notation "T ᵒᵖ'''" := (OppositeNaturalTransformation_Tinv T) (only parsing) : natural_transformation_scope.

Section OppositeNaturalTransformation_Id.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.
  Variable T : NaturalTransformation F G.

  Local Open Scope natural_transformation_scope.

  (** ewww, the transports *)
  Lemma op_op_nt_id
  : match op_op_functor_id F in (_ = F), op_op_functor_id G in (_ = G) return
          NaturalTransformation F G
    with
      | idpath, idpath => match op_op_id C as HC, op_op_id D as HD return
                                (NaturalTransformation
                                   (match HC in (_ = C), HD in (_ = D) return Functor C D with
                                      | idpath, idpath => (F ^op) ^op
                                    end)
                                   (match HC in (_ = C), HD in (_ = D) return Functor C D with
                                      | idpath, idpath => (G ^op) ^op
                                    end))
                          with
                            | idpath, idpath => (T ^op) ^op
                          end
    end = T.
  Proof.
    destruct T, F, G, C, D; reflexivity.
  Defined.
End OppositeNaturalTransformation_Id.
