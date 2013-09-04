Require Export Cat Pseudofunctor.Core.
Require Import Common NaturalTransformation.Isomorphisms.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

(** Every functor to Cat is a pseudofunctor *)
Section of_functor.
  Context `{Funext}.
  Variable C : PreCategory.
  Context `{forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Let Cat := SubPreCat P.

  Variable F : Functor C Cat.

  Definition functor_eq_helper A B (F1 F2 : Functor A B) (pf1 pf2 : F1 = F2)
  : P A -> P B -> pf1 = pf2
    := fun _ _ => allpath_hprop _ _.

  Local Hint Extern 0 (P ?x.1) => exact x.2.

  Local Tactic Notation "transitivity_idtoiso" open_constr(hyp) :=
    lazymatch goal with
      | [ |- ?f (idtoiso ?C _) = _ ] => etransitivity (f (idtoiso C hyp));
                                       [ do 2 apply ap;
                                         apply functor_eq_helper;
                                         unfold SubPreCatCat; simpl; trivial
                                       | nt_eq ]
    end.

  Local Ltac pseudofunctor_t :=
    intros;
    unfold NaturalIsomorphismNT;
    rewrite ?idtoiso_NTWhiskerR, ?idtoiso_NTWhiskerL;
    repeat (
        let C := match goal with |- @paths (@NaturalTransformation ?C ?D ?F ?G) _ _ => constr:([C, D]%category) end in
        first [ eapply (@iso_moveL_pV C)
              | eapply (@iso_moveL_Vp C)
              | eapply (@iso_moveL_pM C)
              | eapply (@iso_moveL_Mp C) ];
        simpl
      );
    rewrite ?idtoiso_inv;
    simpl;
    change @NTComposeT with (fun C D F G H => @Compose [C, D] F G H);
    cbv beta;
    rewrite ?idtoiso_comp;
    first [ transitivity_idtoiso (LeftIdentityFunctor _)
          | transitivity_idtoiso (inverse (LeftIdentityFunctor _))
          | transitivity_idtoiso (RightIdentityFunctor _)
          | transitivity_idtoiso (inverse (RightIdentityFunctor _))
          | transitivity_idtoiso (ComposeFunctorsAssociativity _ _ _)
          | transitivity_idtoiso (inverse (ComposeFunctorsAssociativity _ _ _)) ];
    rewrite eta_idtoiso_FunctorCategory;
    simpl;
    rewrite ?ap_V, ?LeftIdentityFunctor_fst, ?RightIdentityFunctor_fst, ?ComposeFunctorsAssociativity_fst;
    try reflexivity.

  Definition PseudofunctorOfFunctor : Pseudofunctor C.
  Proof.
    refine (Build_Pseudofunctor
              C
              (fun x => projT1 (F x))
              (fun s d m => MorphismOf F m)
              (fun s d d' m0 m1 => idtoiso [_, _] (FCompositionOf F _ _ _ m1 m0))
              (fun x => idtoiso [_, _] (FIdentityOf F x))
              _
              _
              _);
    [ abstract (symmetry; pseudofunctor_t)
    | abstract pseudofunctor_t
    | abstract pseudofunctor_t ].
  Defined.
End of_functor.

Definition FunctorToCat `{Funext} {C} `{forall C D, P C -> P D -> IsHSet (Functor C D)}
  := Functor C (SubPreCat P).
Identity Coercion FunctorToCat_id : FunctorToCat >-> Functor.
Definition PseudofunctorOfFunctorToCat `(F : @FunctorToCat H C P HP)
  := @PseudofunctorOfFunctor _ C P HP F.

Coercion PseudofunctorOfFunctorToCat : FunctorToCat >-> Pseudofunctor.
