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
  Context `{HP : forall C D, P C -> P D -> IsHSet (Functor C D)}.

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

  (* The following helpers were generated with
<<
intros.
    repeat match goal with
             | [ |- appcontext[idtoiso ?C (?f ?x)] ] => generalize (f x); intro
             | [ |- appcontext[MorphismOf ?F ?f] ] => generalize dependent (MorphismOf F f); repeat (let x := fresh "x" in intro x)
             | [ |- appcontext[ObjectOf ?F ?f] ] => generalize dependent (ObjectOf F f); repeat (let x := fresh "x" in intro x)
           end.
    simpl in *.
    unfold SubPreCatCat.
    simpl in *.
    clear.
    destruct_head_hnf @sigT.
    simpl in *.
    repeat match goal with
             | [ H : _ |- _ ] => revert H
           end.
    intros H P.
>> *)

  Lemma PseudofunctorOfFunctor_FCompositionOf
        {x0 x1 x2 x : PreCategory}
        {x7 x11 : Functor x0 x1}
        {x12 : x7 = x11}
        {x6 : Functor x0 x2} {x9 : Functor x2 x1}
        {x14 : x11 = (x9 ∘ x6)%functor}
        {x4 : Functor x0 x} {x5 : Functor x x1}
        {x8 : x7 = (x5 ∘ x4)%functor} {x10 : Functor x x2}
        {x13 : x6 = (x10 ∘ x4)%functor} {x15 : x5 = (x9 ∘ x10)%functor}
        (H0' : P x0) (H1' : P x1) (H2' : P x2) (H' : P x)
  : (ComposeFunctorsAssociator1 x9 x10 x4 ∘ (idtoiso [x, x1] x15 ∘ x4 ∘ idtoiso [x0, x1] x8))%natural_transformation =
    (x9 ∘ idtoiso [x0, x2] x13 ∘ (idtoiso [x0, x1] x14 ∘ idtoiso [x0, x1] x12))%natural_transformation.
  Proof.
    subst_body.
    clear HP F.
    abstract (apply symmetry; simpl; pseudofunctor_t).
  Qed.

  Lemma PseudofunctorOfFunctor_LeftIdentityOf
        {x0 x : PreCategory}
        {x2 : Functor x x} {x3 : x2 = 1%functor}
        {x4 x5 : Functor x0 x} {x6 : x4 = x5} {x7 : x4 = (x2 ∘ x5)%functor}
        (H0' : P x0) (H' : P x)
  : (idtoiso [x, x] x3 ∘ x5 ∘ idtoiso [x0, x] x7)%natural_transformation =
    (LeftIdentityFunctorNaturalTransformation2 x5 ∘ idtoiso [x0, x] x6)%natural_transformation.
  Proof.
    subst_body.
    clear HP F.
    abstract (simpl; pseudofunctor_t).
  Qed.

  Lemma PseudofunctorOfFunctor_RightIdentityOf
        {x0 x : PreCategory}
        {x4 : Functor x0 x0} {x5 : x4 = 1%functor}
        {x2 x3 : Functor x0 x} {x6 : x2 = x3} {x7 : x2 = (x3 ∘ x4)%functor}
        (H0' : P x0) (H' : P x)
  : (x3 ∘ idtoiso [x0, x0] x5 ∘ idtoiso [x0, x] x7)%natural_transformation =
    (RightIdentityFunctorNaturalTransformation2 x3 ∘ idtoiso [x0, x] x6)%natural_transformation.
  Proof.
    subst_body.
    clear HP F.
    abstract (simpl; pseudofunctor_t).
  Qed.

  Definition PseudofunctorOfFunctor : Pseudofunctor C
    := Build_Pseudofunctor
         C
         (fun x => projT1 (F x))
         (fun s d m => MorphismOf F m)
         (fun s d d' m0 m1 => idtoiso [_, _] (FCompositionOf F _ _ _ m1 m0))
         (fun x => idtoiso [_, _] (FIdentityOf F x))
         (fun w x y z _ _ _ => PseudofunctorOfFunctor_FCompositionOf (F w).2 (F z).2 (F y).2 (F x).2)
         (fun x y _ => PseudofunctorOfFunctor_LeftIdentityOf (F x).2 (F y).2)
         (fun x y _ => PseudofunctorOfFunctor_RightIdentityOf (F x).2 (F y).2).
End of_functor.

Definition FunctorToCat `{Funext} {C} `{forall C D, P C -> P D -> IsHSet (Functor C D)}
  := Functor C (SubPreCat P).
Identity Coercion FunctorToCat_id : FunctorToCat >-> Functor.
Definition PseudofunctorOfFunctorToCat `(F : @FunctorToCat H C P HP)
  := @PseudofunctorOfFunctor _ C P HP F.

Coercion PseudofunctorOfFunctorToCat : FunctorToCat >-> Pseudofunctor.
