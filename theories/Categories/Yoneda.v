Require Export Category Functor FunctorCategory Categories.Hom Functor.Attributes.
Require Import Common Category.Product SetCategory ExponentialLaws ProductLaws.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.
Local Open Scope functor_scope.

(*Local Ltac apply_commutes_by_transitivity_and_solve_with tac :=
  repeat (apply functional_extensionality_dep; intro);
    match goal with
      | [ a : _, f : _ |- _ ] => let H := fresh in
        assert (H := fg_equal (Commutes a _ _ f)); simpl in H;
          let fin_tac := (solve [ etransitivity; try apply H; clear H; tac ]) in
            fin_tac || symmetry in H; fin_tac
    end.*)

Section Yoneda.
  Context `{Funext}.
  Variable C : PreCategory.

  Definition CoYoneda : Functor C^op [C, SetCat]
    := ExponentialLaw4Functor_Inverse _ _ _ (HomFunctor C).

  Definition Yoneda : Functor C [C^op, SetCat]
    := ExponentialLaw4Functor_Inverse _ _ _ (HomFunctor C ∘ SwapFunctor _ _).
End Yoneda.

Section YonedaLemma.
  Context `{Funext}.
  Variable C : PreCategory.

  Definition CoYonedaLemmaMorphism (c : C) (X : Object [C, SetCat])
  : Morphism SetCat
             (BuildhSet
                (Morphism [C, SetCat] (CoYoneda _ c) X)
                _)
             (X c).
  Proof.
    simpl; intro a.
    exact (a c (Identity _)).
  Defined.

  Definition CoYonedaLemmaMorphismInverse (c : C) (X : [C, SetCat])
  : Morphism SetCat
             (X c)
             (BuildhSet
                (Morphism [C, SetCat] (CoYoneda C c) X)
                _).
  Proof.
    simpl; intro Xc.
    hnf.
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun c' : C => (fun f : Morphism _ c c' => X.(MorphismOf) f Xc))
          _
        )
    end;
    abstract (
      intros; simpl; apply path_forall; intros; eauto;
        pose (FCompositionOf X);
          simpl in *;
            fg_equal;
            t_with t'
    ).
  Defined.

  Lemma YonedaLemma (c : C) (X : TypeCat ^ C) : IsIsomorphism (@YonedaLemmaMorphism c X).
    exists (@YonedaLemmaMorphismInverse c X).
    unfold YonedaLemmaMorphismInverse, YonedaLemmaMorphism.
    pose (FIdentityOf X).
    pose (FCompositionOf X).
    split; simpl; nt_eq;
    simpl in *; autorewrite with functor; simpl; trivial;
    apply_commutes_by_transitivity_and_solve_with ltac:(rewrite_hyp; autorewrite with morphism; trivial).
  Qed.
End YonedaLemma.

Section CoYonedaLemma.
  Variable C : Category.
  Let COp := OppositeCategory C.

  Definition CoYonedaLemmaMorphism (c : C) (X : TypeCat ^ COp)
  : Morphism TypeCat (Morphism (TypeCat ^ COp) (CoYoneda C c) X) (X c).
    simpl; intro a.
    exact (a c (Identity _)).
  Defined.

  Definition CoYonedaLemmaMorphismInverse (c : C) (X : TypeCat ^ COp)
  : Morphism TypeCat (X c) (Morphism (TypeCat ^ COp) (CoYoneda C c) X).
    simpl; intro Xc.
    hnf.
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun c' : COp => (fun f : COp.(Morphism) c c' => X.(MorphismOf) f Xc))
          _
        )
    end;
    abstract (
      intros; simpl; apply functional_extensionality_dep; intros; eauto;
        pose (FCompositionOf X);
          simpl in *;
            fg_equal;
            t_with t'
    ).
  Defined.

  Lemma CoYonedaLemma (c : C) (X : TypeCat ^ COp) : IsIsomorphism (@CoYonedaLemmaMorphism c X).
    exists (@CoYonedaLemmaMorphismInverse c X).
    split; simpl; nt_eq; clear;
    [ | pose (FIdentityOf X); fg_equal; trivial ];
    pose (FCompositionOf X);
    unfold CoYonedaLemmaMorphism, CoYonedaLemmaMorphismInverse;
    simpl;
    apply_commutes_by_transitivity_and_solve_with ltac:(rewrite_hyp; autorewrite with morphism; trivial).
  Qed.
End CoYonedaLemma.

Section FullyFaithful.
  Variable C : Category.

  Definition YonedaEmbedding : FunctorFullyFaithful (Yoneda C).
    unfold FunctorFullyFaithful.
    intros c c'.
    destruct (YonedaLemma (C := C) c (CovariantHomFunctor C c')) as [ m i ].
    exists (YonedaLemmaMorphism (X := CovariantHomFunctor C c')).
    t_with t'; nt_eq; autorewrite with morphism; trivial.
    apply_commutes_by_transitivity_and_solve_with ltac:(rewrite_hyp; autorewrite with morphism; trivial).
  Qed.

  Definition CoYonedaEmbedding : FunctorFullyFaithful (CoYoneda C).
    unfold FunctorFullyFaithful.
    intros c c'.
    destruct (CoYonedaLemma (C := C) c (ContravariantHomFunctor C c')) as [ m i ].
    exists (CoYonedaLemmaMorphism (X := ContravariantHomFunctor C c')).
    t_with t'; nt_eq; autorewrite with morphism; trivial.
    unfold CoYonedaLemmaMorphism, CoYonedaLemmaMorphismInverse;
      simpl;
      apply_commutes_by_transitivity_and_solve_with ltac:(rewrite_hyp; autorewrite with morphism; trivial).
  Qed.
End FullyFaithful.
