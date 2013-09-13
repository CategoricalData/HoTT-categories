Require Export Functor.Core.
Require Import Common Hom Category.Morphisms Category.Duals Functor.Duals Functor.Product NaturalTransformation SetCategory.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

Section FullFaithful.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable C' : PreCategory.
  Variable D : PreCategory.
  Variable D' : PreCategory.
  Variable F : Functor C D.
  Variable F' : Functor C' D'.

  Definition InducedHomNaturalTransformation
  : NaturalTransformation (HomFunctor C) (HomFunctor D ⟨ F^op ⟨ ─ ⟩ , F ⟨ ─ ⟩ ⟩).
  Proof.
    refine (Build_NaturalTransformation
              (HomFunctor C)
              (HomFunctor D ⟨ F^op ⟨ ─ ⟩ , F ⟨ ─ ⟩ ⟩)
              (fun sd : (C^op * C) =>
                 MorphismOf F (s := _) (d := _))
              _
           ).
    abstract (
        repeat (intros [] || intro);
        simpl in *;
          repeat (apply path_forall; intro);
        unfold compose, HomFunctor_MorphismOf;
        simpl;
        rewrite !FCompositionOf;
        reflexivity
      ).
  Defined.

  (** We really want surjective/injective here, but we only have epi/mono.
      They're equivalent in the category of sets.  Are they equivalent in the
      category of [Type]s? *)
  Definition FunctorFull
    := forall x y : C, IsEpimorphism (InducedHomNaturalTransformation (x, y)).
  Definition FunctorFaithful
    := forall x y : C, IsMonomorphism (InducedHomNaturalTransformation (x, y)).

  Definition FunctorFullyFaithful
    := forall x y : C, IsIsomorphism (InducedHomNaturalTransformation (x, y)).

  Lemma FunctorFullyFaithful_split
  : FunctorFullyFaithful -> FunctorFull /\ FunctorFaithful.
  Proof.
    unfold FunctorFullyFaithful, FunctorFull, FunctorFaithful;
    intro; split; intros;
    typeclasses eauto.
  Qed.

(*
  (* Depends on injective + surjective -> isomorphism, and epi = surj, mono = inj *)
  Definition FunctorFullFaithful_and : FunctorFull /\ FunctorFaithful -> FunctorFullyFaithful.
    intro H; destruct H as [ e m ].
    unfold FunctorFullyFaithful, FunctorFull, FunctorFaithful in *.
    intros x y; specialize (e x y); specialize (m x y).
    unfold IsEpimorphism, IsMonomorphism in *; simpl in *.
    unfold IsIsomorphism; simpl.
    eexists;
      split.
    destruct C, D, F; simpl in *; clear C D F.
    *)
End FullFaithful.
