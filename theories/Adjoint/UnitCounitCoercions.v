Require Export Adjoint.UnitCounit.
Require Import Common.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Section equivalences.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Section from_unit_counit.
    Variable A : AdjunctionUnitCounit F G.

    Local Ltac unit_counit_of_t :=
      repeat match goal with
               | _ => split
               | _ => intro
               | _ => progress auto with morphism
               | _ => progress simpl
               | _ => rewrite !FCompositionOf
               | [ |- appcontext[ComponentsOf ?T] ]
                 => simpl_do_clear try_associativity_quick_rewrite_rev (Commutes T);
                   try_associativity_quick ltac:(progress rewrite ?Adjunction_UnitCounitEquation1, ?Adjunction_UnitCounitEquation2)
               | [ |- appcontext[ComponentsOf ?T] ]
                 => simpl_do_clear try_associativity_quick_rewrite (Commutes T);
                   try_associativity_quick ltac:(progress rewrite ?Adjunction_UnitCounitEquation1, ?Adjunction_UnitCounitEquation2)
               | _ => progress path_induction
             end.

    Definition AdjunctionUnitOfAdjunctionUnitCounit
    : AdjunctionUnit F G.
    Proof.
      exists (Adjunction_Unit A).
      intros c d f.
      exists (Adjunction_Counit A d ∘ F ₁ f).
      abstract unit_counit_of_t.
    Defined.

    Definition AdjunctionCounitOfAdjunctionUnitCounit
    : AdjunctionCounit F G.
    Proof.
      exists (Adjunction_Counit A).
      intros c d g.
      exists (G ₁ g ∘ Adjunction_Unit A c).
      abstract unit_counit_of_t.
    Defined.
  End from_unit_counit.

  Section to_unit_counit.
    Ltac to_unit_counit_nt helper commutes_tac :=
      simpl;
      intros;
      apply helper;
      repeat match goal with
               | _ => reflexivity
               | _ => rewrite !FCompositionOf
               | _ => progress rewrite ?FIdentityOf, ?LeftIdentity, ?RightIdentity
               | [ |- appcontext[?x.1] ]
                 => simpl_do_clear try_associativity_quick_rewrite (fst x.2)
               | [ |- appcontext[ComponentsOf ?T] ]
                 => simpl_do_clear commutes_tac (Commutes T)
             end.

    Lemma CounitNTOfAdjunctionUnit_helper
               (A : AdjunctionUnit F G)
               s d (m : Morphism D s d)
               (η := A.1)
               (ε := fun X => (A.2 (G X) X ─).1)
    : G ₁ (ε d ∘ F ₁ (G ₁ m)) ∘ η (G s) = G ₁ m
      -> G ₁ (m ∘ ε s) ∘ η (G s) = G ₁ m
      -> ε d ∘ F ₁ (G ₁ m) = m ∘ ε s.
    Proof.
      intros.
      transitivity (A.2 _ _ (G ₁ m)).1; [ symmetry | ];
      apply (snd (A.2 _ _ (G ₁ m)).2);
      assumption.
    Qed.

    Definition CounitNTOfAdjunctionUnit
               (A : AdjunctionUnit F G)
    : NaturalTransformation (F ∘ G) ─.
    Proof.
      refine (Build_NaturalTransformation
                (F ∘ G) ─
                (fun d => (A.2 (G d) d (Identity _)).1)
                _).
      abstract (to_unit_counit_nt
                  CounitNTOfAdjunctionUnit_helper
                  try_associativity_quick_rewrite_rev).
    Defined.

    Definition ZigOfAdjunctionUnit
               (A : AdjunctionUnit F G)
               (Y : C)
               (η := A.1)
               (ε := fun X => (A.2 (G X) X ─).1)

    : G ₁ (ε (F Y) ∘ F ₁ (η Y)) ∘ η Y = η Y
      -> ε (F Y) ∘ F ₁ (η Y) = ─.
    Proof.
      intros.
      etransitivity; [ symmetry | ];
      apply (snd (A.2 _ _ (A.1 Y)).2).
      try assumption.
      simpl.
      rewrite ?FIdentityOf, ?LeftIdentity, ?RightIdentity;
        reflexivity.
    Qed.

    Definition AdjunctionUnitCounitOfAdjunctionUnit
               (A : AdjunctionUnit F G)
    : AdjunctionUnitCounit F G.
    Proof.
      exists A.1
             (CounitNTOfAdjunctionUnit A);
      simpl;
      intros;
      try match goal with
            | [ |- appcontext[?x.1] ] => exact (fst x.2)
          end;
      [].
      abstract (to_unit_counit_nt
                  ZigOfAdjunctionUnit
                  try_associativity_quick_rewrite_rev).
    Defined.


    Lemma UnitNTOfAdjunctionCounit_helper
               (A : AdjunctionCounit F G)
               s d (m : Morphism C s d)
               (ε := A.1)
               (η := fun X => (A.2 X (F X) ─).1)
    : ε (F d) ∘ F ₁ (η d ∘ m) = F ₁ m
      -> ε (F d) ∘ F ₁ (G ₁ (F ₁ m) ∘ η s) = F ₁ m
      -> η d ∘ m = G ₁ (F ₁ m) ∘ η s.
    Proof.
      intros.
      transitivity (A.2 _ _ (F ₁ m)).1; [ symmetry | ];
      apply (snd (A.2 _ _ (F ₁ m)).2);
      assumption.
    Qed.

    Definition UnitNTOfAdjunctionCounit
               (A : AdjunctionCounit F G)
    : NaturalTransformation ─ (G ∘ F).
    Proof.
      refine (Build_NaturalTransformation
                ─ (G ∘ F)
                (fun d => (A.2 d (F d) (Identity _)).1)
                _).
      abstract (to_unit_counit_nt
                  UnitNTOfAdjunctionCounit_helper
                  try_associativity_quick_rewrite).
    Defined.

    Definition ZagOfAdjunctionCounit
               (A : AdjunctionCounit F G)
               (X : D)
               (ε := A.1)
               (η := fun X => (A.2 X (F X) ─).1)
    : ε X ∘ F ₁ (G ₁ (ε X) ∘ η (G X)) = ε X
      -> G ₁ (ε X) ∘ η (G X) = ─.
    Proof.
      intros.
      etransitivity; [ symmetry | ];
      apply (snd (A.2 _ _ (A.1 X)).2);
      try assumption.
      simpl.
      rewrite ?FIdentityOf, ?LeftIdentity, ?RightIdentity;
        reflexivity.
    Qed.

    Definition AdjunctionUnitCounitOfAdjunctionCounit
               (A : AdjunctionCounit F G)
    : AdjunctionUnitCounit F G.
    Proof.
      exists (UnitNTOfAdjunctionCounit A)
             A.1;
      simpl;
      intros;
      try match goal with
            | [ |- appcontext[?x.1] ] => exact (fst x.2)
          end;
      [].
      abstract (to_unit_counit_nt
                  ZagOfAdjunctionCounit
                  try_associativity_quick_rewrite).
    Defined.
  End to_unit_counit.
End equivalences.

Coercion AdjunctionUnitOfAdjunctionUnitCounit
: AdjunctionUnitCounit >-> AdjunctionUnit.
Coercion AdjunctionCounitOfAdjunctionUnitCounit
: AdjunctionUnitCounit >-> AdjunctionCounit.

Coercion AdjunctionUnitCounitOfAdjunctionUnit
: AdjunctionUnit >-> AdjunctionUnitCounit.
Coercion AdjunctionUnitCounitOfAdjunctionCounit
: AdjunctionCounit >-> AdjunctionUnitCounit.
