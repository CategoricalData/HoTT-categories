Require Export Category Functor NaturalTransformation Adjoint.UnitCounitCoercions.
Require Import Common FunctorCategory Category.Morphisms Category.Duals Category.Product Categories.Hom Functor.Product Functor.Duals NaturalTransformation.Isomorphisms.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope equiv_scope.
Local Open Scope functor_scope.

Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.

Section Adjunction.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

  (**
     Quoting the 18.705 Lecture Notes:

     Let [C] and [D] be categories, [F : C -> D] and [G : D -> C]
     functors. We call [(F, G)] an adjoint pair, [F] the left adjoint
     of [G], and [G] the right adjoint of [F] if, for each object [A :
     C] and object [A' : D], there is a natural bijection

     [Hom_D (F A) A' ≅ Hom_C A (G A')]

     Here natural means that maps [B -> A] and [A' -> B'] induce a
     commutative diagram:

<<
       Hom_D (F A) A' ≅ Hom_C A (G A')
             |                 |
             |                 |
             |                 |
             |                 |
             V                 V
       Hom_D (F B) B' ≅ Hom_C B (G B')
>>
     *)

  (** We want to [simpl] out the notation machinery *)
  Local Opaque NaturalIsomorphism.
  Let Adjunction_Type := Eval simpl in HomFunctor D ⟨ F ⟨ 1 ⟩ , 1 ⟩ ≅ HomFunctor C ⟨ 1 , G ⟨ 1 ⟩ ⟩.
  (*Set Printing All.
  Print Adjunction_Type.*)
  (** Just putting in [Adjunction_Type] breaks [AMateOf] *)

  Record AdjunctionHom :=
    {
      AMateOf : @NaturalIsomorphism H
                                    (ProductCategory (OppositeCategory C) D)
                                    (@SetCat H)
                                    (@ComposeFunctors
                                       (ProductCategory (OppositeCategory C) D)
                                       (ProductCategory (OppositeCategory D) D)
                                       (@SetCat H) (@HomFunctor H D)
                                       (@FunctorProduct' (OppositeCategory C)
                                                         (OppositeCategory D) D D
                                                         (@OppositeFunctor C D F)
                                                         (IdentityFunctor D)))
                                    (@ComposeFunctors
                                       (ProductCategory (OppositeCategory C) D)
                                       (ProductCategory (OppositeCategory C) C)
                                       (@SetCat H) (@HomFunctor H C)
                                       (@FunctorProduct' (OppositeCategory C)
                                                         (OppositeCategory C) D C
                                                         (IdentityFunctor (OppositeCategory C)) G))
    }.
End Adjunction.

Coercion AMateOf : AdjunctionHom >-> NaturalIsomorphism.
Bind Scope adjunction_scope with AdjunctionHom.

Arguments AMateOf {_} [C%category D%category F%functor G%functor] _%adjunction.

Section AdjunctionEquivalences.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Local Arguments compose / .
  Local Arguments HomFunctor_MorphismOf / .

  Local Open Scope morphism_scope.

  (** We need to jump through some hoops with [simpl] for speed *)
  Section adjunction_naturality.
    Variable A : AdjunctionHom F G.

    Let adjunction_naturalityT c d d'
        (f : Morphism D (F c) d)
        (g : Morphism D d d')
      := Eval simpl in
          G ₁ g ∘ A (c, d) f
          = A (c, d') (g ∘ f).

    Lemma adjunction_naturality c d d' f g : @adjunction_naturalityT c d d' f g.
    Proof.
      subst adjunction_naturalityT.
      pose (Commutes (AMateOf A) (c, d) (c, d') (Identity c, g)) as H''.
      simpl in *.
      pose (apD10 H'' f) as H'.
      simpl in *.
      clearbody H'; clear H''.
      rewrite ?FIdentityOf, ?LeftIdentity, ?RightIdentity in H'.
      symmetry; assumption.
    Qed.

    Let adjunction_naturality'T c' c d
        (f : C.(Morphism) c (G d))
        (h : C.(Morphism) c' c)
      := Eval simpl in
          ((A (c, d))^-1 f) ∘ F ₁ h
          = (A (c', d))^-1 (f ∘ h).

    Lemma adjunction_naturality' c' c d f h : @adjunction_naturality'T c' c d f h.
    Proof.
      subst adjunction_naturality'T.
      pose (Commutes (AMateOf A)^-1 (c, d) (c', d) (h, Identity d)) as H''.
      simpl in *.
      pose (apD10 H'' f) as H'.
      simpl in *.
      clearbody H'; clear H''.
      rewrite ?FIdentityOf, ?LeftIdentity, ?RightIdentity in H'.
      symmetry; assumption.
    Qed.
  End adjunction_naturality.

  (**
     Quoting from Awody's "Category Theory":

     Proposition 9.4. Given categories and functors,

     [F : C <-> D : G]

     the following conditions are equivalent:

     1. [F] is left adjoint to [G]; that is, there is a natural
        transformation

        [η : 1_C -> G ∘ F]

        that has the UMP of the unit:

        For any [c : C], [d : D] and [f : c -> G d] there exists a
        unique [g : F c -> d] such that [f = G g ∘ η c].

     2. For any [c : C] and [d : D] there is an isomorphism,

        [ϕ : Hom_D (F c, d) ≅ Hom_C (c, G d)]

        that is natural in both [c] and [d].

     Moreover, the two conditions are related by the formulas

     [ϕ g = G g ∘ η c]

     [η c = ϕ(1_{F c})]
     *)

  (** We play tricks with ordering and tactics for speed *)
  Local Ltac unit_counit_of_t_with_tac tac :=
    repeat match goal with
             | _ => split
             | _ => intro
             | _ => reflexivity
             | _ => progress tac
             | _ => progress simpl in *
             | _ => rewrite adjunction_naturality
             | _ => rewrite adjunction_naturality'
             | _ => progress rewrite ?FIdentityOf, ?LeftIdentity, ?RightIdentity in *
             | [ |- appcontext[@ComponentsOf ?C ?D ?F ?G ?A ?x] ]
               => exact (apD10 (apD10 (ap ComponentsOf (@iso_compose_pV [C, D] F G A _)) x) _)
             | [ |- appcontext[@ComponentsOf ?C ?D ?F ?G ?A ?x] ]
               => exact (apD10 (apD10 (ap ComponentsOf (@iso_compose_Vp [C, D] F G A _)) x) _)
           end.


  Definition AdjunctionUnitOfAdjunctionHom (A : AdjunctionHom F G)
  : AdjunctionUnit F G.
  Proof.
    eexists (Build_NaturalTransformation
               (IdentityFunctor C) (G ∘ F)
               (fun c => A (c, F c) (Identity _))
               _).
    simpl in *.
    intros c d f.
    exists ((A (c, d))^-1 f); simpl in *.
    abstract unit_counit_of_t_with_tac ltac:(progress path_induction).
    Grab Existential Variables.
    abstract (
        intros s d m;
        pose (ap10 (Commutes A (d, F d) (s, F d) (m, Identity _)) (Identity _));
        unit_counit_of_t_with_tac ltac:(eassumption || (symmetry; eassumption))
      ).
  Defined.
End AdjunctionEquivalences.

Section AdjunctionEquivalences'.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Local Arguments compose / .
  Local Arguments HomFunctor_MorphismOf / .
  Local Open Scope morphism_scope.

  Local Ltac unit_counit_single_t' :=
    idtac;
    match goal with
      | _ => done
      | [ |- ?x.1 = _ ] => apply (snd x.2)
      | [ |- appcontext[?x.1] ] => rewrite (fst x.2)
      | _ => simpl; rewrite <- ?FCompositionOf; try_associativity_quick ltac:(f_ap)
    end.

  Local Ltac unit_counit_t_with tac :=
    simpl;
    repeat match goal with
             | _ => intro
             | _ => progress auto with morphism
             | _ => apply path_forall; intro
             | _ => rewrite !FCompositionOf
             | _ => progress tac
             | _ => progress repeat try_associativity_quick ltac:(f_ap)
             | [ |- appcontext[ComponentsOf ?T] ] => exact (Commutes T _ _ _)
             | [ |- appcontext[ComponentsOf ?T] ] => symmetry; exact (Commutes T _ _ _)
             | [ |- appcontext[ComponentsOf ?T] ]
               => simpl_do_clear try_associativity_quick_rewrite (Commutes T);
                 progress tac
             | [ |- appcontext[ComponentsOf ?T] ]
               => simpl_do_clear try_associativity_quick_rewrite_rev (Commutes T);
                 progress tac
             | _ => progress simpl
           end.

  Local Ltac unit_counit_t_single := unit_counit_t_with unit_counit_single_t'.

  Definition AdjunctionHomOfAdjunctionUnit
             (T : AdjunctionUnit F G)
  : AdjunctionHom F G.
  Proof.
    constructor.
    let F0 := match goal with |- ?R ?F ?G => constr:(F) end in
    let G0 := match goal with |- ?R ?F ?G => constr:(G) end in
    (eexists (Build_NaturalTransformation
                F0 G0
                (fun cd (g : Morphism _ (F (fst cd)) (snd cd)) => MorphismOf G g ∘ projT1 T (fst cd))
                _));
      apply iso_NaturalTransformation1;
      simpl;
      intros cd;
      exists (fun f => projT1 (projT2 T _ _ f));
      abstract unit_counit_t_single.
    Grab Existential Variables.
    abstract unit_counit_t_single.
  Defined.
End AdjunctionEquivalences'.

Coercion AdjunctionUnitOfAdjunctionHom : AdjunctionHom >-> AdjunctionUnit.

Definition AdjunctionUnitWithFunext `{Funext} C D F G := @AdjunctionUnit C D F G.
Definition AdjunctionCounitWithFunext `{Funext} C D F G := @AdjunctionCounit C D F G.
Definition AdjunctionUnitCounitWithFunext `{Funext} C D F G := @AdjunctionUnitCounit C D F G.
Identity Coercion AdjunctionUnit_Funext : AdjunctionUnitWithFunext >-> AdjunctionUnit.
Identity Coercion AdjunctionCounit_Funext : AdjunctionCounitWithFunext >-> AdjunctionCounit.
Identity Coercion AdjunctionUnitCounit_Funext : AdjunctionUnitCounitWithFunext >-> AdjunctionUnitCounit.

Definition AdjunctionHomOfAdjunctionUnit_Funext `{Funext} C D F G
           (A : AdjunctionUnitWithFunext _ _)
: AdjunctionHom _ _
  := @AdjunctionHomOfAdjunctionUnit _ C D F G A.
Definition AdjunctionHomOfAdjunctionCounit_Funext `{Funext} C D F G
           (A : AdjunctionCounitWithFunext _ _)
: AdjunctionHom _ _
  := @AdjunctionHomOfAdjunctionUnit _ C D F G A.
Definition AdjunctionHomOfAdjunctionUnitCounit_Funext `{Funext} C D F G
           (A : AdjunctionUnitCounitWithFunext _ _)
: AdjunctionHom _ _
  := @AdjunctionHomOfAdjunctionUnit _ C D F G A.

Coercion AdjunctionHomOfAdjunctionUnit_Funext
: AdjunctionUnitWithFunext >-> AdjunctionHom.
Coercion AdjunctionHomOfAdjunctionCounit_Funext
: AdjunctionCounitWithFunext >-> AdjunctionHom.
Coercion AdjunctionHomOfAdjunctionUnitCounit_Funext
: AdjunctionUnitCounitWithFunext >-> AdjunctionHom.
