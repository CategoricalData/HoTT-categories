Require Export Category Functor NaturalTransformation UnitCounit.
Require Import Common FunctorCategory Category.Morphisms Category.Duals Category.Product Hom Functor.Product Functor.Duals NaturalTransformation.Isomorphisms.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope equiv_scope.
Local Open Scope functor_scope.

Local Ltac intro_laws_from_inverse :=
  repeat match goal with
           | [ |- appcontext[Inverse ?m] ]
             => unique_pose (LeftInverse m);
               unique_pose (RightInverse m)
         end.

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

  Record Adjunction :=
    {
      AMateOf :> HomFunctor D ⟨ F^op ⟨ ─ ⟩ , ─ ⟩ ≅ HomFunctor C ⟨ ─ , G ⟨ ─ ⟩ ⟩
    }.

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

  Local Open Scope morphism_scope.

  Record HomAdjunction :=
    {
      AComponentsOf :> forall A A', Morphism SetCat (HomFunctor D (F A, A')) (HomFunctor C (A, G A'));
      AIsomorphism : forall A A', IsIsomorphism (C := SetCat) (@AComponentsOf A A');
      ACommutes : forall A A' B B' (m : C.(Morphism) B A) (m' : D.(Morphism) A' B'),
                    (@AComponentsOf B B')
                      ∘ (MorphismOf (HomFunctor D) (s := (F A, A')) (d := (F B, B')) (F.(MorphismOf) m, m'))
                    = (MorphismOf (HomFunctor C) (s := (A, G A')) (d := (B, G B')) (m, G.(MorphismOf) m'))
                        ∘ (@AComponentsOf A A')
    }.

  Bind Scope adjunction_scope with HomAdjunction.

  Global Existing Instance AIsomorphism.

  Lemma ACommutes_Inverse (T : HomAdjunction)
  : forall A A' B B' (m : C.(Morphism) B A) (m' : D.(Morphism) A' B'),
      (MorphismOf (HomFunctor D) (s := (F A, A')) (d := (F B, B')) (F.(MorphismOf) m, m'))
        ∘ ((T A A')^-1)
      = ((T B B')^-1)
          ∘ (MorphismOf (HomFunctor C) (s := (A, G A')) (d := (B, G B')) (m, G.(MorphismOf) m')).
  Proof.
    intros A A' B B' m m'.
    pose proof (ACommutes T A A' B B' m m').
    repeat try_associativity ltac:(first [ apply iso_moveR_Vp
                                         | apply iso_moveR_pV
                                         | apply iso_moveL_Vp
                                         | apply iso_moveL_pV ]).
    assumption.
  Qed.
End Adjunction.

Bind Scope adjunction_scope with Adjunction.
Bind Scope adjunction_scope with HomAdjunction.

Arguments AMateOf {_} [C%category D%category F%functor G%functor] _%adjunction.

Arguments AComponentsOf {_} {C%category D%category} [F%functor G%functor] T%adjunction A%object A'%object _ : simpl nomatch, rename.
Arguments AIsomorphism {_} {C%category D%category} [F%functor G%functor] T%adjunction A%object A'%object : simpl nomatch, rename.
Arguments ACommutes {_} [C%category D%category F%functor G%functor] _%adjunction _%object _%object _%object _%object _%morphism _%morphism.

Infix "-|" := Adjunction : type_scope.
Infix "⊣" := Adjunction : type_scope.

Section AdjunctionEquivalences.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Local Arguments compose / .
  Local Arguments HomFunctor_MorphismOf / .

  Local Open Scope morphism_scope.

  Definition HomAdjunction2Adjunction_AMateOf (A : HomAdjunction F G)
    := Build_NaturalTransformation
         (HomFunctor D ⟨ F^op ⟨ ─ ⟩ , ─ ⟩)
         (HomFunctor C ⟨ ─ , G ⟨ ─ ⟩ ⟩)
         (fun cd => A (fst cd) (snd cd))
         (fun s d m =>
            ACommutes A (fst s) (snd s) (fst d) (snd d) (fst m) (snd m)).

  Definition HomAdjunction2Adjunction (A : HomAdjunction F G)
  : Adjunction F G
    := @Build_Adjunction
         _ _ _ F G
         (@Build_Isomorphic [_, _] _ _
                            (HomAdjunction2Adjunction_AMateOf A)
                            (@iso_NaturalTransformation1 _ _ _ _ _ _ _)).

  Definition Adjunction2HomAdjunction (A : Adjunction F G)
  : HomAdjunction F G
    := Build_HomAdjunction
         F G
         (fun c d => A (c, d))
         (fun A0 A' => (@iso_NaturalTransformation0 _ _ _ _ _ A _ (A0, A')))
         (fun A0 A' B B' m m' => A.(Commutes) (A0, A') (B, B') (m, m')).

  Definition equiv_Adjunction_HomAdjunction
  : Adjunction F G <~> HomAdjunction F G.
  Proof.
    apply (equiv_adjointify
             Adjunction2HomAdjunction
             HomAdjunction2Adjunction);
    abstract (
        intros []; intros; simpl;
        expand;
        f_ap;
        first [ apply Isomorphic_eq;
                nt_eq;
                destruct_head prod;
                reflexivity
              | exact (center _) ]
      ).
  Defined.

  Lemma adjunction_naturality (A : HomAdjunction F G) c d d' (f : D.(Morphism) (F c) d) (g : D.(Morphism) d d')
  : G.(MorphismOf) g ∘ A.(AComponentsOf) _ _ f
    = A.(AComponentsOf) _ _ (g ∘ f).
  Proof.
    assert (H' := fg_equal (A.(ACommutes) _ _ _ _ (Identity c) g) f).
    simpl in *; autorewrite with category in *.
    symmetry.
    assumption.
  Qed.

  Lemma adjunction_naturality' (A : HomAdjunction F G) c' c d (f : C.(Morphism) c (G d)) (h : C.(Morphism) c' c)
  : ((A _ _)^-1 f) ∘ F.(MorphismOf) h
    = (A _ _)^-1 (f ∘ h).
  Proof.
    assert (H' := fg_equal (ACommutes_Inverse A _ _ _ _ h (Identity d)) f).
    simpl in *; autorewrite with category in *.
    assumption.
  Qed.

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

  Local Ltac unit_counit_of_t :=
    repeat match goal with
             | _ => split
             | _ => intro
             | _ => eassumption
             | _ => symmetry; eassumption
             | _ => reflexivity
             | _ => progress rewrite ?iso_compose_pV, ?iso_compose_Vp
             | _ => progress simpl in *
             | _ => progress simpl_do_clear ltac:(fun H => rewrite H) adjunction_naturality
             | _ => progress simpl_do_clear ltac:(fun H => rewrite H) adjunction_naturality'
             | _ => progress autorewrite with category in *
             | _ => progress path_induction
             | [ |- ?f (?g ?x) = ?x ] => change ((f ∘ g) x = (fun x => x) x); f_ap
           end.

  Definition UnitOf (A : HomAdjunction F G) : AdjunctionUnit F G.
  Proof.
    eexists (Build_NaturalTransformation
               (IdentityFunctor C) (G ∘ F)
               (fun c => A.(AComponentsOf) c (F c) (Identity _))
               _).
    simpl in *.
    intros c d f.
    exists ((A c d)^-1 f).
    abstract unit_counit_of_t.
    Grab Existential Variables.
    abstract (
        intros s d m;
        let H := fresh in
        assert (H := fg_equal (A.(ACommutes) d (F d) s (F d) m (Identity _)) (Identity _));
        unit_counit_of_t
      ).
  Defined.


  Definition CounitOf (A : HomAdjunction F G) : AdjunctionCounit F G.
  Proof.
    eexists (Build_NaturalTransformation
               (F ∘ G) (IdentityFunctor D)
               (fun d => (A (G d) d)^-1 (Identity _))
               _).
    simpl.
    intros c d f.
    exists (A c d f).
    abstract unit_counit_of_t.
    Grab Existential Variables.
    abstract (
        intros s d m;
        let H := fresh in assert (H := fg_equal (ACommutes_Inverse A (G s) s (G s) d (Identity (G s)) m) (Identity _));
        unit_counit_of_t
    ).
  Defined.

  (** Quoting Wikipedia on Adjoint Functors:

      The naturality of [Φ] implies the naturality of [ε] and [η], and
      the two formulas

      [Φ_{Y,X}(f) = G(f) ∘ η_Y]

      [Φ_{Y,X}⁻¹(g) = ε_X ∘ F(g)]

      for each [f: F Y → X] and [g : Y → G X] (which completely
      determine [Φ]). *)

  Lemma UnitCounitOf_Helper1
        (Φ : HomAdjunction F G)
        (ε := projT1 (CounitOf Φ))
        (η := projT1 (UnitOf Φ))
  : forall X Y (f : Morphism _ (F Y) X), Φ Y X f = G.(MorphismOf) f ∘ η Y.
  Proof.
    intros.
    destruct Φ as [ ? ? ACommutes'0 ]; simpl in *.
    subst_body.
    pose proof (fg_equal (ACommutes'0 _ _ _ _ (Identity _) f) (Identity _)) as H'.
    simpl in *.
    autorewrite with functor morphism in H'.
    assumption.
  Qed.

  Lemma UnitCounitOf_Helper2
        (Φ : HomAdjunction F G)
        (ε := projT1 (CounitOf Φ))
        (η := projT1 (UnitOf Φ))
        (Φ_Inverse := fun Y X g => (Φ Y X)^-1 g)
  : forall X Y (g : Morphism _ Y (G X)), Φ_Inverse Y X g = ε X ∘ F.(MorphismOf) g.
  Proof.
    pose proof (ACommutes_Inverse Φ) as ACommutes_Inverse'.
    destruct Φ as [ ? ? ACommutes'0 ]; simpl in *.
    subst_body.
    simpl in *.
    intros X Y g.
    pose proof (fg_equal (ACommutes_Inverse' _ _ _ _ g (Identity _)) (Identity _)) as H'.
    simpl in *.
    autorewrite with functor morphism in H'.
    symmetry.
    assumption.
  Qed.

  Local Ltac UnitCounitOf_helper make_H :=
    let H := fresh in
    let X := fresh in
    intro X;
      let HT := constr:(make_H X) in
      pose proof HT as H; simpl in H;
      etransitivity; [ symmetry; apply H | ];
      unit_counit_of_t.

  Definition UnitCounitOf (A : HomAdjunction F G) : AdjunctionUnitCounit F G.
  Proof.
    exists (projT1 (UnitOf A))
           (projT1 (CounitOf A));
    [ abstract UnitCounitOf_helper (fun Y => UnitCounitOf_Helper2 A (F Y) Y (projT1 (UnitOf A)(*η*) Y))
    | abstract UnitCounitOf_helper (fun X => UnitCounitOf_Helper1 A X (G X) (projT1 (CounitOf A)(*ε*) X)) ].
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

  Local Ltac unit_counit_both_t' :=
    idtac;
    first [ progress simpl in *
          | simpl_do_clear ltac:(fun H => try_associativity ltac:(rewrite H)) Adjunction_UnitCounitEquation1
          | simpl_do_clear ltac:(fun H => try_associativity ltac:(rewrite H)) Adjunction_UnitCounitEquation2 ].

  Local Ltac unit_counit_single_t' :=
    idtac;
    match goal with
      | [ |- ?x.1 = _ ] => apply (snd x.2)
      | [ |- appcontext[?x.1] ] => rewrite (fst x.2)
      | [ |- appcontext[MorphismOf ?G (MorphismOf ?F ?m)] ]
        => change (MorphismOf G (MorphismOf F m)) with (MorphismOf (G ∘ F) m)
      | _ => simpl; rewrite <- ?FCompositionOf; f_ap
    end.

  Local Ltac unit_counit_t'_with' t :=
    first [ done
          | intro
          | split
          | apply path_forall
          | rewrite !FCompositionOf
          | progress repeat try_associativity ltac:(f_ap)
          | progress auto with morphism
          | t ].

  Local Ltac unit_counit_t'_with t :=
    simpl;
    repeat first [ unit_counit_t'_with' t
                 | eapply symmetry; progress unit_counit_t'_with' t ].

  Local Ltac unit_counit_t_with t :=
    let progress_tac := (fun tac lem
                         => simpl_do_clear ltac:(fun H => try_associativity ltac:(tac H)) lem;
                         ((try_associativity ltac:(f_ap))
                            || solve [ unit_counit_t'_with t ])) in
    repeat match goal with
             | _ => progress unit_counit_t'_with t
             | [ |- appcontext[ComponentsOf ?T] ] => progress_tac do_rewrite (Commutes T)
             | [ |- appcontext[ComponentsOf ?T] ] => progress_tac do_rewrite_rev (Commutes T)
           end.

  Local Ltac unit_counit_t_both := unit_counit_t_with unit_counit_both_t'.
  Local Ltac unit_counit_t_single := unit_counit_t_with unit_counit_single_t'.

  Definition HomAdjunctionOfUnitCounit  (T : AdjunctionUnitCounit F G)
  : HomAdjunction F G.
  Proof.
    exists (fun c d (g : Morphism _ (F c) d) => MorphismOf G g ∘ Adjunction_Unit T c);
    [ intros; exists (fun f => Adjunction_Counit T A' ∘ F.(MorphismOf) f) | ];
    abstract unit_counit_t_both.
  Defined.

  Definition HomAdjunctionOfUnit (T : AdjunctionUnit F G) : HomAdjunction F G.
  Proof.
    exists (fun c d (g : Morphism _ (F c) d) => G.(MorphismOf) g ∘ projT1 T c);
    [ intros; exists (fun f => projT1 (projT2 T _ _ f)) | ];
    abstract unit_counit_t_single.
  Defined.

  Definition HomAdjunctionOfCounit (T : AdjunctionCounit F G) : HomAdjunction F G.
    exists (fun c d (g : Morphism _ (F c) d) =>
              let inverseOf := (fun s d f => projT1 (projT2 T s d f)) in
              let f := inverseOf _ _ g in
              let AComponentsOf_Inverse := projT1 T d ∘ F.(MorphismOf) f in
              inverseOf _ _ AComponentsOf_Inverse
           );
    [ intros; exists (fun f => projT1 T _ ∘ F.(MorphismOf) f) | ];
    abstract unit_counit_t_single.
  Defined.
End AdjunctionEquivalences'.

Coercion HomAdjunction2Adjunction : HomAdjunction >-> Adjunction.
Coercion Adjunction2HomAdjunction : Adjunction >-> HomAdjunction.

Coercion UnitOf : HomAdjunction >-> AdjunctionUnit.
Coercion CounitOf : HomAdjunction >-> AdjunctionCounit.
Coercion UnitCounitOf : HomAdjunction >-> AdjunctionUnitCounit.

Definition AdjunctionUnitWithFunext `{Funext} C D F G := @AdjunctionUnit C D F G.
Definition AdjunctionCounitWithFunext `{Funext} C D F G := @AdjunctionCounit C D F G.
Definition AdjunctionUnitCounitWithFunext `{Funext} C D F G := @AdjunctionUnitCounit C D F G.
Identity Coercion AdjunctionUnit_Funext : AdjunctionUnitWithFunext >-> AdjunctionUnit.
Identity Coercion AdjunctionCounit_Funext : AdjunctionCounitWithFunext >-> AdjunctionCounit.
Identity Coercion AdjunctionUnitCounit_Funext : AdjunctionUnitCounitWithFunext >-> AdjunctionUnitCounit.

Definition HomAdjunctionOfUnit_Funext `{Funext} C D F G : AdjunctionUnitWithFunext _ _ -> HomAdjunction _ _
  := @HomAdjunctionOfUnit _ C D F G.
Definition HomAdjunctionOfCounit_Funext `{Funext} C D F G : AdjunctionCounitWithFunext _ _ -> HomAdjunction _ _
  := @HomAdjunctionOfCounit _ C D F G.
Definition HomAdjunctionOfUnitCounit_Funext `{Funext} C D F G : AdjunctionUnitCounitWithFunext _ _ -> HomAdjunction _ _
  := @HomAdjunctionOfUnitCounit _ C D F G.

Coercion HomAdjunctionOfUnit_Funext : AdjunctionUnitWithFunext >-> HomAdjunction.
Coercion HomAdjunctionOfCounit_Funext : AdjunctionCounitWithFunext >-> HomAdjunction.
Coercion HomAdjunctionOfUnitCounit_Funext : AdjunctionUnitCounitWithFunext >-> HomAdjunction.
