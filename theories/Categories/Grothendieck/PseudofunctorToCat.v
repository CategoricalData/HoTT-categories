Require Export Category.
Require Import Common Category.Morphisms Functor.CompositionLaws NaturalTransformation.Core FunctorCategory NaturalTransformation.Isomorphisms Cat.Morphisms Pseudofunctor.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section GrothendieckCat.
  Context `{Funext}.

  (** Quoting Wikipedia:

      The Grothendieck construction is an auxiliary construction used
      in the mathematical field of category theory.

      Let

      [F : C -> Set]

      be a functor from any small category to the category of sets.
      The Grothendieck construct for [F] is the category [Γ F] whose
      objects are pairs [(c, x)], where [c : C] is an object and [x :
      F c] is an element, and for which the set [Hom (Γ F) (c1, x1)
      (c2, x2)] is the set of morphisms [f : c1 -> c2] in [C] such
      that [F.(MorphismOf) f x1 = x2].  *)

  Variable C : PreCategory.
  Variable F : Pseudofunctor C.

  Record GrothendieckCatPair :=
    {
      GrothendieckCatC : C;
      GrothendieckCatX : Object (F GrothendieckCatC)
    }.

  Local Notation GrothendieckCatMorphism s d :=
    { f : Morphism C (GrothendieckCatC s) (GrothendieckCatC d)
    | Morphism _ (PMorphismOf F f (GrothendieckCatX s)) (GrothendieckCatX d) }.

  Definition GrothendieckCatCompose s d d'
             (m1 : GrothendieckCatMorphism d d')
             (m2 : GrothendieckCatMorphism s d)
  : GrothendieckCatMorphism s d'.
  Proof.
    exists (m1.1 ∘ m2.1).
    refine (m1.2 ∘ ((PMorphismOf F m1.1) ₁ m2.2 ∘ _)).
    apply (PFCompositionOf F).
  Defined.

  Definition GrothendieckCatIdentity x : GrothendieckCatMorphism x x.
  Proof.
    exists (Identity (GrothendieckCatC x)).
    apply (PFIdentityOf F).
  Defined.

  Global Arguments GrothendieckCatIdentity _ / .
  Global Arguments GrothendieckCatCompose _ _ _ _ _ / .

  Local Ltac try_associativity_f_ap :=
    first [ f_ap; []
          | repeat (etransitivity; [ apply Associativity | ]);
            repeat (etransitivity; [ | symmetry; apply Associativity ]);
            f_ap; []
          | repeat (etransitivity; [ symmetry; apply Associativity | ]);
            repeat (etransitivity; [ | apply Associativity ]);
            f_ap; [] ].

  Local Ltac assoc_before_commutes_tac :=
    rewrite !FCompositionOf;
    rewrite <- !Associativity;
    etransitivity; [ | symmetry; apply compose4associativity_helper2 ].

  Local Ltac assoc_fin_tac :=
    repeat match goal with
             | _ => reflexivity
             | _ => progress rewrite ?LeftIdentity, ?RightIdentity
             | [ |- appcontext[ComponentsOf ?T ?x ∘ ComponentsOf ?T^-1 ?x] ]
               => simpl_do_clear do_rewrite (@iso_compose_pV _ _ _ (T x) _)
             | _ => try_associativity_quick
                      ltac:(first [ f_ap; []
                                  | apply concat_LeftIdentity
                                  | apply concat_RightIdentity
                                  | rewrite compose4associativity_helper2 ])
             | _ => rewrite <- ?FIdentityOf, <- ?FCompositionOf;
                   progress repeat (f_ap; []);
                   rewrite ?FIdentityOf, ?FCompositionOf
           end.

  Local Ltac helper_t before_commutes_tac :=
    repeat intro;
    symmetry;
    apply path_sigma_uncurried;
    simpl in *;
    let ex_hyp := match goal with
                    | [ H : ?A = ?B |- @sigT (?B = ?A) _ ] => constr:(H)
                  end in
    (exists (inverse ex_hyp));
      simpl;
      rewrite ?transport_Fc_to_idtoiso, ?transport_cF_to_idtoiso;
      rewrite ?idtoiso_inv, ?ap_V, ?inv_V;
      simpl;
      let rew_hyp := match goal with
                       | [ H' : appcontext[ex_hyp] |- _ ] => constr:(H')
                     end in
      rewrite rew_hyp;
        clear rew_hyp ex_hyp;
        before_commutes_tac;
        repeat first [ reflexivity
                     | progress rewrite ?LeftIdentity, ?RightIdentity
                     | try_associativity_quick ltac:(f_ap; []) ];
        match goal with
          | _ => reflexivity
          | [ |- appcontext[MorphismOf ?F ?m ∘ ComponentsOf ?T ?x] ]
            => simpl_do_clear do_rewrite_rev (Commutes T _ _ m);
              try reflexivity
          | [ |- appcontext[ComponentsOf ?T ?x ∘ MorphismOf ?F ?m] ]
            => simpl_do_clear do_rewrite (Commutes T _ _ m);
              try reflexivity
        end.

  (* The goal for, e.g., the following associativity helper was made
  with the following code:
<<
intros a b c d [f f'] [g g'] [h h']; simpl.
    pose proof (apD10 (ap ComponentsOf (PFCompositionOfCoherent_for_rewrite F _ _ _ _ f g h))) as rew_hyp.
    revert rew_hyp.
    generalize dependent (Associativity C _ _ _ _ f g h). intros fst_hyp ?.

    simpl in *.
    hnf in rew_hyp.
    simpl in *.

    Local Ltac gen_x x :=
      generalize dependent (GrothendieckCatX x);
      generalize dependent (GrothendieckCatC x);
      repeat (let x1 := fresh "x" in intro x1).
    gen_x a.
    gen_x b.
    gen_x c.
    gen_x d.
    repeat match goal with
             | [ |- appcontext[PFIdentityOf ?F ?x] ]
               => generalize dependent (PFIdentityOf F x)
             | [ |- appcontext[PFCompositionOf ?F ?x ?y ?z ?f ?g] ]
               => generalize dependent (PFCompositionOf F x y z f g)
             | [ |- appcontext[PMorphismOf ?F ?m] ]
               => generalize dependent (PMorphismOf F m)
             | [ |- appcontext[PObjectOf ?F ?x] ]
               => generalize dependent (PObjectOf F x)
             | [ H : appcontext[PMorphismOf ?F ?m] |- _ ]
               => generalize dependent (PMorphismOf F m)
             | [ |- appcontext[@PMorphismOf _ _ ?F ?x ?y] ]
               => generalize dependent (@PMorphismOf _ _ F x y)
           end.
    simpl.

    intros.

    lazymatch goal with
      | [ H : appcontext[ap ?f ?H'] |- _ ]
        => rename H' into fst_hyp;
          rename H into rew_hyp;
          move rew_hyp at top
    end.

    generalize dependent fst_hyp.
    clear.
    intros.
    move rew_hyp at top.

    move H at top.

    repeat match goal with
             | [ H : Isomorphic _ _ |- _ ]
               => let x := fresh "x" in
                  let H' := fresh "H" in
                  destruct H as [x H'];
                    simpl in *
           end.
    move rew_hyp at top.
    repeat match goal with
             | [ H : _ |- _ ] => revert H
           end.

    intro H.
    intro C.
>> *)

  Lemma pseudofunctor_to_cat_assoc_helper
  : forall {x x0 : C} {x2 : Morphism C x x0} {x1 : C}
           {x5 : Morphism C x0 x1} {x4 : C} {x7 : Morphism C x1 x4}
           {p p0 : PreCategory} {f : Morphism C x x4 -> Functor p0 p}
           {p1 p2 : PreCategory} {f0 : Functor p2 p} {f1 : Functor p1 p2}
           {f2 : Functor p0 p2} {f3 : Functor p0 p1} {f4 : Functor p1 p}
           {x16 : Morphism [_, _] (f (x7 ∘ x5 ∘ x2)) (f4 ∘ f3)%functor}
           {x15 : Morphism [_, _] f2 (f1 ∘ f3)%functor} {H2 : IsIsomorphism x15}
           {x11 : Morphism [_, _] (f (x7 ∘ (x5 ∘ x2))) (f0 ∘ f2)%functor}
           {H1 : IsIsomorphism x11} {x9 : Morphism [_, _] f4 (f0 ∘ f1)%functor}
           {fst_hyp : x7 ∘ x5 ∘ x2 = x7 ∘ (x5 ∘ x2)}
           (rew_hyp : forall x3 : p0,
                        (idtoiso [p0, p] (ap f fst_hyp) : Morphism _ _ _) x3 =
                        x11 ⁻¹ x3 ∘ (f0 ₁ (x15 ⁻¹ x3) ∘ (1 ∘ (x9 (f3 x3) ∘ x16 x3))))
           {H0' : IsIsomorphism x16}
           {H1' : IsIsomorphism x9}
           {x13 : p} {x3 : p0} {x6 : p1} {x10 : p2}
           {x14 : Morphism p (f0 x10) x13} {x12 : Morphism p2 (f1 x6) x10}
           {x8 : Morphism p1 (f3 x3) x6},
      existT (fun f5 : Morphism C x x4 => Morphism p ((f f5) x3) x13)
             (x7 ∘ x5 ∘ x2)
             (x14 ∘ (f0 ₁ x12 ∘ x9 x6) ∘ (f4 ₁ x8 ∘ x16 x3)) =
      (x7 ∘ (x5 ∘ x2); x14 ∘ (f0 ₁ (x12 ∘ (f1 ₁ x8 ∘ x15 x3)) ∘ x11 x3)).
  Proof.
    helper_t assoc_before_commutes_tac.
    assoc_fin_tac.
  Qed.

  Lemma pseudofunctor_to_cat_left_identity_helper
  : forall {x1 x2 : C} {f : Morphism C x2 x1} {p p0 : PreCategory}
           {f0 : Morphism C x2 x1 -> Functor p0 p} {f1 : Functor p p}
           {x0 : Morphism [_, _] (f0 (1 ∘ f)) (f1 ∘ f0 f)%functor}
           {x : Morphism [_, _] f1 1%functor}
           {fst_hyp : 1 ∘ f = f}
           (rewrite_hyp : forall x3 : p0,
                            (idtoiso [p0, p] (ap f0 fst_hyp) : Morphism _ _ _) x3
                            = 1 ∘ (x ((f0 f) x3) ∘ x0 x3))
           {H0' : IsIsomorphism x0}
           {H1' : IsIsomorphism x}
           {x3 : p} {x4 : p0} {f' : Morphism p ((f0 f) x4) x3},
      existT (fun f2 : Morphism C x2 x1 => Morphism p ((f0 f2) x4) x3)
             (1 ∘ f)
             (x x3 ∘ (f1 ₁ f' ∘ x0 x4))
      = (f; f').
  Proof.
    abstract helper_t idtac.
  Qed.

  Lemma pseudofunctor_to_cat_right_identity_helper
  : forall {x1 x2 : C} {f : Morphism C x2 x1} {p p0 : PreCategory}
           {f0 : Morphism C x2 x1 -> Functor p0 p} {f1 : Functor p0 p0}
           {x0 : Morphism [_, _] (f0 (f ∘ 1)) (f0 f ∘ f1)%functor}
           {H0' : IsIsomorphism x0}
           {x : Morphism [_, _] f1 1%functor}
           {H1' : IsIsomorphism x}
           {fst_hyp : f ∘ 1 = f}
           (rew_hyp : forall x3 : p0,
                        (idtoiso [p0, p] (ap f0 fst_hyp) : Morphism _ _ _) x3
                        = 1 ∘ ((f0 f) ₁ (x x3) ∘ x0 x3))
           {x3 : p} {x4 : p0} {f' : Morphism p ((f0 f) x4) x3},
        existT (fun f2 : Morphism C x2 x1 => Morphism p ((f0 f2) x4) x3)
               (f ∘ 1)
               (f' ∘ ((f0 f) ₁ (x x4) ∘ x0 x4))
        = (f; f').
  Proof.
    abstract helper_t idtac.
  Qed.

  Definition CategoryOfElements : PreCategory.
  Proof.
    refine (@Build_PreCategory
              GrothendieckCatPair
              (fun s d => GrothendieckCatMorphism s d)
              GrothendieckCatIdentity
              GrothendieckCatCompose
              _
              _
              _
              _);
    [ abstract (
          intros ? ? ? ? [f ?] [g ?] [h ?];
          exact (pseudofunctor_to_cat_assoc_helper
                   (apD10
                      (ap ComponentsOf
                          (PFCompositionOfCoherent_for_rewrite F _ _ _ _ f g h))))
        )
    | abstract (
          intros ? ? [f ?];
          exact (pseudofunctor_to_cat_left_identity_helper
                   (apD10
                      (ap ComponentsOf
                          (PFLeftIdentityOfCoherent_for_rewrite F _ _ f))))
        )
    | abstract (
          intros ? ? [f ?];
          exact (pseudofunctor_to_cat_right_identity_helper
                   (apD10
                      (ap ComponentsOf
                          (PFRightIdentityOfCoherent_for_rewrite F _ _ f))))
    ) ].
  Defined.

  Definition GrothendieckCatFunctor : Functor CategoryOfElements C
    := Build_Functor CategoryOfElements C
                     GrothendieckCatC
                     (fun s d => @projT1 _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End GrothendieckCat.
