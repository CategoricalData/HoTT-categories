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

  Local Tactic Notation "id_rule_t" tactic(ex_tac) constr(rew_hyp) tactic(before_commutes_tac) :=
    repeat intro;
    symmetry;
    apply path_sigma_uncurried;
    ex_tac;
    destruct_head' sigT; simpl;
    rewrite ?transport_Fc_to_idtoiso, ?transport_cF_to_idtoiso;
    rewrite ?idtoiso_inv, ?ap_V, ?inv_V;
    simpl;
    simpl_do_clear do_rewrite rew_hyp;
    simpl;
    try_associativity_f_ap;
    rewrite ?LeftIdentity, ?RightIdentity;
    before_commutes_tac;
    match goal with
      | _ => reflexivity
      | [ |- appcontext[MorphismOf ?F ?m ∘ ComponentsOf ?T ?x] ]
        => simpl_do_clear do_rewrite_rev (Commutes T _ _ m);
          try reflexivity
      | [ |- appcontext[ComponentsOf ?T ?x ∘ MorphismOf ?F ?m] ]
        => simpl_do_clear do_rewrite (Commutes T _ _ m);
          try reflexivity
    end.

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
          (id_rule_t
             (exists (inverse (Associativity _ _ _ _ _ _ _ _)))
             (PFCompositionOfCoherent_for_rewrite F)
             assoc_before_commutes_tac);
          assoc_fin_tac
        )
    | abstract
        (id_rule_t
           (exists (inverse (LeftIdentity _ _ _ _)))
           (PFLeftIdentityOfCoherent_for_rewrite F)
           idtac)
    | abstract
        (id_rule_t
           (exists (inverse (RightIdentity _ _ _ _)))
           (PFRightIdentityOfCoherent_for_rewrite F)
           idtac) ].
  Defined.

  Definition GrothendieckCatFunctor : Functor CategoryOfElements C
    := Build_Functor CategoryOfElements C
                     GrothendieckCatC
                     (fun s d => @projT1 _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End GrothendieckCat.
