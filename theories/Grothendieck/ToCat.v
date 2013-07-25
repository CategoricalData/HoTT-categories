Require Export Category Functor Cat.
Require Import Common Category.Morphisms.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section GrothendieckCat.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (SubPreCat P).

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
  Variable F : Functor C Cat.

  Record GrothendieckCatPair :=
    {
      GrothendieckCatC : C;
      GrothendieckCatX : Object (projT1 (F GrothendieckCatC))
    }.

  Local Notation GrothendieckCatMorphism s d :=
    { f : Morphism C (GrothendieckCatC s) (GrothendieckCatC d)
    | Morphism _ (MorphismOf F f (GrothendieckCatX s)) (GrothendieckCatX d) }.
Notation X s := (GrothendieckCatX s).
  Definition GrothendieckCatCompose s d d'
             (m1 : GrothendieckCatMorphism d d')
             (m2 : GrothendieckCatMorphism s d)
  : GrothendieckCatMorphism s d'.
  Proof.
    exists (m1.1 ∘ m2.1).
    refine (m1.2 ∘ ((F ₁ m1.1) ₁ m2.2 ∘ idtoiso _ _)).
    exact (ap10 (ap ObjectOf (FCompositionOf F _ _ _ _ _ )) _).
  Defined.

  Definition GrothendieckCatIdentity x : GrothendieckCatMorphism x x.
  Proof.
    exists (Identity (GrothendieckCatC x)).
    refine (idtoiso _ _).
    exact (ap10 (ap ObjectOf (FIdentityOf F _)) _).
  Defined.

  Global Arguments GrothendieckCatIdentity _ / .
  Global Arguments GrothendieckCatCompose _ _ _ _ _ / .

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
    repeat intro;
    symmetry;
    apply path_sigma_uncurried;
    [ (exists (inverse (Associativity _ _ _ _ _ _ _ _)))
    | (exists (inverse (LeftIdentity _ _ _ _)))
    | (exists (inverse (RightIdentity _ _ _ _))) ].
    Focus 3.
    destruct f; simpl.
    repeat rewrite ?transport_to_idtoiso, ?idtoiso_inv, ?ap_const, ?LeftIdentity, ?RightIdentity, ?idtoiso_functor, ?idtoiso_comp.
    repeat (f_ap; []).
    simpl.
    clear m.
    rename x into m.


    progress repeat match goal with
                      | [ |- appcontext[inverse (@ap ?A ?B ?f ?x ?y ?p)] ]
                        => rewrite !(@inverse_ap A B f x y p)
                      | [ |- appcontext[inverse (@ap10 ?A ?B ?f ?g ?h ?x)] ]
                        => rewrite <- !(@ap10_V A B f g h x)
                      | [ |- appcontext[fun x => ?f (?g x)] ]
                        => progress change (fun x => f (g x)) with (compose f g)
                      (*| [ |- appcontext[@ap ?B ?C ?h _ _ (@ap10 ?A ?B ?f ?g ?p ?a)] ]
                        => rewrite !(@ap_ap10 A B C f g h p a); unfold compose; simpl*)
                      (*| [ |- appcontext[@ap ?B ?C ?g _ _ (@ap ?A ?B ?f ?x ?y ?p)] ]
                        => let H := fresh in
                           pose proof (@ap_compose A B C f g x y p) as H;
                             simpl in H |- *;
                             rewrite <- !H;
                             clear H;
                             unfold compose; simpl*)
                      | [ |- appcontext[fun x => ?f (?g x) ?y] ]
                        => progress change (fun x => f (g x) y) with (compose (fun x => x y) (fun x => f (g x)))
                    end.
    rewrite ?ap_compose.
    rewrite ?ap_apply_l.

    let GL := match goal with |- ?GL = ?GR => constr:(GL) end in
    let GR := match goal with |- ?GL = ?GR => constr:(GR) end in
    lazymatch GR with
      | appcontext GRC[ap (ObjectOf ?F) (ap10 (ap (@ObjectOf ?C ?D) ?H) ?x)]
        => let GR' := context GRC[ap10 (ap (@ObjectOf _ _) (ap (Compose F) H)) x] in
           (*let GR'' := context GRC[ap (ObjectOf F) (ap10 (ap (@ObjectOf C D) H) x)] in
           assert (GR' = GR''); [ f_ap; generalize H | ]
           transitivity GR''; [ | reflexivity ]; *)
           transitivity GR';
           [
             | f_ap;
               let A := constr:(ap10 (ap (@ObjectOf _ _) (ap (Compose F) H)) x) in
               let B := constr:(ap (ObjectOf F) (ap10 (ap (@ObjectOf C D) H) x)) in
               change (A = B); (* XXX So fragile... :-( *) (*fix indentation - )*)
                 destruct H;
                 reflexivity ]
    end.


    Lemma pre_compose_inverse0 A (x y z : A)
          (p : x = y) (q : x = z) (r : z = y)
          (H' : (q^ @ p = r)%path)
    : (p = q @ r)%path.
    Proof.
      path_induction; reflexivity.
    Defined.
    apply pre_compose_inverse0.

    unfold compose in *.
    simpl.
    simpl in *; admit. (** simpl in * breaks admit >:-( *)
