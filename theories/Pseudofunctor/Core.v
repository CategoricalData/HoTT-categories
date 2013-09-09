Require Export Category.Core Category.Morphisms FunctorCategory FunctorCategory.Morphisms NaturalTransformation.CompositionLaws.
Require Import Common NaturalTransformation.Isomorphisms.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section PseudoFunctor.
  Local Open Scope natural_transformation_scope.
  Context `{Funext}.

  Variable C : PreCategory.

  (** Quoting from nCatLab (http://ncatlab.org/nlab/show/pseudofunctor):

      Given bicategories [C] and [D], a pseudofunctor (or weak 2-functor,
      or just functor) [P : C → D] consists of:

      * for each object [x] of [C], an object [P_x] of [D];

      * for each hom-category [C(x,y)] in [C], a functor [P_{x,y} :
        C(x,y) → D(P_x, P_y)];

      * for each object [x] of [C], an invertible 2-morphism (2-cell)
        [P_{id_x} : id_{P_x} ⇒ P_{x,x}(id_x);

      * for each triple [x],[y],[z] of [C]-objects, a isomorphism
        (natural in [f : x → y] and [g : y → z]) [P_{x,y,z}(f,g) :
        P_{x,y}(f);P_{y,z}(g) ⇒ P_{x,z}(f;g)];

      * for each hom-category [C(x,y)],
<<
                                    id_{Pₓ} ; P_{x, y}(f)
                                      //              \\
                                    //                  \\
        P_{idₓ} ; id_{P_{x,y}(f)} //                      \\  λ_{P_{x,y}(f)}
                                //                          \\
                               ⇙                              ⇘
              Pₓ,ₓ(idₓ) ; P_{x,y}(f)                       P_{x,y}(f)
                               \\                             ⇗
                                 \\                         //
                P_{x,x,y}(idₓ, f)  \\                     // P_{x,y}(λ_f)
                                     \\                 //
                                       ⇘              //
                                        P_{x,y}(idₓ ; f)
>>
        and
<<
                                    P_{x, y}(f) ; id_{P_y}
                                      //              \\
                                    //                  \\
       id_{P_{x,y}(f)} ; P_{id_y} //                      \\  ρ_{P_{x,y}(f)}
                                //                          \\
                               ⇙                              ⇘
              P_{x,y}(f) ; P_{y,y}(id_y)                   P_{x,y}(f)
                               \\                             ⇗
                                 \\                         //
                P_{x,y,y}(f, id_y) \\                     // P_{x,y}(ρ_f)
                                     \\                 //
                                       ⇘              //
                                       P_{x,y}(f ; id_y)
>>
        commute; and

      * for each quadruple [w],[x],[y],[z] of [C]-objects,
<<
                                                  α_{P_{w,x}(f),P_{x,y}(g),P_{y,z}(h)}
        (P_{w,x}(f) ; P_{x,y}(g)) ; P_{y,z}(h) ========================================⇒ P_{w,x}(f) ; (P_{x,y}(g) ; P_{y,z}(h))
                                         ∥                                                   ∥
                                         ∥                                                   ∥
        P_{w,x,y}(f,g) ; id_{P_{y,z}(h)} ∥                                                   ∥ id_{P_{w,x}(f)} ; P_{x,y,z}(g, h)
                                         ∥                                                   ∥
                                         ⇓                                                   ⇓
                   P_{w,y}(f ; g) ; P_{y,z}(h)                                           P_{w,x}(f) ; P_{x,z}(g ; h)
                                         ∥                                                   ∥
                                         ∥                                                   ∥
                     P_{w,y,z}(f ; g, h) ∥                                                   ∥ P_{w,x,z}(f, g ; h)
                                         ∥                                                   ∥
                                         ⇓                                                   ⇓
                          P_{w,z}((f ; g) ; h) ========================================⇒ P_{w,z}(f ; (g ; h))
                                                          P_{w,z}(α_{f,g,h})
>>
        commutes.
*)

  (* To obtain the [PFCompositionOfCoherent] type, I ran
<<
  Unset Implicit Arguments.
  Variable F : Pseudofunctor.
  Goal forall (w x y z : C) (f : Morphism C w x) (g : Morphism C x y) (h : Morphism C y z), Type.
  Proof.
    intros.
    pose ((idtoiso [_, _] (ap (PMorphismOf F w z) (Associativity C _ _ _ _ f g h))) : Morphism _ _ _).
    pose ((PFCompositionOf F w y z h (g ∘ f)) : NaturalTransformation _ _).
    pose (PMorphismOf F y z h ∘ PFCompositionOf F w x y g f).

    pose (ComposeFunctorsAssociator1 (PMorphismOf F y z h) (PMorphismOf F x y g) (PMorphismOf F w x f)).
    pose (PFCompositionOf F x y z h g ∘ PMorphismOf F w x f).
    pose ((PFCompositionOf F w x z (h ∘ g) f) : NaturalTransformation _ _).
    simpl in *.
    repeat match goal with
             | [ H : _, H' : _ |- _ ] => unique_pose_with_body (NTComposeT H H'); subst H H'
           end.
    match goal with
      | [ H := _, H' := _ |- _ ] => assert (H = H'); subst H H'
    end.
>>

<<
  Unset Implicit Arguments.
  Variable F : Pseudofunctor.
  Goal forall (x y : C) (f : Morphism C x y), Type.
  Proof.
    intros.
    pose (PFIdentityOf F y ∘ PMorphismOf F x y f).
    pose (PFCompositionOf F x y y (Identity y) f : NaturalTransformation _ _).
    pose (idtoiso [_, _] (ap (PMorphismOf F x y) (LeftIdentity _ _ _ f)) : Morphism _ _ _).
    pose (LeftIdentityFunctorNaturalTransformation2 (PMorphismOf F x y f)).
    simpl in *.
    repeat match goal with
             | [ H : _, H' : _ |- _ ] => unique_pose_with_body (NTComposeT H H'); subst H H'
           end.
    match goal with
      | [ H := _, H' := _ |- _ ] => assert (H = H'); subst H H'
    end.
>>

<<
  Unset Implicit Arguments.
  Variable F : Pseudofunctor.
  Goal forall (x y : C) (f : Morphism C x y), Type.
  Proof.
    intros.
    pose (PMorphismOf F x y f ∘ PFIdentityOf F x).
    pose (PFCompositionOf F x x y f (Identity x) : NaturalTransformation _ _).
    pose (idtoiso [_, _] (ap (PMorphismOf F x y) (RightIdentity _ _ _ f)) : Morphism _ _ _).
    pose (RightIdentityFunctorNaturalTransformation2 (PMorphismOf F x y f)).
    simpl in *.
    repeat match goal with
             | [ H : _, H' : _ |- _ ] => unique_pose_with_body (NTComposeT H H'); subst H H'
           end.
    match goal with
      | [ H := _, H' := _ |- _ ] => assert (H = H'); subst H H'
    end.
>>
 *)

  Record Pseudofunctor :=
    {
      PObjectOf :> C -> PreCategory;
      PMorphismOf : forall s d, Morphism C s d -> Functor (PObjectOf s) (PObjectOf d);
      PFCompositionOf : forall s d d' (m1 : Morphism C d d') (m2 : Morphism C s d),
                          (PMorphismOf _ _ (m1 ∘ m2))
                            ≅ (PMorphismOf _ _ m1 ∘ PMorphismOf _ _ m2);
      PFIdentityOf : forall x,
                       (PMorphismOf x x (Identity x))
                         ≅ (IdentityFunctor _);
      PFCompositionOfCoherent
      : forall w x y z
               (f : Morphism C w x) (g : Morphism C x y) (h : Morphism C y z),
          (NTComposeT
             (ComposeFunctorsAssociator1 (PMorphismOf y z h) (PMorphismOf x y g) (PMorphismOf w x f))
             (NTComposeT
                (NTWhiskerR (PFCompositionOf x y z h g) (PMorphismOf w x f))
                (PFCompositionOf w x z (h ∘ g) f)))
          = (NTComposeT
               (NTWhiskerL (PMorphismOf y z h) (PFCompositionOf w x y g f))
               (NTComposeT
                  (PFCompositionOf w y z h (g ∘ f))
                  (idtoiso [_, _] (ap (PMorphismOf w z) (Associativity C w x y z f g h)) : Morphism _ _ _)));
      PFLeftIdentityOfCoherent
      : forall x y (f : Morphism C x y),
          NTComposeT (NTWhiskerR (PFIdentityOf y) (PMorphismOf x y f))
                     (PFCompositionOf x y y ─ f)
          = NTComposeT (LeftIdentityFunctorNaturalTransformation2 (PMorphismOf x y f))
                       (idtoiso [_, _] (ap (PMorphismOf x y) (LeftIdentity C x y f)) : Morphism _ _ _);
      PFRightIdentityOfCoherent
      : forall x y (f : Morphism C x y),
          NTComposeT (NTWhiskerL (PMorphismOf x y f) (PFIdentityOf x))
                       (PFCompositionOf x x y f ─)
          = NTComposeT (RightIdentityFunctorNaturalTransformation2 (PMorphismOf x y f))
                       (idtoiso [_, _] (ap (PMorphismOf x y) (RightIdentity C x y f)) : Morphism _ _ _)
    }.
End PseudoFunctor.

Bind Scope pseudofunctor_scope with Pseudofunctor.

Create HintDb pseudofunctor discriminated.

Arguments PObjectOf {_} {C%category} F%pseudofunctor c%object : rename, simpl nomatch.
Arguments PMorphismOf {_} [C%category] F%pseudofunctor [s d]%object m%morphism : rename, simpl nomatch.

(*Notation "F ₀ x" := (PObjectOf F x) : object_scope.
Notation "F ₁ m" := (PMorphismOf F m) : morphism_scope.*)

Section lemmas.
  Local Open Scope natural_transformation_scope.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable F : Pseudofunctor C.

  Lemma PFCompositionOfCoherent_for_rewrite w x y z
        (f : Morphism C w x) (g : Morphism C x y) (h : Morphism C y z)
  : (idtoiso [_, _] (ap (@PMorphismOf _ _ F w z) (Associativity C w x y z f g h)) : Morphism _ _ _)
    = (NTComposeT
         (PFCompositionOf F w y z h (g ∘ f))^-1
         (NTComposeT
            (NTWhiskerL (PMorphismOf F h) (PFCompositionOf F w x y g f)^-1)
            (NTComposeT
               (ComposeFunctorsAssociator1 (PMorphismOf F h) (PMorphismOf F g) (PMorphismOf F f))
               (NTComposeT
                  (NTWhiskerR (PFCompositionOf F x y z h g) (PMorphismOf F f))
                  (PFCompositionOf F w x z (h ∘ g) f))))).
  Proof.
    simpl_do_clear do_rewrite (@PFCompositionOfCoherent _ C F w x y z f g h).
    let C := match goal with |- @paths (@NaturalTransformation ?C ?D ?F ?G) _ _ => constr:([C, D])%category end in
    apply (@iso_moveL_Vp C);
      apply (@iso_moveL_Mp C _ _ _ _ _ _ (iso_NTWhiskerL _ _ _ _ _ _ _)).
    nt_eq.
    reflexivity.
  Qed.

  Lemma PFLeftIdentityOfCoherent_for_rewrite x y (f : Morphism C x y)
  : (idtoiso [_, _] (ap (@PMorphismOf _ _ F x y) (LeftIdentity C x y f)) : Morphism _ _ _)
    = NTComposeT (LeftIdentityFunctorNaturalTransformation1 (PMorphismOf F f))
                 (NTComposeT (NTWhiskerR (PFIdentityOf F y) (PMorphismOf F f))
                             (PFCompositionOf F x y y ─ f)).
  Proof.
    simpl_do_clear do_rewrite (@PFLeftIdentityOfCoherent _ C F x y f).
    nt_eq.
    symmetry.
    etransitivity; apply LeftIdentity.
  Qed.

  Lemma PFRightIdentityOfCoherent_for_rewrite x y (f : Morphism C x y)
  : (idtoiso [_, _] (ap (@PMorphismOf _ _ F x y) (RightIdentity C x y f)) : Morphism _ _ _)
    = NTComposeT (RightIdentityFunctorNaturalTransformation1 (PMorphismOf F f))
                 (NTComposeT (NTWhiskerL (PMorphismOf F f) (PFIdentityOf F x))
                             (PFCompositionOf F x x y f ─)).
  Proof.
    simpl_do_clear do_rewrite (@PFRightIdentityOfCoherent _ C F x y f).
    nt_eq.
    symmetry.
    etransitivity; apply LeftIdentity.
  Qed.
End lemmas.
