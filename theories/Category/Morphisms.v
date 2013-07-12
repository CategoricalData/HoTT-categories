Require Export Category.Core.
Require Import Common Notations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Class IsIsomorphism {C : PreCategory} {s d} (m : Morphism C s d) :=
  {
    Inverse : Morphism C d s;
    LeftInverse : Inverse ∘ m = Identity _;
    RightInverse : m ∘ Inverse = Identity _
  }.

Notation "m ^-1" := (Inverse (m := m)) : morphism_scope.
Notation "m ⁻¹" := (Inverse (m := m)) : morphism_scope.

Class Isomorphic {C : PreCategory} s d :=
  {
    IsomorphicMorphism :> Morphism C s d;
    Isomorphic_IsIsomorphism :> IsIsomorphism IsomorphicMorphism
  }.

(*Coercion Build_Isomorphic : IsIsomorphism >-> Isomorphic.*)
Coercion IsomorphicMorphism : Isomorphic >-> Morphism.
Coercion Isomorphic_IsIsomorphism : Isomorphic >-> IsIsomorphism.

Infix "<~=~>" := Isomorphic : category_scope.
Infix "≅" := Isomorphic : category_scope.

Existing Instance Isomorphic_IsIsomorphism.

Section iso_contr.
  Variable C : PreCategory.

  Local Open Scope equiv_scope.

  Variables s d : C.

  Section IsIsomorphism.
    Variable m : Morphism C s d.

    Lemma inverse_unique (m_inv0 m_inv1 : Morphism C d s)
          (left_inverse_0 : m_inv0 ∘ m = Identity _)
          (right_inverse_1 : m ∘ m_inv1 = Identity _)
    : m_inv0 = m_inv1.
    Proof.
      transitivity (m_inv0 ∘ m ∘ m_inv1);
      try_associativity ltac:(rewrite_hyp; autorewrite with morphism; reflexivity).
    Qed.

    Local Notation IsIsomorphism_sig_T :=
      { inverse : Morphism C d s
      | { _ : inverse ∘ m = Identity _
        | m ∘ inverse = Identity _ } } (only parsing).

    Lemma IsIsomorphism_sig
    : IsIsomorphism_sig_T <~> IsIsomorphism m.
    Proof.
      issig (@Build_IsIsomorphism _ _ _ m)
            (@Inverse _ _ _ m)
            (@LeftInverse _ _ _ m)
            (@RightInverse _ _ _ m).
    Defined.

    Global Instance trunc_IsIsomorphism : IsHProp (IsIsomorphism m).
    Proof.
      eapply trunc_equiv'; [ exact IsIsomorphism_sig | ].
      apply hprop_allpath.
      intros [x [? ?]] [y [? ?]].
      let H := fresh in
      assert (H : x = y) by (apply inverse_unique; assumption);
        destruct H.
      repeat match goal with
               | _ => progress simpl
               | _ => exact (center _)
               | _ => (exists idpath)
               | _ => apply path_sigma_uncurried
             end.
    Qed.
  End IsIsomorphism.

  Local Notation Isomorphic_sig_T :=
    { m : Morphism C s d
    | IsIsomorphism m }.

  Lemma Isomorphic_sig
  : Isomorphic_sig_T <~> Isomorphic s d.
  Proof.
    issig (@Build_Isomorphic C s d)
          (@IsomorphicMorphism C s d)
          (@Isomorphic_IsIsomorphism C s d).
  Defined.

  Global Instance trunc_Isomorphic : IsHSet (Isomorphic s d).
  Proof.
    eapply trunc_equiv'; [ exact Isomorphic_sig | ].
    typeclasses eauto.
  Qed.
End iso_contr.

Section iso_equiv_relation.
  Variable C : PreCategory.

  Global Instance isomorphic_refl : Reflexive (@Isomorphic C)
    := fun x : C =>
         {| IsomorphicMorphism := Identity x;
            Isomorphic_IsIsomorphism :=
              {|
                Inverse := Identity x;
                LeftInverse := LeftIdentity C x x (Identity x);
                RightInverse := RightIdentity C x x (Identity x) |}
         |}.

  Global Instance isomorphic_sym : Symmetric (@Isomorphic C)
    := fun x y X =>
         {| IsomorphicMorphism := Inverse;
            Isomorphic_IsIsomorphism :=
              {|
                Inverse := X;
                LeftInverse := RightInverse;
                RightInverse := LeftInverse |}
         |}.

  Global Instance isomorphic_trans : Transitive (@Isomorphic C).
  Proof.
    repeat intro.
    exists (X0 ∘ X).
    exists (Inverse ∘ Inverse);
      [ abstract (
            etransitivity; [ | apply LeftInverse ];
            instantiate;
            try_associativity ltac:(apply ap);
            try_associativity ltac:(rewrite LeftInverse);
            auto with morphism
          )
      | abstract (
            etransitivity; [ | apply RightInverse ];
            instantiate;
            try_associativity ltac:(apply ap);
            try_associativity ltac:(rewrite RightInverse);
            auto with morphism
          )
      ].
  Defined.

  Definition idtoiso (x y : C) (H : x = y) : Isomorphic x y
    := match H in (_ = y0) return (x ≅ y0) with
         | 1%path => reflexivity x
       end.
End iso_equiv_relation.

Ltac find_composition_to_identity :=
  match goal with
    | [ H : @Compose _ _ _ _ ?a ?b = @Identity _ _ |- appcontext[@Compose ?B ?C ?D ?E ?c ?d] ]
      => let H' := fresh in
         assert (H' : b = d /\ a = c) by (split; reflexivity); clear H';
         assert (H' : @Compose B C D E c d = @Identity _ _)
           by (
               exact H ||
                     (simpl in H |- *; exact H || (rewrite H; reflexivity))
             );
         first [ rewrite H'
               | simpl in H' |- *; rewrite H'
               | let H'T := type of H' in fail 2 "error in rewriting a found identity" H "[" H'T "]"
               ]; clear H'
  end.

(* Quoting Wikipedia:

   In category theory, an epimorphism (also called an epic morphism
   or, colloquially, an epi) is a morphism [f : X → Y] which is
   right-cancellative in the sense that, for all morphisms [g, g' : Y
   → Z], [g ∘ f = g' ∘ f -> g = g']

   Epimorphisms are analogues of surjective functions, but they are
   not exactly the same. The dual of an epimorphism is a monomorphism
   (i.e. an epimorphism in a category [C] is a monomorphism in the
   dual category [Cᵒᵖ]).  *)

Class IsEpimorphism {C} {x y} (m : Morphism C x y) :=
  is_epimorphism : forall z (m1 m2 : Morphism C y z),
                     m1 ∘ m = m2 ∘ m
                     -> m1 = m2.
Class IsMonomorphism {C} {x y} (m : Morphism C x y) :=
  is_monomorphism : forall z (m1 m2 : Morphism C z x),
                      m ∘ m1 = m ∘ m2
                      -> m1 = m2.

Record > Epimorphism {C} x y :=
  {
    Epimorphism_Morphism :> Morphism C x y;
    Epimorphism_IsEpimorphism :> IsEpimorphism Epimorphism_Morphism
  }.

Record > Monomorphism {C} x y :=
  {
    Monomorphism_Morphism :> Morphism C x y;
    Monomorphism_IsMonomorphism :> IsMonomorphism Monomorphism_Morphism
  }.

Infix "->>" := Epimorphism.
Infix "(->" := Monomorphism.
Infix "↠" := Epimorphism.
Infix "↪" := Monomorphism.

Section EpiMono.
  Variable C : PreCategory.

  Section properties.
    Global Instance IdentityIsEpimorphism (x : C) : IsEpimorphism (Identity x).
    Proof.
      repeat intro; autorewrite with morphism in *; trivial.
    Qed.

    Global Instance IdentityIsMonomorphism (x : C) : IsMonomorphism (Identity x).
    Proof.
      repeat intro; autorewrite with morphism in *; trivial.
    Qed.

    Global Instance IsEpimorphismComposition s d d' m0 m1
    : IsEpimorphism m0
      -> IsEpimorphism m1
      -> IsEpimorphism (Compose (C := C) (s := s) (d := d) (d' := d') m0 m1).
    Proof.
      repeat intro.
      rewrite <- !Associativity in *.
      apply_hyp.
    Qed.

    Global Instance IsMonomorphismComposition s d d' m0 m1
    : IsMonomorphism m0
      -> IsMonomorphism m1
      -> IsMonomorphism (Compose (C := C) (s := s) (d := d) (d' := d') m0 m1).
    Proof.
      repeat intro.
      rewrite !Associativity in *.
      apply_hyp.
    Qed.
  End properties.

  Section equiv.
    Global Instance epimorphism_refl : Reflexive (@Epimorphism C)
      := IdentityIsEpimorphism.

    Global Instance monomorphism_refl : Reflexive (@Monomorphism C)
      := IdentityIsMonomorphism.

    Global Instance epimorphism_trans : Transitive (@Epimorphism C)
      := fun _ _ _ m0 m1 => IsEpimorphismComposition m1 m0.

    Global Instance monomorphism_trans : Transitive (@Monomorphism C)
      := fun _ _ _ m0 m1 => IsMonomorphismComposition m1 m0.
  End equiv.
End EpiMono.

Hint Immediate @IdentityIsEpimorphism @IdentityIsMonomorphism @IsMonomorphismComposition @IsEpimorphismComposition : category morphism.

Section AssociativityComposition.
  Variable C : PreCategory.
  Variables x0 x1 x2 x3 x4 : C.

  Lemma compose4associativity_helper
    (a : Morphism C x3 x4) (b : Morphism C x2 x3)
    (c : Morphism C x1 x2) (d : Morphism C x0 x1)
  : (a ∘ b) ∘ (c ∘ d) = (a ∘ ((b ∘ c) ∘ d)).
  Proof.
    rewrite !Associativity; reflexivity.
  Qed.
End AssociativityComposition.

Ltac compose4associativity' a b c d := transitivity (a ∘ ((b ∘ c) ∘ d)); try solve [ apply compose4associativity_helper ].
Ltac compose4associativity :=
  match goal with
    | [ |- (?a ∘ ?b) ∘ (?c ∘ ?d) = _ ] => compose4associativity' a b c d
    | [ |- _ = (?a ∘ ?b) ∘ (?c ∘ ?d) ] => compose4associativity' a b c d
  end.
