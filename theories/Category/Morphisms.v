Require Export Category.Core Functor.Core.
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

Hint Resolve LeftInverse RightInverse : category morphism.

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

  Definition path_isomorphic (i j : Isomorphic s d)
  : @IsomorphicMorphism _ _ _ i = @IsomorphicMorphism _ _ _ j
    -> i = j.
  Proof.
    destruct i, j; simpl.
    intro; path_induction.
    f_ap.
    exact (center _).
  Defined.

  Definition Isomorphic_eq := path_isomorphic.

  Global Instance isequiv_path_isomorphic
  : IsEquiv (path_isomorphic i j).
  Proof.
    intros.
    apply (isequiv_adjointify
             (path_isomorphic i j)
             (ap (@IsomorphicMorphism _ _ _)));
      intro; [ destruct i | destruct i, j ];
      super_path_induction.
  Defined.
End iso_contr.

Section iso_equiv_relation.
  Variable C : PreCategory.

  Global Instance isisomorphism_identity (x : C) : IsIsomorphism (Identity x)
    := {| Inverse := Identity x;
          LeftInverse := LeftIdentity C x x (Identity x);
          RightInverse := RightIdentity C x x (Identity x) |}.

  Definition isisomorphism_inverse `(@IsIsomorphism C x y m) : IsIsomorphism m^-1
    := {| Inverse := m;
          LeftInverse := RightInverse;
          RightInverse := LeftInverse |}.

  Local Ltac iso_comp_t inv_lemma :=
    etransitivity; [ | apply inv_lemma ];
    instantiate;
    try_associativity ltac:(apply ap);
    try_associativity ltac:(rewrite inv_lemma);
    auto with morphism.

  Global Instance isisomorphism_composition `(@IsIsomorphism C y z m0) `(@IsIsomorphism C x y m1)
  : IsIsomorphism (m0 ∘ m1).
  Proof.
    exists (m1^-1 ∘ m0^-1);
    [ abstract iso_comp_t @LeftInverse
    | abstract iso_comp_t @RightInverse ].
  Defined.

  Hint Immediate isisomorphism_inverse : typeclass_instances.

  Global Instance isomorphic_refl : Reflexive (@Isomorphic C)
    := fun x : C => {| IsomorphicMorphism := Identity x |}.

  Global Instance isomorphic_sym : Symmetric (@Isomorphic C)
    := fun x y X => {| IsomorphicMorphism := Inverse |}.

  Global Instance isomorphic_trans : Transitive (@Isomorphic C)
    := fun x y z X Y => {| IsomorphicMorphism := @IsomorphicMorphism _ _ _ Y ∘ @IsomorphicMorphism _ _ _ X |}.

  Definition idtoiso (x y : C) (H : x = y) : Isomorphic x y
    := match H in (_ = y0) return (x ≅ y0) with
         | 1%path => reflexivity x
       end.
End iso_equiv_relation.

Hint Immediate isisomorphism_inverse : typeclass_instances.

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

Section iso_lemmas.
  Lemma transport_to_idtoiso (C D : PreCategory) s d
        (m1 m2 : Morphism C s d)
        (p : m1 = m2)
        (s' d' : Morphism C s d -> D) u
  : @transport _ (fun m => Morphism D (s' m) (d' m)) _ _ p u
    = idtoiso _ (ap d' p) ∘ u ∘ (idtoiso _ (ap s' p))^-1.
  Proof.
    path_induction; simpl; autorewrite with morphism; reflexivity.
  Qed.

  Lemma idtoiso_inv (C : PreCategory) (s d : C) (p : s = d)
  : (idtoiso _ p)^-1 = idtoiso _ (p^)%path.
  Proof.
    path_induction; reflexivity.
  Defined.

  Lemma idtoiso_comp (C : PreCategory) (s d d' : C)
        (m1 : d = d') (m2 : s = d)
  : idtoiso _ m1 ∘ idtoiso _ m2 = idtoiso _ (m2 @ m1)%path.
  Proof.
    path_induction; simpl; auto with morphism.
  Qed.

  Lemma idtoiso_functor (C D : PreCategory) (s d : C) (m : s = d)
        (F : Functor C D)
  : MorphismOf F (idtoiso _ m) = idtoiso _ (ap (ObjectOf F) m).
  Proof.
    path_induction; simpl; apply FIdentityOf.
  Defined.

  Global Instance iso_functor C D (F : Functor C D) `(@IsIsomorphism C s d m)
  : IsIsomorphism (MorphismOf F m)
    := {| Inverse := MorphismOf F m^-1 |}.
  Proof.
    abstract (rewrite <- FCompositionOf, ?LeftInverse, ?RightInverse, FIdentityOf; reflexivity).
    abstract (rewrite <- FCompositionOf, ?LeftInverse, ?RightInverse, FIdentityOf; reflexivity).
  Defined.
End iso_lemmas.

Hint Rewrite transport_to_idtoiso idtoiso_inv idtoiso_comp idtoiso_functor.

Section iso_concat_lemmas.
  Variable C : PreCategory.

  Local Ltac iso_concat_t' :=
    intros;
    repeat match goal with
             | [ H : ?x = ?y |- _ ] => atomic y; induction H
             | [ H : ?x = ?y |- _ ] => atomic x; symmetry in H; induction H
           end;
    repeat first [ done
                 | try_associativity ltac:(progress rewrite ?LeftIdentity, ?RightIdentity, ?LeftInverse, ?RightInverse)
                 | try_associativity ltac:(progress f_ap; []) ].

  Local Ltac iso_concat_t_id_fin :=
    match goal with
      | [ |- appcontext[@Identity ?C ?x] ]
        => generalize dependent (@Identity C x)
    end;
    iso_concat_t'.

  Local Ltac iso_concat_t_id lem :=
    first [ solve [
                etransitivity; [ | eapply lem ];
                iso_concat_t_id_fin
              ]
          | solve [
                etransitivity; [ eapply symmetry; eapply lem | ];
                iso_concat_t_id_fin
          ] ].

  Local Ltac iso_concat_t :=
    iso_concat_t';
    try first [ solve [ iso_concat_t_id @LeftIdentity ]
              | solve [ iso_concat_t_id @RightIdentity ] ].

  Definition iso_compose_pV `(@IsIsomorphism C x y p)
  : p ∘ p^-1 = Identity _
    := RightInverse.
  Definition iso_compose_Vp `(@IsIsomorphism C x y p)
  : p^-1 ∘ p = Identity _
    := LeftInverse.

  Definition iso_compose_V_pp `(@IsIsomorphism C y z p) `(q : Morphism C x y)
  : p^-1 ∘ (p ∘ q) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_compose_p_Vp `(@IsIsomorphism C x z p) `(q : Morphism C y z)
  : p ∘ (p^-1 ∘ q) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_compose_pp_V `(p : Morphism C y z) `(@IsIsomorphism C x y q)
  : (p ∘ q) ∘ q^-1 = p.
  Proof. iso_concat_t. Qed.

  Definition iso_compose_pV_p `(p : Morphism C x z) `(@IsIsomorphism C x y q)
  : (p ∘ q^-1) ∘ q = p.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_pp `(@IsIsomorphism C y z p) `(@IsIsomorphism C x y q)
  : (p ∘ q)^-1 = q^-1 ∘ p^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_Vp `(@IsIsomorphism C y z p) `(@IsIsomorphism C x z q)
  : (p^-1 ∘ q)^-1 = q^-1 ∘ p.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_pV `(@IsIsomorphism C x y p) `(@IsIsomorphism C x z q)
  : (p ∘ q^-1)^-1 = q ∘ p^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_inv_VV `(@IsIsomorphism C x y p) `(@IsIsomorphism C y z q)
  : (p^-1 ∘ q^-1)^-1 = q ∘ p.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_Mp `(p : Morphism C x y) `(q : Morphism C x z) `(@IsIsomorphism C y z r)
  : p = (r^-1 ∘ q) -> (r ∘ p) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_pM `(@IsIsomorphism C x y p) `(q : Morphism C x z) `(r : Morphism C y z)
  : r = (q ∘ p^-1) -> (r ∘ p) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_Vp `(p : Morphism C x y) `(q : Morphism C x z) `(@IsIsomorphism C z y r)
  : p = (r ∘ q) -> (r^-1 ∘ p) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_pV `(@IsIsomorphism C x y p) `(q : Morphism C y z) `(r : Morphism C x z)
  : r = (q ∘ p) -> (r ∘ p^-1) = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_Mp `(p : Morphism C x y) `(q : Morphism C x z) `(@IsIsomorphism C y z r)
  : (r^-1 ∘ q) = p -> q = (r ∘ p).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_pM `(@IsIsomorphism C x y p) `(q : Morphism C x z) `(r : Morphism C y z)
  : (q ∘ p^-1) = r -> q = (r ∘ p).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_Vp `(p : Morphism C x y) `(q : Morphism C x z) `(@IsIsomorphism C _ _ r)
  : (r ∘ q) = p -> q = (r^-1 ∘ p).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_pV `(@IsIsomorphism C x y p) `(q : Morphism C y z) r
  : (q ∘ p) = r -> q = (r ∘ p^-1).
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_1M `(p : Morphism C x y) `(@IsIsomorphism C x y q)
  : p ∘ q^-1 = Identity _ -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_M1 `(p : Morphism C x y) `(@IsIsomorphism C x y q)
  : q^-1 ∘ p = Identity _ -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_1V `(p : Morphism C x y) `(@IsIsomorphism C y x q)
  : p ∘ q = Identity _ -> p = q^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_moveL_V1 `(p : Morphism C x y) `(@IsIsomorphism C y x q)
  : q ∘ p = Identity _ -> p = q^-1.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_M1 `(@IsIsomorphism C x y p) q
  : Identity _ = p^-1 ∘ q -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_1M `(@IsIsomorphism C x y p) q
  : Identity _ = q ∘ p^-1 -> p = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_1V `(@IsIsomorphism C x y p) q
  : Identity _ = q ∘ p -> p^-1 = q.
  Proof. iso_concat_t. Qed.

  Definition iso_moveR_V1 `(@IsIsomorphism C x y p) q
  : Identity _ = p ∘ q -> p^-1 = q.
  Proof. iso_concat_t. Qed.
End iso_concat_lemmas.
