Require Export Category Functor.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope equiv_scope.
Local Open Scope category_scope.
Local Open Scope morphism_scope.

Section ProductCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition ProductPreCategory : PreCategory.
    refine (@Build_PreCategory (C * D)%type
                               (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type)
                               (fun x => (Identity (fst x), Identity (snd x)))
                               (fun s d d' m2 m1 => (fst m2 ∘ fst m1, snd m2 ∘ snd m1))
                               _
                               _
                               _
                               _);
    abstract (
        intros; destruct_head prod; simpl;
        try f_ap; auto with morphism;
        typeclasses eauto
      ).
  Defined.
End ProductCategory.

Infix "*" := ProductPreCategory : category_scope.

Section isomorphism.
  Variable A : PreCategory.
  Variable B : PreCategory.
  Variables x y : Object (A * B).

  Definition ProductPreCategory_isomorphism_f
  : x ≅ y -> (fst x ≅ fst y) * (snd x ≅ snd y)
    := fun i =>
         ({|
             IsomorphicMorphism := fst IsomorphicMorphism;
             Isomorphic_IsIsomorphism :=
               {|
                 Inverse := fst i ⁻¹;
                 LeftInverse := ap fst LeftInverse;
                 RightInverse := ap fst RightInverse |} |},
          {|
            IsomorphicMorphism := snd IsomorphicMorphism;
            Isomorphic_IsIsomorphism :=
              {|
                Inverse := snd i ⁻¹;
                LeftInverse := ap snd LeftInverse;
                RightInverse := ap snd RightInverse |} |}).

  Definition ProductPreCategory_isomorphism_f_inv
  : (fst x ≅ fst y) * (snd x ≅ snd y) -> x ≅ y.
  Proof.
    refine (fun i =>
         Build_Isomorphic
           (@Build_IsIsomorphism
              (A * B) x y
              (@IsomorphicMorphism _ _ _ (fst i), @IsomorphicMorphism _ _ _ (snd i))
              ((fst i) ⁻¹, (snd i) ⁻¹)
              _
              _));
    [ apply path_prod; apply LeftInverse
    | apply path_prod; apply RightInverse ].
  Defined.

  Global Instance ProductPreCategory_isomorphism_isequiv
  : IsEquiv ProductPreCategory_isomorphism_f.
  Proof.
    apply (isequiv_adjointify ProductPreCategory_isomorphism_f ProductPreCategory_isomorphism_f_inv);
    [ intros [[? [? ? ?]] [? [? ? ?]]];
      apply path_prod; expand;
      repeat f_ap;
      path_induction;
      reflexivity
    | intros [[? ?] [[? ?] ? ?]]].
    expand;
      repeat f_ap;
      apply eta_path_prod.
  Defined.

  Global Instance ProductPreCategory_isomorphism_inv_isequiv
  : IsEquiv ProductPreCategory_isomorphism_f_inv
    := isequiv_inverse.

  Definition ProductPreCategory_isomorphism_equiv
  : x ≅ y <~> (fst x ≅ fst y) * (snd x ≅ snd y)
    := BuildEquiv _ _ _ ProductPreCategory_isomorphism_isequiv.
End isomorphism.

Lemma ProductPreCategory_isotoid `{IsCategory A, IsCategory B}
: forall x y : Object (A * B), x ≅ y -> x = y.
Proof.
  intros x y i.
  pose proof (fst (ProductPreCategory_isomorphism_equiv x y i)).
  pose proof (snd (ProductPreCategory_isomorphism_equiv x y i)).
  apply path_prod;
    apply (isotoid _ _ _);
    assumption.
Defined.

Instance ProductCategory_IsCategory `{Funext} `{IsCategory A, IsCategory B} : IsCategory (A * B).
Proof.
  (* We should be able to just compose some equivalences to make this
     work, but I can't quite figure it out.

  intros s d.
  hnf in *.
  pose proof (_ : IsEquiv (compose (@ProductPreCategory_isomorphism_f_inv _ _ s d)
                                   ((compose (functor_prod (@idtoiso A (fst s) (fst d))
                                                           (@idtoiso B (snd s) (snd d)))
                                             ((path_prod_uncurried s d) ^-1)%equiv)))).
  let f0 := match type of X with IsEquiv ?f0 => constr:(f0) end in
  let f := match goal with |- IsEquiv ?f => constr:(f) end in
  assert (f0 = f).
  expand.
  clear X.
  clear H1.
  clear H0.
  unfold ProductPreCategory_isomorphism_f_inv.
  unfold functor_prod, idtoiso, compose; simpl.
  apply path_forall; intro; simpl.
  destruct x.
  expand.
  repeat (f_ap; expand);
  refine (center _).*)
  repeat intro.
  apply (isequiv_adjointify (idtoiso (A * B) (x := _) (y := _))
                            (ProductPreCategory_isotoid (x := _) (y := _)));
    repeat intro.
  destruct s as [sa sb], d as [da db].
  repeat unfold ProductPreCategory_isotoid, path_prod, idtoiso, category_is_category, ProductPreCategory_isomorphism_equiv, equiv_inv, path_prod_uncurried;
    simpl.
  repeat match goal with
           | [ H : IsCategory _ |- _ ]
             => repeat match goal with
                         | _ => clear H
                         | [ |- appcontext[H ?a ?b] ] => generalize (H a b); intro
                       end
         end.
  destruct x as [[? ?] [[? ?] ? ?]].
  simpl in *.
  destruct
  destruct i, i0; simpl in *.
    clear H0.
  simpl ProductPreCategory_isotoid.

  generalize (ProductPreCategory_isotoid x).
  intro.
  path_induction.
  simpl.
  assert (@IsomorphicMorphism _ _ _ (idtoiso (A * B) (ProductPreCategory_isotoid x)) = @IsomorphicMorphism _ _ _ x).
  expand; destruct x; simpl.
  unfold ProductPreCategory_isotoid; simpl.

  expand.
  destruct x; simpl.

  unfold ProductPreCategory_isotoid; simpl.

  destruct s, d.
  unfold ProductPreCategory_isotoid.

  unfold path_prod, ProductPreCategory_isomorphism_equiv, idtoiso.
  simpl.
  unfold equiv_inv.
  pose proof (fun s d => isotoid A s d).
  pose proof (fun s d => isotoid B s d).
  repeat intro.
  hnf in H, H0.
  hnf; intros; expand.
  destruct x.
  unfold ProductPreCategory_isotoid.
  simpl.
  unfold path_prod.
  unfold path_prod_uncurried.
  destruct s as [sa sb], d as [da db].
  unfold idtoiso.
  simpl.
  Unset Printing Notations.
  unfold equiv_inv.
  unfold category_is_category.
  destruct (H sa da); clear H.
  destruct (H0 sb db); clear H0.
  simpl.
  repeat match goal with
           | [ |- appcontext [match ?f ?x with _ => _ end] ] => let fx := fresh "fx" in set (fx := f x)
         end.
  clearbody fx.
  clearbody fx0.
  clear.
  unfold reflexivity.
  unfold ismorphic_refl.
  destruct Isomorphic_IsIsomorphism.
  path_induction.
  simpl.
  apply (isequiv_adjointify ProductPreCategory_isotoid).
  pose (isequiv_
  pose (ProductPreCategory_isotoid (x := s) (y := d)).
  eexists p _ _.
  intros [sa sb] [da db].
  pose (idtoiso (A * B)).
  pose @isequiv_adjointify.
  apply isequiv_fcontr.
  pose proof (fcontr_isequiv _ (H sa da)).
  pose proof (fcontr_isequiv _ (H0 sb db)).
  eapply fcontr_isequiv in H.
  SearchAbout IsEquiv.
repeat intro.
  apply isequiv_adjointify.
  unfold idtoiso.
  hnf.

  hnf.
  Check idtoiso (A * B).
  Print Sect.
  SearchAbout Sect.
Notation "m ^-1" := (Inverse m) : morphism_scope.
  hnf.
  simpl.
  intros.
  unfold idtoiso.
  ksimpl.

Section ProductCategoryFunctors.
  Context {C : PreCategory}.
  Context {D : PreCategory}.

  Definition fst_Functor : Functor (C * D) C
    := Build_Functor (C * D) C
                     (@fst _ _)
                     (fun _ _ => @fst _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition snd_Functor : Functor (C * D) D
    := Build_Functor (C * D) D
                     (@snd _ _)
                     (fun _ _ => @snd _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End ProductCategoryFunctors.
