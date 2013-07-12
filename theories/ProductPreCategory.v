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

Instance ProductCategory_IsCategory `{IsCategory A, IsCategory B} : IsCategory (A * B).
Proof.
  intros s d.
  pose (_ : IsEquiv (@ProductPreCategory_isomorphism_f_inv _ _ s d)).
  pose (_ : IsEquiv ((functor_prod (@idtoiso A (fst s) (fst d))
                                                     (@idtoiso B (snd s) (snd d)))
                                       ((path_prod_uncurried s d) ^-1)%equiv))))
  pose (_ : IsEquiv ((compose (functor_prod (@idtoiso A (fst s) (fst d))
                                                     (@idtoiso B (snd s) (snd d)))
                                       ((path_prod_uncurried s d) ^-1)%equiv))).
  Print Implicit isequiv_compose.

  SearchAbout IsEquiv.
  pose (_ : IsEquiv (compose (@ProductPreCategory_isomorphism_f_inv _ _ s d)
                             ((compose (functor_prod (@idtoiso A (fst s) (fst d))
                                                     (@idtoiso B (snd s) (snd d)))
                                       ((path_prod_uncurried s d) ^-1)%equiv)))).
  pose proof (fun s d => isotoid A s d).
  pose proof (fun s d => isotoid B s d).
  repeat intro.
  hnf in H, H0.
  Check (idtoiso (A * B) (x:=s) (y:=d)).
  Check (functor_prod (@idtoiso A (fst s) (fst d))
                      (@idtoiso B (snd s) (snd d))).
  Check ((path_prod_uncurried s d) ^-1)%equiv.
  Check (compose (ProductPreCategory_isomorphism_f_inv s d)
                 ((compose (functor_prod (@idtoiso A (fst s) (fst d))
                                         (@idtoiso B (snd s) (snd d)))
                           (compose ((path_prod_uncurried s d) ^-1)%equiv
                                    (fun x => x))))).

  pose (_ : IsEquiv (compose (functor_prod (@idtoiso A (fst s) (fst d))
                                           (@idtoiso B (snd s) (snd d)))
                             ((path_prod_uncurried s d) ^-1)%equiv)).

  SearchAbout path_prod_uncurried.
  SearchAbout (prod _ _ -> _ = _).
  Print Implicit isequiv_functor_prod.
  Check @functor_prod.
  Check @isequiv_functor_prod.
  SearchAbout Equiv.
  SearchAbout prod.
  Check prod_eta.
  Check sum_eta.
  pose proof (isequiv_functor_prod (f := @idtoiso A (fst s) (fst d))
                                   (g := @idtoiso B (snd s) (snd d))) as i.

  unfold functor_prod in i.
  pattern @fst in i.
  pattern @snd in i.
  pattern
  simpl in i.
  pose proof (equiv_path_prod s d).

  Print idtoiso.
  pattern ((fst s = fst d) * (snd s = snd d))%type in i.
  SearchAbout Equiv.

  SearchAbout (_ * _ <~> _).
  unfold idtoiso in i |- *.
  simpl in *.
  unfold equiv_inv in *.
  unfold
  Check @isequiv_functor_prod.
  pose (equiv_functor_prod').

  apply (isequiv_adjointify (idtoiso (A * B) (x := _) (y := _))
                            (ProductPreCategory_isotoid (x := _) (y := _))).
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
