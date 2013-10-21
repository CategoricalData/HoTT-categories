Require Export SetCategory.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope equiv_scope.
Local Open Scope category_scope.

Instance trunc_path_IsHProp `{Univalence, Funext} X Y `{IsHProp Y}
: IsHProp (X = Y).
Proof.
  apply hprop_allpath.
  intros pf1 pf2.
  rewrite <- (eta_path_universe pf1), <- (eta_path_universe pf2).
  lazymatch goal with
    | [ |- @path_universe _ _ _ (equiv_fun _ _ ?f) ?Hf
           = @path_universe _ _ _ (equiv_fun _ _ ?g) ?Hg ]
      => change Hf with (equiv_isequiv _ _ f);
        change Hg with (equiv_isequiv _ _ g);
        generalize (equiv_isequiv _ _ f) (equiv_isequiv _ _ g);
        generalize (equiv_fun _ _ f) (equiv_fun _ _ g)
  end.
  let f' := fresh in
  let g' := fresh in
  intros f' g' ? ?;
    assert (f' = g'); [ | subst; apply ap; apply allpath_hprop ].
  apply path_forall; intro.
  apply allpath_hprop.
Qed.

Instance trunc_hProp `{Univalence, Funext} : IsHSet hProp.
Proof.
  eapply trunc_equiv'; [ apply issig_hProp | ].
  (intros [? ?] ?).
  apply hprop_allpath.
  repeat match goal with
           | _ => reflexivity
           | _ => intro
           | _ => progress subst
           | [ H : @paths (sigT _) _ _ |- _ ]
             => rewrite <- (eta_path_sigma H);
               generalize (H..1) (H..2);
               clear H;
               simpl in *
           | [ H : _ = _ |- _ ] => assert (H = idpath) by apply allpath_hprop
         end.
Qed.

Instance IsStrictCategory_PropCat `{Funext, Univalence}
: IsStrictCategory PropCat
  := trunc_hProp.

Local Ltac do_equiv_iso_equiv :=
  repeat first [ etransitivity; [ apply symmetry; by apply Isomorphic_sig | ]
               | etransitivity; [ | by apply issig_equiv ]
               | etransitivity; [ apply symmetry; by apply IsIsomorphism_sig | ]
               | etransitivity; [ | by apply issig_isequiv ]
               | apply equiv_functor_sigma_id; intro ];
  apply equiv_iff_hprop;
  intros;
  repeat match goal with
           | _ => intro
           | [ H : _ |- _ ] => (exists (ap10 H.1))
           | [ H : _ |- _ ] => (exists (path_forall _ _ H.1))
           | [ H : _ |- _ ] => (exact (path_forall _ _ H.1))
           | [ H : _ |- _ ] => (exists (ap10 H.2))
           | [ H : _ |- _ ] => (exists (path_forall _ _ H.2))
           | [ H : _ |- _ ] => (exact (path_forall _ _ H.2))
           | [ H : _ |- _ ] => (exists (ap10 H.2.1))
           | [ H : _ |- _ ] => (exists (path_forall _ _ H.2.1))
           | [ H : _ |- _ ] => (exact (path_forall _ _ H.2.1))
           | _ => by apply allpath_hprop
         end.

Lemma equiv_iso_equiv_PropCat `{Funext} (s d : PropCat)
: s ≅ d <~> (s <~> d).
Proof.
  do_equiv_iso_equiv.
Defined.

Lemma equiv_iso_equiv_SetCat `{Funext} (s d : SetCat)
: s ≅ d <~> (s <~> d).
Proof.
  do_equiv_iso_equiv.
Defined.

Lemma equiv_iso_equiv_PropCat_fun_refl `{Funext} x
: equiv_iso_equiv_SetCat x x (reflexivity x) = reflexivity _.
Proof.
  expand.

Eval cbv beta iota zeta delta [equiv_iso_equiv_SetCat transitivity transitive_equiv equiv_compose equiv_fun issig_equiv equiv_functor_sigma_id equiv_functor_sigma functor_sigma compose equiv_idmap]
  in equiv_iso_equiv_SetCat _ _.

Lemma idtoiso_equiv_path_PropCat `{Funext} (s d : PropCat) (p : s = d)
: idtoiso _ p = (equiv_iso_equiv_PropCat s d)^-1 (equiv_path s d (ap _ p)).
Proof.
  induction p.
  unfold ap.
  unfold equiv_path.
  apply Isomorphic_eq.
  apply path_forall.
  intro.
  etransitivity; [ simpl; reflexivity | ].
  unfold equiv_iso_equiv_PropCat.
  unfold equiv_fun.
  unfold equiv_inv.
  unfold equiv_isequiv.
  unfold transitivity.
  unfold symmetry.
  unfold transitive_equiv, symmetric_equiv.
  unfold equiv_compose.
  unfold isequiv_compose.


  unfold IsomorphicMorphism.
  simpl.

  Unfold Idtoiso.
  Simpl.
  Unfold ap.
  SearchAbout idtoiso idpath.
  apply path_equiv.
  unfold equiv_path.
  SearchAbout equiv_path.
simpl.*)

Definition eta_path_universe_uncurried `{Univalence} A B (p : A = B)
: path_universe_uncurried (equiv_path A B p) = p
  := eissect _ _.

Instance contr_idpath_hset `{IsHSet X} (x : X) : Contr (x = x)
  := contr_inhabited_hprop _ idpath.

Hint Extern 1 => apply @contr_idpath_hset : typeclass_instances.


Instance IsCategory_PropCat `{Funext, Univalence}
: IsCategory PropCat.
Proof.
  intros C D.

  apply (isequiv_adjointify _ (@isotoid_PropCat _ _ C D));
    hnf; intros;
    [ apply Isomorphic_eq | ];
    apply allpath_hprop.
Defined.


Instance IsCategory_SetCat `{Funext, Univalence}
: IsCategory SetCat.
Proof.
  intros C D.
  apply (isequiv_adjointify _ (@isotoid_SetCat _ _ C D));
    hnf; intros;
    [ apply Isomorphic_eq | ].


  destruct x as [f ?]; simpl.
  expand.
unfold idtoiso.
unfold isotoid_SetCat.
simpl in *.
destruct C, D; simpl in *.



  subst; simpl.
  unfold isotoid_PropCat.
  destruct C; simpl.
  unfold ap10.
  unfold apD10.
  match goal with
    | [ |- appcontext[match path_universe_uncurried ?E with _ => _ end] ]
      => let H := fresh in
         assert (H : path_universe_uncurried E = idpath);
           [ | rewrite H ]
  end.
  - rewrite <- eta_path_universe.
    unfold path_universe.
    apply ap.
    expand.
    apply ap.
    eapply @allpath_hprop.
    typeclasses eauto.
  - compute.
    match goal with
      | [ |- appcontext[match ?E with _ => _ end] ]
        => generalize E;
          let E := fresh in
          intro E;
            assert (E = idpath) by apply allpath_hprop; subst; trivial
    end.

    apply allpath_hprop.
Defined.
