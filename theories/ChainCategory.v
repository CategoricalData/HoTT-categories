Require Export Category.Core.
Require Import Common Coq.Logic.Decidable Coq.Arith.Le Coq.Arith.Compare_dec Subcategory.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section ChainCat.
  Definition le_dec n m : (n <= m) + (~n <= m).
  Proof.
    induction m in n |- *.
    - destruct n.
      + left. trivial.
      + right. apply le_Sn_0.
    - induction n in *.
      + left; clear; induction m; auto.
      + destruct (IHm n); [ left | right ].
        * apply le_n_S. assumption.
        * intro H. apply le_S_n in H.
          auto.
  Defined.

  Lemma le_dec_n n : le_dec n n = inl (le_n n).
  Proof.
    induction n; trivial; simpl in *.
    rewrite IHn.
    reflexivity.
  Defined.

(*  Lemma le_dec_S n m : le_dec n (S m) = match le_dec (S le_S _ _ (@le_dec_value n m H').
  Proof.
    destruct n; trivial.
    induction m in *; trivial.
    - intros.
      refine (match le_Sn_0 _ _ with end); eassumption.
    -
unfold le_dec_value in *.
      simpl in *.
      intros.
      specialize (IHm ).
    set (le_dec_n_Sm := le_dec n (S m)) in *.
    assert (le_dec n n = le_dec_n_n) by reflexivity.
    clearbody le_dec_n_n.
    destruct le_dec_n_n.
    - rewrite IHn by auto.
      simpl.
      reflexivity.
    - refine (match _ : Empty with end).
      auto.
  Defined.*)

  Global Instance trunc_le n m : IsHProp (n <= m).
  Proof.
    apply hprop_allpath.
    intros H0 H1.
    apply (@inl_injective (n <= m) (~n <= m)).
    transitivity (le_dec n m); [ symmetry | ]; clear.
    - induction H0; simpl.
      + induction n; trivial.
        simpl.
        rewrite IHn; trivial.
      + induction m, n; simpl in *.
        * apply inl_injective in IHle.
          path_induction.
          reflexivity.
        *
    - induction H1.
      + induction n; trivial.
        simpl.
        rewrite IHn; trivial.
      + idtac.
    induction H0.
    - induction n; try reflexivity.
      unfold le_dec_value in *.
      simpl in *.
     unfold le_gt_dec.
     unfold le_lt_dec.
     simpl.
    induction 0.

    Focus 2.


   change m with (pred (S m)) in y, IHy |- *.
    change (S (pred (S m))) with (S m).
    generalize dependent (S m); clear m; intros.
    induction H0.
    Focus 2.
    induction H
    refine (_ : match H1 as H1 return Type with
                  | le_n n => le_n n = le_n n
                  | le_S

    transitivity (match le_dec n m with
                    | inl H => H
                    | inr nH => match nH H0 with end
                  end).

    induction H0; simpl.
    compute.
    induction n; simpl.
    compute.
    Locate Le.le_0_n.
    Focus 2.

    Print le_dec.
    SearchAbout le_dec.
    induction H0.



  Definition OmegaCategory : PreCategory.
  Proof.
    refine (@Build_PreCategory nat
                               le
                               le_refl
                               (fun _ _ _ H0 H1 => le_trans _ _ _ H1 H0)
                               _
                               _
                               _
                               _).

    abstract (intros; apply proof_irrelevance).
  Defined.

  Let ChainCategory' (n : nat) : Category.
    simpl_definition_by_tac_and_exact (FullSubcategory OmegaCategory (fun m => m <= n)) ltac:(unfold Subcategory in *).
  Defined.
  Definition ChainCategory n := Eval cbv beta iota zeta delta [ChainCategory'] in ChainCategory' n.
End ChainCat.

Notation "[ n ]" := (ChainCategory n) : category_scope.
Notation "[ ∞ ]" := (OmegaCategory) : category_scope.
Notation "[ 'ω' ]" := (OmegaCategory) : category_scope.
