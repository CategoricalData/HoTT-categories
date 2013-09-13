Require Export Category.Core Functor.Core Functor.Composition Functor.Identity.
Require Import Common Functor.Attributes Functor.Equality.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section sigT_obj_mor.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Local Notation obj := (sigT Pobj).

  Variable Pmor : forall s d : obj, Morphism A s.1 d.1 -> Type.

  Local Notation mor s d := (sigT (Pmor s d)).
  Context `(HPmor : forall s d, IsHSet (mor s d)).

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 ∘ m2).

  Local Notation identity x := (@Identity A x.1; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 ∘ m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_Associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).

  Hypothesis P_LeftIdentity
  : forall a b (f : mor a b),
      compose (identity b) f = f.

  Hypothesis P_RightIdentity
  : forall a b (f : mor a b),
      compose f (identity a) = f.

  Definition Category_sigT : PreCategory.
  Proof.
    refine (@Build_PreCategory
              obj
              (fun s d => mor s d)
              (fun x => identity x)
              (fun s d d' m1 m2 => compose m1 m2)
              _
              _
              _
              _);
    assumption.
  Defined.

  Definition projT1_functor : Functor Category_sigT A
    := Build_Functor
         Category_sigT A
         (@projT1 _ _)
         (fun _ _ => @projT1 _ _)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).
End sigT_obj_mor.

Arguments projT1_functor {A Pobj Pmor HPmor Pidentity Pcompose P_Associativity P_LeftIdentity P_RightIdentity}.

Section sigT_obj_mor_hProp.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Local Notation obj := (sigT Pobj).

  Variable Pmor : forall s d : obj, Morphism A s.1 d.1 -> Type.

  Local Notation mor s d := (sigT (Pmor s d)).
  Context `(HPmor : forall s d m, IsHProp (Pmor s d m)).

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 ∘ m2).

  Local Notation identity x := (@Identity A x.1; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 ∘ m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Local Ltac t ex_tac :=
    intros;
    simpl;
    apply path_sigma_uncurried;
    simpl;
    ex_tac;
    apply allpath_hprop.

  Let P_Associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).
  Proof.
    abstract t ltac:(exists (Associativity _ _ _ _ _ _ _ _)).
  Qed.

  Let P_LeftIdentity
  : forall a b (f : mor a b),
      compose (identity b) f = f.
  Proof.
    subst_body.
    abstract t ltac:(exists (LeftIdentity _ _ _ _)).
  Defined.

  Let P_RightIdentity
  : forall a b (f : mor a b),
      compose f (identity a) = f.
  Proof.
    subst_body.
    abstract t ltac:(exists (RightIdentity _ _ _ _)).
  Defined.

  Definition Category_sig : PreCategory
    := Eval cbv delta [P_Associativity P_LeftIdentity P_RightIdentity]
      in @Category_sigT A Pobj Pmor _ Pidentity Pcompose P_Associativity P_LeftIdentity P_RightIdentity.

  Definition proj1_sig_functor : Functor Category_sig A
    := projT1_functor.
End sigT_obj_mor_hProp.

Arguments proj1_sig_functor {A Pobj Pmor HPmor Pidentity Pcompose}.

Section sigT_obj.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Definition Category_sigT_obj : PreCategory.
  Proof.
    refine (@Build_PreCategory
              (sigT Pobj)
              (fun s d => A.(Morphism) (projT1 s) (projT1 d))
              (fun x => Identity (C := A) (projT1 x))
              (fun s d d' m1 m2 => Compose (C := A) m1 m2)
              _
              _
              _
              _
           );
    simpl; intros; auto with category.
  Defined.

  Definition projT1_obj_functor : Functor Category_sigT_obj A
    := Build_Functor
         Category_sigT_obj A
         (@projT1 _ _)
         (fun s d m => m)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition Category_sigT_obj_as_sigT : PreCategory
    := @Category_sig A Pobj (fun _ _ _ => Unit) _ (fun _ => tt) (fun _ _ _ _ _ _ _ => tt).

  Definition sigT_functor_obj : Functor Category_sigT_obj_as_sigT Category_sigT_obj
    := Build_Functor Category_sigT_obj_as_sigT Category_sigT_obj
                     (fun x => x)
                     (fun _ _ => @projT1 _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition sigT_functor_obj_inv : Functor Category_sigT_obj Category_sigT_obj_as_sigT
    := Build_Functor Category_sigT_obj Category_sigT_obj_as_sigT
                     (fun x => x)
                     (fun _ _ m => existT _ m tt)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Local Open Scope functor_scope.

  Lemma sigT_obj_eq `{Funext}
  : sigT_functor_obj ∘ sigT_functor_obj_inv = IdentityFunctor _
    /\ sigT_functor_obj_inv ∘ sigT_functor_obj = IdentityFunctor _.
  Proof.
    split; functor_eq.
    repeat (apply path_forall; intro).
    destruct_head_hnf @sigT.
    destruct_head_hnf Unit.
    reflexivity.
  Qed.

  Local Transparent ComposeFunctors_FCompositionOf ComposeFunctors_FIdentityOf.

  Definition sigT_obj_compat : projT1_obj_functor ∘ sigT_functor_obj = projT1_functor
    := idpath.
End sigT_obj.

Arguments projT1_obj_functor {A Pobj}.

Section sigT_mor.
  Variable A : PreCategory.
  Variable Pmor : forall s d, Morphism A s d -> Type.

  Local Notation mor s d := (sigT (Pmor s d)).
  Context `(HPmor : forall s d, IsHSet (mor s d)).

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 ∘ m2).

  Local Notation identity x := (@Identity A x; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 ∘ m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_Associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).

  Hypothesis P_LeftIdentity
  : forall a b (f : mor a b),
      compose (identity b) f = f.

  Hypothesis P_RightIdentity
  : forall a b (f : mor a b),
      compose f (identity a) = f.

  Definition Category_sigT_mor : PreCategory.
  Proof.
    refine (@Build_PreCategory
              (Object A)
              (fun s d => mor s d)
              (fun x => identity x)
              (fun s d d' m1 m2 => compose m1 m2)
              _
              _
              _
              _);
    assumption.
  Defined.

  Definition projT1_mor_functor : Functor Category_sigT_mor A
    := Build_Functor
         Category_sigT_mor A
         idmap
         (fun _ _ => @projT1 _ _)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition Category_sigT_mor_as_sigT : PreCategory.
  Proof.
    refine (@Category_sigT A (fun _ => Unit) (fun s d => @Pmor (projT1 s) (projT1 d)) _ (fun _ => Pidentity _) (fun _ _ _ _ _ m1 m2 => Pcompose m1 m2) _ _ _);
    intros; trivial.
  Defined.

  Definition sigT_functor_mor : Functor Category_sigT_mor_as_sigT Category_sigT_mor
    := Build_Functor
         Category_sigT_mor_as_sigT Category_sigT_mor
         (@projT1 _ _)
         (fun _ _ => idmap)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition sigT_functor_mor_inv : Functor Category_sigT_mor Category_sigT_mor_as_sigT
    := Build_Functor
         Category_sigT_mor Category_sigT_mor_as_sigT
         (fun x => existT _ x tt)
         (fun _ _ => idmap)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Local Open Scope functor_scope.

  Lemma sigT_mor_eq `{Funext}
  : sigT_functor_mor ∘ sigT_functor_mor_inv = IdentityFunctor _
    /\ sigT_functor_mor_inv ∘ sigT_functor_mor = IdentityFunctor _.
  Proof.
    split; functor_eq; simpl.
    refine (existT
              _
              (path_forall
                 _
                 _
                 (fun x
                  => match x with
                       | (_; tt) => _
                     end))
              _).
    instantiate (1 := idpath).
    repeat (apply path_forall; intro).
    destruct_head @sigT.
    destruct_head Unit.
    rewrite !transport_forall_constant.
      (* pull out the parts of the goal to use [path_forall_recr_beta] *)
      let F := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(F) end in
      let H := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(H) end in
      let X := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(X) end in
      let T := match goal with |- appcontext[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(T) end in
      let t0 := fresh "t0" in
      let t1 := fresh "t1" in
      let T1 := lazymatch type of F with (?T -> _) -> _ => constr:(T) end in
      evar (t1 : T1);
      let T0 := lazymatch type of F with (forall a : ?A, @?B a) -> ?C => constr:((forall a : A, B a) -> B t1 -> C) end in
      evar (t0 : T0);
      (* make a dummy goal to figure out the functional form of [P] in [@transport _ P] *)
      let dummy := fresh in
      assert (dummy : forall x0, F x0 = t0 x0 (x0 t1));
      [ let x0 := fresh in
        intro x0;
          simpl in *;
          let GL0 := lazymatch goal with |- ?GL0 = _ => constr:(GL0) end in
          let GL0' := fresh in
          let GL1' := fresh in
          set (GL0' := GL0);
            (* find [x0] applied to some argument, and note the argument *)
            let arg := match GL0 with appcontext[x0 ?arg] => constr:(arg) end in
            assert (t1 = arg) by (subst t1; reflexivity); subst t1;
            pattern (x0 arg) in GL0';
            match goal with
              | [ GL0'' := ?GR _ |- _ ] => constr_eq GL0' GL0'';
                                          pose GR as GL1'
            end;
            (* remove the other instances of [x0], and figure out the shape *)
            pattern x0 in GL1';
            match goal with
              | [ GL1'' := ?GR _ |- _ ] => constr_eq GL1' GL1'';
                                          assert (t0 = GR)
            end;
            subst t0; [ reflexivity | reflexivity ]
      | clear dummy ];
      let p := fresh in
      pose (@path_forall_recr_beta H X T t1 t0) as p;
      simpl in *;
        rewrite p;
      subst t0 t1 p.
          Print Universes.
          rewrite transport_path_prod'_beta'.
    Print Ltac transport_path_forall_hammer.
    simpl.
    SearchAbout transport
    SearchAbout transport path_forall.
  Qed.

  Lemma sigT_mor_compat : ComposeFunctors projT1_mor_functor sigT_functor_mor = projT1_functor.
    functor_eq.
  Qed.
End sigT_mor.

Arguments projT1_mor_functor {A Pmor Pidentity Pcompose P_Associativity P_LeftIdentity P_RightIdentity}.
