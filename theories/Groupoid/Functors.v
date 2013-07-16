Require Export Groupoid Functor SetCategory NaturalTransformation ComputableCat.
Require Import Common (*Adjoint*).

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section FunctorFromGroupoid.
  Context `{IsTrunc 1 X}.
  Variable D : PreCategory.
  Variable objOf : X -> D.

  Let FunctorFromGroupoid_MorphismOf s d (m : Morphism (Groupoid X) s d)
  : Morphism D (objOf s) (objOf d)
    := match m with
         | idpath => Identity _
       end.

  Local Ltac t :=
    intros; simpl in *; path_induction; simpl; apply symmetry; auto with morphism.

  Lemma FunctorFromGroupoid_FCompositionOf s d d'
        (m1 : Morphism (Groupoid X) s d)
        (m2 : Morphism (Groupoid X) d d')
  : FunctorFromGroupoid_MorphismOf (m2 ∘ m1) =
    FunctorFromGroupoid_MorphismOf m2 ∘ FunctorFromGroupoid_MorphismOf m1.
  Proof.
    t.
  Defined.

  Lemma FunctorFromGroupoid_FIdentityOf x
  : FunctorFromGroupoid_MorphismOf (Identity x) = Identity (objOf x).
  Proof.
    t.
  Defined.

  Global Arguments FunctorFromGroupoid_FCompositionOf / .
  Global Arguments FunctorFromGroupoid_FIdentityOf / .
  Global Opaque FunctorFromGroupoid_FIdentityOf FunctorFromGroupoid_FCompositionOf.

  Definition FunctorFromGroupoid : Functor (Groupoid X) D
    := @Build_Functor (Groupoid X)
                      D
                      objOf
                      FunctorFromGroupoid_MorphismOf
                      FunctorFromGroupoid_FCompositionOf
                      FunctorFromGroupoid_FIdentityOf.
End FunctorFromGroupoid.

Section Obj.
  Context `{fs : Funext}.
  Variable I : Type.
  Variable Index2Cat : I -> PreCategory.

  Local Notation build_obj_functor C D :=
    (@Build_Functor C D
                    (fun C' : I => (Object (Index2Cat C'); _))
                    (fun _ _ F => ObjectOf F)
                    (fun _ _ _ _ _ => idpath)
                    (fun _ => idpath)).

  Local Hint Extern 0 => solve [ apply_hyp ] : typeclass_instances.
  Local Hint Extern 0 => progress hnf in * |- : typeclass_instances.
  Typeclasses eauto := debug.
  Typeclasses Transparent ComputableCat Object.
  Set Printing All.
  Definition SetObjectFunctor `{H0 : forall i : I, IsTrunc 0 (Index2Cat i)}
  : Functor (@ComputableCat fs I Index2Cat
                            (fun C D : I =>
                               @Functor_IsTrunc fs (Index2Cat C) (Index2Cat D) 0
                                                (H0 D) (@MorphismIsHSet (Index2Cat D))))
            (@SetCat fs)
    := build_obj_functor (@ComputableCat fs I Index2Cat (fun C D : I =>
                                                           @Functor_IsTrunc fs (Index2Cat C) (Index2Cat D) 0
                                                                            (H0 D) (@MorphismIsHSet (Index2Cat D))))
                         (@SetCat fs).

    Set Printing Implicit. Show Proof.

    Grab Existential Variables.
    typeclasses eauto.

  Definition PropObjectFunctor `{H0 : forall i : I, IsHProp (Index2Cat i)}
    := build_obj_functor H0 (ComputableCat Index2Cat) PropCat.
End Obj.

Arguments SetObjectFunctor {_ _ _ _}.
Arguments PropObjectFunctor {_ _ _ _}.

Section Mor.
  Context `{Funext}.
  Variable I : Type.
  Variable Index2Cat : I -> PreCategory.
  Context `{H0 : forall i : I, IsHSet (Index2Cat i)}.

  Definition MorphismFunctor : Functor (ComputableCat Index2Cat) SetCat.
    let C := match goal with |- Functor ?C ?D => constr:(C) end in
    let D := match goal with |- Functor ?C ?D => constr:(D) end in
    refine (Build_Functor
              C D
              (fun C' => ({ sd : Index2Cat C' * Index2Cat C' & (Index2Cat C').(Morphism) (fst sd) (snd sd) }; _))
              (fun _ _ F => (fun sdm =>
                               existT (fun sd => Morphism _ (fst sd) (snd sd))
                                      (F (fst (projT1 sdm)), F (snd (projT1 sdm)))
                                      (MorphismOf F (s := fst (projT1 sdm)) (d := snd (projT1 sdm)) (projT2 sdm))
              ))
              (fun _ _ _ _ _ => idpath)
              _
           );
      simpl; intro; apply path_forall; intros [[? ?] ?]; exact idpath.
    Grab Existential Variables.
    Local Hint Extern 0 => cbv beta
      simpl.
    destruct sdm as [[? ?] ?].
    simpl.
    Show Proof.
    exact (match sdm as sdm return ((fst sdm.1, snd sdm.1); sdm.2) = sdm with existT _ _ => idpath end).
    apply path_forall.
    Show Pro
    simpl; intros.
    apply path_forall; intro.
    destruct x0 as [[? ?] ?].
    simpl.
    Show Proof.
    unfold compose; simpl.
    apply path_forall; intro; simpl.
    unfold compose; simpl.
    simpl; apply path_forall.


    build_mor_functor Index2Cat.
  Defined.

  Local Ltac build_mor_functor Index2Cat :=
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          (fun C' => { sd : Index2Cat C' * Index2Cat C' & (Index2Cat C').(Morphism) (fst sd) (snd sd) } )
          (fun _ _ F => (fun sdm =>
            existT (fun sd => Morphism _ (fst sd) (snd sd))
            (F (fst (projT1 sdm)), F (snd (projT1 sdm)))
            (MorphismOf F (s := fst (projT1 sdm)) (d := snd (projT1 sdm)) (projT2 sdm))
          ))
          _
          _
        )
    end;
    intros; simpl in *; try reflexivity;
      repeat (apply functional_extensionality_dep; intro);
        simpl_eq;
        reflexivity.

  Section type.
  End type.
End Mor.

Arguments MorphismFunctor {I Index2Cat}.

Section dom_cod.
  Local Ltac build_dom_cod fst_snd :=
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun _ => (fun sdf => fst_snd _ _ (projT1 sdf)))
          _
        )
    end;
    reflexivity.

  Section type.
    Variable I : Type.
    Variable Index2Cat : I -> Category.

    Definition DomainNaturalTransformation : NaturalTransformation (@MorphismFunctor _ Index2Cat) ObjectFunctor.
      build_dom_cod @fst.
    Defined.

    Definition CodomainNaturalTransformation : NaturalTransformation (@MorphismFunctor _ Index2Cat) ObjectFunctor.
      build_dom_cod @snd.
    Defined.
  End type.
End dom_cod.

Section InducedFunctor.
  Variable O : Type.
  Variable O' : Category.
  Variable f : O -> O'.

  Definition InducedGroupoidFunctor : Functor (Groupoid O) O'.
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          f
          (fun s d_ m => match m return _ with eq_refl => Identity (f s) end)
          _
          _
        )
    end;
    abstract (
      intros; simpl in *; repeat subst; trivial;
        repeat rewrite RightIdentity; repeat rewrite LeftIdentity;
          repeat rewrite Associativity;
            reflexivity
    ).
  Defined.
End InducedFunctor.

Section disc.
  Local Ltac t := simpl; intros; functor_eq;
    repeat (apply functional_extensionality_dep; intro);
      hnf in *; subst;
        auto.

  Definition GroupoidFunctor : Functor TypeCat Cat.
    refine (Build_Functor TypeCat Cat
      (fun O => Groupoid O : Category)
      (fun s d f => InducedGroupoidFunctor (Groupoid d) f)
      _
      _
    );
    abstract t.
  Defined.

  Definition GroupoidSetFunctor : Functor SetCat Cat.
    refine (Build_Functor SetCat Cat
      (fun O => Groupoid O : Category)
      (fun s d f => InducedGroupoidFunctor (Groupoid d) f)
      _
      _
    );
    abstract t.
  Defined.
End disc.

Section Adjoints.
  Lemma GroupoidObjectIdentity : ComposeFunctors ObjectFunctor GroupoidFunctor = IdentityFunctor _.
    functor_eq.
  Qed.

  Definition GroupoidObjectAdjunction : HomAdjunction GroupoidFunctor ObjectFunctor.
    match goal with
      | [ |- HomAdjunction ?F ?G ] =>
        refine (Build_HomAdjunction F G
          (fun _ _ F => (fun x => F x))
          _
          _
        )
    end;
    try abstract trivial;
      simpl; intros.
    exists (fun f => (InducedGroupoidFunctor _ f));
      abstract (repeat match goal with
                         | _ => progress trivial
                         | _ => progress repeat (apply functional_extensionality_dep; intro)
                         | _ => hnf in *;
                           match goal with
                             | [ H : _ = _ |- _ ] => destruct H; simpl in *
                           end
                         | _ => rewrite FIdentityOf
                         | _ => progress functor_eq
                       end).
  Defined.
End Adjoints.
