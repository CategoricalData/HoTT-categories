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

  Local Notation build_obj_functor_evar C D typ build :=
    (@Build_Functor C D
                    (fun C' : I => build (Object (Index2Cat C')) (typ C'))
                    (fun _ _ F => ObjectOf F)
                    (fun _ _ _ _ _ => idpath)
                    (fun _ => idpath)).

  Local Ltac build_obj_functor build :=
    let C := match goal with |- Functor ?C ?D => constr:(C) end in
    let D := match goal with |- Functor ?C ?D => constr:(D) end in
    let T := fresh in
    let t := fresh in
    evar (T : Type);
      cut T; subst T;
      [ intro t;
        exact (build_obj_functor_evar C D t build)
      | ];
      instantiate;
      typeclasses eauto.

  Definition SetObjectFunctor `{H0 : forall i : I, IsTrunc 0 (Index2Cat i)}
  : Functor (ComputableCat Index2Cat) SetCat.
  Proof.
    build_obj_functor BuildhSet.
  Defined.

  (** We need to force the shape of the computable cat, or else
      [PropObjectFunctor] and [PropMorphismFunctor] pick up different
      instances.  Pick this typeclass instance arbitrarily. *)

  Definition PropObjectFunctor `{H0 : forall i : I, IsHProp (Index2Cat i)}
  : Functor (@ComputableCat _ _ Index2Cat (fun _ _ => Functor_IsTrunc _ _)) PropCat.
  Proof.
    build_obj_functor hp.
  Defined.
End Obj.

Arguments SetObjectFunctor {_ _ _ _}.
Arguments PropObjectFunctor {_ _ _ _}.

Section Mor.
  Context `{Funext}.
  Variable I : Type.
  Variable Index2Cat : I -> PreCategory.

  Local Ltac build_mor_functor build :=
    let C := match goal with |- Functor ?C ?D => constr:(C) end in
    let D := match goal with |- Functor ?C ?D => constr:(D) end in
    refine (Build_Functor
              C D
              (fun C' => build { sd : Index2Cat C' * Index2Cat C' & Morphism (Index2Cat C') (fst sd) (snd sd) } _)
              (fun _ _ F => (fun sdm =>
                               existT (fun sd => Morphism _ (fst sd) (snd sd))
                                      (F (fst (projT1 sdm)), F (snd (projT1 sdm)))
                                      (MorphismOf F (s := fst (projT1 sdm)) (d := snd (projT1 sdm)) (projT2 sdm))))
              (fun _ _ _ _ _ => idpath)
              _);
      simpl; intro; apply path_forall; intros [[? ?] ?]; exact idpath.

  Definition SetMorphismFunctor `{forall i : I, IsHSet (Index2Cat i)}
  : Functor (ComputableCat Index2Cat) SetCat.
  Proof.
    build_mor_functor BuildhSet.
  Defined.

  Definition PropMorphismFunctor `{forall i : I, IsHProp (Index2Cat i)}
             `{forall i s d, IsHProp (Morphism (Index2Cat i) s d)}
  : Functor (@ComputableCat _ _ Index2Cat (fun _ _ => Functor_IsTrunc _ _)) PropCat.
  Proof.
    build_mor_functor hp.
  Defined.
End Mor.

Arguments SetMorphismFunctor {_ _ _ _}.
Arguments PropMorphismFunctor {_ _ _ _ _}.

Section dom_cod.
  Context `{Funext}.
  Variable I : Type.
  Variable Index2Cat : I -> PreCategory.

  Local Notation build_dom_cod F G fst_snd :=
    (*let F := match goal with |- NaturalTransformation ?F ?G => constr:(F) end in
    let G := match goal with |- NaturalTransformation ?F ?G => constr:(G) end in*)
    (Build_NaturalTransformation
       F G
       (fun _ => (fun sdf => fst_snd _ _ (projT1 sdf)))
       (fun _ _ _ => idpath)).

  Definition SetDomainNaturalTransformation
             `{forall i, IsHSet (Index2Cat i)}
    := build_dom_cod (SetMorphismFunctor (Index2Cat := Index2Cat))
                     SetObjectFunctor
                     (@fst).

  Definition SetCodomainNaturalTransformation
             `{forall i, IsHSet (Index2Cat i)}
    := build_dom_cod (SetMorphismFunctor (Index2Cat := Index2Cat))
                     SetObjectFunctor
                     (@snd).

  Definition PropDomainNaturalTransformation
             `{forall i, IsHProp (Index2Cat i)}
             `{forall i s d, IsHProp (Morphism (Index2Cat i) s d)}
    := build_dom_cod (PropMorphismFunctor (Index2Cat := Index2Cat))
                     PropObjectFunctor
                     (@fst).

  Definition PropCodomainNaturalTransformation
             `{forall i, IsHProp (Index2Cat i)}
             `{forall i s d, IsHProp (Morphism (Index2Cat i) s d)}
    := build_dom_cod (PropMorphismFunctor (Index2Cat := Index2Cat))
                     PropObjectFunctor
                     (@snd).
End dom_cod.
(*
Section disc.
(*  Local Ltac t := simpl; intros; functor_eq;
    repeat (apply functional_extensionality_dep; intro);
      hnf in *; subst;
        auto.*)

  Definition DiscreteSetFunctor : Functor SetCat Cat.
    refine (Build_Functor TypeCat Cat
      (fun O => Groupoid O : PreCategory)
      (fun s d f => InducedGroupoidFunctor (Groupoid d) f)
      _
      _
    );
    abstract t.
  Defined.

  Definition GroupoidSetFunctor : Functor SetCat Cat.
    refine (Build_Functor SetCat Cat
      (fun O => Groupoid O : PreCategory)
      (fun s d f => InducedGroupoidFunctor (Groupoid d) f)
      _
      _
    );
    abstract t.
  Defined.
End disc.
*)(*
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
*)
