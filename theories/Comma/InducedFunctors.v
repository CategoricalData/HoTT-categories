Require Export Comma.Projection Cat Category.Duals FunctorCategory Category.Product.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

Section CommaCategoryInducedFunctor.
  Context `{Funext}.
  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.

  Definition CommaCategoryInducedFunctor_ObjectOf s d
             (m : Morphism ([A, C]^op * [B, C]) s d)
             (x : fst s ↓ snd s)
  : (fst d ↓ snd d)
    := Build_CommaCategory_Object
         (fst d) (snd d)
         (CCO_a x)
         (CCO_b x)
         ((snd m) (CCO_b x) ∘ CCO_f x ∘ (fst m) (CCO_a x)).

  Definition CommaCategoryInducedFunctor_MorphismOf s d m s0 d0
             (m0 : Morphism (fst s ↓ snd s) s0 d0)
  : Morphism (fst d ↓ snd d)
             (@CommaCategoryInducedFunctor_ObjectOf s d m s0)
             (@CommaCategoryInducedFunctor_ObjectOf s d m d0).
  Proof.
    simpl.
    let s := match goal with |- CommaCategory_Morphism ?s ?d => constr:(s) end in
    let d := match goal with |- CommaCategory_Morphism ?s ?d => constr:(d) end in
    refine (Build_CommaCategory_Morphism s d (CCM_g m0) (CCM_h m0) _);
      simpl in *; clear.
    abstract (
        destruct_head prod;
        destruct_head CommaCategory_Morphism;
        destruct_head CommaCategory_Object;
        simpl in *;
          repeat try_associativity ltac:(rewrite <- !Commutes || (progress f_ap));
        repeat try_associativity ltac:(rewrite !Commutes || (progress f_ap));
        assumption
      ). (* 2.465 s *)
  Defined.

  Definition CommaCategoryInducedFunctor s d
             (m : Morphism ([A, C]^op * [B, C]) s d)
  : Functor (fst s ↓ snd s) (fst d ↓ snd d).
  Proof.
    refine (Build_Functor (fst s ↓ snd s) (fst d ↓ snd d)
                          (@CommaCategoryInducedFunctor_ObjectOf s d m)
                          (@CommaCategoryInducedFunctor_MorphismOf s d m)
                          _
                          _
           );
    abstract (
        intros; apply CommaCategory_Morphism_eq; reflexivity
      ).
  Defined.
End CommaCategoryInducedFunctor.

Section SliceCategoryInducedFunctor.
  Context `{Funext}.
  Variable C : PreCategory.

  Section Slice_Coslice.
    Variable D : PreCategory.

    (* TODO(jgross): See if this can be recast as an exponential law functor about how Cat ^ 1 is isomorphic to Cat, or something *)
    Definition SliceCategoryInducedFunctor_NT s d (m : Morphism D s d)
    : NaturalTransformation (FunctorFromTerminal D s)
                            (FunctorFromTerminal D d).
    Proof.
      exists (fun _ : Unit => m);
      simpl; intros; clear;
      abstract (autorewrite with category; reflexivity).
    Defined.

    Variable F : Functor C D.
    Variable a : D.

    Section Slice.
      Definition SliceCategoryInducedFunctor F' a' (m : Morphism D a a') (T : NaturalTransformation F' F)
      : Functor (F ↓ a) (F' ↓ a')
        := CommaCategoryInducedFunctor (s := (F, FunctorFromTerminal D a))
                                       (d := (F', FunctorFromTerminal D a'))
                                       (T, @SliceCategoryInducedFunctor_NT a a' m).

      Definition SliceCategoryNTInducedFunctor F' T := @SliceCategoryInducedFunctor F' a (Identity _) T.
      Definition SliceCategoryMorphismInducedFunctor a' m := @SliceCategoryInducedFunctor F a' m (IdentityNaturalTransformation _).
    End Slice.

    Section Coslice.
      Definition CosliceCategoryInducedFunctor F' a' (m : Morphism D a' a) (T : NaturalTransformation F F')
      : Functor (a ↓ F) (a' ↓ F')
        := CommaCategoryInducedFunctor (s := (FunctorFromTerminal D a, F))
                                       (d := (FunctorFromTerminal D a', F'))
                                       (@SliceCategoryInducedFunctor_NT a' a m, T).

      Definition CosliceCategoryNTInducedFunctor F' T := @CosliceCategoryInducedFunctor F' a (Identity _) T.
      Definition CosliceCategoryMorphismInducedFunctor a' m := @CosliceCategoryInducedFunctor F a' m (IdentityNaturalTransformation _).
    End Coslice.
  End Slice_Coslice.

  Definition SliceCategoryOverInducedFunctor a a' (m : Morphism C a a') : Functor (C / a) (C / a')
    := Eval hnf in SliceCategoryMorphismInducedFunctor _ _ _ m.
  Definition CosliceCategoryOverInducedFunctor a a' (m : Morphism C a' a) : Functor (a \ C) (a' \ C)
    := Eval hnf in CosliceCategoryMorphismInducedFunctor _ _ _ m.
End SliceCategoryInducedFunctor.

Section CatOverInducedFunctor.
  Context `{Funext}.
  Variable P : PreCategory -> Type.
  Context `{forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (SubPreCat P).

  Definition CatOverInducedFunctor a a' (m : Morphism Cat a a') : Functor (Cat / a) (Cat / a')
    := SliceCategoryOverInducedFunctor Cat a a' m.

  Definition OverCatInducedFunctor a a' (m : Morphism Cat a' a) : Functor (a \ Cat) (a' \ Cat)
    := CosliceCategoryOverInducedFunctor Cat a a' m.
End CatOverInducedFunctor.
