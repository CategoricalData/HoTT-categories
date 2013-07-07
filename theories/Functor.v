Require Export PreCategory.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section Functor.
  Variable C : PreCategory.
  Variable D : PreCategory.

  (** Quoting from the lecture notes for 18.705, Commutative Algebra:

      A map of categories is known as a functor. Namely, given
      categories [C] and [C'], a (covariant) functor [F : C -> C'] is
      a rule that assigns to each object [A] of [C] an object [F A] of
      [C'] and to each map [m : A -> B] of [C] a map [F m : F A -> F
      B] of [C'] preserving composition and identity; that is,

     (1) [F (m' ∘ m) = (F m') ∘ (F m)] for maps [m : A -> B] and [m' :
         B -> C] of [C], and

     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A]
         is the identity morphism of [A]. **)

  Record Functor :=
    {
      ObjectOf :> C -> D;
      MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
      FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
                          MorphismOf _ _ (m2 ∘ m1) = (MorphismOf _ _ m2) ∘ (MorphismOf _ _ m1);
      FIdentityOf : forall x, MorphismOf _ _ (Identity x) = Identity (ObjectOf x)
    }.
End Functor.

Bind Scope functor_scope with Functor.

Create HintDb functor discriminated.

Arguments Functor C D.
Arguments ObjectOf {C%category D%category} F%functor c%object : rename, simpl nomatch.
Arguments MorphismOf [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.

Arguments FCompositionOf [C D] F _ _ _ _ _ : rename.
Arguments FIdentityOf [C D] F _ : rename.

Notation "F ₀ x" := (ObjectOf F x) : object_scope.
Notation "F ₁ m" := (MorphismOf F m) : morphism_scope.

Hint Resolve @FCompositionOf @FIdentityOf : category functor.
Hint Rewrite @FIdentityOf : category.
Hint Rewrite @FIdentityOf : functor.

Section FunctorComposition.
  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variable G : Functor D E.
  Variable F : Functor C D.

  Local Notation CObjectOf c := (G (F c)).
  Local Notation CMorphismOf m := (MorphismOf G (MorphismOf F m)).
  (* We use [rewrite <-] because the resulting [match]es look better. *)
  Let ComposeFunctors_FCompositionOf' s d d' (m1 : Morphism C s d) (m2 : Morphism C d d')
  : CMorphismOf (m2 ∘ m1) = CMorphismOf m2 ∘ CMorphismOf m1.
  Proof.
    rewrite <- !FCompositionOf.
    reflexivity.
  Defined.
  Definition ComposeFunctors_FCompositionOf s d d' m1 m2
    := Eval cbv beta iota zeta delta [ComposeFunctors_FCompositionOf' internal_paths_rew] in
        @ComposeFunctors_FCompositionOf' s d d' m1 m2.

  Let ComposeFunctors_FIdentityOf' x
  : CMorphismOf (Identity x) = Identity (CObjectOf x).
  Proof.
    rewrite <- !FIdentityOf.
    reflexivity.
  Defined.
  Definition ComposeFunctors_FIdentityOf x
    := Eval cbv beta iota zeta delta [ComposeFunctors_FIdentityOf' internal_paths_rew] in
        @ComposeFunctors_FIdentityOf' x.

  Global Arguments ComposeFunctors_FCompositionOf / .
  Global Arguments ComposeFunctors_FIdentityOf / .
  Global Opaque ComposeFunctors_FCompositionOf ComposeFunctors_FIdentityOf.

  Definition ComposeFunctors : Functor C E
    := Build_Functor C E
                     (fun c => G (F c))
                     (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
                     ComposeFunctors_FCompositionOf
                     ComposeFunctors_FIdentityOf.
End FunctorComposition.

Infix "'o'" := ComposeFunctors : functor_scope.
Infix "∘" := ComposeFunctors : functor_scope.

Section IdentityFunctor.
  (** There is an identity functor.  It does the obvious thing. *)
  Definition IdentityFunctor C : Functor C C
    := Build_Functor C C
                     (fun x => x)
                     (fun _ _ x => x)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End IdentityFunctor.

Global Arguments ComposeFunctors_FCompositionOf / .
Global Arguments ComposeFunctors_FIdentityOf / .

Local Ltac functor_t :=
  destruct_head Functor; expand; f_ap;
  repeat (apply path_forall; intro);
  try refine (center _).

Section IdentityFunctorLemmas.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Context `{Funext}.

  Local Open Scope functor_scope.

  Local Transparent ComposeFunctors_FIdentityOf.
  Local Transparent ComposeFunctors_FCompositionOf.

  Lemma LeftIdentityFunctor (F : Functor D C) : IdentityFunctor _ ∘ F = F.
    functor_t.
  Qed.

  Lemma RightIdentityFunctor (F : Functor C D) : F ∘ IdentityFunctor _ = F.
    functor_t.
  Qed.
End IdentityFunctorLemmas.

Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : category.
Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : functor.
Hint Immediate @LeftIdentityFunctor @RightIdentityFunctor : category functor.

Section FunctorCompositionLemmas.
  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Context `{H0 : Funext}.

  Local Open Scope functor_scope.

  Local Transparent ComposeFunctors_FCompositionOf.
  Local Transparent ComposeFunctors_FIdentityOf.

  Lemma ComposeFunctorsAssociativity (F : Functor B C) (G : Functor C D) (H : Functor D E)
  : (H ∘ G) ∘ F = H ∘ (G ∘ F).
  Proof.
    functor_t.
  Qed.
End FunctorCompositionLemmas.

Hint Resolve @ComposeFunctorsAssociativity : category functor.
