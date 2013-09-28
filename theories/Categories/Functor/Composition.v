Require Export Category.Core Functor.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

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

Infix "o" := ComposeFunctors : functor_scope.
Infix "∘" := ComposeFunctors : functor_scope.

Global Arguments ComposeFunctors_FCompositionOf / .
Global Arguments ComposeFunctors_FIdentityOf / .
