Require Export Functor.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section NaturalTransformation.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of functors is known as a natural transformation. Namely,
     given two functors [F : C -> D], [G : C -> D], a natural
     transformation [T: F -> G] is a collection of maps [T A : F A ->
     G A], one for each object [A] of [C], such that [(T B) ∘ (F m) =
     (G m) ∘ (T A)] for every map [m : A -> B] of [C]; that is, the
     following diagram is commutative:

<<
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    G m     V
     G A --------> G B
>>
     **)

  Record NaturalTransformation :=
    Build_NaturalTransformation' {
        ComponentsOf :> forall c, D.(Morphism) (F c) (G c);
        Commutes : forall s d (m : C.(Morphism) s d),
                     ComponentsOf d ∘ F.(MorphismOf) m = G.(MorphismOf) m ∘ ComponentsOf s;
        (* We require the following symmetrized version so we don't
           need functional extensionality to prove [(T ^op) ^op =
           T]. *)
        Commutes_sym : forall s d (m : C.(Morphism) s d),
                         G.(MorphismOf) m ∘ ComponentsOf s = ComponentsOf d ∘ F.(MorphismOf) m
      }.

  Definition Build_NaturalTransformation CO COM
    := Build_NaturalTransformation' CO COM (fun _ _ _ => symmetry _ _ (COM _ _ _)).
End NaturalTransformation.

Bind Scope natural_transformation_scope with NaturalTransformation.

Create HintDb natural_transformation discriminated.

Arguments ComponentsOf {C%category D%category F%functor G%functor} T%natural_transformation c%object : rename, simpl nomatch.
Arguments Commutes [C D F G] T _ _ _ : rename.

Hint Resolve @Commutes : category natural_transformation.
