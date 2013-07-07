Require Export Functor NaturalTransformation.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section NaturalTransformationComposition.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variables F F' F'' : Functor C D.
  Variables G G' : Functor D E.

  (*
     We have the diagram
<<
          F
     C -------> D
          |
          |
          | T
          |
          V
     C -------> D
          F'
          |
          | T'
          |
          V
     C ------> D
          F''
>>

     And we want the commutative diagram
<<
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    F' m    V
     F' A -------> F' B
      |            |
      |            |
      | T' A       | T' B
      |            |
      V    F'' m   V
     F'' A ------> F'' B
>>
  *)

  Section NTComposeT.
    Variable T' : NaturalTransformation F' F''.
    Variable T : NaturalTransformation F F'.

    Let CO := fun c => T' c ∘ T c.

    Local Ltac t_fin :=
      match goal with
        | _ => apply Associativity
        | _ => symmetry; apply Associativity
      end.

    Local Ltac t :=
      match goal with
        | _ => t_fin
        | [ T : _, m : _ |- _ ] => case (Commutes T _ _ m); t_fin
        | [ T : _, m : _ |- _ ] => case (symmetry _ _ (Commutes T _ _ m)); t_fin
      end.

    Definition NTComposeT_Commutes s d (m : Morphism C s d)
    : CO d ∘ MorphismOf F m = MorphismOf F'' m ∘ CO s.
      transitivity (T' _ ∘ (MorphismOf F' m ∘ T _));
      [
      | transitivity ((T' _ ∘ MorphismOf F' m) ∘ T _);
        [
        | ]];
      t.
    Defined.

    Global Arguments NTComposeT_Commutes / .
    Global Opaque NTComposeT_Commutes.

    Definition NTComposeT
    : NaturalTransformation F F''
      := Build_NaturalTransformation F F''
                                     (fun c => T' c ∘ T c)
                                     NTComposeT_Commutes.
  End NTComposeT.

  (*
     We have the diagram

<<
          F          G
     C -------> D -------> E
          |          |
          |          |
          | T        | U
          |          |
          V          V
     C -------> D -------> E
          F'         G'
>>

     And we want the commutative diagram

<<
             G (F m)
     G (F A) -------> G (F B)
        |                |
        |                |
        | U (T A)        | U (T B)
        |                |
        V     G' (F' m)  V
     G' (F' A) -----> G' (F' B)
>>
  *)

  Section NTComposeF.
    Variable U : NaturalTransformation G G'.
    Variable T : NaturalTransformation F F'.

    Notation CO := (fun c => G'.(MorphismOf) (T c) ∘ U (F c)).

    Definition NTComposeF_Commutes s d (m : Morphism C s d)
    : CO d ∘ (MorphismOf G (MorphismOf F m))
      = MorphismOf G' (MorphismOf F' m) ∘ CO s.
    Proof.
      simpl.
      repeat try_associativity ltac:(rewrite <- ?Commutes; rewrite <- ?FCompositionOf).
      reflexivity.
    Defined.

    Global Arguments NTComposeF_Commutes / .
    Global Opaque NTComposeF_Commutes.

    Definition NTComposeF
    : NaturalTransformation (G ∘ F) (G' ∘ F')
      := Build_NaturalTransformation (G ∘ F) (G' ∘ F')
                                     CO
                                     NTComposeF_Commutes.
  End NTComposeF.
End NaturalTransformationComposition.

(** As per Wikipedia (http://en.wikipedia.org/wiki/2-category), we use
    [∘₀] to denote composition along 0-cells (functors), and [∘₁] to
    denote composition along 1-cells (natural transformations). *)

Infix "'o0'" := NTComposeF : natural_transformation_scope.
Infix "'o1'" := NTComposeT : natural_transformation_scope.
Infix "∘₀" := NTComposeF : natural_transformation_scope.
Infix "∘₁" := NTComposeT : natural_transformation_scope.
