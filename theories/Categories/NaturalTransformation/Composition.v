Require Export Functor.Composition NaturalTransformation.Core.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section NaturalTransformationComposition.

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
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variables F F' F'' : Functor C D.

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

  Local Ltac whisker_t :=
    simpl;
    repeat first [ apply Commutes
                 | apply ap
                 | progress (etransitivity; try apply FCompositionOf); []
                 | progress (etransitivity; try (symmetry; apply FCompositionOf)); [] ].

  Section NTWhisker.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable E : PreCategory.

    Section L.
      Variable F : Functor D E.
      Variables G G' : Functor C D.
      Variable T : NaturalTransformation G G'.

      Local Notation CO c := (MorphismOf F (T c)).

      Definition NTWhiskerL_Commutes s d (m : Morphism C s d)
      : F ₁ (T d) ∘ (F ∘ G) ₁ m = (F ∘ G') ₁ m ∘ F ₁ (T s).
      Proof.
        whisker_t.
      Defined.

      Global Arguments NTWhiskerL_Commutes / .
      Global Opaque NTWhiskerL_Commutes.

      Definition NTWhiskerL
        := Build_NaturalTransformation (F ∘ G) (F ∘ G')
                                       (fun c => CO c)
                                       NTWhiskerL_Commutes.
    End L.

    Section R.
      Variables F F' : Functor D E.
      Variable T : NaturalTransformation F F'.
      Variable G : Functor C D.

      Local Notation CO c := (T (G c)).

      Definition NTWhiskerR_Commutes s d (m : Morphism C s d)
      : T (G d) ∘ (F ∘ G) ₁ m = (F' ∘ G) ₁ m ∘ T (G s).
      Proof.
        whisker_t.
      Defined.

      Global Arguments NTWhiskerR_Commutes / .
      Global Opaque NTWhiskerR_Commutes.

      Definition NTWhiskerR
        := Build_NaturalTransformation (F ∘ G) (F' ∘ G)
                                       (fun c => CO c)
                                       NTWhiskerR_Commutes.
    End R.
  End NTWhisker.
End NaturalTransformationComposition.

Section notations.
  (** We do some black magic with typeclasses to make notations play
      well.  The cost is extra verbosity, but it will all disappear
      with [simpl]. *)

  Global Class NTC_Composable A B (a : A) (b : B) (T : Type) (term : T) := {}.

  Definition NTC_Composable_term `{@NTC_Composable A B a b T term} := term.
  Global Arguments NTC_Composable_term / .

  Global Instance NTC_FunctorComposition C D E (F : Functor D E) (G : Functor C D)
  : NTC_Composable F G (ComposeFunctors F G) | 1000.

  Global Instance NTC_NTComposition C D (F F' F'' : Functor C D)
         (T' : NaturalTransformation F' F'') (T : NaturalTransformation F F')
  : NTC_Composable T' T (NTComposeT T' T) | 10.

  Global Instance NTC_NTWhiskerL C D E (F : Functor D E) (G G' : Functor C D)
         (T : NaturalTransformation G G')
  : NTC_Composable F T (NTWhiskerL F T) | 100.

  Global Instance NTC_NTWhiskerR C D E (F F' : Functor D E)
         (T : NaturalTransformation F F')
         (G : Functor C D)
  : NTC_Composable T G (NTWhiskerR T G) | 100.
End notations.

Hint Unfold NTC_Composable_term : typeclass_instances.

(* ASCII notations *)
(* Set some notations for printing *)
Infix "o" := NTComposeT : natural_transformation_scope.
Infix "o" := NTWhiskerL : natural_transformation_scope.
Infix "o" := NTWhiskerR : natural_transformation_scope.
Infix "o" := ComposeFunctors : natural_transformation_scope.
(* Notation for parsing *)
Notation "T 'o' U"
  := (@NTC_Composable_term _ _ T%natural_transformation U%natural_transformation _ _ _)
     : natural_transformation_scope.


(* Unicode Notations *)
(* Set some notations for printing *)
Infix "∘" := NTComposeT : natural_transformation_scope.
Infix "∘" := NTWhiskerL : natural_transformation_scope.
Infix "∘" := NTWhiskerR : natural_transformation_scope.
Infix "∘" := ComposeFunctors : natural_transformation_scope.
(* Notation for parsing *)
Notation "T ∘ U"
  := (@NTC_Composable_term _ _ T%natural_transformation U%natural_transformation _ _ _)
     : natural_transformation_scope.

(*
Unset Printing Notations.
Eval simpl in (_ ∘ _)%natural_transformation. (* should be NTComposeT *)
Eval simpl in (_ ∘ (_ : Functor _ _))%natural_transformation. (* should be NTWhiskerR *)
Eval simpl in ((_ : Functor _ _) ∘ _)%natural_transformation. (* should be NTWhiskerL *)
Eval simpl in ((_ : Functor _ _) ∘ (_ : Functor _ _))%natural_transformation. (* should be ComposeFunctors *)
Check (fun C D E (F : Functor D E) (G : Functor C D) => (F ∘ G)%natural_transformation).
Eval simpl in (fun C D E (F : Functor D E) (G : Functor C D) => (F ∘ G)%natural_transformation).
Check (fun B C D E (F : Functor D E) (G : Functor C D) (H : Functor B C) => (F ∘ G ∘ H)%natural_transformation).
Eval simpl in (fun B C D E (F : Functor D E) (G : Functor C D) (H : Functor B C) => (F ∘ G ∘ H)%natural_transformation).
Check (fun C D E (F : Functor D E) (G G' : Functor C D) (T : NaturalTransformation G G') => (F ∘ T)%natural_transformation).
Eval simpl in (fun C D E (F : Functor D E) (G G' : Functor C D) (T : NaturalTransformation G G') => (F ∘ T)%natural_transformation).
*)
