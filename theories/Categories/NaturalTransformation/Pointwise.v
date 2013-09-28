Require Export FunctorCategory Functor.Pointwise.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.

Section PointwiseNaturalTransformation.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable C' : PreCategory.
  Variable D' : PreCategory.

  Local Ltac t :=
    nt_eq; simpl;
    rewrite <- ?FCompositionOf;
    try apply ap;
    first [ apply Commutes
          | symmetry; apply Commutes ].

  Definition PointwiseNaturalTransformation1
             (F G : Functor C D)
             (T : NaturalTransformation F G)
             (F' : Functor C' D')
  : NaturalTransformation [F, F'] [G, F'].
  Proof.
    refine (Build_NaturalTransformation
              [F, F'] [G, F']
              (fun f : Object [D, C'] => F' ∘ f ∘ T)%natural_transformation
              _).
    abstract t.
  Defined.

  Definition PointwiseNaturalTransformation2
             (F : Functor C D)
             (F' G' : Functor C' D')
             (T' : NaturalTransformation F' G')
  : NaturalTransformation [F, F'] [F, G'].
  Proof.
    refine (Build_NaturalTransformation
              [F, F'] [F, G']
              (fun f : Object [D, C'] => T' ∘ f ∘ F)%natural_transformation
              _).
    abstract t.
  Defined.
End PointwiseNaturalTransformation.

Section notations.
  (** We do some black magic with typeclasses to make notations play
      well.  The cost is extra verbosity, but it will all disappear
      with [simpl]. *)

  Global Class PNT `{Funext} A B (a : A) (b : B) (T : Type) (term : T) := {}.

  Definition PNT_term `{@PNT H A B a b T term} := term.
  Global Arguments PNT_term / .

  Global Instance PNT_Functor_Functor `{Funext} C D C' D' F G
  : PNT F G (@PointwiseFunctor _ C D C' D' F G) | 1000.

  Global Instance PNT_Functor_NT `{Funext} C D C' D' F G T F'
  : PNT T F' (@PointwiseNaturalTransformation1 _ C D C' D' F G T F') | 10.

  Global Instance PNT_NT_Functor `{Funext} C D C' D' F F' G' T'
  : PNT F T' (@PointwiseNaturalTransformation2 _ C D C' D' F F' G' T') | 10.
End notations.

Hint Unfold PNT_term : typeclass_instances.

(* Set some notations for printing *)
Notation "[ F , G ]" := (PointwiseFunctor F G) : natural_transfomation_scope.
Notation "[ T , F ]" := (PointwiseNaturalTransformation1 T F) : natural_transformation_scope.
Notation "[ F , T ]" := (PointwiseNaturalTransformation2 F T) : natural_transformation_scope.

(* Notation for parsing *)
Notation "U ^ T"
  := (@PNT_term _ _ _ T%natural_transformation U%natural_transformation _ _ _)
     : natural_transformation_scope.

Notation "[ T , U ]"
  := (@PNT_term _ _ _ T%natural_transformation U%natural_transformation _ _ _)
     : natural_transformation_scope.
