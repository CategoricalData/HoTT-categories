Require Export NaturalTransformation.Core NaturalTransformation.Composition Category.Morphisms FunctorCategory.Morphisms.
Require Import Common.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope natural_transformation_scope.
Local Open Scope morphism_scope.


Local Ltac iso_whisker_t :=
  nt_eq;
  try rewrite <- FCompositionOf, <- FIdentityOf;
  try f_ap;
  match goal with
    | [ H : IsIsomorphism _ |- appcontext[ComponentsOf ?T0 ?x ∘ ComponentsOf ?T1 ?x] ]
      => change (T0 x ∘ T1 x) with (ComponentsOf ((T0 : Morphism [_, _] _ _)
                                                    ∘ (T1 : Morphism [_, _] _ _))%morphism
                                                 x);
        progress rewrite ?(@LeftInverse _ _ _ _ H), ?(@RightInverse _ _ _ _ H)
  end;
  reflexivity.

Section composition.
  Context `{Funext}.

  Global Instance iso_NTComposeT
         `(T' : @NaturalTransformation C D F' F'')
         `(T : @NaturalTransformation C D F F')
         `{@IsIsomorphism [C, D] F' F'' T'}
         `{@IsIsomorphism [C, D] F F' T}
  : @IsIsomorphism [C, D] F F'' (NTComposeT T' T)
    := @isisomorphism_composition [C, D] _ _ T' _ _ T _.

  Global Instance iso_NTWhiskerL C D E
         (F : Functor D E)
         (G G' : Functor C D)
         (T : NaturalTransformation G G')
         `{@IsIsomorphism [C, D] G G' T}
  : @IsIsomorphism [C, E] (F ∘ G)%functor (F ∘ G')%functor (NTWhiskerL F T).
  Proof.
    exists (NTWhiskerL F (T : Morphism [_, _] _ _)^-1);
    abstract iso_whisker_t.
  Defined.

  Global Instance iso_NTWhiskerR C D E
         (F F' : Functor D E)
         (T : NaturalTransformation F F')
         (G : Functor C D)
         `{@IsIsomorphism [D, E] F F' T}
  : @IsIsomorphism [C, E] (F ∘ G)%functor (F' ∘ G)%functor (NTWhiskerR T G).
  Proof.
    exists (NTWhiskerR (T : Morphism [_, _] _ _)^-1 G);
    abstract iso_whisker_t.
  Defined.

  Definition idtoiso_NTComposeT C D
         (F F' F'' : Functor C D)
         (T' : F' = F'')
         (T : F = F')
  : NTComposeT (idtoiso [_, _] T' : Morphism _ _ _)
               (idtoiso [_, _] T : Morphism _ _ _)
    = (idtoiso [_, _] (T @ T')%path : Morphism _ _ _).
  Proof.
    nt_eq; path_induction; simpl; auto with morphism.
  Defined.

  Definition idtoiso_NTWhiskerL C D E
         (F : Functor D E)
         (G G' : Functor C D)
         (T : G = G')
  : NTWhiskerL F (idtoiso [_, _] T : Morphism _ _ _)
    = (idtoiso [_, _] (ap _ T) : Morphism _ _ _).
  Proof.
    nt_eq; path_induction; simpl; auto with functor.
  Defined.

  Definition idtoiso_NTWhiskerR C D E
         (F F' : Functor D E)
         (T : F = F')
         (G : Functor C D)
  : NTWhiskerR (idtoiso [_, _] T : Morphism _ _ _) G
    = (idtoiso [_, _] (ap (fun _ => ComposeFunctors _ _) T) : Morphism _ _ _).
  Proof.
    nt_eq; path_induction; simpl; auto with functor.
  Defined.

End composition.
