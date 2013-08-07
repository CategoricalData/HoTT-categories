Require Export Category.Core Functor.Core Category.Morphisms Cat FunctorCategory FunctorCategory.Morphisms.
Require Import Common.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Section iso_lemmas.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Variables s d : C.
  Variables m1 m2 : Morphism C s d.
  Variable p : m1 = m2.

  Let Cat := SubPreCat P.

  Lemma transport_Fc_to_idtoiso
        (F : Functor C Cat) s' d' u
  : @transport _ (fun m => Morphism _ (MorphismOf F m s') d') _ _ p u
    = u ∘ ComponentsOf (idtoiso [_, _] (ap (MorphismOf F (s := s) (d := d)) p) : Morphism _ _ _)^-1 s'.
  Proof.
    case p; clear p; simpl; autorewrite with morphism; reflexivity.
  Qed.

  Lemma transport_cF_to_idtoiso
        (F : Functor C Cat) s' d' u
  : @transport _ (fun m => Morphism _ s' (MorphismOf F m d')) _ _ p u
    = ComponentsOf (idtoiso [_, _] (ap (MorphismOf F (s := s) (d := d)) p) : Morphism _ _ _) d' ∘ u.
  Proof.
    case p; clear p; simpl; autorewrite with morphism; reflexivity.
  Qed.
End iso_lemmas.
