Require Export Category.Core Functor.Core Category.Morphisms FunctorCategory FunctorCategory.Morphisms.
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

  Variables s d : C.
  Variables m1 m2 : Morphism C s d.
  Variable p : m1 = m2.

  Variable Fs : PreCategory.
  Variable Fd : PreCategory.
  Variable Fm : Morphism C s d -> Functor Fs Fd.

  Lemma transport_Fc_to_idtoiso
        s' d' u
  : @transport _ (fun m => Morphism _ (Fm m s') d') _ _ p u
    = u ∘ ComponentsOf (idtoiso [_, _] (ap Fm p) : Morphism _ _ _)^-1 s'.
  Proof.
    case p; clear p; simpl; autorewrite with morphism; reflexivity.
  Qed.

  Lemma transport_cF_to_idtoiso
        s' d' u
  : @transport _ (fun m => Morphism _ s' (Fm m d')) _ _ p u
    = ComponentsOf (idtoiso [_, _] (ap Fm p) : Morphism _ _ _) d' ∘ u.
  Proof.
    case p; clear p; simpl; autorewrite with morphism; reflexivity.
  Qed.
End iso_lemmas.
