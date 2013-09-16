Require Export Category Category.Objects InitialTerminalCategory Functor.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section SubPreCat.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  (** There is a precategory of precategories which satisfy the proposition P *)

  Definition SubPreCatObject := { C : PreCategory | P C }.
  Definition SubPreCatCat : SubPreCatObject -> PreCategory
    := @projT1 _ _.
  Global Coercion SubPreCatCat : SubPreCatObject >-> PreCategory.

  Definition SubPreCat : PreCategory
    := @Build_PreCategory
         SubPreCatObject
         Functor
         IdentityFunctor
         ComposeFunctors
         (fun _ _ _ _ _ _ _ => ComposeFunctorsAssociativity _ _ _)
         (fun _ _ _ => LeftIdentityFunctor _)
         (fun _ _ _ => RightIdentityFunctor _)
         (fun s d => HF (projT2 s) (projT2 d)).
End SubPreCat.

Definition StrictCat `{Funext} : PreCategory
  := @SubPreCat _ (fun C => IsStrictCategory C) _.

(*Definition Cat `{Funext} : PreCategory.
  refine (@SubPreCat _ (fun C => IsCategory C) _).
  *)

Section Objects.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Lemma TerminalCategory_Terminal
        `(IsTerminalCategory one)
        (HT : P one)
  : IsTerminalObject (SubPreCat P) (one; HT).
  Proof.
    typeclasses eauto.
  Defined.

  Lemma InitialCategory_Initial
        `(IsInitialCategory zero)
        (HI : P zero)
  : IsInitialObject (SubPreCat P) (zero; HI).
  Proof.
    typeclasses eauto.
  Defined.
End Objects.
