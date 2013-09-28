Require Export Category.
Require Import Common.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Definition UniqueUpToUniqueIsomorphism (C : PreCategory) (P : C -> Type) :=
  forall x (_ : P x) x' (_ : P x'),
    { c : Contr (Morphism C x x')
    | IsIsomorphism (center (Morphism C x x')) }.

(** A terminal object is an object with a unique morphism from every
    other object. *)
Notation IsTerminalObject C x :=
  (forall x' : Object C, Contr (Morphism C x' x)).

Record TerminalObject (C : PreCategory) :=
  {
    TerminalObject_Object :> C;
    TerminalObject_IsTerminalObject :> IsTerminalObject C TerminalObject_Object
  }.

Existing Instance TerminalObject_IsTerminalObject.

(** An initial object is an object with a unique morphism from every
    other object. *)
Notation IsInitialObject C x :=
  (forall x' : Object C, Contr (Morphism C x x')).

Record InitialObject (C : PreCategory) :=
  {
    InitialObject_Object :> C;
    InitialObject_IsInitialObject :> IsInitialObject C InitialObject_Object
  }.

Existing Instance InitialObject_IsInitialObject.

Arguments UniqueUpToUniqueIsomorphism [C] P.

Section CategoryObjectsTheorems.
  Variable C : PreCategory.

  Ltac unique :=
   repeat first [ intro
                 | exists _
                 | exists (center (Morphism C _ _))
                 | etransitivity; [ symmetry | ]; apply contr
                 ].

  (** The terminal object is unique up to unique isomorphism. *)
  Theorem TerminalObjectUnique
  : UniqueUpToUniqueIsomorphism (fun x => IsTerminalObject C x).
  Proof.
    unique.
  Qed.

  (** The initial object is unique up to unique isomorphism. *)
  Theorem InitialObjectUnique
  : UniqueUpToUniqueIsomorphism (fun x => IsInitialObject C x).
  Proof.
    unique.
  Qed.
End CategoryObjectsTheorems.
