Require Import HoTT.HoTT.
Require Import Common Notations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Record PreCategory :=
  Build_PreCategory' {
    Object :> Type;
    Morphism : Object -> Object -> Type;

    Identity : forall x, Morphism x x;
    Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d' where "f ∘ g" := (Compose f g);

    Associativity : forall x1 x2 x3 x4
                           (m1 : Morphism x1 x2)
                           (m2 : Morphism x2 x3)
                           (m3 : Morphism x3 x4),
                      (m3 ∘ m2) ∘ m1 = m3 ∘ (m2 ∘ m1);
    (* Ask for the symmetrized version of [Associativity], so that [(C ᵒᵖ) ᵒᵖ] and [C] are equal without [Funext] *)
    Associativity_sym : forall x1 x2 x3 x4
                               (m1 : Morphism x1 x2)
                               (m2 : Morphism x2 x3)
                               (m3 : Morphism x3 x4),
                          m3 ∘ (m2 ∘ m1) = (m3 ∘ m2) ∘ m1;

    LeftIdentity : forall a b (f : Morphism a b), (Identity b) ∘ f = f;
    RightIdentity : forall a b (f : Morphism a b), f ∘ (Identity a) = f;
    (* Ask for the double-identity version so that [FunctorFromTerminal Cᵒᵖ X] and [(FunctorFromTerminal C X)ᵒᵖ] are convertible. *)
    IdentityIdentity : forall x, Identity x ∘ Identity x = Identity x;

    MorphismIsHSet : forall s d, IsHSet (Morphism s d)
  }.

Bind Scope category_scope with PreCategory.
Bind Scope object_scope with Object.
Bind Scope morphism_scope with Morphism.

Arguments Object C%category : rename.
Arguments Morphism !C%category s d : rename.
Arguments Identity [!C%category] x%object : rename.
Arguments Compose [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Infix "o" := Compose : morphism_scope.
Infix "∘" := Compose : morphism_scope.
(* I'm not sure how much I like this notation... *)
Notation "─" := (Identity _) : morphism_scope.
Notation "1" := (Identity _) : morphism_scope.

Definition Build_PreCategory
           Object Morphism Compose Identity Associativity LeftIdentity RightIdentity
  := @Build_PreCategory' Object
                         Morphism
                         Compose
                         Identity
                         Associativity
                         (fun _ _ _ _ _ _ _ => symmetry _ _ (Associativity _ _ _ _ _ _ _))
                         LeftIdentity
                         RightIdentity
                         (fun _ => LeftIdentity _ _ _).

Existing Instance MorphismIsHSet.
Instance MorphismIsHSet' C s d (m1 m2 : Morphism C s d) (pf1 pf2 : m1 = m2)
: Contr (pf1 = pf2)
  := @MorphismIsHSet C s d m1 m2 pf1 pf2.

(* create a hint db for all category theory things *)
Create HintDb category discriminated.
(* create a hint db for morphisms in categories *)
Create HintDb morphism discriminated.

Hint Resolve @LeftIdentity @RightIdentity @Associativity : category morphism.
Hint Rewrite @LeftIdentity @RightIdentity : category.
Hint Rewrite @LeftIdentity @RightIdentity : morphism.

Section IdentityUnique.
  Variable C : PreCategory.

  (** The Identity morphism is uniuqe. *)
  Lemma IdentityUnique (id0 id1 : forall x, Morphism C x x)
        (id1_left : forall s d (m : Morphism C s d), id1 _ ∘ m = m)
        (id0_right : forall s d (m : Morphism C s d), m ∘ id0 _ = m)
  : id0 == id1.
    intro.
    etransitivity;
      [ symmetry; apply id1_left
      | apply id0_right ].
  Qed.

  (** Anything equal to the identity acts like it.  This is obvious,
      but useful as a helper lemma for automation. *)
  Definition concat_LeftIdentity s d (m : Morphism C s d) i
  : i = ─ -> i ∘ m = m
    := fun H => (ap10 (ap _ H) _ @ LeftIdentity _ _ _ m)%path.

  Definition concat_RightIdentity s d (m : Morphism C s d) i
  : i = ─ -> m ∘ i = m
    := fun H => (ap _ H @ RightIdentity _ _ _ m)%path.
End IdentityUnique.
(** * Version of [Associativity] that avoids going off into the weeds in the presence of unification variables *)

Definition NoEvar T (_ : T) := True.

Lemma AssociativityNoEvar (C : PreCategory) x1 x2 x3 x4
      (m1 : C.(Morphism) x1 x2)
      (m2 : C.(Morphism) x2 x3)
      (m3 : C.(Morphism) x3 x4)
: NoEvar (m1, m2) \/ NoEvar (m2, m3) \/ NoEvar (m1, m3)
  -> (m3 ∘ m2) ∘ m1 = m3 ∘ (m2 ∘ m1).
Proof.
  intros; apply Associativity.
Qed.

Ltac noEvar_tauto :=
  (eassumption
     || (left; noEvar_tauto)
     || (right; noEvar_tauto)).

Ltac noEvar := match goal with
                 | [ |- context[NoEvar ?X] ]
                   => (has_evar X; fail 1)
                        || cut (NoEvar X); [ intro; noEvar_tauto | constructor ]
               end.

Hint Rewrite @AssociativityNoEvar using noEvar : category.
Hint Rewrite @AssociativityNoEvar using noEvar : morphism.

Ltac try_associativity_quick tac := try_rewrite Associativity tac.
Ltac try_associativity tac := try_rewrite_by AssociativityNoEvar ltac:(idtac; noEvar) tac.
Ltac try_associativity_quick_rewrite H := try_associativity_quick ltac:(rewrite H).
Ltac try_associativity_quick_rewrite_rev H := try_associativity_quick ltac:(rewrite <- H).
Ltac try_associativity_rewrite H := try_associativity ltac:(rewrite H).
Ltac try_associativity_rewrite_rev H := try_associativity ltac:(rewrite <- H).
