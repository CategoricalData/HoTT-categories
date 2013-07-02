Require Import HoTT.HoTT.
Require Import HoTT.Categories.Notations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Record PreCategory :=
  {
    Object :> Type;
    Morphism : Object -> Object -> Type;

    Identity : forall x, Morphism x x;
    Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d' where "f 'o' g" := (Compose f g);

    Associativity : forall x1 x2 x3 x4
                           (m1 : Morphism x1 x2)
                           (m2 : Morphism x2 x3)
                           (m3 : Morphism x3 x4),
                      (m3 o m2) o m1 = m3 o (m2 o m1);
    LeftIdentity : forall a b (f : Morphism a b), (Identity b) o f = f;
    RightIdentity : forall a b (f : Morphism a b), f o (Identity a) = f;

    MorphismHSet : forall s d, IsHSet (Morphism s d)
  }.

Bind Scope category_scope with PreCategory.
Bind Scope object_scope with Object.
Bind Scope morphism_scope with Morphism.

Arguments Object C%category : rename.
Arguments Morphism !C%category s d : rename.
Arguments Identity [!C%category] x%object : rename.
Arguments Compose [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Infix "'o'" := Compose : morphism_scope.
Infix "∘" := Compose : morphism_scope.

Existing Instance MorphismHSet.

(* create a hint db for all category theory things *)
Create HintDb category discriminated.
(* create a hint db for morphisms in categories *)
Create HintDb morphism discriminated.

Hint Resolve @LeftIdentity @RightIdentity @Associativity : category morphism.
Hint Rewrite @LeftIdentity @RightIdentity : category.
Hint Rewrite @LeftIdentity @RightIdentity : morphism.

Section IdentityUnique.
  Variable C : PreCategory.

  Lemma IdentityUnique (id0 id1 : forall x, Morphism C x x)
        (id1_left : forall s d (m : Morphism C s d), id1 _ ∘ m = m)
        (id0_right : forall s d (m : Morphism C s d), m ∘ id0 _ = m)
  : id0 == id1.
    intro.
    eapply transitivity.
    - apply symmetry.
      apply id1_left.
    - apply id0_right.
  Qed.
End IdentityUnique.
