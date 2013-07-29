Require Export Category Category.Objects.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section preobject.
  (** Quoting nCatLab (http://ncatlab.org/nlab/show/natural+numbers+object):

    Idea

    Recall that a topos is a category that behaves likes the category
    Set of sets.

    A natural numbers object (NNO) in a topos is an object that
    behaves in that topos like the set ℕ of natural numbers does in
    Set; thus it provides a formulation of the “axiom of infinity” in
    structural set theory (such as ETCS). The definition is due to
    William Lawvere.

    Definition

      In a topos or cartesian closed category:

        A natural numbers object in a topos (or any cartesian closed
        category) E with terminal object 1 is
        * an object ℕ in E
        * equipped with
          + a morphism [z : 1 → ℕ] from the terminal object 1;
          + a morphism [s : ℕ → ℕ] (successor);
        * such that
          + for every other diagram [1 -- q --> A -- f --> A]
          + there is a unique morphism [u : ℕ → A] such that
          [[
                  z        s
              1 -----> ℕ -----> ℕ
               \       |        |
               q \     | u      | u
                   \   |        |
                     ↘ ↓   f    ↓
                       A -----> A
          ]]

      All this may be summed up by saying that a natural numbers
      object is an initial algebra for the endofunctor
      [X ↦ 1 + X]. Equivalently, it is an initial algebra for the
      endo-profunctor [Hom E (1 , =) × Hom E (− , =)].

      By the universal property, the natural numbers object is unique
      up to isomorphism.

    In a general category with finite products

      Note that this definition actually makes sense in any category E
      having finite products. However, if E is not cartesian closed,
      then it is better to explicitly assume a stronger version of
      this definition “with parameters” (which follows automatically
      when E is cartesian closed, such as when E is a topos). What
      this amounts to is demanding that (ℕ,z,s) not only be a natural
      numbers object (in the above, unparametrized sense) in E, but
      that also, for each object A, this is preserved by the free
      coalgebra functor into the Kleisli category of the comonad X↦A×X
      (which may be thought of as the category of maps parametrized by
      A). (Put another way, the finite product structure of E gives
      rise to a canonical self-indexing, and we are demanding the
      existence of an (unparametrized) NNO within this indexed
      category, rather than just within the base E).

      The functions which are constructable out of the structure of a
      category with finite products and such a “parametrized NNO” are
      precisely the primitive recursive? ones. Specifically, the
      unique structure-preserving functor from the free such category
      F into Set yields a bijection between Hom F(1,ℕ) and the actual
      natural numbers, as well as surjections from Hom F(ℕ m,ℕ) onto
      the primitive recursive functions of arity m for each finite
      m. With cartesian closure, however, this identification no
      longer holds, since non-primitive recursive functions (such as
      the Ackermann function?) become definable as well.
   *)

  (** XXX nCatLab says that we're not in a topos, we need a stronger
          notion of natural numbers object.  But I want the natural
          numbers object to prove that [Set] is cartesian, and I don't
          have the other notions yet.  So I'll call this a
          [NaturalNumbersPreObject], to make the distinction slightly
          more obvious. *)

  Variable E : Category.

  Local Reserved Notation "'ℕ'".
  Local Reserved Notation "'S'".

  Record NaturalNumbersPreObject :=
    {
      NaturalNumbersPreObject_Object :> E where "'ℕ'" := NaturalNumbersPreObject_Object;
      NaturalNumbersPreObject_TerminalObject : TerminalObject E where "1" := (NaturalNumbersPreObject_TerminalObject : E);
      NaturalNumbersPreObject_Zero : Morphism E 1 ℕ where "0" := NaturalNumbersPreObject_Zero;
      NaturalNumbersPreObject_Successor : Morphism E ℕ ℕ where "'S'" := NaturalNumbersPreObject_Successor;
      NaturalNumbersPreObject_Property : forall A (q : Morphism E 1 A) (f : Morphism E A A),
                                           { u : Morphism E ℕ A |
                                             unique (fun u => u ∘ 0 = q
                                                              /\ f ∘ u = u ∘ S)
                                                    u }
    }.
End preobject.
