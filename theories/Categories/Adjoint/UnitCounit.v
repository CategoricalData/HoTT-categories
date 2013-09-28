Require Export Category Functor NaturalTransformation.
Require Import Common Category.Duals Functor.Duals NaturalTransformation.Duals.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Section Adjunction.
  (** Quoting from Awody's "Category Theory":

      An adjunction between categories [C] and [D] consists of
      functors

      [F : C <-> D : G]

      and a natural transformation

      [T : 1_C -> G ∘ F]

      with the property:

      (o) For any [c : C], [d : D], and [f : c -> G d], there exists a
          unique [g : F c -> d] such that [f = (G g) ∘ (T c)] as
          indicated in

<<
                g
     F c ..................> d

                 G g
     G (F c) --------------> G d
       ^                    _
       |                    /|
       |                  /
       |                /
       |              /
       | T c        /
       |          /  f
       |        /
       |      /
       |    /
       |  /
        c
>>

     Terminology and notation:

     * [F] is called the left adjoint, [G] is called the right
       adjoint, and [T] is called the unit of the adjunction.

     * One sometimes writes [F -| G] for ``[F] is left and [G] right
       adjoint.''

     * The statement (o) is the UMP of the unit [T].

     Note that the situation [F ⊣ G] is a generalization of
     equivalence of categories, in that a pseudo-inverse is an
     adjoint. In that case, however, it is the relation between
     categories that one is interested in. Here, one is concerned with
     the relation between special functors. That is to say, it is not
     the relation on categories ``there exists an adjunction,'' but
     rather ``this functor has an adjoint'' that we are concerned
     with.  **)

  Section unit.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.

    Definition AdjunctionUnit :=
      { T : NaturalTransformation (IdentityFunctor C) (G ∘ F)
      | forall (c : C) (d : D) (f : C.(Morphism) c (G d)),
          { g : D.(Morphism) (F c) d | unique (fun g => G ₁ g ∘ T c = f) g }
      }.
  End unit.

  (**
     Paraphrasing and quoting from Awody's "Category Theory":

     An adjunction between categories [C] and [D] consists of functors

     [F : C <-> D : G]

     and a natural transformation

     [U : F ∘ G -> 1_D]

     with the property:

     (o) For any [c : C], [d : D], and [g : F c -> d], there exists a
         unique [f : c -> G d] such that [g = (U d) ∘ (F f)] as
         indicated in the diagram

<<
                f
     c ..................> G d

               F f
     F c --------------> F (G d)
      \                    |
        \                  |
          \                |
            \              |
              \            | U d
             g  \          |
                  \        |
                    \      |
                      \    |
                       _\| V
                          d
>>

    Terminology and notation:

    * The statement (o) is the UMP of the counit [U].
    **)
  Section counit.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.

    Definition AdjunctionCounit :=
      { U : NaturalTransformation (F ∘ G) (IdentityFunctor D)
      | forall (c : C) (d : D) (g : D.(Morphism) (F c) d),
          { f : C.(Morphism) c (G d) | unique (fun f => U d ∘ F ₁ f = g) f }
      }.
  End counit.

  (** The counit is just the dual of the unit.  We formalize this here
      so that we can use it to make coercions easier. *)

  Section unit_counit_op.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.

    Definition AdjunctionUnitOpCounit (A : AdjunctionUnit G^op F^op)
    : AdjunctionCounit F G
      := existT
           (fun U : NaturalTransformation (F ∘ G) 1 =>
              forall (c : C) (d : D) (g : Morphism D (F c) d),
                {f : Morphism C c (G d)
                | unique (fun f0 : Morphism C c (G d) => U d ∘ F ₁ f0 = g) f})
           (@OppositeNaturalTransformation_Tinv _ _ (F ∘ G) 1 A.1)
           (fun c d g => A.2 d c g).

    Definition AdjunctionUnitOpCounit_inv (A : AdjunctionUnit G F)
    : AdjunctionCounit F^op G^op
      := existT
           (fun U : NaturalTransformation (F ^op ∘ G ^op) 1
            => forall (c : C ^op) (d : D ^op) (g : Morphism D ^op ((F ^op)%functor c) d),
                 {f : Morphism C ^op c ((G ^op)%functor d)
                 | unique
                     (fun f0 : Morphism C ^op c ((G ^op)%functor d) => U d ∘ F ^op ₁ f0 = g)
                     f})
           (@OppositeNaturalTransformation_Finv _ _ (F^op ∘ G^op) 1 A.1)
           (fun c d g => A.2 d c g).

    Definition AdjunctionCounitOpUnit (A : AdjunctionCounit G^op F^op)
    : AdjunctionUnit F G
      := existT
           (fun T : NaturalTransformation 1 (G ∘ F) =>
              forall (c : C) (d : D) (f : Morphism C c (G d)),
                { g : Morphism D (F c) d
                | unique (fun g0 : Morphism D (F c) d =>
                            G ₁ g0 ∘ T c = f) g })
           (@OppositeNaturalTransformation_Tinv _ _ 1 (G ∘ F) A.1)
           (fun c d g => A.2 d c g).

    Definition AdjunctionCounitOpUnit_inv (A : AdjunctionCounit G F)
    : AdjunctionUnit F^op G^op
      := existT
           (fun T : NaturalTransformation 1 (G ^op ∘ F ^op)
            => forall (c : C ^op) (d : D ^op) (f : Morphism C ^op c ((G ^op)%functor d)),
                 {g : Morphism D ^op ((F ^op)%functor c) d
                 | unique
                     (fun g0 : Morphism D ^op ((F ^op)%functor c) d => G ^op ₁ g0 ∘ T c = f)
                     g})
           (@OppositeNaturalTransformation_Finv _ _ 1 (G^op ∘ F^op) A.1)
           (fun c d g => A.2 d c g).
  End unit_counit_op.

  (** Quoting Wikipedia on Adjoint Functors:

      A counit-unit adjunction between two categories [C] and [D]
      consists of two functors [F : C ← D] and [G : C → D and two
      natural transformations

<<
      ε : FG → 1_C
      η : 1_D → GF
>>

      respectively called the counit and the unit of the adjunction
      (terminology from universal algebra), such that the compositions

<<
          F η            ε F
      F -------> F G F -------> F

          η G            G ε
      G -------> G F G -------> G
>>

      are the identity transformations [1_F] and [1_G] on [F] and [G]
      respectively.

      In this situation we say that ``[F] is left adjoint to [G]'' and
      ''[G] is right adjoint to [F]'', and may indicate this
      relationship by writing [(ε, η) : F ⊣ G], or simply [F ⊣ G].

      In equation form, the above conditions on (ε, η) are the
      counit-unit equations

<<
      1_F = ε F ∘ F η
      1_G = G ε ∘ η G
>>

      which mean that for each [X] in [C] and each [Y] in [D],

<<
      1_{FY} = ε_{FY} ∘ F(η_Y)
      1_{GX} = G(ε_X) ∘ η_{GX}
>>

      These equations are useful in reducing proofs about adjoint
      functors to algebraic manipulations.  They are sometimes called
      the ``zig-zag equations'' because of the appearance of the
      corresponding string diagrams.  A way to remember them is to
      first write down the nonsensical equation [1 = ε ∘ η] and then
      fill in either [F] or [G] in one of the two simple ways which
      make the compositions defined.

      Note: The use of the prefix ``co'' in counit here is not
      consistent with the terminology of limits and colimits, because
      a colimit satisfies an initial property whereas the counit
      morphisms will satisfy terminal properties, and dually.  The
      term unit here is borrowed from the theory of monads where it
      looks like the insertion of the identity 1 into a monoid.  *)

  Section unit_counit.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.

    Local Reserved Notation "'ε'".
    Local Reserved Notation "'η'".

    (** Use the per-object version of the equations, so that we don't
        need the associator in the middle.  Also, explicitly simplify
        some of the types so that [rewrite] works better. *)
    Record AdjunctionUnitCounit :=
      {
        Adjunction_Unit : NaturalTransformation (IdentityFunctor C) (G ∘ F)
                                                where "'η'" := Adjunction_Unit;
        Adjunction_Counit : NaturalTransformation (F ∘ G) (IdentityFunctor D)
                                                  where "'ε'" := Adjunction_Counit;
        Adjunction_UnitCounitEquation1
        : forall Y : C, (*ε (F Y) ∘ F ₁ (η Y) = Identity (F Y);*)
            @Compose D (F Y) (F (G (F Y))) (F Y)
                     (ε (F Y))
                     (MorphismOf F (s := Y) (d := G (F Y)) (η Y))
            = Identity (F Y);
        Adjunction_UnitCounitEquation2
        : forall X : D, (* G ₁ (ε X) ∘ η (G X) = Identity (G X) *)
            @Compose C (G X) (G (F (G X))) (G X)
                     (MorphismOf G (s := F (G X)) (d := X) (ε X))
                     (η (G X))
            = Identity (G X)
      }.
  End unit_counit.
End Adjunction.

Bind Scope adjunction_scope with AdjunctionUnit.
Bind Scope adjunction_scope with AdjunctionCounit.
Bind Scope adjunction_scope with AdjunctionUnitCounit.

Arguments Adjunction_Unit [C%category D%category F%functor G%functor] _%adjunction.
Arguments Adjunction_Counit [C%category D%category F%functor G%functor] _%adjunction.
Arguments Adjunction_UnitCounitEquation1 [C%category D%category F%functor G%functor] _%adjunction _%object.
Arguments Adjunction_UnitCounitEquation2 [C%category D%category F%functor G%functor] _%adjunction _%object.

Notation Adjunction := AdjunctionUnitCounit.

Infix "-|" := Adjunction : type_scope.
Infix "⊣" := Adjunction : type_scope.
