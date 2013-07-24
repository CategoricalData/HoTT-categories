Require Export CommaCategory Category.Morphisms Category.Objects Category.Duals Functor.Duals.
Require Import Common.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section UniversalMorphism.
  (** Quoting Wikipedia:

      Suppose that [U : D -> C] is a functor from a category [D] to a
      category [C], and let [X] be an object of [C].  Consider the
      following dual (opposite) notions: *)

  Section InitialMorphism.
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable X : C.
    Variable U : Functor D C.
    (** An initial morphism from [X] to [U] is an initial object in
        the category [(X ↓ U)] of morphisms from [X] to [U].  In other
        words, it consists of a pair [(A, φ)] where [A] is an object
        of [D] and [φ: X -> U A] is a morphism in [C], such that the
        following initial property is satisfied:

       * Whenever [Y] is an object of [D] and [f : X -> U Y] is a
         morphism in [C], then there exists a unique morphism [g : A
         -> Y] such that the following diagram commutes:

<<
             φ
         X -----> U A       A
          \        .        .
            \      . U g    . g
           f  \    .        .
               ↘   ↓        ↓
                 U Y        Y
>>
       *)

    Definition IsInitialMorphism (Aφ : Object (X ↓ U)) :=
      IsInitialObject (X ↓ U) Aφ.

    Section IntroductionAbstractionBarrier.
      Definition Build_IsInitialMorphism
                 (*(Aφ : Object (X ↓ U))*)
                 (A : D)(* := CCO_b Aφ*)
                 (φ : Morphism C X (U A))(*:= CCO_f Aφ*)
                 (Aφ := Build_CommaCategory_Object (FunctorFromTerminal C X) U tt A φ)
                 (UniversalProperty : forall (A' : D) (φ' : Morphism C X (U A')),
                                        { m : Morphism D A A'
                                        | MorphismOf U m ∘ φ = φ'
                                          /\
                                          forall m' : Morphism D A A',
                                            MorphismOf U m' ∘ φ = φ'
                                            -> m' = m } )
      : IsInitialMorphism Aφ.
      Proof.
        intro x.
        specialize (UniversalProperty (CCO_b x) (CCO_f x)).
        apply contr_inhabited_hprop;
          [
          | exists (center (Morphism _ _ _)) (UniversalProperty.1);
            abstract (
                rewrite ?LeftIdentity, ?RightIdentity;
                exact (fst UniversalProperty.2)
          ) ].
        abstract (
            apply hprop_allpath;
            intros;
            apply CommaCategory_Morphism_eq;
            [ exact (center _)
            | etransitivity; [ | symmetry ];
              apply (snd UniversalProperty.2);
              destruct x0, y; simpl in *;
              rewrite ?LeftIdentity, ?RightIdentity in *;
              assumption
            ]
          ).
      Defined.
    End IntroductionAbstractionBarrier.

    Section EliminationAbstractionBarrier.
      Variable Aφ : Object (X ↓ U).

      Definition IsInitialMorphism_Object (M : IsInitialMorphism Aφ) : D
        := CCO_b Aφ.
      Definition IsInitialMorphism_Morphism (M : IsInitialMorphism Aφ)
      : Morphism C X (U (IsInitialMorphism_Object M))
        := CCO_f Aφ.
      Definition IsInitialProperty_Morphism (M : IsInitialMorphism Aφ)
                 (Y : D) (f : Morphism C X (U Y))
      : Morphism D (IsInitialMorphism_Object M) Y
        := Eval simpl in CCM_h (@center _ (M (Build_CommaCategory_Object
                                                (FunctorFromTerminal C X)
                                                U
                                                tt
                                                Y
                                                f))).

      (* TODO: Automate this better *)
      Lemma InitialProperty (M : IsInitialMorphism Aφ)
            (Y : D) (f : Morphism C X (U Y))
      : unique (fun g => U ₁ g ∘ (IsInitialMorphism_Morphism M) = f)
               (IsInitialProperty_Morphism M Y f).
      Proof.
        unfold IsInitialProperty_Morphism, IsInitialMorphism_Object, IsInitialMorphism_Morphism in *.
        split;
          [ abstract (
                let x := match goal with |- appcontext[CCM_h ?x] => constr:(x) end in
                pose proof (CCM_p x);
                autorewrite with morphism in *;
                  assumption
              )
          | ].
        intros.
        let CCM_h' := match goal with |- ?CCM_h _ = _ => constr:(CCM_h) end in
        etransitivity (CCM_h' {| CCM_h := _ |});
          [ apply ap;
            apply contr
          | simpl; reflexivity ].
        Grab Existential Variables.
        simpl; autorewrite with morphism in *; trivial.
        refine (center _).
      Qed.
    End EliminationAbstractionBarrier.
  End InitialMorphism.

  Section TerminalMorphism.
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable U : Functor D C.
    Variable X : C.
    (** A terminal morphism from [U] to [X] is a terminal object in
       the comma category [(U ↓ X)] of morphisms from [U] to [X].  In
       other words, it consists of a pair [(A, φ)] where [A] is an
       object of [D] and [φ : U A -> X] is a morphism in [C], such
       that the following terminal property is satisfied:

       * Whenever [Y] is an object of [D] and [f : U Y -> X] is a
         morphism in [C], then there exists a unique morphism [g : Y
         -> A] such that the following diagram commutes:

<<
         Y      U Y
         .       . \
       g .   U g .   \  f
         .       .     \
         ↓       ↓       ↘
         A      U A -----> X
                      φ
>>
       *)
    Local Notation op_object Aφ
      := (Build_CommaCategory_Object
            (FunctorFromTerminal C ^op X) (U ^op)
            (CCO_b (Aφ : Object (U ↓ X)))
            (CCO_a (Aφ : Object (U ↓ X)))
            (CCO_f (Aφ : Object (U ↓ X)))
          : Object ((X : Object C^op) ↓ U^op)).

    Definition IsTerminalMorphism (Aφ : Object (U ↓ X)) : Type
      := @IsInitialMorphism
           (C^op)
           _
           X
           (U^op)
           (op_object Aφ).

    Section IntroductionAbstractionBarrier.
      Definition Build_IsTerminalMorphism
                 (*(Aφ : Object (U ↓ X))*)
                 (A : D)(* := CCO_a Aφ*)
                 (φ : Morphism C (U A) X)(*:= CCO_f Aφ*)
                 (Aφ := Build_CommaCategory_Object U (FunctorFromTerminal C X) A tt φ)
                 (UniversalProperty : forall (A' : D) (φ' : Morphism C (U A') X),
                                        { m : Morphism D A' A
                                        | φ ∘ MorphismOf U m  = φ'
                                          /\
                                          forall m' : Morphism D A' A,
                                            φ ∘ MorphismOf U m' = φ'
                                            -> m' = m } )
      : IsTerminalMorphism Aφ
        := @Build_IsInitialMorphism
             (C^op)
             (D^op)
             X
             (U^op)
             A
             φ
             UniversalProperty.
    End IntroductionAbstractionBarrier.

    Section AbstractionBarrier.
      Variable Aφ : Object (U ↓ X).
      Variable M : IsTerminalMorphism Aφ.

      Definition IsTerminalMorphism_Object : D := @IsInitialMorphism_Object C^op D^op X U^op (op_object Aφ) M.
      Definition IsTerminalMorphism_Morphism : Morphism C (U IsTerminalMorphism_Object) X
        := @IsInitialMorphism_Morphism C^op D^op X U^op (op_object Aφ) M.
      Definition IsTerminalProperty_Morphism
      : forall (Y : D) (f : Morphism C (U Y) X), Morphism D Y IsTerminalMorphism_Object
        := @IsInitialProperty_Morphism C^op D^op X U^op (op_object Aφ) M.

      Definition TerminalProperty
      : forall (Y : D) (f : Morphism C (U Y) X),
          unique
            (fun g : Morphism D Y IsTerminalMorphism_Object =>
               IsTerminalMorphism_Morphism ∘ MorphismOf U g = f)
            (IsTerminalProperty_Morphism Y f)
     := @InitialProperty C^op D^op X U^op (op_object Aφ) M.
    End AbstractionBarrier.
  End TerminalMorphism.

  Section UniversalMorphism.
    (** The term universal morphism refers either to an initial
        morphism or a terminal morphism, and the term universal
        property refers either to an initial property or a terminal
        property.  In each definition, the existence of the morphism
        [g] intuitively expresses the fact that [(A, φ)] is ``general
        enough'', while the uniqueness of the morphism ensures that
        [(A, φ)] is ``not too general''.  *)
  End UniversalMorphism.
End UniversalMorphism.

Arguments Build_IsInitialMorphism [C D] X U A φ UniversalProperty _.
Arguments Build_IsTerminalMorphism [C D] U X A φ UniversalProperty _.

Ltac intro_from_universal_objects :=
  repeat match goal with
           | [ |- appcontext[IsTerminalMorphism_Object ?x] ] => unique_pose_with_body x
           | [ _ : appcontext[IsTerminalMorphism_Object ?x] |- _ ] => unique_pose_with_body x
           | [ |- appcontext[IsInitialMorphism_Object ?x] ] => unique_pose_with_body x
           | [ _ : appcontext[IsInitialMorphism_Object ?x] |- _ ] => unique_pose_with_body x
         end.

Ltac intro_universal_objects :=
  repeat match goal with
           | [ m : IsTerminalMorphism _ |- _ ] => unique_pose_with_body (IsTerminalMorphism_Object m)
           | [ m : IsInitialMorphism _ |- _ ] => unique_pose_with_body (IsInitialMorphism_Object m)
         end.

Ltac intro_universal_morphisms := intro_from_universal_objects;
  repeat match goal with
           | [ m : IsTerminalMorphism _ |- _ ] => unique_pose_with_body (IsTerminalMorphism_Morphism m)
           | [ m : IsInitialMorphism _ |- _ ] => unique_pose_with_body (IsInitialMorphism_Morphism m)
         end.

Ltac intro_universal_property_morphisms :=
  repeat match goal with
           | [ m : IsTerminalMorphism _ |- _ ] => unique_pose (IsTerminalProperty_Morphism m)
           | [ m : IsInitialMorphism _ |- _ ] => unique_pose (IsInitialProperty_Morphism m)
         end.

Ltac intro_universal_properties :=
  repeat match goal with
           | [ m : IsTerminalMorphism _ |- _ ] => unique_pose (TerminalProperty m)
           | [ m : IsInitialMorphism _ |- _ ] => unique_pose (InitialProperty m)

           | [ _ : appcontext[IsTerminalProperty_Morphism ?a] |- _ ] => unique_pose (TerminalProperty a)
           | [ _ : appcontext[IsInitialProperty_Morphism ?a] |- _ ] => unique_pose (InitialProperty a)
           | [ |- appcontext[IsTerminalProperty_Morphism ?a] ] => unique_pose (TerminalProperty a)
           | [ |- appcontext[IsInitialProperty_Morphism ?a] ] => unique_pose (InitialProperty a)

           | [ _ : appcontext[IsTerminalProperty_Morphism ?a ?b] |- _ ] => unique_pose (TerminalProperty a b)
           | [ _ : appcontext[IsInitialProperty_Morphism ?a ?b] |- _ ] => unique_pose (InitialProperty a b)
           | [ |- appcontext[IsTerminalProperty_Morphism ?a ?b] ] => unique_pose (TerminalProperty a b)
           | [ |- appcontext[IsInitialProperty_Morphism ?a ?b] ] => unique_pose (InitialProperty a b)

           | [ _ : appcontext[IsTerminalProperty_Morphism ?a ?b ?c] |- _ ] => unique_pose (TerminalProperty a b c)
           | [ _ : appcontext[IsInitialProperty_Morphism ?a ?b ?c] |- _ ] => unique_pose (InitialProperty a b c)
           | [ |- appcontext[IsTerminalProperty_Morphism ?a ?b ?c] ] => unique_pose (TerminalProperty a b c)
           | [ |- appcontext[IsInitialProperty_Morphism ?a ?b ?c] ] => unique_pose (InitialProperty a b c)
         end.
