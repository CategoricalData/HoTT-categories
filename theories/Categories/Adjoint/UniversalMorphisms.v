Require Export Adjoint.UnitCounit Adjoint.UnitCounitCoercions UniversalProperties Adjoint.Duals Comma.Duals.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section AdjunctionUniversal.
  Section initial.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.
    Variable A : F ⊣ G.
    Variable Y : C.

    Definition InitialMorphismOfAdjunction
    : Object (Y ↓ G)
      := @Build_CommaCategory_Object
           TerminalCategory D C
           (! Y) G
           tt
           (F Y)
           ((Adjunction_Unit A) Y).

    Definition IsInitialMorphismOfAdjunction
    : IsInitialMorphism InitialMorphismOfAdjunction.
    Proof.
      unfold InitialMorphismOfAdjunction.
      pose (projT1 (A : AdjunctionCounit F G)) as ε.
      pose (projT1 (A : AdjunctionUnit F G)) as η.
      rename η into i, Y into c, G into R, F into L.
      apply Build_IsInitialMorphism.
      intros d f.
      exists ((Adjunction_Counit A) d ∘ L ₁ f).
      abstract (
          repeat match goal with
                   | _ => intro
                   | _ => split
                   | _ => progress simpl in *
                   | _ => solve [ auto with morphism
                                | apply symmetry; auto with morphism ]
                   | _ => progress rewrite ?FCompositionOf
                   | _ => progress subst
                   | [ |- appcontext[ComponentsOf ?T] ]
                     => simpl_do_clear try_associativity_quick_rewrite_rev (Commutes T);
                   first [ try_associativity_quick_rewrite Adjunction_UnitCounitEquation2
                         | try_associativity_quick_rewrite Adjunction_UnitCounitEquation1 ]
                   | [ |- appcontext[ComponentsOf ?T] ]
                     => simpl_do_clear try_associativity_quick_rewrite (Commutes T);
                   first [ try_associativity_quick_rewrite Adjunction_UnitCounitEquation2
                         | try_associativity_quick_rewrite Adjunction_UnitCounitEquation1 ]
                 end
        ).
    Defined.
  End initial.

  Global Arguments InitialMorphismOfAdjunction [C D F G] A Y.
  Global Arguments IsInitialMorphismOfAdjunction [C D F G] A Y _.

  Section terminal.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.
    Variable A : F ⊣ G.
    Variable X : D.

    Definition TerminalMorphismOfAdjunction
    : Object (F ↓ X)
      := Eval simpl in
          CommaDualFunctor_inv
            F (! X)
            (InitialMorphismOfAdjunction A^op X).

    Definition IsTerminalMorphismOfAdjunction
    : IsTerminalMorphism TerminalMorphismOfAdjunction
      := IsInitialMorphismOfAdjunction A^op X.
  End terminal.

  Global Arguments TerminalMorphismOfAdjunction [C D F G] A X.
  Global Arguments IsTerminalMorphismOfAdjunction [C D F G] A X _.
End AdjunctionUniversal.

Section AdjunctionFromUniversal.
  Section initial.
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable G : Functor D C.
    Context `(HM : forall Y, @IsInitialMorphism _ _ Y G (M Y)).

    Definition AdjointFunctorOfInitialMorphism : Functor C D.
    Proof.
      refine (Build_Functor
                C D
                (fun Y
                 => let ηY := IsInitialMorphism_Morphism (@HM Y) in
                    let F0Y := IsInitialMorphism_Object (@HM Y) in
                    F0Y)
                (fun Y0 Y1 f
                 => let ηY1 := IsInitialMorphism_Morphism (@HM Y1) in
                    (IsInitialProperty_Morphism (@HM Y0) _ (ηY1 ∘ f)))
                _
                _);
      abstract (
          simpl in *;
          repeat intro;
          repeat match goal with
                   | [ |- context[@HM ?x] ]
                     => generalize (@HM x); intro
                 end;
          clear HM;
          intro_universal_properties;
          unfold unique in *;
            split_and;
          apply_hyp';
          rewrite ?FCompositionOf, ?FIdentityOf, ?LeftIdentity, ?RightIdentity;
          try reflexivity;
          try_associativity_quick ltac:(rewrite_hyp);
          try_associativity_quick ltac:(f_ap)
        ).
    Defined.

    Definition AdjunctionOfInitialMorphism
    : AdjointFunctorOfInitialMorphism ⊣ G.
    Proof.
      refine (_ : AdjunctionUnit AdjointFunctorOfInitialMorphism G).
      exists (Build_NaturalTransformation
                (IdentityFunctor C)
                (G ∘ AdjointFunctorOfInitialMorphism)
                (fun x => IsInitialMorphism_Morphism (@HM x))
                (fun s d m => symmetry _ _ (fst (InitialProperty (@HM s) _ _)))).
      simpl.
      exact (fun c d f => (IsInitialProperty_Morphism (@HM c) d f
                           ; InitialProperty (@HM c) d f)).
    Defined.
  End initial.

  Section terminal.
    Variable C : PreCategory.
    Variable D : PreCategory.

    Variable F : Functor C D.
    Context `(HM : forall X, @IsTerminalMorphism _ _ F X (M X)).

    Definition AdjointFunctorOfTerminalMorphism : Functor D C
      := (@AdjointFunctorOfInitialMorphism
            (D^op) (C^op)
            (F^op)
            (fun x => CommaDualFunctor F (FunctorFromTerminal D x) (M x)) HM)^op'.

    Definition AdjunctionOfTerminalMorphism
    : F ⊣ AdjointFunctorOfTerminalMorphism
      := ((@AdjunctionOfInitialMorphism
             (D^op) (C^op)
             (F^op)
             (fun x => CommaDualFunctor F (FunctorFromTerminal D x) (M x)) HM)^op'R)%adjunction.
  End terminal.
End AdjunctionFromUniversal.
