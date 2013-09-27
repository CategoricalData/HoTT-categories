Require Export FunctorCategory Category.Product.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope functor_scope.

Section Law4.
  Context `{Funext}.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Local Open Scope morphism_scope.

  Local Ltac do_exponential4_helper rew_comp :=
    intros; simpl;
    repeat (simpl;
            match goal with
              | _ => reflexivity
              | _ => progress rew_comp
              | _ => rewrite !FIdentityOf
              | _ => rewrite !LeftIdentity
              | _ => rewrite !RightIdentity
              | _ => try_associativity_quick ltac:(f_ap)
              | _ => rewrite !Commutes
              | _ => try_associativity_quick ltac:(rewrite !Commutes)
            end).

  Section functor.
    Local Ltac do_exponential4
      := do_exponential4_helper ltac:(rewrite !FCompositionOf).

    Definition ExponentialLaw4Functor_ObjectOf
    : [C1, [C2, D]]%category -> [C1 * C2, D]%category.
    Proof.
      intro F; hnf in F |- *.
      refine (Build_Functor
                (C1 * C2) D
                (fun c1c2 => F (fst c1c2) (snd c1c2))
                (fun s d m => F (fst d) ₁ (snd m) ∘ (F ₁ (fst m)) (snd s))
                _
                _);
        abstract do_exponential4.
    Defined.

    Definition ExponentialLaw4Functor_MorphismOf
               s d (m : Morphism [C1, [C2, D]] s d)
    : Morphism [C1 * C2, D]
               (ExponentialLaw4Functor_ObjectOf s)
               (ExponentialLaw4Functor_ObjectOf d).
    Proof.
      simpl.
      refine (Build_NaturalTransformation
                (ExponentialLaw4Functor_ObjectOf s)
                (ExponentialLaw4Functor_ObjectOf d)
                (fun c => m (fst c) (snd c))
                _);
        abstract (
            repeat match goal with
                     | [ |- appcontext[ComponentsOf ?T ?x ∘ ComponentsOf ?U ?x] ] =>
                       change (T x ∘ U x) with ((Compose (C := [_, _]) T U) x)
                     | _ => f_ap
                     | _ => rewrite !Commutes
                     | _ => do_exponential4
                   end
          ).
    Defined.

    Definition ExponentialLaw4Functor
    : Functor [C1, [C2, D]] [C1 * C2, D].
    Proof.
      refine (Build_Functor
                [C1, [C2, D]] [C1 * C2, D]
                ExponentialLaw4Functor_ObjectOf
                ExponentialLaw4Functor_MorphismOf
                _
                _);
      abstract by nt_eq.
    Defined.
  End functor.

  Section inverse.
    Local Ltac do_exponential4_inverse
      := do_exponential4_helper ltac:(rewrite <- !FCompositionOf).

    Section ObjectOf.
      Variable F : Functor (C1 * C2) D.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf
      : C1 -> [C2, D]%category.
      Proof.
        intro c1.
        refine (Build_Functor
                  C2 D
                  (fun c2 => F (c1, c2))
                  (fun s2 d2 m2 => F.(MorphismOf) (s := (c1, s2)) (d := (c1, d2)) (Identity c1, m2))
                  _
                  _);
          abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf_MorphismOf
                 s d (m : Morphism C1 s d)
      : Morphism [C2, D]
                 (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf s)
                 (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf d).
      Proof.
        refine (Build_NaturalTransformation
                  (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf s)
                  (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf d)
                  (fun c => F.(MorphismOf) (s := (s, c)) (d := (d, c)) (m, Identity c))
                  _);
        abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf
      : [C1, [C2, D]]%category.
      Proof.
        refine (Build_Functor
                  C1 [C2, D]
                  ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf
                  ExponentialLaw4Functor_Inverse_ObjectOf_MorphismOf
                  _
                  _);
        abstract (nt_eq; do_exponential4_inverse).
      Defined.
    End ObjectOf.

    Section MorphismOf.
      Definition ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf
                 s d (m : Morphism [C1 * C2, D] s d)
      : forall c, Morphism [C2, D]
                           ((ExponentialLaw4Functor_Inverse_ObjectOf s) c)
                           ((ExponentialLaw4Functor_Inverse_ObjectOf d) c).
      Proof.
        intro c.
        refine (Build_NaturalTransformation
                  ((ExponentialLaw4Functor_Inverse_ObjectOf s) c)
                  ((ExponentialLaw4Functor_Inverse_ObjectOf d) c)
                  (fun c' => m (c, c'))
                  _).
        abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_MorphismOf
                 s d (m : Morphism [C1 * C2, D] s d)
      : Morphism [C1, [C2, D]]
                 (ExponentialLaw4Functor_Inverse_ObjectOf s)
                 (ExponentialLaw4Functor_Inverse_ObjectOf d).
      Proof.
        refine (Build_NaturalTransformation
                  (ExponentialLaw4Functor_Inverse_ObjectOf s)
                  (ExponentialLaw4Functor_Inverse_ObjectOf d)
                  (ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf m)
                  _).
        abstract (nt_eq; do_exponential4_inverse).
      Defined.
    End MorphismOf.

    Arguments ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf / _ _ _ _ .

    Definition ExponentialLaw4Functor_Inverse
    : Functor [C1 * C2, D] [C1, [C2, D]].
    Proof.
      refine (Build_Functor
                [C1 * C2, D] [C1, [C2, D]]
                ExponentialLaw4Functor_Inverse_ObjectOf
                ExponentialLaw4Functor_Inverse_MorphismOf
                _
                _);
      abstract by nt_eq.
    Defined.
  End inverse.
End Law4.
