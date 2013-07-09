Require Export PreCategory.
Require Import Common StrictCategory.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section BoolCat.
  Local Notation obj := Bool (only parsing).
  Local Notation mor s d := (if (implb s d) then Unit else Empty) (only parsing).

  Definition BoolCat_Compose s d d' (m1 : mor d d') (m2 : mor s d) : mor s d'.
    destruct_head Bool; trivial.
  Defined.

  Definition BoolCat_Identity x : mor x x :=
    if x return mor x x then tt else tt.

  Global Arguments BoolCat_Compose [!s !d !d'] m1 m2 / .
  Global Arguments BoolCat_Identity !x / .

  Definition BoolCat : PreCategory.
    refine (@Build_PreCategory Bool
                               (fun s d => mor s d)
                               BoolCat_Identity
                               BoolCat_Compose
                               _
                               _
                               _
                               _);
    abstract (
        intros;
        destruct_head Bool;
        destruct_head Empty;
        destruct_head Unit;
        trivial;
        typeclasses eauto
      ).
  Defined.
End BoolCat.

Instance BoolCatIsStrict : IsStrictCategory BoolCat.
Proof.
  apply hset_decidable.
  repeat intro;
    destruct_head_hnf Bool;
    solve [ left; trivial
          | right; trivial ].
Defined.
