Require Export Category DiscreteCategory.
Require Import Common.

Set Universe Polymorphism.

Fixpoint CardinalityRepresentative (n : nat) : Set :=
  match n with
    | 0 => Empty
    | 1 => Unit
    | S n' => (CardinalityRepresentative n' + Unit)%type
  end.

Coercion CardinalityRepresentative : nat >-> Sortclass.

Local Open Scope equiv_scope.

Definition sigT_of_sum A B (x : A + B) : { b : Bool & if b then A else B }
  := (_;
      match
        x as s
        return
        (if match s with
              | inl _ => true
              | inr _ => false
            end then A else B)
      with
        | inl a => a
        | inr b => b
      end).

Definition sum_of_sigT A B (x : { b : Bool & if b then A else B }) : A + B
  := match x with
       | (true; a) => inl a
       | (false; b) => inr b
     end.

Instance isequiv_sigT_of_sum A B : IsEquiv (sigT_of_sum A B).
Proof.
  apply (isequiv_adjointify (sigT_of_sum A B)
                            (sum_of_sigT A B));
  repeat intro; expand;
  destruct_head sigT;
  destruct_head sum;
  destruct_head Bool;
  simpl;
  reflexivity.
Defined.

Instance isequiv_sum_of_sigT A B : IsEquiv (sum_of_sigT A B)
  := isequiv_inverse.

Instance trunc_if n A B `{IsTrunc n A, IsTrunc n B} (b : Bool)
: IsTrunc n (if b then A else B)
  := if b as b return (IsTrunc n (if b then A else B)) then _ else _.

Instance trunc_sum n A B `{IsTrunc n Bool, IsTrunc n A, IsTrunc n B} : IsTrunc n (A + B).
Proof.
  eapply trunc_equiv'; [ esplit;
                         exact (@isequiv_sum_of_sigT _ _)
                       | ].
  typeclasses eauto.
Defined.

Instance trunc_CardinalityRepresentative (n : nat) : IsHSet (CardinalityRepresentative n).
Proof.
  induction n; [ typeclasses eauto |].
  induction n; [ typeclasses eauto |].
  intros [x|x] [y|y];
  typeclasses eauto.
Qed.

Definition NatCategory (n : nat) := DiscreteCategory n.

Coercion NatCategory : nat >-> PreCategory.

Typeclasses Transparent NatCategory.
Hint Unfold NatCategory.
Arguments NatCategory / .
