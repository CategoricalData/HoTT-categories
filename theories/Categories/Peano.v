(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The type [nat] of Peano natural numbers (built from [O] and [S])
    is defined in [Datatypes.v] *)

(** This module defines the following operations on natural numbers :
    - predecessor [pred]
    - addition [plus]
    - multiplication [mult]
    - less or equal order [le]
    - less [lt]
    - greater or equal [ge]
    - greater [gt]

   It states various lemmas and theorems about natural numbers,
   including Peano's axioms of arithmetic (in Coq, these are provable).
   Case analysis on [nat] and induction on [nat * nat] are provided too
 *)

Require Import HoTT.Overture HoTT.types.Empty HoTT.types.Unit.

Open Scope nat_scope.

Local Notation "a <> b" := (~a = b).

Definition paths_S := @ap _ _ S.
Definition ap_nat := @ap nat.
Arguments paths_S : default implicits.
Arguments ap_nat : default implicits.

Hint Resolve paths_S: v62.
Hint Resolve ap_nat: core.

(** The predecessor function *)

Definition pred (n:nat) : nat := match n with
                                 | O => n
                                 | S u => u
                                 end.
Definition ap_pred := @ap _ _ pred.
Arguments ap_pred : default implicits.
Hint Resolve ap_pred: v62.

Theorem pred_Sn : forall n:nat, n = pred (S n).
Proof.
  simpl; reflexivity.
Qed.

(** Injectivity of successor *)

Definition paths_add_S n m (H: S n = S m): n = m := ap pred H.
Hint Immediate paths_add_S: core.

Theorem not_paths_S : forall n m:nat, n <> m -> S n <> S m.
Proof.
  red; auto.
Qed.
Hint Resolve not_paths_S: core.

Definition IsSucc (n:nat) : Prop :=
  match n with
  | O => False
  | S p => True
  end.

(** Zero is not the successor of a number *)

Theorem O_S : forall n:nat, 0 <> S n.
Proof.
  exact (fun n H =>
           match H in (_ = y)
                        return match y with
                                 | 0 => Unit
                                 | _ => Empty
                               end
           with
             | idpath => tt
           end).
Qed.
Hint Resolve O_S: core.

Theorem n_Sn : forall n:nat, n <> S n.
Proof.
  induction n; auto.
Qed.
Hint Resolve n_Sn: core.

(** Addition *)

Fixpoint plus (n m:nat) : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end

where "n + m" := (plus n m) : nat_scope.

(*Definition f_equal2_plus := f_equal2 plus.
Hint Resolve f_equal2_plus: v62.
Definition f_equal2_nat := f_equal2 (A1:=nat) (A2:=nat).
Hint Resolve f_equal2_nat: core.*)

Lemma plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n; simpl; auto.
Qed.
Hint Resolve plus_n_O: core.

Lemma plus_O_n : forall n:nat, 0 + n = n.
Proof.
  auto.
Qed.

Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Proof.
  intros n m; induction n; simpl; auto.
Qed.
Hint Resolve plus_n_Sm: core.

Lemma plus_Sn_m : forall n m:nat, S n + m = S (n + m).
Proof.
  auto.
Qed.

(** Standard associated names *)

Notation plus_0_r_reverse := plus_n_O (compat "8.2").
Notation plus_succ_r_reverse := plus_n_Sm (compat "8.2").

(** Multiplication *)

Fixpoint mult (n m:nat) : nat :=
  match n with
  | O => 0
  | S p => m + p * m
  end

where "n * m" := (mult n m) : nat_scope.
(*Definition f_equal2_mult := f_equal2 mult.
Hint Resolve f_equal2_mult: core.*)

Lemma mult_n_O : forall n:nat, 0 = n * 0.
Proof.
  induction n; simpl; auto.
Qed.
Hint Resolve mult_n_O: core.

Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.
Proof.
  intros; induction n as [| p H]; simpl; auto.
  destruct H; rewrite <- plus_n_Sm; apply paths_S.
  pattern m at 1 3; elim m; simpl; auto.
Qed.
Hint Resolve mult_n_Sm: core.

(** Standard associated names *)

Notation mult_0_r_reverse := mult_n_O (compat "8.2").
Notation mult_succ_r_reverse := mult_n_Sm (compat "8.2").

(** Truncated subtraction: [m-n] is [0] if [n>=m] *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => n
  | S k, O => n
  | S k, S l => k - l
  end

where "n - m" := (minus n m) : nat_scope.

(** Definition of the usual orders, the basic properties of [le] and [lt]
    can be found in files Le and Lt *)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m:nat, n <= m -> n <= S m

where "n <= m" := (le n m) : nat_scope.

Hint Constructors le: core.
(*i equivalent to : "Hints Resolve le_n le_S : core." i*)

Definition lt (n m:nat) := S n <= m.
Hint Unfold lt: core.

Infix "<" := lt : nat_scope.

Definition ge (n m:nat) := m <= n.
Hint Unfold ge: core.

Infix ">=" := ge : nat_scope.

Definition gt (n m:nat) := m < n.
Hint Unfold gt: core.

Infix ">" := gt : nat_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : nat_scope.
Notation "x < y < z" := (x < y /\ y < z) : nat_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : nat_scope.

Theorem le_pred : forall n m, n <= m -> pred n <= pred m.
Proof.
induction 1; auto. destruct m; simpl; auto.
Qed.

Theorem le_S_n : forall n m, S n <= S m -> n <= m.
Proof.
intros n m. exact (le_pred (S n) (S m)).
Qed.

(** Case analysis *)

Theorem nat_case :
 forall (n:nat) (P:nat -> Prop), P 0 -> (forall m:nat, P (S m)) -> P n.
Proof.
  induction n; auto.
Qed.

(** Principle of double induction *)

Theorem nat_double_ind :
 forall R:nat -> nat -> Prop,
   (forall n:nat, R 0 n) ->
   (forall n:nat, R (S n) 0) ->
   (forall n m:nat, R n m -> R (S n) (S m)) -> forall n m:nat, R n m.
Proof.
  induction n; auto.
  destruct m; auto.
Qed.

(** Maximum and minimum : definitions and specifications *)

Fixpoint max n m : nat :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

Fixpoint min n m : nat :=
  match n, m with
    | O, _ => 0
    | S n', O => 0
    | S n', S m' => S (min n' m')
  end.

(*Theorem max_l : forall n m : nat, m <= n -> max n m = n.
Proof.
induction n; destruct m; simpl; auto. inversion 1.
intros. apply f_equal. apply IHn. apply le_S_n. trivial.
Qed.

Theorem max_r : forall n m : nat, n <= m -> max n m = m.
Proof.
induction n; destruct m; simpl; auto. inversion 1.
intros. apply f_equal. apply IHn. apply le_S_n. trivial.
Qed.

Theorem min_l : forall n m : nat, n <= m -> min n m = n.
Proof.
induction n; destruct m; simpl; auto. inversion 1.
intros. apply f_equal. apply IHn. apply le_S_n. trivial.
Qed.

Theorem min_r : forall n m : nat, m <= n -> min n m = m.
Proof.
induction n; destruct m; simpl; auto. inversion 1.
intros. apply f_equal. apply IHn. apply le_S_n. trivial.
Qed.*)

Lemma nat_rect_succ_r {A} (f: A -> A) (x:A) n :
  nat_rect (fun _ => A) x (fun _ => f) (S n) = nat_rect (fun _ => A) (f x) (fun _ => f) n.
Proof.
  induction n; intros; simpl; rewrite <- ?IHn; trivial.
Qed.

Theorem nat_rect_plus :
  forall (n m:nat) {A} (f:A -> A) (x:A),
    nat_rect (fun _ => A) x (fun _ => f) (n + m) =
      nat_rect (fun _ => A) (nat_rect (fun _ => A) x (fun _ => f) m) (fun _ => f) n.
Proof.
  induction n; intros; simpl; rewrite ?IHn; trivial.
Qed.
