(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(** Typeerties of decidable propositions *)

Require Export HoTT.Overture.

Definition decidable (P:Type) := P \/ ~ P.

Definition dec_not_not : forall P:Type, decidable P -> (~ P -> Empty) -> P
  := fun P ponp nnp => match ponp with
                         | inl p => p
                         | inr np => match nnp np with end
                       end.

Definition dec_True : decidable True
  := inl I.

Definition dec_Empty : decidable Empty
  := inr (fun x => x).

Definition dec_or :
 forall A B:Type, decidable A -> decidable B -> decidable (A \/ B)
  := fun A B HA HB => match HA, HB with
                        | inl a, _ => inl (inl a)
                        | _, inl b => inl (inr b)
                        | inr na, inr nb => inr (fun ab => match ab with
                                                             | inl a => na a
                                                             | inr b => nb b
                                                           end)
                      end.

Definition dec_and :
 forall A B:Type, decidable A -> decidable B -> decidable (A /\ B)
  := fun A B HA HB =>
       match HA, HB with
         | inr na, _ => inr (fun ab => na (fst ab))
         | _, inr nb => inr (fun ab => nb (snd ab))
         | inl a, inl b => inl (a, b)
       end.

Definition dec_not : forall A:Type, decidable A -> decidable (~ A)
  := fun A HA => match HA with
                   | inl a => inr (fun na => na a)
                   | inr na => inl na
                 end.

Definition dec_imp :
 forall A B:Type, decidable A -> decidable B -> decidable (A -> B)
  := fun A B HA HB =>
       match HA, HB with
         | _, inl b => inl (fun _ => b)
         | inr na, _ => inl (fun a => match na a with end)
         | inl a, inr nb => inr (fun f => nb (f a))
       end.

Definition dec_iff :
 forall A B:Type, decidable A -> decidable B -> decidable (A<->B)
  := Eval compute in
      fun A B HA HB =>
        match dec_imp A B HA HB, dec_imp B A HB HA with
          | inl f, inl g => inl (Iff f g)
          | inr nf, _ => inr (fun fg : A <-> B => let (f, g) := fg in nf f)
          | _, inr ng => inr (fun fg : A <-> B => let (f, g) := fg in ng g)
        end.

Definition not_not : forall P:Type, decidable P -> ~ ~ P -> P
  := fun P HP nnP =>
       match HP with
         | inl p => p
         | inr np => match nnP np with end
       end.

Definition not_or : forall A B:Type, ~ (A \/ B) -> ~ A /\ ~ B
  := fun A B nab => (fun a => nab (inl a), fun b => nab (inr b)).

Definition not_and : forall A B:Type, decidable A -> ~ (A /\ B) -> ~ A \/ ~ B
  := fun A B HA nab => match HA with
                         | inl a => inr (fun b => nab (a, b))
                         | inr na => inl na
                       end.

Definition not_imp : forall A B:Type, decidable A -> ~ (A -> B) -> A /\ ~ B
  := fun A B HA nab => (match HA with
                          | inl a => a
                          | inr na => match nab (fun a => match na a with end) with end
                        end,
                        fun b => nab (fun _ => b)).

Definition imp_simp : forall A B:Type, decidable A -> (A -> B) -> ~ A \/ B
  := fun A B HA f => match HA with
                       | inl a => inr (f a)
                       | inr na => inl na
                     end.

Definition not_iff :
  forall A B:Type, decidable A -> decidable B ->
    ~ (A <-> B) -> (A /\ ~ B) \/ (~ A /\ B)
  := fun A B HA HB nab => match HA, HB with
                            | inl a, inr nb => inl (a, nb)
                            | inr na, inl b => inr (na, b)
                            | inl a, inl b => match nab (Iff (fun _ => b) (fun _ => a)) with end
                            | inr na, inr nb => match nab (Iff (fun a => match na a with end) (fun b => match nb b with end)) with end
                          end.

(** Results formulated with iff, used in FSetDecide.
    Negation are expanded since it is unclear whether setoid rewrite
    will always perform conversion. *)

(** We begin with lemmas that, when read from left to right,
    can be understood as ways to eliminate uses of [not]. *)

Definition not_true_iff : (True -> Empty) <-> Empty.
Proof.
  constructor; auto.
Defined.

Definition not_false_iff : (Empty -> Empty) <-> True.
Proof.
  constructor; auto.
Defined.

Local Ltac decide_by_auto :=
  repeat (intros [?|?] || intro);
  constructor; intros; auto;
  refine (match _ : Empty with end);
  unfold not in *;
  auto.

Definition not_not_iff : forall A:Type, decidable A ->
  (((A -> Empty) -> Empty) <-> A).
Proof.
  decide_by_auto.
Defined.

Definition contrapositive : forall A B:Type, decidable A ->
  (((A -> Empty) -> (B -> Empty)) <-> (B -> A)).
Proof.
  decide_by_auto.
Defined.

Definition or_not_l_iff_1 : forall A B: Type, decidable A ->
  ((A -> Empty) \/ B <-> (A -> B))
  := fun A B HA => Iff (fun nab => fun a => match nab with
                                              | inl na => match na a : Empty with end
                                              | inr b => b
                                            end)
                       (fun ab => match HA with
                                    | inl a => inr (ab a)
                                    | inr na => inl na
                                  end).
(*
Lemma or_not_l_iff_2 : forall A B: Type, decidable B ->
  ((A -> Empty) \/ B <-> (A -> B)).
Proof.
unfold decidable. tauto.
Qed.

Lemma or_not_r_iff_1 : forall A B: Type, decidable A ->
  (A \/ (B -> Empty) <-> (B -> A)).
Proof.
unfold decidable. tauto.
Qed.

Lemma or_not_r_iff_2 : forall A B: Type, decidable B ->
  (A \/ (B -> Empty) <-> (B -> A)).
Proof.
unfold decidable. tauto.
Qed.

Lemma imp_not_l : forall A B: Type, decidable A ->
  (((A -> Empty) -> B) <-> (A \/ B)).
Proof.
unfold decidable. tauto.
Qed.


(** Moving Negations Around:
    We have four lemmas that, when read from left to right,
    describe how to push negations toward the leaves of a
    proposition and, when read from right to left, describe
    how to pull negations toward the top of a proposition. *)

Definition not_or_iff : forall A B:Type,
  (A \/ B -> Empty) <-> (A -> Empty) /\ (B -> Empty).
Proof.
tauto.
Qed.

Lemma not_and_iff : forall A B:Type,
  (A /\ B -> Empty) <-> (A -> B -> Empty).
Proof.
tauto.
Qed.

Lemma not_imp_iff : forall A B:Type, decidable A ->
  (((A -> B) -> Empty) <-> A /\ (B -> Empty)).
Proof.
unfold decidable. tauto.
Qed.

Lemma not_imp_rev_iff : forall A B : Type, decidable A ->
  (((A -> B) -> Empty) <-> (B -> Empty) /\ A).
Proof.
unfold decidable. tauto.
Qed.

(* Functional relations on decidable co-domains are decidable *)

Definition dec_functional_relation :
  forall (X Y : Type) (A:X->Y->Type), (forall y y' : Y, decidable (y=y')) ->
  (forall x, exists! y, A x y) -> forall x y, decidable (A x y).
Proof.
intros X Y A Hdec H x y.
destruct (H x) as (y',(Hex,Huniq)).
destruct (Hdec y y') as [->|Hnot]; firstorder.
Qed.
*)
(** With the following hint database, we can leverage [auto] to check
    decidability of propositions. *)

Hint Resolve dec_True dec_Empty dec_or dec_and dec_imp dec_not dec_iff
 : decidable_prop.

(** [solve_decidable using lib] will solve goals about the
    decidability of a proposition, assisted by an auxiliary
    database of lemmas.  The database is intended to contain
    lemmas stating the decidability of base propositions,
    (e.g., the decidability of equality on a particular
    inductive type). *)

Tactic Notation "solve_decidable" "using" ident(db) :=
  match goal with
   | |- decidable _ =>
     solve [ auto 100 with decidable_prop db ]
  end.

Tactic Notation "solve_decidable" :=
  solve_decidable using core.
