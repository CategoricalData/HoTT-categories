Require Export HoTT.
Require Export Notations.

(* fail if [tac] succeeds, do nothing otherwise *)
Tactic Notation "not_tac" tactic(tac) := (tac; fail 1) || idtac.

(* fail if [tac] fails, but don't actually execute [tac] *)
Tactic Notation "test_tac" tactic(tac) := not_tac (not_tac tac).

(* fail if [x] is a function application, a dependent product ([fun _ => _]),
   or a sigma type ([forall _, _]) *)
Ltac atomic x :=
  match x with
    | ?f _ => fail 1 x "is not atomic"
    | (fun _ => _) => fail 1 x "is not atomic"
    | forall _, _ => fail 1 x "is not atomic"
    | _ => idtac
  end.

(* [pose proof defn], but only if no hypothesis of the same type exists.
   most useful for proofs of a proposition *)
Ltac unique_pose defn :=
  let T := type of defn in
    match goal with
      | [ H : T |- _ ] => fail 1
      | _ => pose proof defn
    end.

(* [pose defn], but only if that hypothesis doesn't exist *)
Ltac unique_pose_with_body defn :=
  match goal with
    | [ H := defn |- _ ] => fail 1
    | _ => pose defn
  end.

(* check's if the given hypothesis has a body, i.e., if [clearbody]
   could ever succeed.  We can't just do [test_tac (clearbody H)],
   because maybe the correctness of the proof depends on the body
   of H *)
Tactic Notation "has_no_body" hyp(H) :=
  not_tac (let H' := fresh in pose H as H'; unfold H in H').

Tactic Notation "has_body" hyp(H) :=
  not_tac (has_no_body H).

(* find the head of the given expression *)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

(* call [tac H], but first [simpl]ify [H].
   This tactic leaves behind the simplified hypothesis. *)
Ltac simpl_do tac H :=
  let H' := fresh in pose H as H'; simpl; simpl in H'; tac H'.

(* clear the left-over hypothesis after [simpl_do]ing it *)
Ltac simpl_do_clear tac H := simpl_do ltac:(fun H => tac H; try clear H) H.

Ltac do_with_hyp tac :=
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

Ltac rewrite_hyp' := do_with_hyp ltac:(fun H => rewrite H).
Ltac rewrite_hyp := repeat rewrite_hyp'.
Ltac rewrite_rev_hyp' := do_with_hyp ltac:(fun H => rewrite <- H).
Ltac rewrite_rev_hyp := repeat rewrite_rev_hyp'.

Ltac apply_hyp' := do_with_hyp ltac:(fun H => apply H).
Ltac apply_hyp := repeat apply_hyp'.
Ltac eapply_hyp' := do_with_hyp ltac:(fun H => eapply H).
Ltac eapply_hyp := repeat eapply_hyp'.

(* given a [matcher] that succeeds on some hypotheses and fails on
   others, destruct any matching hypotheses, and then execute [tac]
   after each [destruct].

   The [tac] part exists so that you can, e.g., [simpl in *], to
   speed things up. *)
Ltac destruct_all_matches_then matcher tac :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; tac
         end.

Ltac destruct_all_matches matcher := destruct_all_matches_then matcher ltac:(simpl in *).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

(* matches anything whose type has a [T] in it *)
Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
    | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac destruct_head_hnf_matcher T HT :=
  match head_hnf HT with
    | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(destruct_head_hnf_matcher T).
Ltac destruct_head_hnf' T := destruct_all_matches' ltac:(destruct_head_hnf_matcher T).

(* [expand] replaces both terms of an equality (either [eq] or [JMeq]
   in the goal with their head normal forms *)
Ltac expand :=
  match goal with
    | [ |- ?X = ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' = Y')
    | [ |- ?X == ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' == Y')
  end; simpl.

Definition ap_both A B (f g : A -> B) x y (pf : f = g) (px : x = y) : f x = g y
  := match pf, px with
       | 1%path, 1%path => 1%path
     end.

(* similar to [f_equal], which used to exist in the standard library *)
Ltac f_ap :=
  apply ap_both;
  [ done || f_ap
  | trivial ].
