Require Export Subcategory.Sigma Functor.Composition Functor.Identity.
Require Import Common Functor.Equality.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section sigT_mor.
  Variable A : PreCategory.
  Variable Pmor : forall s d, Morphism A s d -> Type.

  Local Notation mor s d := (sigT (Pmor s d)).
  Context `(HPmor : forall s d, IsHSet (mor s d)).

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 ∘ m2).

  Local Notation identity x := (@Identity A x; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 ∘ m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_Associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).

  Hypothesis P_LeftIdentity
  : forall a b (f : mor a b),
      compose (identity b) f = f.

  Hypothesis P_RightIdentity
  : forall a b (f : mor a b),
      compose f (identity a) = f.

  Definition Category_sigT_mor : PreCategory.
  Proof.
    refine (@Build_PreCategory
              (Object A)
              (fun s d => mor s d)
              (fun x => identity x)
              (fun s d d' m1 m2 => compose m1 m2)
              _
              _
              _
              _);
    assumption.
  Defined.

  Definition projT1_mor_functor : Functor Category_sigT_mor A
    := Build_Functor
         Category_sigT_mor A
         idmap
         (fun _ _ => @projT1 _ _)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition Category_sigT_mor_as_sigT : PreCategory.
  Proof.
    refine (@Category_sigT A (fun _ => Unit) (fun s d => @Pmor (projT1 s) (projT1 d)) _ (fun _ => Pidentity _) (fun _ _ _ _ _ m1 m2 => Pcompose m1 m2) _ _ _);
    intros; trivial.
  Defined.

  Definition sigT_functor_mor : Functor Category_sigT_mor_as_sigT Category_sigT_mor
    := Build_Functor
         Category_sigT_mor_as_sigT Category_sigT_mor
         (@projT1 _ _)
         (fun _ _ => idmap)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition sigT_functor_mor_inv : Functor Category_sigT_mor Category_sigT_mor_as_sigT
    := Build_Functor
         Category_sigT_mor Category_sigT_mor_as_sigT
         (fun x => existT _ x tt)
         (fun _ _ => idmap)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Local Open Scope functor_scope.

  Lemma sigT_mor_eq `{Funext}
  : sigT_functor_mor ∘ sigT_functor_mor_inv = IdentityFunctor _
    /\ sigT_functor_mor_inv ∘ sigT_functor_mor = IdentityFunctor _.
  Proof.
    split; functor_eq; simpl.
    refine (existT
              _
              (path_forall
                 _
                 _
                 (fun x
                  => match x with
                       | (_; tt) => _
                     end))
              _).
    instantiate (1 := idpath).
    repeat (apply path_forall; intro).
    destruct_head @sigT.
    destruct_head Unit.
    rewrite !transport_forall_constant.
    (** [transport_path_forall_hammer] gives
<<
Toplevel input, characters 21-49:
In nested Ltac calls to "transport_path_forall_hammer" and
"rewrite ?transport_path_prod'_beta', ?transport_const", last call failed.
Anomaly: Uncaught exception Invalid_argument("to_constraints: non-trivial algebraic constraint between universes", _).
Please report.
frame @ file "tactics/tacinterp.ml", line 72, characters 6-11
frame @ file "proofs/refiner.ml", line 107, characters 46-77
frame @ file "proofs/refiner.ml", line 85, characters 6-134
frame @ file "lib/cList.ml", line 290, characters 19-24
frame @ file "proofs/refiner.ml", line 43, characters 16-35
frame @ file "proofs/refiner.ml", line 234, characters 37-54
raise @ file "proofs/refiner.ml", line 226, characters 15-16
frame @ file "proofs/refiner.ml", line 232, characters 4-8
frame @ file "proofs/refiner.ml", line 170, characters 13-22
frame @ file "proofs/refiner.ml", line 125, characters 30-60
frame @ file "proofs/refiner.ml", line 85, characters 6-134
frame @ file "lib/cList.ml", line 290, characters 19-24
frame @ file "proofs/refiner.ml", line 43, characters 16-35
frame @ file "proofs/refiner.ml", line 429, characters 14-49
frame @ file "proofs/refiner.ml", line 107, characters 13-78
frame @ file "proofs/refiner.ml", line 85, characters 6-134
frame @ file "lib/cList.ml", line 290, characters 19-24
frame @ file "proofs/refiner.ml", line 43, characters 16-35
frame @ file "proofs/refiner.ml", line 107, characters 46-77
frame @ file "proofs/refiner.ml", line 85, characters 6-134
frame @ file "lib/cList.ml", line 290, characters 19-24
frame @ file "proofs/refiner.ml", line 43, characters 16-35
frame @ file "tactics/equality.ml", line 332, characters 10-144
frame @ file "proofs/refiner.ml", line 107, characters 13-78
frame @ file "proofs/refiner.ml", line 85, characters 6-134
frame @ file "lib/cList.ml", line 290, characters 19-24
frame @ file "proofs/refiner.ml", line 43, characters 16-35
frame @ file "tactics/equality.ml", line 299, characters 4-183
frame @ file "proofs/refiner.ml", line 107, characters 46-77
frame @ file "proofs/refiner.ml", line 85, characters 6-134
frame @ file "lib/cList.ml", line 290, characters 19-24
frame @ file "proofs/refiner.ml", line 43, characters 16-35
frame @ file "proofs/refiner.ml", line 107, characters 13-78
frame @ file "proofs/refiner.ml", line 85, characters 6-134
frame @ file "lib/cList.ml", line 290, characters 19-24
frame @ file "proofs/refiner.ml", line 43, characters 16-35
frame @ file "proofs/refiner.ml", line 180, characters 13-21
frame @ file "proofs/clenvtac.ml", line 80, characters 26-66
frame @ file "proofs/clenv.ml", line 283, characters 12-58
raise @ unknown
frame @ file "pretyping/unification.ml", line 1269, characters 7-49
frame @ file "pretyping/unification.ml", line 1199, characters 22-72
raise @ unknown
frame @ file "pretyping/unification.ml", line 1177, characters 5-62
raise @ unknown
frame @ file "pretyping/unification.ml", line 1098, characters 6-17
raise @ unknown
frame @ file "pretyping/unification.ml", line 1060, characters 3-14
raise @ unknown
frame @ file "pretyping/unification.ml", line 1050, characters 12-50
frame @ file "pretyping/unification.ml", line 1010, characters 5-70
frame @ file "pretyping/unification.ml", line 499, characters 12-60
raise @ unknown
frame @ file "pretyping/unification.ml", line 507, characters 6-117
frame @ file "lib/cArray.ml", line 233, characters 33-52
frame @ file "pretyping/unification.ml", line 480, characters 34-82
raise @ unknown
frame @ file "pretyping/unification.ml", line 508, characters 1-50
frame @ file "pretyping/unification.ml", line 401, characters 15-62
frame @ file "pretyping/unification.ml", line 377, characters 13-67
raise @ unknown
frame @ file "pretyping/reductionops.ml", line 781, characters 14-59
frame @ file "set.ml", line 310, characters 37-58
raise @ file "kernel/univ.ml", line 1752, characters 9-102
>> *)
    lazymatch goal with
      | [ |- appcontext[transport (fun f => sigT (?P (f ?x0).1 (f ?x1).1)) (path_forall ?f ?g _)] ]
        => simpl_do_clear do_rewrite (@path_forall_2_beta _ _ _ x0 x1 (fun fx0 fx1 => sigT (P fx0.1 fx1.1)) f g)
    end.
    reflexivity.
  Qed.

  Definition sigT_mor_compat : projT1_mor_functor ∘ sigT_functor_mor = projT1_functor
    := idpath.
End sigT_mor.

Arguments projT1_mor_functor {A Pmor _ Pidentity Pcompose P_Associativity P_LeftIdentity P_RightIdentity}.
