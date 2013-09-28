Require Export Category.Duals Functor.Duals Cat.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope category_scope.

Section OppositeFunctor.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (SubPreCat P).

  Hypothesis CatHasOps : forall C : Cat, P C.1^op.

  Definition DualFunctor : Functor Cat Cat
    := Build_Functor
         Cat Cat
         (fun C => (C.1^op; CatHasOps _))
         (fun _ _ F => F^op)%functor
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Local Open Scope functor_scope.

  Local Opaque path_sigma_uncurried.

  Definition DualFunctorInvolutive
  : DualFunctor ∘ DualFunctor = IdentityFunctor _.
  Proof.
    functor_eq.
    refine (path_forall
              _
              _
              (fun x
               => path_sigma_uncurried
                    P
                    (((x.1^op)^op)%category;
                     CatHasOps ((x.1^op)%category;
                                CatHasOps x))
                    x
                    (op_op_id x.1; allpath_hprop _ _));
            _).
    repeat (apply path_forall; intro).
    rewrite !transport_forall_constant.
    (* [transport_path_forall_hammer] gives
<<
Toplevel input, characters 20-48:
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
    unfold SubPreCatCat.
    lazymatch goal with
      | [ |- appcontext[transport (fun f => ?P (f ?x0).1 (f ?x1).1) (path_forall ?f ?g _)] ]
        => simpl_do_clear do_rewrite (@path_forall_2_beta _ _ _ x0 x1 (fun fx0 fx1 => P fx0.1 fx1.1) f g)
    end.
    rewrite ?transport_path_prod'_beta.
    simpl in *.
    repeat match goal with
             | [ |- appcontext[transport _ (@path_sigma_uncurried ?A ?P ?u ?v ?pq) ?Qx] ]
               => rewrite (@transport_projT1_path_sigma_uncurried A P u v pq _ Qx);
                 simpl
             | [ |- appcontext[transport (fun x => ?f x.1 ?y) (@path_sigma_uncurried ?A ?P ?u ?v ?pq) ?Qx] ]
               => rewrite (@transport_projT1_path_sigma_uncurried A P u v pq (fun x => f x y) Qx);
                 simpl
           end.
    destruct_head_hnf @sigT.
    destruct_head_hnf @Functor.
    destruct_head_hnf @PreCategory.
    reflexivity.
  Qed.
End OppositeFunctor.
