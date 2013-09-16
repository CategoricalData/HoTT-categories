Require Export Category.Sum Functor.Core Functor.Composition Functor.Identity.
Require Import Common Functor.Equality.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section SumCategoryFunctors.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition inl_Functor : Functor C (C + D)
    := Build_Functor C (C + D)
                     (@inl _ _)
                     (fun _ _ m => m)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition inr_Functor : Functor D (C + D)
    := Build_Functor D (C + D)
                     (@inr _ _)
                     (fun _ _ m => m)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End SumCategoryFunctors.

Section sum_functor.
  Variable C : PreCategory.
  Variable C' : PreCategory.
  Variable D : PreCategory.

  Definition sum_Functor (F : Functor C D) (F' : Functor C' D)
  : Functor (C + C') D.
  Proof.
    refine (Build_Functor
              (C + C') D
              (fun cc'
               => match cc' with
                    | inl c => F c
                    | inr c' => F' c'
                  end)
              (fun s d
               => match s, d with
                    | inl cs, inl cd => MorphismOf F (s := cs) (d := cd)
                    | inr c's, inr c'd => MorphismOf F' (s := c's) (d := c'd)
                    | _, _ => fun m => match m with end
                  end)
              _
              _);
    abstract (
        repeat (intros [] || intro);
        simpl in *;
          auto with functor
      ).
  Defined.
End sum_functor.

Section swap_functor.
  Definition sum_swap_Functor C D
  : Functor (C + D) (D + C)
    := sum_Functor (inr_Functor _ _) (inl_Functor _ _).

  Local Open Scope functor_scope.

  Definition sum_swap_swap_id_helper {C D} c
  : (sum_swap_Functor C D) ((sum_swap_Functor D C) c)
    = c
    := match c with inl _ => idpath | inr _ => idpath end.

  Lemma sum_swap_swap_id `{Funext} C D
  : sum_swap_Functor C D ∘ sum_swap_Functor D C = 1.
  Proof.
    functor_eq.
    exists (path_forall _ _ sum_swap_swap_id_helper).
    repeat (apply (@path_forall _) || intros [] || intro);
      repeat match goal with
               | [ |- appcontext[transport (fun x => forall y, @?C x y) ?p ?f ?x] ]
                 => simpl_do_clear do_rewrite (@transport_forall_constant _ _ C _ _ p f x)
             end;
      transport_path_forall_hammer;
      trivial.
  Qed.
End swap_functor.

Notation "F + G" := (sum_Functor F G) : functor_scope.
