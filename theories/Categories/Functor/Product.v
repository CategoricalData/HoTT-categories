Require Export Category Functor.Core Category.Product NaturalTransformation.Core.
Require Import Common Functor.Equality InitialTerminalCategory Functor.Duals.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section ProductCategoryFunctors.
  Context {C : PreCategory}.
  Context {D : PreCategory}.

  Definition fst_Functor : Functor (C * D) C
    := Build_Functor (C * D) C
                     (@fst _ _)
                     (fun _ _ => @fst _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition snd_Functor : Functor (C * D) D
    := Build_Functor (C * D) D
                     (@snd _ _)
                     (fun _ _ => @snd _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End ProductCategoryFunctors.

Section FunctorProduct.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable D' : PreCategory.

  Definition FunctorProduct (F : Functor C D) (F' : Functor C D')
  : Functor C (D * D')
    := Build_Functor
         C (D * D')
         (fun c => (F c, F' c))
         (fun s d m => (MorphismOf F m, MorphismOf F' m))
         (fun _ _ _ _ _ => path_prod' (FCompositionOf F _ _ _ _ _)
                                      (FCompositionOf F' _ _ _ _ _))
         (fun _ => path_prod' (FIdentityOf F _) (FIdentityOf F' _)).

  Local Infix "*" := FunctorProduct : functor_scope.

  Definition FunctorProductFunctorial
             (F G : Functor C D)
             (F' G' : Functor C D')
             (T : NaturalTransformation F G)
             (T' : NaturalTransformation F' G')
  : NaturalTransformation (F * F') (G * G')
    := Build_NaturalTransformation
         (F * F') (G * G')
         (fun x => (T x, T' x))
         (fun _ _ _ => path_prod' (Commutes T _ _ _) (Commutes T' _ _ _)).
End FunctorProduct.

Infix "*" := FunctorProduct : functor_scope.

Section FunctorProduct'.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable C' : PreCategory.
  Variable D' : PreCategory.
  Variable F : Functor C D.
  Variable F' : Functor C' D'.

  Local Open Scope functor_scope.

  Definition FunctorProduct' : Functor (C * C') (D * D')
    := (F ∘ fst_Functor) * (F' ∘ snd_Functor).
End FunctorProduct'.

(*Notation "( x , y , .. , z )" := (FunctorProduct' .. (FunctorProduct' x y) .. z) : functor_scope.*)

Section FunctorProductUniversal.
  Context `{Funext}.

  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.

  Local Open Scope functor_scope.

  Section universal.
    Variable a : Functor C A.
    Variable b : Functor C B.

    Local Transparent ComposeFunctors_FCompositionOf ComposeFunctors_FIdentityOf.

    Lemma FunctorProduct_Commutes_fst : fst_Functor ∘ (a * b) = a.
    Proof.
      functor_eq; trivial.
    Defined.

    Lemma FunctorProduct_Commutes_snd : snd_Functor ∘ (a * b) = b.
    Proof.
      functor_eq; trivial.
    Defined.

    Section unique.
      Variable F : Functor C (A * B).
      Hypothesis H1 : fst_Functor ∘ F = a.
      Hypothesis H2 : snd_Functor ∘ F = b.

      Lemma FunctorProduct_unique_helper
            c
      : (a * b) c = F c.
      Proof.
        pose proof (ap (fun F => ObjectOf F c) H1).
        pose proof (ap (fun F => ObjectOf F c) H2).
        simpl in *.
        path_induction.
        apply eta_prod.
      Defined.

      Lemma FunctorProduct_unique_helper2
      :  transport
           (fun GO : C -> A * B =>
              forall s d : C,
                Morphism C s d ->
                Morphism A (fst (GO s)) (fst (GO d)) *
                Morphism B (snd (GO s)) (snd (GO d)))
           (path_forall (a * b) F FunctorProduct_unique_helper)
           (fun (s d : C) (m : Morphism C s d) =>
              ((a ₁ m)%morphism, (b ₁ m)%morphism)) = MorphismOf F.
      Proof.
        repeat (apply path_forall; intro).
        repeat match goal with
                 | _ => reflexivity
                 | _ => progress simpl
                 | _ => rewrite !transport_forall_constant
                 | [ |- appcontext[?f (transport ?P ?p ?z)] ]
                   => rewrite (@ap_transport _ P _ _ _ p (fun _ => f) z)
               end.
        lazymatch goal with
        | [ |- appcontext[transport
                            (fun f => prod
                                        (?P0 (?fst (f ?x0)) (?fst (f ?x1)))
                                        (?P1 (?snd (f ?x0)) (?snd (f ?x1))))
                            (@path_forall ?H ?A ?B ?f ?g ?e)] ]
          => simpl_do_clear do_rewrite (@path_forall_2_beta
                                          H A B x0 x1
                                          (fun fx0 fx1
                                           => prod (P0 (fst fx0) (fst fx1))
                                                   (P1 (snd fx0) (snd fx1)))
                                          f g)
        end.
        rewrite transport_path_prod'.
        unfold FunctorProduct_unique_helper.
        case H1; simpl; clear H1.
        case H2; simpl; clear H2.
        repeat match goal with
                 | [ |- appcontext[@MorphismOf ?C ?D ?F ?s ?d ?m] ]
                   => destruct (@MorphismOf C D F s d m); clear m
                 | [ |- appcontext[@ObjectOf ?C ?D ?F ?x] ]
                   => destruct (@ObjectOf C D F x); clear x
               end.
        reflexivity.
      Qed.

      Lemma FunctorProduct_unique
      : a * b = F.
      Proof.
        functor_eq.
        exists (path_forall _ _ FunctorProduct_unique_helper).
        apply FunctorProduct_unique_helper2.
      Defined.
    End unique.

    Global Instance FunctorProduct_contr
           `{IsHSet (Functor C A), IsHSet (Functor C B)}
    : Contr { F : Functor C (A * B)
            | fst_Functor ∘ F = a
              /\ snd_Functor ∘ F = b }
      := let x := {| center := (a * b;
                                (FunctorProduct_Commutes_fst,
                                 FunctorProduct_Commutes_snd)) |}
         in x.
    Proof.
      intro y.
      apply path_sigma_uncurried.
      simpl.
      exists (FunctorProduct_unique (fst y.2) (snd y.2)).
      exact (center _).
    Qed.
  End universal.

  Definition path_prod_functor (F G : Functor C (A * B))
             (H1 : fst_Functor ∘ F = fst_Functor ∘ G)
             (H2 : snd_Functor ∘ F = snd_Functor ∘ G)
  : F = G.
  Proof.
    etransitivity; [ apply symmetry | ];
    apply FunctorProduct_unique; try eassumption; reflexivity.
  Defined.
End FunctorProductUniversal.

Section ProductInducedFunctors.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Variable F : Functor (C * D) E.

  Local Ltac t :=
    simpl; intros;
    repeat (rewrite <- ?FCompositionOf, <- ?FIdentityOf, ?LeftIdentity, ?RightIdentity; simpl);
    trivial.

  (** Note: This is just the currying exponential law *)
  Definition InducedProductFstFunctor (d : D) : Functor C E.
  Proof.
    refine (Build_Functor C E
                          (fun c => F (c, d))
                          (fun _ _ m => MorphismOf F (s := (_, _)) (d := (_, _)) (m, Identity d))
                          _
                          _);
    abstract t.
  Defined.

  Definition InducedProductSndFunctor (c : C) : Functor D E.
  Proof.
    refine (Build_Functor D E
                          (fun d => F (c, d))
                          (fun _ _ m => MorphismOf F (s := (_, _)) (d := (_, _)) (Identity c, m))
                          _
                          _);
    abstract t.
  Defined.
End ProductInducedFunctors.

Section notation.
  Global Class FunctorApplicationInterpretable
         {C D} (F : Functor C D)
         {argsT : Type} (args : argsT)
         {T : Type} (rtn : T)
    := {}.

  Definition FunctorApplicationOf {C D} F {argsT} args {T} {rtn}
             `{@FunctorApplicationInterpretable C D F argsT args T rtn}
    := rtn.

  Global Arguments FunctorApplicationOf / {C} {D} F {argsT} args {T} {rtn} {_}.

  Global Instance FunctorApplicationObject C D (F : Functor C D) (x : C)
  : FunctorApplicationInterpretable F x (F x) | 0.

  Global Instance FunctorApplicationDash C D (F : Functor C D)
  : FunctorApplicationInterpretable F (IdentityFunctor C) F | 0.

  Global Instance FunctorApplicationFunctorTerminal C D (F : Functor C D) (c : C)
  : FunctorApplicationInterpretable F (FunctorFromTerminal _ c) (F c) | 0.

  Global Instance FunctorApplicationFunctor B C D (F : Functor C D) (G : Functor B C)
  : FunctorApplicationInterpretable F G (F ∘ G)%functor | 100.

  Global Instance FunctorApplicationObjObj A B D (F : Functor (A * B) D) (a : A) (b : B)
  : FunctorApplicationInterpretable F (a, b) (F (a, b)) | 100.

  Global Instance FunctorApplicationObjFunctorTerminal A B D (F : Functor (A * B) D) (a : A) (b : B)
  : FunctorApplicationInterpretable F (a, FunctorFromTerminal _ b) (F (a, b)) | 0.

  Global Instance FunctorApplicationFunctorTerminalObj A B D (F : Functor (A * B) D) (a : A) (b : B)
  : FunctorApplicationInterpretable F (FunctorFromTerminal _ a, b) (F (a, b)) | 0.

  Global Instance FunctorApplicationFunctorTerminalFunctorFromTerminal A B D (F : Functor (A * B) D) (a : A) (b : B)
  : FunctorApplicationInterpretable F (FunctorFromTerminal _ a, FunctorFromTerminal _ b) (F (a, b)) | 0.

  Global Instance FunctorApplicationObjFunctor A B C D (F : Functor (A * B) D) (a : A) (F' : Functor C B)
  : FunctorApplicationInterpretable F (a, F') (InducedProductSndFunctor F a ∘ F')%functor | 10.

  Global Instance FunctorApplicationObjIdentity A B D (F : Functor (A * B) D) (a : A)
  : FunctorApplicationInterpretable F (a, IdentityFunctor B) (InducedProductSndFunctor F a)%functor | 5.

  Global Instance FunctorApplicationFunctorObj A B C D (F : Functor (A^op * B) D) (F' : Functor C A) (b : B)
  : FunctorApplicationInterpretable F (F', b) (InducedProductFstFunctor F b ∘ F'^op)%functor | 10.

  Global Instance FunctorApplicationIdentityObj A B D (F : Functor (A * B) D) (b : B)
  : FunctorApplicationInterpretable F (IdentityFunctor A, b) (InducedProductFstFunctor F b)%functor | 5.

  (** Do we want this?  (to special case pairs of functors from the
      same category, so that, e.g., if [F : C * C -> D], then [F ⟨ ─ ,
      ─ ⟩] would be the diagonal functor [C -> D], ather than [F]
      itself.  Freenode says:

   freenode / ##categorytheory / jgross  2013-08-03 18:19  ()
       If F is a functor C * C -> D, and you see F(─, ─), how do you interpret it?
   freenode / ##categorytheory / jgross  2013-08-03 18:21  ()
       In particular, is it the functor C -> D which factors through F and the diagonal functor C -> C * C, or is it F itself?
-> freenode / ##categorytheory / Eduard_Munteanu  2013-08-03 18:21  (Eduard_Munteanu!~Eduard_Mu@188.25.7.132)
       jgross: F itself, I'd say
   freenode / ##categorytheory / jgross  2013-08-03 18:22  ()
       Ok, thanks.
   freenode / ##categorytheory / Eduard_Munteanu  2013-08-03 18:22  (Eduard_Munteanu!~Eduard_Mu@188.25.7.132)
       jgross: https://en.wikipedia.org/wiki/Hom_functor#Internal_Hom_functor seems to use that interpretation too
   freenode / ##categorytheory / Cale  2013-08-03 18:23  (Cale!~Cale@99.247.222.118)
       jgross: By * do you mean × ?
   freenode / ##categorytheory / Cale  2013-08-03 18:23  (Cale!~Cale@99.247.222.118)
       (I suppose you do)
   freenode / ##categorytheory / Eduard_Munteanu  2013-08-03 18:23  (Eduard_Munteanu!~Eduard_Mu@188.25.7.132)
       Actually https://en.wikipedia.org/wiki/Hom_functor#Formal_definition too, near the end
   freenode / ##categorytheory / Cale  2013-08-03 18:23  (Cale!~Cale@99.247.222.118)
       In any case, yeah, I would say it would mean F itself.
   freenode / ##categorytheory / jgross  2013-08-03 18:27  ()
       Yes, by * I mean ×.
 *)
  (**  Global Instance FunctorApplicationFunctorFunctor A B C D (F : Functor (A * B) D) (G : Functor C A) (H : Functor C B)
  : FunctorApplicationInterpretable F (G, H) (F ∘ (FunctorProduct G H))%functor | 10.*)

  Global Instance FunctorApplicationFunctorFunctor' A B C C' D (F : Functor (A^op * B) D) (G : Functor C A) (H : Functor C' B)
  : FunctorApplicationInterpretable F (G, H) (F ∘ (FunctorProduct' G^op H))%functor | 100.
End notation.

(** First, a bunch of notations for display *)
Notation "F ⟨ a , F' ⟨ 1 ⟩ ⟩" := (InducedProductSndFunctor F a^op ∘ F')%functor : functor_scope.
Notation "F ⟨ F' ⟨ 1 ⟩ , b ⟩" := (InducedProductFstFunctor F b^op ∘ F')%functor : functor_scope.
Notation "F ⟨ a , 1 ⟩" := (InducedProductSndFunctor F a^op)%functor : functor_scope.
Notation "F ⟨ 1 , b ⟩" := (InducedProductFstFunctor F b^op)%functor : functor_scope.
Notation "F ⟨ a , b ⟩" := (F (a, b)) : functor_scope.
Notation "F ⟨ G ⟨ 1 ⟩ , H ⟨ 1 ⟩ ⟩" := (F ∘ (FunctorProduct' G^op H))%functor : functor_scope.
Notation "F ⟨ 1 , H ⟨ 1 ⟩ ⟩" := (F ∘ (FunctorProduct' (IdentityFunctor _) H))%functor : functor_scope.
Notation "F ⟨ G ⟨ 1 ⟩ , 1 ⟩" := (F ∘ (FunctorProduct' G^op (IdentityFunctor _)))%functor : functor_scope.

(** Now, the fully general notation so the defaults can parse *)
Notation "F ⟨ x ⟩" := (FunctorApplicationOf F%functor x%functor) : functor_scope.
Notation "F ⟨ x , y ⟩" := (FunctorApplicationOf F%functor (x%functor , y%functor)) : functor_scope.

(** Now, the default notations, so that anything we don't cover can
    parse, and everything parses in terms of the general notation *)
Notation "F ⟨ 1 ⟩" := (F ⟨ ( 1 ) ⟩)%functor : functor_scope.
Notation "F ⟨ x , 1 ⟩" := (F ⟨ x , ( 1 ) ⟩)%functor : functor_scope.
Notation "F ⟨ 1 , y ⟩" := (F ⟨ ( 1 ) , y ⟩)%functor : functor_scope.
Notation "F ⟨ 1 , 1 ⟩" := (F ⟨ ( 1 ) , ( 1 ) ⟩)%functor : functor_scope.
Notation "F ⟨ x ⟨ 1 ⟩ ⟩" := (F ⟨ ( x ⟨ 1 ⟩ ) ⟩)%functor : functor_scope.
Notation "F ⟨ x ⟨ 1 ⟩ , y ⟨ 1 ⟩ ⟩" := (F ⟨ ( x ⟨ 1 ⟩ ) , ( y ⟨ 1 ⟩ ) ⟩)%functor : functor_scope.
Notation "F ⟨ x , y ⟨ 1 ⟩ ⟩" := (F ⟨ x , ( y ⟨ 1 ⟩ ) ⟩)%functor : functor_scope.
Notation "F ⟨ 1 , y ⟨ 1 ⟩ ⟩" := (F ⟨ ( 1 ) , ( y ⟨ 1 ⟩ ) ⟩)%functor : functor_scope.
Notation "F ⟨ x ⟨ 1 ⟩ , y ⟩" := (F ⟨ ( x ⟨ 1 ⟩ ) , y ⟩)%functor : functor_scope.
Notation "F ⟨ x ⟨ 1 ⟩ , 1 ⟩" := (F ⟨ ( x ⟨ 1 ⟩ ) , ( 1 ) ⟩)%functor : functor_scope.

(** Redefine the general notation, so it takes precedence when it can *)
Notation "F ⟨ x ⟩" := (FunctorApplicationOf F%functor x%functor) : functor_scope.
Notation "F ⟨ x , y ⟩" := (FunctorApplicationOf F%functor (x%functor , y%functor)) : functor_scope.
(*Notation "F ⟨ c , - ⟩" := (InducedProductSndFunctor F c) : functor_scope.
Notation "F ⟨ - , d ⟩" := (InducedProductFstFunctor F d) : functor_scope.*)
