Require Export Category Functor Cat.
Require Import Common Category.Morphisms.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section GrothendieckCat.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (SubPreCat P).

  (** Quoting Wikipedia:

      The Grothendieck construction is an auxiliary construction used
      in the mathematical field of category theory.

      Let

      [F : C -> Set]

      be a functor from any small category to the category of sets.
      The Grothendieck construct for [F] is the category [Γ F] whose
      objects are pairs [(c, x)], where [c : C] is an object and [x :
      F c] is an element, and for which the set [Hom (Γ F) (c1, x1)
      (c2, x2)] is the set of morphisms [f : c1 -> c2] in [C] such
      that [F.(MorphismOf) f x1 = x2].  *)

  Variable C : PreCategory.
  Variable F : Functor C Cat.

  Record GrothendieckCatPair :=
    {
      GrothendieckCatC : C;
      GrothendieckCatX : Object (projT1 (F GrothendieckCatC))
    }.

  Local Notation GrothendieckCatMorphism s d :=
    { f : Morphism C (GrothendieckCatC s) (GrothendieckCatC d)
    | Morphism _ (MorphismOf F f (GrothendieckCatX s)) (GrothendieckCatX d) }.
Notation X s := (GrothendieckCatX s).
  Definition GrothendieckCatCompose s d d'
             (m1 : GrothendieckCatMorphism d d')
             (m2 : GrothendieckCatMorphism s d)
  : GrothendieckCatMorphism s d'.
  Proof.
    exists (m1.1 ∘ m2.1).
    refine (m1.2 ∘ ((F ₁ m1.1) ₁ m2.2 ∘ idtoiso _ _)).
    exact (ap10 (ap ObjectOf (FCompositionOf F _ _ _ _ _ )) _).
  Defined.

  Definition GrothendieckCatIdentity x : GrothendieckCatMorphism x x.
  Proof.
    exists (Identity (GrothendieckCatC x)).
    refine (idtoiso _ _).
    exact (ap10 (ap ObjectOf (FIdentityOf F _)) _).
  Defined.

  Global Arguments GrothendieckCatIdentity _ / .
  Global Arguments GrothendieckCatCompose _ _ _ _ _ / .

  Definition CategoryOfElements : PreCategory.
  Proof.
    refine (@Build_PreCategory
              GrothendieckCatPair
              (fun s d => GrothendieckCatMorphism s d)
              GrothendieckCatIdentity
              GrothendieckCatCompose
              _
              _
              _
              _);
    repeat intro;
    symmetry;
    apply path_sigma_uncurried;
    [ (exists (inverse (Associativity _ _ _ _ _ _ _ _)))
    | (exists (inverse (LeftIdentity _ _ _ _)))
    | (exists (inverse (RightIdentity _ _ _ _))) ].
    Focus 3.
    destruct f; simpl.
    repeat rewrite ?transport_to_idtoiso, ?idtoiso_inv, ?ap_const, ?LeftIdentity, ?RightIdentity, ?idtoiso_functor, ?idtoiso_comp.
    repeat (f_ap; []).
    simpl.
    clear m.
    rename x into m.


    progress repeat match goal with
                      | [ |- appcontext[inverse (@ap ?A ?B ?f ?x ?y ?p)] ]
                        => rewrite !(@inverse_ap A B f x y p)
                      | [ |- appcontext[inverse (@ap10 ?A ?B ?f ?g ?h ?x)] ]
                        => rewrite <- !(@ap10_V A B f g h x)
                      | [ |- appcontext[fun x => ?f (?g x)] ]
                        => progress change (fun x => f (g x)) with (compose f g)
                      (*| [ |- appcontext[@ap ?B ?C ?h _ _ (@ap10 ?A ?B ?f ?g ?p ?a)] ]
                        => rewrite !(@ap_ap10 A B C f g h p a); unfold compose; simpl*)
                      (*| [ |- appcontext[@ap ?B ?C ?g _ _ (@ap ?A ?B ?f ?x ?y ?p)] ]
                        => let H := fresh in
                           pose proof (@ap_compose A B C f g x y p) as H;
                             simpl in H |- *;
                             rewrite <- !H;
                             clear H;
                             unfold compose; simpl*)
                      | [ |- appcontext[fun x => ?f (?g x) ?y] ]
                        => progress change (fun x => f (g x) y) with (compose (fun x => x y) (fun x => f (g x)))
                    end.
    rewrite ?ap_compose.
    rewrite ?ap_apply_l.

    let GL := match goal with |- ?GL = ?GR => constr:(GL) end in
    let GR := match goal with |- ?GL = ?GR => constr:(GR) end in
    lazymatch GR with
      | appcontext GRC[ap (ObjectOf ?F) (ap10 (ap (@ObjectOf ?C ?D) ?H) ?x)]
        => let GR' := context GRC[ap10 (ap (@ObjectOf _ _) (ap (Compose F) H)) x] in
           (*let GR'' := context GRC[ap (ObjectOf F) (ap10 (ap (@ObjectOf C D) H) x)] in
           assert (GR' = GR''); [ f_ap; generalize H | ]
           transitivity GR''; [ | reflexivity ]; *)
           transitivity GR';
           [
             | f_ap;
               let A := constr:(ap10 (ap (@ObjectOf _ _) (ap (Compose F) H)) x) in
               let B := constr:(ap (ObjectOf F) (ap10 (ap (@ObjectOf C D) H) x)) in
               change (A = B); (* XXX So fragile... :-( *) (*fix indentation - )*)
                 destruct H;
                 reflexivity ]
    end.


    Lemma pre_compose_inverse0 A (x y z : A)
          (p : x = y) (q : x = z) (r : z = y)
          (H' : (q^ @ p = r)%path)
    : (p = q @ r)%path.
    Proof.
      path_induction; reflexivity.
    Defined.
    apply pre_compose_inverse0.
    SearchAbout ap10 inverse.
    Print Implicit ap10_V.
    unfold compose in *; simpl in *.
    repeat match goal with
             | [ |- appcontext[inverse (@ap10 ?A ?B ?f ?g ?h ?x)] ]
               => rewrite <- !(@ap10_V A B f g h x)
             | [ |- appcontext[inverse (@ap ?A ?B ?f ?x ?y ?p)] ]
               => simpl_do_clear ltac:(fun H => rewrite !H) (@inverse_ap A B f x y p)
           end.



    lazymatch goal with
      | [ |- appcontext[@concat ?B ?fx ?f'x ?f''x (@ap10 ?A ?B ?f ?f' ?h ?x) (@ap10 ?A ?B ?f' ?f'' ?h' ?x)] ]
        => pattern (@concat B fx f'x f''x (@ap10 A B f f' h x) (@ap10 A B f' f'' h' x));
          let H := constr:(@ap10_pp A B f f' f'' h h' x) in
          let c := (lazymatch goal with |- ?G ?c => constr:(c) end) in
          let G := (lazymatch goal with |- ?G ?c => constr:(G) end) in
          let c' := (lazymatch type of H with ?c' = ?c'' => constr:(c') end) in
          let c'' := (lazymatch type of H with ?c' = ?c'' => constr:(c'') end) in
          (* sanity check *)
          let sanity_check := constr:(idpath : c = c'') in
          eapply (@transport _ G c' c H)
    end.

lazymatch goal with
      | [ |- appcontext[@concat ?B ?fx ?f'x ?f''x (@ap ?A ?B ?f ?x ?y ?p) (@ap ?A ?B ?f ?y ?z ?q)] ]
        => pattern (@concat B fx f'x f''x (@ap A B f x y p) (@ap A B f y z q));
          let H := constr:(@ap_pp A B f x y z p q) in
          let c := (lazymatch goal with |- ?G ?c => constr:(c) end) in
          let G := (lazymatch goal with |- ?G ?c => constr:(G) end) in
          let c' := (lazymatch type of H with ?c' = ?c'' => constr:(c') end) in
          let c'' := (lazymatch type of H with ?c' = ?c'' => constr:(c'') end) in
          (* sanity check *)
          let sanity_check := constr:(idpath : c = c'') in
          eapply (@transport _ G c' c H)
    end.


    repeat match goal with
             | [ |- appcontext[?f ?x] ]
               => let fx := constr:(f x) in
                  match type of fx with
                    | @paths (Morphism _ _ _) _ _ => generalize (f x); intro
                  end
           end.


    Set Printing Coercions.
    Implicit Arguments ap10 [].
    (** XXX BROKEN CODE HERE *)
(*    progress repeat progress change (fun x => ?f x) with f.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?f' ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => progress change f with f'
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?f' ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let check := constr:(idpath : f = f') in idtac
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?f' ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let F := eval hnf in f in let F' := eval hnf in f' in constr_eq F F'
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?f' ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => pose Type as stupid;
      let F := eval cbv delta [stupid] in f in let F' := eval cbv delta [stupid] in f' in constr_eq F F'
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?f' ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let T := type of f in let T' := type of f' in constr_eq T T'
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?f' ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let F := constr:(fun _ : Set => f) in let F' := constr:(fun _ : Set => f') in constr_eq F F'
    end.
*)

    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let check := constr:(idpath : f = g) in idtac
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => change f with g
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let F := eval hnf in f in let G := eval hnf in g in constr_eq F G
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => pose Type as stupid;
      let F := eval cbv delta [stupid] in f in let G := eval cbv delta [stupid] in g in constr_eq F G
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let T := type of f in let T' := type of g in constr_eq T T'
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let F := constr:(fun _ : Set => f) in let G := constr:(fun _ : Set => g) in constr_eq F G
    end.



    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let check := constr:(eq_refl : f = g) in idtac
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => change f with g
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let F := eval hnf in f in let G := eval hnf in g in constr_eq F G
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => pose Type as stupid;
      let F := eval cbv delta [stupid] in f in let G := eval cbv delta [stupid] in g in constr_eq F G
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let T := type of f in let T' := type of g in constr_eq T T'
    end.
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => let F := constr:(fun _ : Set => f) in let G := constr:(fun _ : Set => g) in constr_eq F G
    end.
and the following fail:
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?g ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => constr_eq f g
    end.
    (* note the lack of the ?f' in the
    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?f ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => constr_eq f f'
    end.





    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?f' ?x0 ?x1 ?x2 ?x3 ?x4' ?x5
    => progress change f with f'
    end.

    lazymatch goal with |- ?f ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = ?f' ?x0' ?x1' ?x2' ?x3' ?x4' ?x5' => generalize f end.





apply ap11.




    rewrite <- ap_pp.



    Implicit Arguments ap10 [].
    rewrite <- ap10_pp.
    re
    rewrite <- H''.
    rewrite <- !ap10_V.
    SearchAbout
    match goal with
      | [ |- ?a = concat ?b ?c ]
        => cut (concat b (concat (inverse b) a) = concat b (concat (inverse b) (concat b c)));
          [ generalize a b c;
            let H := fresh in
            intros ? ? ? H;
              rewrite !concat_p_pp, !concat_pV, !concat_1p in H;
              exact H
          | apply ap;
            rewrite !concat_p_pp, !concat_Vp, !concat_1p ]
    end.
    Print Implicit concat_pV.
    rewrite
    SearchAbout idpath concat.
    SearchAbout (_ @ (_ @ _))%path.

    SearchAbout inverse concat.

    Set Printing Implicit.
    Print Implicit ap10_pp.
    simpl.
    lazymatch goal with
      | [ |- appcontext[@concat ?B ?fx ?f'x ?f''x (@ap10 ?A ?B ?f ?f' ?h ?x) (@ap10 ?A ?B ?f' ?f'' ?h' ?x)] ]
        => pattern (@concat B fx f'x f''x (@ap10 A B f f' h x) (@ap10 A B f' f'' h' x));
          let H := constr:(@ap10_pp A B f f' f'' h h' x) in
          let c := (lazymatch goal with |- ?G ?c => constr:(c) end) in
          let G := (lazymatch goal with |- ?G ?c => constr:(G) end) in
          let c' := (lazymatch type of H with ?c' = ?c'' => constr:(c') end) in
          let c'' := (lazymatch type of H with ?c' = ?c'' => constr:(c'') end) in
          (* sanity check *)
          let sanity_check := constr:(idpath : c = c'') in
          eapply (@transport _ G c' c H)
    end.


    lazymatch goal with
      | [ |- appcontext[concat (@ap10 ?A ?B ?f ?f' ?h ?x)
                               (@ap10 _ _ _ ?f'' ?h' ?x)] ]
        => idtac
    end.

    repeat match goal with
             | [ |- appcontext[?f ?x] ]
               => let fx := constr:(f x) in
                  match type of fx with
                    | @paths (Morphism _ _ _) _ _ => generalize (f x); intro
                  end
           end.

    Set Printing Coercions.



    lazymatch goal with

    end.
    SearchAbout ap compose.
    rewrite ap_compose.


    (*progress repeat match goal with
                      | [ |- appcontext[inverse (@ap ?A ?B ?f ?x ?y ?p)] ]
                        => rewrite !(@inverse_ap A B f x y p)
                      (*| [ |- appcontext[@ap ?B ?C ?h _ _ (@ap10 ?A ?B ?f ?g ?p ?a)] ]
                        => rewrite !(@ap_ap10 A B C f g h p a); unfold compose; simpl*)
                      | [ |- appcontext[@ap ?B ?C ?g _ _ (@ap ?A ?B ?f ?x ?y ?p)] ]
                        => let H := fresh in
                           pose proof (@ap_compose A B C f g x y p) as H;
                             simpl in H |- *;
                             rewrite <- !H;
                             clear H;
                             unfold compose; simpl
                      | [ |- appcontext[fun x => ?f (?g x) ?y] ]
                        => progress change (fun x => f (g x) y) with (compose (fun x => x y) (fun x => f (g x)))
                    end.
    rewrite ?ap_compose.
    rewrite ?ap_apply_l.
    rewrite concat_p_pp.
    simpl.
    progress repeat match goal with
                      | [ |- appcontext[fun x => ?f (?g x)] ]
                        => progress change (fun x => f (g x)) with (compose f g)
                    end.*)
    rewrite ?ap_compose.
(*    progress repeat match goal with
                      | [ |- appcontext[fun x => ?f (?g x)] ]
                        => progress change (fun x => f (g x)) with (compose f g)
                      | [ |- appcontext[fun x y => ?f (?g x y)] ]
                        => progress change (fun x y => f (g x y)) with (fun x => compose f (g x))
                    end.
    rewrite ap_compose.*)

    (*Print ap.
    lazymatch goal with
      | [ |- appcontext[@ap ?A' ?B' (@compose ?A ?B ?C ?g)] ]
        => change (@ap A' B' (@compose A B C g)) with (@ap A' B' (fun f => @compose A B C g f))
    end.*)
    unfold SubPreCatCat.
    simpl.

    Print transport.

(*    etransitivity.
    eapply ap10.
    apply ap.*)

    lazymatch goal with
      | [ |- appcontext[@concat ?B ?fx ?f'x ?f''x (@ap10 ?A ?B ?f ?f' ?h ?x) (@ap10 ?A ?B ?f' ?f'' ?h' ?x)] ]
        => pattern (@concat B fx f'x f''x (@ap10 A B f f' h x) (@ap10 A B f' f'' h' x));
          let H := constr:(@ap10_pp A B f f' f'' h h' x) in
          let c := (lazymatch goal with |- ?G ?c => constr:(c) end) in
          let G := (lazymatch goal with |- ?G ?c => constr:(G) end) in
          let c' := (lazymatch type of H with ?c' = ?c'' => constr:(c') end) in
          let c'' := (lazymatch type of H with ?c' = ?c'' => constr:(c'') end) in
          (* sanity check *)
          let sanity_check := constr:(idpath : c = c'') in
          eapply (@transport _ G c' c H)
    end.

    lazymatch goal with
      | [ |- appcontext[@concat ?B ?fx ?f'x ?f''x (@ap ?A ?B ?f ?x ?y ?p) (@ap ?A ?B ?f ?y ?z ?q)] ]
        => pattern (@concat B fx f'x f''x (@ap A B f x y p) (@ap A B f y z q));
          let H := constr:(@ap_pp A B f x y z p q) in
          let c := (lazymatch goal with |- ?G ?c => constr:(c) end) in
          let G := (lazymatch goal with |- ?G ?c => constr:(G) end) in
          let c' := (lazymatch type of H with ?c' = ?c'' => constr:(c') end) in
          let c'' := (lazymatch type of H with ?c' = ?c'' => constr:(c'') end) in
          (* sanity check *)
          let sanity_check := constr:(idpath : c = c'') in
          eapply (@transport _ G c' c H)
    end.


    repeat match goal with
             | [ |- appcontext[?f ?x] ]
               => let fx := constr:(f x) in
                  match type of fx with
                    | @paths (Morphism _ _ _) _ _ => generalize (f x); intro
                  end
           end.
    rename p into hprop_proof_1.
    rename p0 into hprop_proof_2.
    rename p1 into hprop_proof_3.
    rename x into α, m into β.
    rename a into x, b into y.
    generalize (GrothendieckCatX x); intro Xx.
    simpl in *.

    match goal with
      | [ |- concat (ap10 (ap _ ?f) _) _ = _ ] => generalize f; intro
    end.
    rename p into hprop_proof_4.
    clear hprop_proof_1.
    clear hprop_proof_2.
    move hprop_proof_3 at bottom.
(*    match goal with |- concat ?a ?b = _ => pose b end.
    Set Printing Coercions.
    Check (ap (F ₁ α) (ap10 (ap ObjectOf hprop_proof_3) Xx).
    Set Printing Coercions.
    SearchAbout ap10 ap.
    Print Implicit ap_ap10.
    match goal with
      | [ |- appcontext[@ap ?B ?C ?h ?fa ?ga (@ap10 ?A ?B ?f ?g ?p ?a)] ]
        => rewrite !(@ap_ap10 A B C f g h p a)
    end.
    match goal with
      | [ |- appcontext[@ap ?B ?C ?z ?Nx ?Ny (@ap ?A ?B ?N ?x ?y ?p)] ]
          => pose proof (@ap_apply_Fr A B C x y p z N)
    end.
    conv_rewrite (inverse X).
    match goal with
      | [ |- appcontext[fun x => ?g (?f x)] ] => change (fun x => g (f x)) with (compose g f)
    end.
    SearchAbout ap.
    unfold compose.
    Set Printing Coercions.
    match goal with
      | [ |- appcontext[fun x => ?g (?f x)] ] => change (fun x => g (f x)) with (compose g f)
    end.
    SearchAbout ap.
    etransitivity.
    apply ap.
    rewrite ap_lambda.
    simpl.
    SearchAbout ap compose.
    change
      (fun
                 a : Functor (projT1 (ObjectOf F (GrothendieckCatC x)))
                       (projT1 (ObjectOf F (GrothendieckCatC x))) =>
               compose (ObjectOf (MorphismOf F α)) (ObjectOf a))
      with
      (compose (compose (ObjectOf (MorphismOf F α))) ObjectOf).
    SearchAbout ap.
    Set Printing All.
    Print Implicit ap_apply_Fr.

    Print Implicit ap_pp.
    Print Implicit concat.
    Print Implicit ap.
    lazymatch goal with
      | [ |- appcontext[@concat ?B'' ?fx ?fy ?fz (@ap ?A ?B ?f ?x ?y _)] ]
        => idtac
    end.
    rewrite X.
    conv_rewrite @ap_ap10.
    rewrite <- !ap_apply_l.
    SearchAbout ap10 ap.    Check (fun x => f y x)
    Check (

    Set Printing Implicit.
    Set Printing All.
    Check @ap_pp.
    SearchAbout compose ap.




    left; reflexivity.
    simpl in *.
        => exact (@ap10_pp A B f f' f'' h h' x)
      | [ |- @concat ?B _ _ _ (@ap10 ?A ?B ?f ?f' ?h ?x) (@ap10 ?A ?B ?f' ?f'' ?h' ?x) = _ ]
        => symmetry; exact (@ap10_pp A B f f' f'' h h' x)
    end.

    etransitivity.
    eapply ap10.
    apply ap.
    revert Xx.

    apply ap10.
    apply ap10.
    Set Printing Implicit.
    eapply ap10.
    apply ap.

    rewrite <- ap_pp.

    Focus.
    apply ap10.
    apply ap.
    exact H1.
    let TH := type of H1 in
    let TG := match goal with |- ?G => constr:(G) end in
    assert (TH = TG).
    Focus.


    Set Printing All.
    exact H1.
    Set Printing All.
    apply ap10_pp.
    apply ap.

    Unset Printing Notations.
    Set Printing Implicit.
    Print ap10_pp.






    SearchAbout ap compose.
    Set Printing Implicit.
    Print Implicit ap10_pp.


    unfold SubPreCatCat.
    Set Printing Coercions.
    Unset Printing Notations.
    fold SubPreCatCat.
    unfold SubPreCatCat.
    Set Printing Implicit.
    Unset PRinting
    Set Printing All.
    rewrite <- ap_ap10.
    progress change (fun C0 : PreCategory => P C0) with P.
    Print compose.
    Unset Printing Notations.
    Set Printing Coercions.

    lazymatch goal with
      | [ |- appcontext[fun (x0 : ?T0) (x1 : ?T1) => ?f (ObjectOf x0 x1)] ]
        => change (fun (x0 : T0) (x1 : T1) => f (ObjectOf x0 x1))
           with (compose (fun (x0 : T0) (x1 : T1) => ObjectOf x0 x1) f)
    end.
    Unset Printing Notations.
    change (paths
     (concat
        (concat
           (ap10
              (ap
                 (fun
                    m0 : Morphism C (GrothendieckCatC x) (GrothendieckCatC y) =>
                  MorphismOf F m0) hprop_proof_1) Xx)
           (ap10 (ap ObjectOf hprop_proof_2) Xx))
        (ap10
           (ap
              (fun
                 (x0 : Functor (F (GrothendieckCatC x))
                         (F (GrothendieckCatC x)))
                 (x1 : F (GrothendieckCatC x)) => (MorphismOf F α) (x0 x1))
              hprop_proof_3) Xx)) idpath).
    match goal with
      | [ |- appcontext G[fun m0 : Morphism _ _ _ => ?f m0] ]
        =>
           pose f
    end.
    change ((fun
                         m0 : Morphism C (GrothendieckCatC x) (GrothendieckCatC y) =>
                         @MorphismOf C (@SubPreCat H P HF) F
                                     (GrothendieckCatC x) (GrothendieckCatC y) m0)) with
    (@MorphismOf C (@SubPreCat H P HF) F
                 (GrothendieckCatC x) (GrothendieckCatC y)).
    assert ((fun m0 : Morphism C (GrothendieckCatC x) (GrothendieckCatC y) =>.
               F ₁ m0) = MorphismOf F (s := _) (d := _)).
    reflexivity.
    rewrite X.
    match goal with
      | [ |- appcontext[concat (@ap10 ?A ?B ?f ?f' ?h ?x) (@ap10 ?A' ?B' ?f' ?f'' ?h' ?x)] ]
        => pose proof (@ap10_pp A B f f' f'' h h' x);
          set (X'0 := (@ap10 A B f f' h x)) in *;
          set (X'1 := (@ap10 A' B' f' f'' h' x)) in *;
          set (X'2 := (@ap10 A B' f' f'' h' x)) in *
    end.
    simpl in *.
    rewrite <- X.
    rewrite <- ap10_pp.
    SearchAbout concat ap10.
*) (*   Unset Printing Notations.
    Unset Printing Coercions.
(
    Print ap.
    do 10 match goal with
      | [ |- appcontext[@ap ?A ?B ?f] ] => progress (simpl; change (@ap A B f) with (@ap A B ObjectOf); simpl)
    end.
    rewri.te <- ap10_pp.
    SearchAbout concat.
    SearchAbout ap.
    match goal with
      | [ |- appcontext[(fun m : ?T => @?f m)] ]
        => progress change (fun m : T => f m) with f
    end.
    progress change ((fun m0 : Morphism C (GrothendieckCatC a) (GrothendieckCatC b) =>
                        F ₁ m0)) with (MorphismOf F).


    SearchAbout ap compose.
    Print Implicit ObjectOf.
    match goal with
      | [ |- appcontext[ap (@ObjectOf ?A ?B)] ] =>
        set (OO := @ObjectOf A B)
    end.
    match goal with
      | [ |- appcontext[ap (fun (x0 : ?T0) (x1 : @?T1 x0) => @?T2 x0 x1)] ]
        => set (OO' := (fun (x0 : T0) (x1 : T1 x0) => T2 x0 x1))
    end.
    subst OO OO'.
    simpl.
    unfold OO, OO'.
    simpl.

    Check (GrothendieckCatX a).
    pose (change OO' with OO.)
    simpl in *.
   o
        match goal with
          | [ |- appcontext[ap ?f] ] =>
            progress change f with (@ObjectOf A B)
        end
    end.
    Set Printing Implicit.
    match goal with
      | [ |-
    change ((fun
             (x0 : Functor (F (GrothendieckCatC a)) (F (GrothendieckCatC a)))
             (x1 : F (GrothendieckCatC a)) => (F ₁ x) (x0 x1))) with ObjectOf.
    simpl in *.
    rewrite <- p.
    change ((fun (f' : F (GrothendieckCatC a) -> F (GrothendieckCatC a))
             (x0 : F (GrothendieckCatC a)) => (F ₁ x) (f' x0))) with ObjectOf.
    ap10_pp:
  forall (A B : Type) (f f' f'' : A -> B) (h : f = f')
    (h' : f' = f'') (x : A),

  ap10 (h @ h')%path x = (ap10 h x @ ap10 h' x)%path

*)

    SearchAbout ap ap11.
    Print Implicit ap11.
    Print Implicit ap.
    Print Implicit ap10.

    Print inverse_ap.
    Print Implicit ap11.
    Lemma inverse_ap11 A B (f g : A -> B) (p1 : f = g) (x y : A) (p2 : x = y)
    : ((ap11 p1 p2)^ = ap11 p1^ p2^)%path.
    Proof.
      path_induction; reflexivity.
    Defined.
    Print Implicit ap11.
    Print ap_pp.
    SearchAbout ap inverse.
    Print ap.
    repeat match goal with
             | [ |- appcontext[inverse (@ap ?A ?B ?f ?x ?y ?p)] ]
               => rewrite !(@inverse_ap A B f x y p)
           end.
    Lemma ap11_pp A B (f g h : A -> B) (p1 : f = g) (p2 : g = h)
          (x y z : A) (q1 : x = y) (q2 : y = z)
    : (ap11 (p1 @ p2) (q1 @ q2) = ap11 p1 q1 @ ap11 p2 q2)%path.
    Proof.
      path_induction; reflexivity.
    Defined.
    Lemma ap10_ap_ap11 A B (f g : A -> B) (p : f = g)
          (x y : A) (q : x = y)
    : (ap10 p x @ ap g q = ap11 p q)%path.
    Proof.
      path_induction; reflexivity.
    Defined.
    Lemma ap_ap10_ap11 A B (f g : A -> B) (p : f = g)
          (x y : A) (q : x = y)
    : (ap f q @ ap10 p y = ap11 p q)%path.
    Proof.
      path_induction; reflexivity.
    Defined.
    SearchAbout ap10 ap.
    (*match goal with
      | [ |- appcontext[concat (@ap10 ?A ?B ?f ?g ?e ?x') (@ap ?A ?B ?e' ?x ?y ?p)] ]
        => pose proof (@ap11 A B f g e x y p)
    end.
    *)

    repeat match goal with
             | [ |- appcontext[@ap ?A ?B ?f ?x ?y ?e] ]
               => progress change (@ap A B f x y e) with (@ap11 A B f f idpath x y e)
             | [ |- appcontext[@ap10 ?A ?B ?f ?g ?e ?x] ]
               => progress change (@ap10 A B f g e x) with (@ap11 A B f g e x x idpath)
             | [ |- appcontext[inverse (@ap11 ?A ?B ?f ?g ?e ?x ?y ?p)] ]
               => rewrite !(@inverse_ap11 A B f g e x y p)
           end.
    Opaque ap11.
    simpl.

    lazymatch goal with
      | [ |- concat (ap11 ?f idpath) (ap11 idpath ?g) = _ ]
        => pose (ap11 f g)
    end.


    Implicit Arguments ap11 [A B x y].

        simpl in *.
    etransitivity p.


    Print Implicit ap11.
    repeat match goal with
             | [ |- appcontext[@ap11 ?A ?B ?f ?g ?p ?x ?y ?q] ]
               => first [ generalize dependent f
                        | generalize dependent g
                        | generalize dependent x
                        | generalize dependent y ];
                 intros
           end.



    repeat match goal with
             | [ |- appcontext[?f ?x] ]
               => let fx := constr:(f x) in
                  match type of fx with
                    | @paths (Morphism _ _ _) _ _ => generalize (f x); intro
                  end
           end.
    rename p into hprop_proof_1.
    rename p0 into hprop_proof_2.
    rename p1 into hprop_proof_3.
    rename x into α, m into β.
    rename a into x, b into y.

    repeat match goal with
             | [ |- appcontext[@ap11 ?A ?B ?f ?g ?e ?x ?y ?p] ]
               => let H := fresh in
                  set (H := @ap11 A B f g e x y p)
           end.

    Set Printing Implicit.
    Transparent ap11.
    pose (ap11 1%path hprop_proof_3).




    Print ap.
    Check ((ap ObjectOf hprop_proof_2)).
     Check (F ₁ (α ∘ Identity (GrothendieckCatC x))).
     Check (F ₁ α).
    Check ((ap
      (fun m : Morphism C (GrothendieckCatC x) (GrothendieckCatC y) =>
       (F ₁ m) (GrothendieckCatX x)) hprop_proof_1)).
    Local Notation "x _∫₁" := (GrothendieckCatC x) (at level 30).
    Local Notation "x _∫₂" := (GrothendieckCatX x) (at level 30).
    Local Notation "x ~~C~~> y" := (Morphism C x y) (at level 30).
Print ap.    Local Notation FunctorOnObjects := ObjectOf.
∫₁ ₂
    lazymatch goal with
    | [ |- appcontext[concat (@ap11 ?A ?B ?f ?g ?e ?x ?y ?p) (@ap11 ?A ?B ?f' ?g' ?e' ?x' ?y' ?p')] ]
      => pose proof (@ap11_pp A B f g); pose e; pose e'
    end.
    simpl in *.
    rewrite <- !ap11_pp.

    rewrite inverse_ap11.
    SearchAbout inverse ap11.

    ap11 :
forall (A B : Type) (f g : A -> B),
f = g -> forall x y : A, x = y -> f x = g y
    Print Implicit apD10.
//    Print Implicit ap.
    SearchAbout ap ap10.
    SearchAbout (_ @ apD10 _ _)%path.
    rewrite ap_const.
    SearchAbout ap.
    SearchAbout (ap (fun _ => _)).
    Focus 2.
        simpl.
    repeat match goal with
             | [ |- appcontext[idtoiso _ (?f ?x)] ] => generalize (f x); intro
           end.
    pose (GrothendieckCatX b).
    simpl in *.
    simpl in *.
    unfold SubPreCatCat in *.
    simpl in *.
    Set Printing All.

    unfold SubPreCat in *.
    simpl in *.
    destruct ((RightIdentity C (GrothendieckCatC a) (GrothendieckCatC b) x)).
    autorewrite with morphism.

    Print transport.




    Goal forall (C : PreCategory) s d (m : Morphism C s d)

    Check ((F ₁ (Identity (GrothendieckCatC b)))).
    Check ((F ₁ (Identity (GrothendieckCatC b))) ₁ m).
    etransitivity; [ apply ap | ].


    unfold GrothendieckCatCompose, GrothendieckCatIdentity.
    simpl.
    destruct f.
    simpl.

    progress change (@existT (Morphism C (GrothendieckCatC a) (GrothendieckCatC b))
                             (fun f : Morphism C (GrothendieckCatC a) (GrothendieckCatC b) =>
                                Morphism (F (GrothendieckCatC b) : SubPreCatObject _) ((F ₁ f) (GrothendieckCatX a))
                                         (GrothendieckCatX b)))
    with (@existT (Morphism C (GrothendieckCatC a) (GrothendieckCatC b))
                  (fun f : Morphism C (GrothendieckCatC a) (GrothendieckCatC b) =>
                     Morphism (F (GrothendieckCatC b) : SubPreCatObject _) ((F ₁ f) (GrothendieckCatX a))
                              ((Identity (F (GrothendieckCatC b))) (GrothendieckCatX b)))).


    change ((IdentityFunctor (F (GrothendieckCatC b) : SubPreCatObject _))) with (Identity (F (GrothendieckCatC b))).
    change idmap with (ObjectOf (Identity (F (GrothendieckCatC b)))).
    let C := match goal with |- appcontext[@idtoiso ?C ?a _] => constr:(C) end in
    let a := match goal with |- appcontext[@idtoiso ?C ?a _] => constr:(a) end in
    let b := match goal with |- appcontext[@idtoiso ?C ?a (GrothendieckCatX ?b)] => constr:(b) end in
    change (@idtoiso C a (GrothendieckCatX b))
    with (@idtoiso C a ((Identity (F (GrothendieckCatC b))) (GrothendieckCatX b)));
      change (@IsomorphicMorphism C a (GrothendieckCatX b))
      with (@IsomorphicMorphism C a ((Identity (F (GrothendieckCatC b))) (GrothendieckCatX b))).
    let C := match goal with |- appcontext[@Compose ?C ?x ?y (GrothendieckCatX ?b)] => constr:(C) end in
    let x := match goal with |- appcontext[@Compose ?C ?x ?y (GrothendieckCatX ?b)] => constr:(x) end in
    let y := match goal with |- appcontext[@Compose ?C ?x ?y (GrothendieckCatX ?b)] => constr:(y) end in
    let b := match goal with |- appcontext[@Compose ?C ?x ?y (GrothendieckCatX ?b)] => constr:(b) end in
    change (@Compose C x y (GrothendieckCatX b))
    with (@Compose C x y ((Identity (F (GrothendieckCatC b))) (GrothendieckCatX b))).
    Print transport.
    Require Import HoTT.hit.Interval.
    Goal forall A (x x0 : A) (H : x = x0), transport (fun _ : interval => A) seg x = x0.
    clear; intros; generalize seg; generalize one; intros s []; assumption.
    Qed.
  Eval simpl in fun (A : Type) (x x0 : A) (H : x = x0) =>
(fun (s : interval) (p : zero = s) =>
 match
   p as p0 in (_ = y) return (transport (fun _ : interval => A) p0 x = x0)
 with
 | 1%path => H
 end) one seg.
  Print Unnamed_thm.
    intros.
    generalize seg.
    generalize one.
    intros.
    destruct p.
    simpl.
    assumption.
  Qed.

    destruct ((FIdentityOf F (GrothendieckCatC b))).
    Implicit Arguments idtoiso [].
    pose ((FIdentityOf F (GrothendieckCatC b))).
apply path_sigma_uncurried; simpl; exists (LeftIdentity _ _ _ _); simpl.

    Implicit Arguments ap10 [].
    pose (Identity (F (GrothendieckCatC b))).
    simpl in m0.

    unfold ap.
    unfold ap10.
    unfold apD10.
    unfold idtoiso.
    simpl.
    destruct ((FIdentityOf F (GrothendieckCatC b))).
    destruct (LeftIdenntity
    apply path_sigma_uncurried;
    [ (exists (Associativity _ _ _ _ _ _ _ _))
    | (exists (LeftIdentity _ _ _ _))
    | (exists (RightIdentity _ _ _ _)) ].
    simpl.
    Focus 2.
    destruct f; simpl.
    etransitivity.
    apply ap.
    match goal with |- ?a = ?b => generalize b end.
    apply ap.

    simpl.
   lazymatch goal with
    | [ |- transport ?P ?f ?x = _ ]
      => etransitivity (transport P f ((idtoiso _
                                                (ap10 (ap ObjectOf (FIdentityOf F (GrothendieckCatC b)))
                                                      (GrothendieckCatX b)))
                                         ∘ m))
    end.
    apply ap.
    match goal with |- ?a = ?b => generalize b end.

    etransitivity
    apply ap.
    instantiate (1 := m).
    destruct C; simpl.
    pose (LeftIdentity C (GrothendieckCatC a) (GrothendieckCatC b) x).

    generalize ((FIdentityOf F (GrothendieckCatC b))).


    unfold transport.
    simpl in *.
    case (FIdentityOf F (GrothendieckCatC b)).
    Show Proof.
    match goal with |- @paths ?T _ _ => pose T end.
    simpl in *.

    abstract (
        repeat intro;
        apply path_sigma_uncurried; simpl;
            exact (center _)
      ).
  Defined.

  Definition GrothendieckCatFunctor : Functor CategoryOfElements C
    := Build_Functor CategoryOfElements C
                     GrothendieckCatC
                     (fun s d => @projT1 _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End GrothendieckCat.
*)
