Require Export Category Functor.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Notation CatOf obj :=
  (@Build_PreCategory obj
                      (fun x y => x -> y)
                      (fun _ x => x)
                      (fun _ _ _ f g => f o g)
                      (fun _ _ _ _ _ _ _ => idpath)
                      (fun _ _ _ => idpath)
                      (fun _ _ _ => idpath)
                      _).

(** There is a category [Set], where the objects are sets and the
    morphisms are set morphisms *)

Definition PropCat `{Funext} : PreCategory := CatOf hProp.
Definition SetCat `{Funext} : PreCategory := CatOf hSet.

Section SetCoercionsDefinitions.
  Context `{Funext}.

  Variable C : PreCategory.

  Definition FunctorToProp := Functor C PropCat.
  Definition FunctorToSet := Functor C SetCat.

  Definition FunctorFromProp := Functor PropCat C.
  Definition FunctorFromSet := Functor SetCat C.
End SetCoercionsDefinitions.

Identity Coercion FunctorToProp_Id : FunctorToProp >-> Functor.
Identity Coercion FunctorToSet_Id : FunctorToSet >-> Functor.
Identity Coercion FunctorFromProp_Id : FunctorFromProp >-> Functor.
Identity Coercion FunctorFromSet_Id : FunctorFromSet >-> Functor.

Section SetCoercions.
  Context `{Funext}.

  Variable C : PreCategory.

  Definition FunctorTo_Prop2Set (F : FunctorToProp C) : FunctorToSet C :=
    Build_Functor C SetCat
                  (fun x => BuildhSet (F x) _)
                  (fun s d m => MorphismOf F m)
                  (fun s d d' m m' => FCompositionOf F s d d' m m')
                  (fun x => FIdentityOf F x).

  Definition FunctorFrom_Set2Prop (F : FunctorFromSet C) : FunctorFromProp C
    := Build_Functor PropCat C
                     (fun x => F (BuildhSet x _))
                     (fun s d m => MorphismOf F (m : Morphism SetCat
                                                              (BuildhSet s _)
                                                              (BuildhSet d _)))
                     (fun s d d' m m' => FCompositionOf F
                                                        (BuildhSet s _)
                                                        (BuildhSet d _)
                                                        (BuildhSet d' _)
                                                        m
                                                        m')
                     (fun x => FIdentityOf F (BuildhSet x _)).
End SetCoercions.

Coercion FunctorTo_Prop2Set : FunctorToProp >-> FunctorToSet.
Coercion FunctorFrom_Set2Prop : FunctorFromSet >-> FunctorFromProp.
