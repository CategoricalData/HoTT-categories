Require Export Category Category.Objects.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

Section OppositeCategory.
  Definition OppositeCategory (C : PreCategory) : PreCategory
    := @Build_PreCategory' C
                           (fun s d => Morphism C d s)
                           (Identity (C := C))
                           (fun _ _ _ m1 m2 => Compose m2 m1)
                           (fun _ _ _ _ _ _ _ => @Associativity_sym _ _ _ _ _ _ _ _)
                           (fun _ _ _ _ _ _ _ => @Associativity _ _ _ _ _ _ _ _)
                           (fun _ _ => @RightIdentity _ _ _)
                           (fun _ _ => @LeftIdentity _ _ _)
                           _.
End OppositeCategory.

Notation "C ^op" := (OppositeCategory C) : category_scope.


(* This notation should be [only parsing] for now, because otherwise
   copy/paste doesn't work, because the parser doesn't recognize the
   unicode characters [ᵒᵖ].  So, really, this notation is just a
   reminder to do something when Coq's parser is better. *)

Notation "C ᵒᵖ" := (OppositeCategory C) (only parsing) : category_scope.

Section DualCategories.
  Lemma op_op_id C : (C ^op) ^op = C.
    destruct C; exact idpath.
  Defined.
End DualCategories.

Hint Rewrite @op_op_id : category.

Section DualObjects.
  Variable C : Category.

  Definition terminal_opposite_initial (x : C)
             `(H : IsTerminalObject C x)
  : IsInitialObject (C ^op) x
    := fun x' => H x'.

  Definition initial_opposite_terminal (x : C)
             `(H : IsInitialObject C x)
  : IsTerminalObject (C ^op) x
    := fun x' => H x'.
End DualObjects.
