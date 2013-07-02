(*Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x == y == z" (at level 70, no associativity, y at next level). *)

Reserved Notation "x ≅ y" (at level 70, no associativity).
Reserved Notation "x <~=~> y" (at level 70, no associativity).

Reserved Notation "x ~= y" (at level 70, no associativity).
Reserved Notation "x ~= y ~= z" (at level 70, no associativity, y at next level).

Reserved Notation "i ⁻¹" (at level 3).
Reserved Notation "i ^-1" (at level 3).
Reserved Notation "C ᵒᵖ" (at level 10).

Reserved Notation "C ★^ M D" (at level 70, no associativity).
Reserved Notation "C ★^{ M } D" (at level 70, no associativity).

Reserved Notation "S ↓ T" (at level 70, no associativity).

Reserved Notation "S ⇑ T" (at level 70, no associativity).
Reserved Notation "S ⇓ T" (at level 70, no associativity).
Reserved Notation "'CAT' ⇑ D" (at level 70, no associativity).
Reserved Notation "'CAT' ⇓ D" (at level 70, no associativity).

Reserved Notation "x ⊗ y" (at level 40, left associativity).
Reserved Notation "x ⊗m y" (at level 40, left associativity).

Reserved Infix "○" (at level 40, left associativity).
Reserved Infix "∘" (at level 40, left associativity).
Reserved Infix "∘₀" (at level 40, left associativity).
Reserved Infix "∘₁" (at level 40, left associativity).
Reserved Infix "∘'" (at level 40, left associativity).
Reserved Infix "∘₀'" (at level 40, left associativity).
Reserved Infix "∘₁'" (at level 40, left associativity).
Reserved Infix "'o'" (at level 40, left associativity).
Reserved Infix "'o0'" (at level 40, left associativity).
Reserved Infix "'o1'" (at level 40, left associativity).

Reserved Notation "x ~> y" (at level 99, right associativity, y at level 200).

Reserved Notation "x ∏ y" (at level 40, left associativity).
Reserved Notation "x ∐ y" (at level 50, left associativity).
Reserved Infix "Π" (at level 40, left associativity).
Reserved Infix "⊔" (at level 50, left associativity).

Reserved Notation "∏_{ x } f" (at level 0, x at level 99).
Reserved Notation "∏_{ x : A } f" (at level 0, x at level 99).
Reserved Notation "∐_{ x } f" (at level 0, x at level 99).
Reserved Notation "∐_{ x : A } f" (at level 0, x at level 99).

(* I'm not terribly happy with this notation, but '('s don't work
   because they interfere with things like [prod]s and grouping,
   and '['s interfere with list notation in Program. *)
Reserved Notation "F ⟨ c , - ⟩" (at level 70, no associativity).
Reserved Notation "F ⟨ - , d ⟩" (at level 70, no associativity).
Reserved Notation "F ₀" (at level 10, no associativity).
Reserved Notation "F ₁" (at level 10, no associativity).
Reserved Notation "F ₀ x" (at level 10, no associativity).
Reserved Notation "F ₁ m" (at level 10, no associativity).

(* Forced by the notation in Program *)
Reserved Notation "[ x ]" (at level 0, x at level 200).

Reserved Notation "∫ F" (at level 0).

Reserved Infix "\" (at level 40, left associativity).

Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope functor_scope with functor.
Delimit Scope natural_transformation_scope with natural_transformation.

Delimit Scope graph_scope with graph.
Delimit Scope group_elements_scope with group.
Delimit Scope groups_scope with groups.
Delimit Scope vertex_scope with vertex.
Delimit Scope edge_scope with edge.
