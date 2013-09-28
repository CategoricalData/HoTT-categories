(*Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x == y == z" (at level 70, no associativity, y at next level). *)

Reserved Notation "x <~=~> y" (at level 70, no associativity).

Reserved Notation "x ~= y" (at level 70, no associativity).
Reserved Notation "x ~= y ~= z" (at level 70, no associativity, y at next level).

Reserved Notation "i ^-1" (at level 3).
Reserved Notation "i ^op" (at level 3).
Reserved Notation "i ^op'" (at level 3).
Reserved Notation "i ^op''" (at level 3).
Reserved Notation "i ^op'''" (at level 3).
Reserved Notation "i ^op'L" (at level 3).
Reserved Notation "i ^op'R" (at level 3).

Reserved Notation "S |v| T" (at level 70, no associativity).

Reserved Infix "o" (at level 40, left associativity).
Reserved Infix "o0" (at level 40, left associativity).
Reserved Infix "o1" (at level 40, left associativity).

Reserved Notation "x ~> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x (-> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x ->> y" (at level 99, right associativity, y at level 200).

Reserved Notation "! x" (at level 10, no associativity).

(* Forced by the notation in Program *)
Reserved Notation "[ x ]" (at level 0, x at level 200).

Reserved Infix "\" (at level 40, left associativity).

Reserved Infix "-|" (at level 60, right associativity).

Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope functor_scope with functor.
Delimit Scope pseudofunctor_scope with pseudofunctor.
Delimit Scope natural_transformation_scope with natural_transformation.
Delimit Scope adjunction_scope with adjunction.

Delimit Scope graph_scope with graph.
Delimit Scope group_elements_scope with group.
Delimit Scope groups_scope with groups.
Delimit Scope vertex_scope with vertex.
Delimit Scope edge_scope with edge.
