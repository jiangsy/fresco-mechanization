(** Frost — paper-faithful scoped notations. *)

Require Export src.frost.def_ott.
Require Export src.frost.prop_ln.
Require Export src.frost.def_extra.

Notation "x ∉ L" := (x `notin` L) (at level 70, no associativity).

Notation "` X" := (typ_var_f X)
  (at level 0, X at level 0, no associativity) : type_scope.

Notation "{ B ᵗ/ₜ X } A" :=
  (subst_typ_in_typ B X A)
    (at level 49, B at level 50, X at level 0, right associativity) : type_scope.

Notation "{ e' ᵉ/ₑ x } e" :=
  (subst_exp_in_exp e' x e)
    (at level 49, e' at level 50, x at level 0, right associativity) : type_scope.

Notation "{ A ᵉ/ₜ X } e" :=
  (subst_typ_in_exp A X e)
    (at level 49, A at level 50, X at level 0, right associativity) : type_scope.

Notation "⌈ e ⌉" := (exp_freeze e) (at level 0, e at level 0) : type_scope.
