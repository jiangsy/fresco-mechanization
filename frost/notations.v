(** Frost — paper-faithful scoped notations (cross-system).

    This file exports notations that depend ONLY on the cross-system
    definitions (def_ott / prop_ln / def_extra). Notations for declarative
    judgments live in `frost/decl/notations.v` to avoid a circular import
    (decl/def_extra.v → frost/notations.v).

    Conventions:
    - Greek letters in the paper map to the same letters here (Γ, Δ, Ψ, ε, φ, ψ).
    - Mode subscripts are written as `⊢[ M ]`; mode + tag-context as `⊢[ M ; Δ ]`.
*)

Require Export src.frost.def_ott.
Require Export src.frost.prop_ln.
Require Export src.frost.def_extra.

(** ** Lightweight aliases. *)

Notation "x ∉ L" := (x `notin` L) (at level 70, no associativity).

Notation "` X" := (ptyp_var_f X)
  (at level 0, X at level 0, no associativity) : type_scope.

Notation "⌈ e ⌉" := (exp_freeze e) (at level 0, e at level 0) : type_scope.

(** ** Substitution. *)

Notation "{ A' ᵗ/ₜ X } A" :=
  (subst_ptyp_in_ptyp A' X A)
    (at level 49, A' at level 50, X at level 0, right associativity) : type_scope.

Notation "{ e' ᵉ/ₑ x } e" :=
  (subst_exp_in_exp e' x e)
    (at level 49, e' at level 50, x at level 0, right associativity) : type_scope.

Notation "{ A ᵉ/ₜ X } e" :=
  (subst_ptyp_in_exp A X e)
    (at level 49, A at level 50, X at level 0, right associativity) : type_scope.
