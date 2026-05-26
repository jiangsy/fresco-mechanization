(** Frost — declarative-system paper-faithful notations.

    Most judgment notations are now declared via [Reserved Notation] +
    [where] clauses inline in [decl/def_extra.v] (so the rule bodies
    themselves are paper-faithful and the rules are easy to audit).
    This file only carries notations for judgments whose definitions
    haven't been inlined yet (d_wf_ptyp, d_wf_utyp, d_wf_uskl,
    d_shallow_sub, d_refine, d_refine_syn, d_typing, d_pat). *)

Require Export src.frost.notations.
Require Export src.frost.decl.def_extra.

(** ** Well-formedness judgments. *)

Notation "Γ ⊢ₚ A" := (d_wf_ptyp Γ A)
  (at level 75, A at level 75, no associativity) : type_scope.

Notation "Δ ⨟ Γ ⊢ᵤₜ C" := (d_wf_utyp Δ Γ C)
  (at level 75, Γ at level 75, C at level 75, no associativity) : type_scope.

Notation "Δ ⨟ Γ ⊢ᵤₛ R" := (d_wf_uskl Δ Γ R)
  (at level 75, Γ at level 75, R at level 75, no associativity) : type_scope.

(** ** Shallow subtyping (separate from main d_sub). *)

Notation "Γ ⊢ A ≤ B" := (d_shallow_sub Γ A B)
  (at level 75, A at level 74, B at level 74, no associativity) : type_scope.

(** ** Typing and skeleton inference (mutual). *)

Notation "Γ ⊢[ M ] e ⦂ A" := (d_typing M Γ e A)
  (at level 100, M at level 0, e at level 75, A at level 75, no associativity)
  : type_scope.

Notation "Γ ⊢[ M ] e ⇨ P" := (d_pat M Γ e P)
  (at level 100, M at level 0, e at level 75, P at level 75, no associativity)
  : type_scope.

(** ** Skeleton refinement. [⊢ᵣ … ⊳ …] = the (single, coloured)
    refinement relation, filling ghosts with synthesised skeletons.
    Subscripted [⊢] disambiguates from [d_shallow_sub]'s bare
    [Γ ⊢ A ≤ B].  (The former uncoloured [▸] relation was dropped to
    match the paper's single coloured refinement relation.) *)

Notation "Ψ ⨟ Γ ⊢ᵣ P ⊳ Q" := (d_refine_syn Ψ Γ P Q)
  (at level 75, Γ at level 75, P at level 74, Q at level 74, no associativity)
  : type_scope.
