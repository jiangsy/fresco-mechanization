(** Frost — declarative-system paper-faithful notations.

    Imports the decl/def_extra.v judgments and adds notations for them.
    Phase 2 metatheory files should `Require Import src.frost.decl.notations.`
    instead of `src.frost.notations.` directly.
*)

Require Export src.frost.notations.
Require Export src.frost.decl.def_extra.

(** ** Well-formedness judgments.
    `d_wf_typ Γ A` is left without a dedicated notation: a bare `Γ ⊢ A`
    would clash with `Γ ⊢ A ≤ B`, and any disambiguating shape (e.g.
    `Γ ⊢ A type`) buys little over the direct application form. *)

Notation "Ψ ⨟ Γ ⊢ₛₖ P" := (d_wf_skel Ψ Γ P)
  (at level 75, Γ at level 75, P at level 75, no associativity) : type_scope.

Notation "Δ ⨟ Γ ⊢ₜₜ φ" := (d_wf_ttyp Δ Γ φ)
  (at level 75, Γ at level 75, φ at level 75, no associativity) : type_scope.

Notation "Δ ⨟ Γ ⊢ᵤₜ T" := (d_wf_utyp Δ Γ T)
  (at level 75, Γ at level 75, T at level 75, no associativity) : type_scope.

(** ** Subtyping, consistency, and shallow subtyping. *)

Notation "Γ ⊢ A ≤ B" := (d_shallow_sub Γ A B)
  (at level 75, A at level 74, B at level 74, no associativity) : type_scope.

Notation "Δ ⨟ Γ ⊨ T ~ A" := (d_consis Δ Γ T A)
  (at level 75, Γ at level 75, T at level 74, A at level 74, no associativity)
  : type_scope.

Notation "Γ ⊢[ M ; Δ ] T ⊑ A" := (d_sub M Δ Γ T A)
  (at level 75, M at level 0, Δ at level 0, T at level 74, A at level 74,
   no associativity) : type_scope.

(** ** Typing and skeleton inference. *)

Notation "Γ ⊢[ M ] e ⇒ A" := (d_typing M Γ e A)
  (at level 75, M at level 0, e at level 74, A at level 74, no associativity)
  : type_scope.

Notation "Γ ⊢[ M ] e ⇨ P" := (d_pat M Γ e P)
  (at level 75, M at level 0, e at level 74, P at level 74, no associativity)
  : type_scope.

(** ** Skeleton refinement. ▸ uncoloured, ⊳ filled with synthesised. *)

Notation "Ψ ⨟ Γ ⊢ P ▸ Q" := (d_refine Ψ Γ P Q)
  (at level 75, Γ at level 75, P at level 74, Q at level 74, no associativity)
  : type_scope.

Notation "Ψ ⨟ Γ ⊢ P ⊳ Q" := (d_refine_syn Ψ Γ P Q)
  (at level 75, Γ at level 75, P at level 74, Q at level 74, no associativity)
  : type_scope.

(** ** Skeleton consistency and subtyping. *)

Notation "Δ ⨟ Γ ⊨ₛ S ~ P" := (d_pat_consis Δ Γ S P)
  (at level 75, Γ at level 75, S at level 74, P at level 74, no associativity)
  : type_scope.

Notation "Γ ⊢ₛ[ M ; Δ ] S ⊑ P" := (d_pat_sub M Δ Γ S P)
  (at level 75, M at level 0, Δ at level 0, S at level 74, P at level 74,
   no associativity) : type_scope.
