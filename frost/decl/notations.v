(** Frost — declarative-system paper-faithful notations.

    Most judgment notations are now declared via [Reserved Notation] +
    [where] clauses inline in [decl/def_extra.v] (so the rule bodies
    themselves are paper-faithful and the rules are easy to audit).
    This file only carries notations for judgments whose definitions
    haven't been inlined yet (d_wf_ptyp, d_wf_utyp, d_wf_uskl,
    d_shallow_sub, d_refine, d_refine_syn, d_typing, d_pat). *)

Require Export src.frost.notations.
Require Export src.frost.decl.def_extra.

(** ** Well-formedness judgments.

    [d_wf_utyp] ([{{ Γ ⊢ᵤ C }}d]) and [d_wf_uskl] ([{{ Γ ⨟ Δ ⊢ᵤₛ R }}d]) are already
    notated inline via [where] clauses in [decl/def_extra.v]; the earlier
    duplicate declarations here ([⊢ᵤₜ], and a positional copy of [⊢ᵤₛ]) were
    removed to avoid two glyphs for one relation. *)

(** ** Shallow subtyping (separate from main d_sub). *)


(** ** Typing and skeleton inference (mutual). *)



(** ** Skeleton refinement. [{{ Γ ⨟ Δ ⊢ᵣ Q ⊳ P }}d] = the (single, coloured)
    refinement relation, filling ghosts with synthesised skeletons; its
    pskl-subject twin is [{{ Γ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}d].  The [ᵣ] subscript
    disambiguates from [d_shallow_sub]'s bare [{{ Γ ⊢ A ≤ B }}d].  (The former
    uncoloured [▸] relation was dropped to match the paper's single coloured
    refinement relation, and the earlier three-context form
    [Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P] collapsed to one Δ.)

    ⚙ The [ad] layer's copies read the SAME inside the braces —
    [{{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad] — because the system is now the delimiter; see
    the legend in [frost/notations.v]. *)
