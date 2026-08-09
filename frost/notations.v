(** Frost — paper-faithful scoped notations (cross-system).

    This file exports notations that depend ONLY on the cross-system
    definitions (def_ott / prop_ln / def_extra). Notations for declarative
    judgments live in `frost/decl/notations.v` to avoid a circular import
    (decl/def_extra.v → frost/notations.v).

    Conventions:
    - Greek letters in the paper map to the same letters here (Γ, Δ, Ψ, ε, φ, ψ).
    - Mode subscripts are written as `⊢[ M ]`; subtyping writes the tag context first as `Δ ⨟ Γ ⊢[ M ]`.

    ** THE TURNSTILE LEGEND — two axes, two devices.

    This is the whole scheme; it is what makes "the same relation, three
    systems" readable at a glance.  ⚠️ Each axis owns ONE device, and they
    must never swap: a subscript `ₐ` for the algorithmic system (what
    `a_consis` / `a_sub` / `a_pat` / `a_typing` used until 2026-08-09) reads
    as a SORT, and an `ᵃ` that means `a_` in one file and `ad_` in another
    (what `a_wf_pskl` and `ad_pat_consis` did) is worse than no marker.

    - SUPERSCRIPT = the SYSTEM.  Absence is the declarative base case:
        `⊢`     declarative        (`d_*`,  over Γ)
        `⊢ᵃᵈ`   declarative over algorithmic contexts (`ad_*`, over Θ)
        `⊢ᵃ`    algorithmic        (`a_*`,  over Θ, with `⊣ Θ'`)
        `⊢ᵗ`    ε-tagged decorated (`a_subtag` / `a_consistag`, dotted `⩽˙`/`∼˙`)
        `⊢ˢ`    syntax-directed    (`d_sd_typing`; composes: `⊢ˢᵃᵈ`)
    - SUBSCRIPT = WHICH JUDGEMENT — the sort first of all, and it is the SAME
      in every system, so the superscript is the only thing that changes
      between one relation's copies.  Absence is the type sort:
        `⊢`     types      (ptyp / btyp / utyp — A, B, C)
        `⊢ₛ`    skeletons  (pskl / bskl / uskl — P, Q, R)
      The sort subscript appears exactly where a system has one relation PER
      sort, so that it is what tells the siblings apart: `Γ ⊢ₛ[ M ] e ⦂ P`
      (skeleton inference) vs `Γ ⊢[ M ] e ⦂ A` (typing); `⊢ₛ R ∼ Q` vs
      `⊢ C ∼ B`.  Where ONE relation covers both sorts, the sort is a bracket
      INDEX instead and the subscript is omitted, so it is never stated twice:
      `Θ ⊢ᵃ[ N | m | P0 ] P ⩽ Q ⊣ Θ'`, `Ψ ⨟ Θ ⊢ᵃᵈ[ NM | M ] R ⩽ Q`.
      For well-formedness the sort is spelled out — `⊢ₚ`/`⊢ᵦ`/`⊢ᵤ` (ptyp /
      btyp / utyp), `⊢ₚₛ`/`⊢ᵤₛ` for their skeleton counterparts — and where a
      system has several same-sort relations the subscript names the relation:
      `⊢ᵣ` refinement, `⊢ᵣₚ` its pskl-subject variant, `⊢ₚᵣ` precision.
      All of them keep their spelling across systems (`⊢ᵣ` / `⊢ᵣᵃᵈ`,
      `⊢ₚₛ` / `⊢ₚₛᵃ`, `⊢ₚᵣᵃᵈ`).
    - `[ … ]` carries the indices (mode M, sort N, input skeleton P0, tag
      scope Ψ); `⊣ Θ'` the output context; the tag context comes FIRST
      (`Ψ ⨟ Γ ⊢ …`) and the ∀-scope Δ AFTER (`Γ ⨟ Δ ⊢ …`).
    - RELATION SYMBOLS are the paper's: `∼` consistency, `⩽` subtyping,
      `⊳` refinement, `⊑ᵖ` precision, `⦂` a term's type or skeleton.
      ⚠️ `⦂` at EVERY mode: the mech used to write skeleton inference
      `⊢[ M ] e ⇨ P`, but `⇨` claims the term SYNTHESISES its skeleton and
      that only holds at `M = TI` — at TC the skeleton is an input.  The
      paper writes its own mode-generic typing with a plain colon for the
      same reason (`\typp`, macro.tex:1087).

    ⚙ Judgements that exist ONLY inside the algorithm (`a_looksub`,
    `a_solve_sub` / `a_solve_consis`, `a_solve_cstr`, `a_extract`, `a_assign`,
    `a_unify`, `a_split`, `a_tyequiv`) carry no system marker: the marker's
    job is to separate one relation's copies across systems, and these have
    no counterpart to be confused with — their own symbols (`≼ … ⤳`, `≔`,
    `≈ᵘ`, `▹`, `≡ᵗ`) already identify them.  ⚠️ The one residue is
    `a_solve_sub`'s `⊢ₛ` / `a_solve_consis`'s `⊢ₑ`, where the subscript marks
    the SOLVE layer rather than a sort; renaming those needs a look-vs-solve
    marker, which is a separate pass (see docs/PROPOSAL-notation-pass.md §6).
*)

Require Export Metalib.Metatheory.

Require Export src.frost.def_ott.
Require Export src.frost.prop_ln.
Require Export src.frost.def_extra.

(** ** Atom sets.

    `Metalib.Metatheory` abbreviates only PART of the atom-set interface:
    it declares `Notation add/empty/remove/singleton/union := AtomSetImpl.…`
    and re-exports `AtomSetFacts` (so `add_iff`, `mem_iff`, … resolve
    unqualified), but leaves `inter`, `diff`, `mem` and every `AtomSetImpl`
    lemma name behind the module path.  Metalib deliberately does not
    `Module Export AtomSetImpl` — that would drop `In`, `eq`, `filter`, `fold`,
    … on top of `List`'s — so we finish the job selectively here, in exactly
    metalib's own style: abbreviations for what we use, and nothing else.
    After this file no statement or proof needs to write `AtomSetImpl.` or
    `AtomSetFacts.`. *)

Notation inter := AtomSetImpl.inter.
Notation diff := AtomSetImpl.diff.
Notation mem := AtomSetImpl.mem.

Notation union_1 := AtomSetImpl.union_1.
Notation union_2 := AtomSetImpl.union_2.
Notation union_3 := AtomSetImpl.union_3.
Notation inter_1 := AtomSetImpl.inter_1.
Notation inter_2 := AtomSetImpl.inter_2.
Notation inter_3 := AtomSetImpl.inter_3.
Notation singleton_1 := AtomSetImpl.singleton_1.
Notation add_2 := AtomSetImpl.add_2.
Notation remove_1 := AtomSetImpl.remove_1.
Notation remove_3 := AtomSetImpl.remove_3.

(** The set operations the paper writes infix.  `∪` mirrors metalib's
    `` `union` `` (level 65, right); `∩` and `∖` bind tighter, as in maths.
    All three sit below `[=]` / `[<=]` (level 70), so `Δ ∩ ftvar_in_pskl P
    [=] empty` — the disjointness side condition that dominates the
    refinement / consistency / subtyping statements — parses and prints as
    written. *)

Notation "X ∪ Y" := (AtomSetImpl.union X Y)
  (at level 65, right associativity) : set_scope.

Notation "X ∩ Y" := (AtomSetImpl.inter X Y)
  (at level 63, right associativity) : set_scope.

Notation "X ∖ Y" := (AtomSetImpl.diff X Y)
  (at level 61, left associativity) : set_scope.

(** ** Lightweight aliases. *)

Notation "x ∉ L" := (x `notin` L) (at level 70, no associativity).

Notation "` α" := (ptyp_var_f α)
  (at level 0, α at level 0, no associativity) : type_scope.

Notation "⌈ e ⌉" := (exp_freeze e) (at level 0, e at level 0) : type_scope.

(** ** Substitution. *)

Notation "{ A' ᵗ/ₜ α } A" :=
  (subst_ptyp_in_ptyp A' α A)
    (at level 49, A' at level 50, α at level 0, right associativity) : type_scope.

Notation "{ e' ᵉ/ₑ x } e" :=
  (subst_exp_in_exp e' x e)
    (at level 49, e' at level 50, x at level 0, right associativity) : type_scope.

Notation "{ A ᵉ/ₜ α } e" :=
  (subst_ptyp_in_exp A α e)
    (at level 49, A at level 50, α at level 0, right associativity) : type_scope.
