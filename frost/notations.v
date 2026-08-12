(** Frost — paper-faithful scoped notations (cross-system).

    This file exports notations that depend ONLY on the cross-system
    definitions (def_ott / prop_ln / def_extra). Notations for declarative
    judgments live in `frost/decl/notations.v` to avoid a circular import
    (decl/def_rules.v → frost/notations.v).

    Conventions:
    - Greek letters in the paper map to the same letters here (Γ, Δ, Ψ, ε, φ, ψ).
    - Mode subscripts are written as `⊢[ M ]`; subtyping writes the tag context first as `Δ ⨟ Γ ⊢[ M ]`.

    ** THE JUDGEMENT LEGEND — the system is the DELIMITER, not the turnstile.

    Every judgement of every system is written inside a system-tagged brace
    pair, and each pair is the delimiter of its own notation scope:

        {{ Γ ⨟ Δ ⊢ᵣ Q ⊳ P }}d      declarative           (`d_*`,  over Γ)
        {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad     declarative over algorithmic contexts
                                                          (`ad_*`, over Θ)
        {{ Θ ⊢[ m ; P0 ] e ⦂ B ⊣ Θ' }}a   algorithmic     (`a_*`, with `⊣ Θ'`)
        {{ Θ ⊢[ Δ1 | Δ2 | P0 | Ψ ] R ∼ Q ⊣ Θ' }}da  decorated algorithmic
                                                          (`a_*tag`, over `uskl`)

    ⚠️ `}}ad` and `}}da` are NOT the same word read twice.  `ad` is
    *`a`lgorithmic-context `d`eclarative* — the DECLARATIVE rules with `Θ` in
    place of `Γ` (the paper's `app:decl-in-algo-context`).  `da` is the paper's
    *`d`ecorated `a`lgorithmic* system (`app:decorated-algosub`) — the
    ALGORITHM's rules, a run with `⊣ Θ'`, over decorated (unresolved) skeletons
    `uskl` with a tag context `Ψ`.  They differ on opposite axes: `d → ad`
    keeps the rules and changes the CONTEXT; `a → da` keeps the rules and
    changes the SUBJECT (erased `pskl` → decorated `uskl`).  Soundness is the
    chain `}}a` ⇒ `}}da` ⇒ `}}ad` ⇒ `}}d`.

    The four scopes are `frost_d_scope` / `frost_ad_scope` / `frost_a_scope` /
    `frost_da_scope`, delimited `%d` / `%ad` / `%a` / `%da`; every file that
    declares a judgement notation in one of them also `Open Scope`s it, so the
    scope is open exactly where the notation is visible.

    ⭐ WHY THE DELIMITER AND NOT A SUPERSCRIPT.  The tree spent two passes
    trying to carry the system on the turnstile (`⊢ₐ`, then `⊢ᵃ`/`⊢ᵃᵈ`), and
    both failed the same way: the mark competed with the marks the judgement
    itself needs.  `⊢ᵣᵃᵈ` / `⊢ᵣₚᵃᵈ` / `⊢ₚᵣᵃᵈ` / `⊢ₛᵃᵈ[` stack three glyphs
    where two carry meaning, and `ad_sd_typing` had to DROP its `ˢ` (leaving a
    plain `⊢ᵃᵈ[ M ]`) purely to avoid a three-deep superscript.  Moving the
    system out to the delimiter frees the turnstile completely, so one
    relation's copies across systems now differ by the delimiter ALONE:

        {{ Γ ⨟ Δ ⊢ᵣ Q ⊳ P }}d   ~   {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad
        {{ Γ ⊢ˢᵈ[ M ] e ⦂ A }}d  ~   {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad
        {{ Γ ⨟ Δ ⊢ₚₛ P }}d      ~   {{ Θ ⨟ Δ ⊢ₚₛ P }}a

    and every judgement is self-delimiting, so it reads unambiguously in a
    long premise chain and needs no level juggling against `->` / `/\`.

    - SUPERSCRIPT = WHICH COPY of the judgement — in practice, the SORT the
      judgement is about.  Absence is the type sort:
        `⊢`      types              (ptyp / btyp / utyp — A, B, C)
        `⊢ˢ`     skeletons          (pskl / bskl / uskl — P, Q, R)
        `⊢ᵉ`     expressions        (`a_wf_exp`: `{{ Θ ⊢ᵉ e }}a`)
        `⊢ˢᵈ`    syntax-directed     (`d_sd_typing`, `ad_sd_typing`)
      So `{{ Γ ⊢ˢ[ M ] e ⦂ P }}d` is skeleton inference and
      `{{ Γ ⊢[ M ] e ⦂ A }}d` is typing; `{{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d` is skeleton
      consistency and `{{ Ψ ⨟ Γ ⊢ C ∼ B }}d` is type consistency.
      ⚠️ `ˢ` and `ˢᵈ` are SIBLINGS, not a mark and its refinement: `ˢ` says the
      subject sort is skeletons, `ˢᵈ` says the RULES are the syntax-directed
      ones.  They never combine (there is no skeleton-sorted `d_sd_pat`).
      Where ONE relation covers both sorts the sort is a bracket INDEX
      instead, so it is never stated twice: `{{ Θ ⊢[ N | m | P0 ] P ⩽ Q ⊣ Θ' }}a`,
      `{{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ Q }}ad`.
    - SUBSCRIPT = WHICH RELATION, when a system has several at one sort:
      `⊢ᵣ` refinement, `⊢ᵣₚ` its pskl-subject variant, `⊢ₚᵣ` precision,
      `⊢ₛ` / `⊢ₑ` the two solve-layer judgements.  Well-formedness spells its
      sort out the same way: `⊢ₚ`/`⊢ᵦ`/`⊢ᵤ` (ptyp / btyp / utyp) and
      `⊢ₚₛ`/`⊢ᵤₛ` for their skeleton counterparts.
      ⚙ `⊢ₛ` (a_solve_sub) and `⊢ˢ` (the skeleton sort) are different axes and
      only ever meet inside `}}a`, where the solve pair's `≼[ m ] … ⤳ … ⨾ …`
      shape tells them apart at a glance.  The same goes for `⊢ₑ`
      (a_solve_eq, a RELATION) beside `⊢ᵉ` (a_wf_exp, a SORT) — `a_wf_exp`
      would otherwise want the subscript `ₑ` that the solve layer holds, and
      freeing it means renaming the solve pair, a separate pass.
    - ⚙ A judgement about a CONTEXT ALONE puts the turnstile first, as usual:
      `{{ ⊢ Θ }}a` is `a_wf_aenv` (the paper's `Θ ⊢ ctx`).  It is the one
      notation here whose token comes before its slot, and camlp5 factors it
      against the constr-headed rules and metalib's `{{ x }}` without
      complaint — verified, not assumed.
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
    - ⚙ The decorated system no longer needs its dots: `a_consistag` /
      `a_subtag` wrote `∼˙` / `⩽˙` — the paper's own `\consisdec` / `\subtypedec`
      (macro.tex:1439) — only to stay apart from the algorithmic `∼` / `⩽`, and
      `}}da` now does that job, so they are plain again.  ⚠️ This IS a
      departure from the paper's notation: the paper separates decorated from
      ordinary by the RELATION SYMBOL, and the mech separates them by the
      DELIMITER.  The one thing that still tells them apart INSIDE the braces
      is the fourth bracket index, the tag scope `Ψ`.

    ⚙ WHAT IS NOT WRAPPED.  The delimiter separates SYSTEMS, so a relation
    with no cross-system twin keeps its bare form: the information-increase
    relation `κ ∷ Θ ⊑ Θ'` (`a_inc`) and its ordering `Θ ⊴ Θ'` (`a_isub`), and
    the conversion / substitution functions (`⌊ R ⌋ˢ`, `⇓ᵗ[ Θ ] A`,
    `{ A' ᵗ/ₜ α } A`).  These are meta-level, not judgements of a system, and
    wrapping them would say "which system?" about something that has no answer.
*)

Require Export Metalib.Metatheory.

Require Export src.frost.def_ott.
Require Export src.frost.prop_ln.
Require Export src.frost.def_shapes.

(** ** The four judgement scopes.

    Declared here (so every judgement notation, wherever it is defined, can
    name its scope) and OPENED here as well.  Coq replays a file's `Open
    Scope` when that file is `Import`ed, and a judgement notation is only
    visible through an import chain that reaches its defining file — which in
    turn reaches this one — so the "declare the notation in scope X" and
    "scope X is open" halves always travel together.  ⚠️ Each defining file
    (`decl/def_rules.v`, `algo/def_rules.v`, …) repeats the `Open Scope` for
    its own scopes: `Open Scope` is NOT transitive through `Require Import`,
    so a file that reaches a notation via a two-step chain would otherwise see
    the notation with its scope closed, and Coq reports that as the notation
    simply not existing. *)

Declare Scope frost_d_scope.
Delimit Scope frost_d_scope with d.
Open Scope frost_d_scope.

Declare Scope frost_ad_scope.
Delimit Scope frost_ad_scope with ad.
Open Scope frost_ad_scope.

Declare Scope frost_a_scope.
Delimit Scope frost_a_scope with a.
Open Scope frost_a_scope.

Declare Scope frost_da_scope.
Delimit Scope frost_da_scope with da.
Open Scope frost_da_scope.

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
(* ⚙ [choose] / [cardinal] and the two cardinal facts below are what a
   FINITE-SET INDUCTION needs — the ε-tag freshening (decl/prop_tag_swap.v)
   moves one bad tag per step and measures progress by the cardinality of the
   bad set. *)
Notation choose := AtomSetImpl.choose.
Notation choose_1 := AtomSetImpl.choose_1.
Notation choose_2 := AtomSetImpl.choose_2.
Notation cardinal := AtomSetImpl.cardinal.
Notation Empty := AtomSetImpl.Empty.
Notation cardinal_Empty := AtomSetProperties.cardinal_Empty.
Notation subset_cardinal_lt := AtomSetProperties.subset_cardinal_lt.

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
