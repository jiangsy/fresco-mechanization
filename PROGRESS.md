# Frost Re-Mechanization — Progress

Clean restart against the **finalized paper** (branch `re-mech`, paper merge
`8dfafca`).  Ground rules: the paper's definitions and proofs are never
changed; the mechanization follows the paper's proof appendices bottom-up.
Pre-restart history: [`docs/PROGRESS-legacy-2026-07.md`](docs/PROGRESS-legacy-2026-07.md).
Decl↔paper sync findings: [`docs/REPORT-remech-decl-sync.md`](docs/REPORT-remech-decl-sync.md).

Legacy proof files live beside their originals as `*.v.legacy` (git-tracked,
excluded from the build); mine them when re-proving.

# Part 1: Paper → mechanization map

## Definitions (all 🟢 compiled)

| Paper | Mechanization | Status |
|---|---|---|
| Syntax (types/terms/skeletons, decl §3) | `frost/language.ott` → `def_ott.v` (`ptyp/btyp/utyp/pskl/bskl/uskl`, `exp`) | 🟢 synced |
| Colour/shape predicates (syn/inh/decorated/guarded/values) | `frost/def_extra.v`, `frost/predicates.v` | 🟢 synced (`is_tskl` fixed) |
| `tags{Ψ}{φ}` / `tags{Ψ}{ψ}` | `decl/def_extra.v` `d_tags` / `d_tags_skl` | 🟢 synced (ψ-grammar exact) |
| Typing (fig:decl-typing) | `d_typing` | 🟢 |
| Syntax-directed typing (§3.3) | `d_sd_typing` | 🟢 |
| Subtyping + consistency (fig:decl-subtyping-consistency) | `d_sub`, `d_consis` | 🟢 |
| Skeleton wf / refinement (§3.5) | `d_wf_pskl/uskl`, `d_refine_syn` | 🟢 |
| Skeleton inference (fig:decl-skeleton-inference) | `d_pat` | 🟢 restructured to embedded-subtyping base rules |
| Skeleton subtyping/consistency (fig:decl-skeleton-subtyping-consistency) | `d_pat_sub`, `d_pat_consis` | 🟢 |
| Algorithmic contexts/suffixes (§5.1) | `algo/def_extra.v` `aenv/abind/a_suffix` | 🟢 rewritten |
| `skmod[TY]/[SK]` on input skeletons | `a_ty_mode_compat`, `a_sk_mode_compat` | 🟢 |
| guess^TY / guess^N (LaTeX `\guessMono`/`\guess`) | `a_guess_mono`, `a_guess` | 🟢 |
| Constraint collection (fig:poly-info-extraction) | `a_looksub`, `a_lookeq` | 🟢 no-refresh, □-Vacuous |
| Constraint solving (fig:constraint-solving) | `a_solve_sub`, `a_solve_eq`, `a_solve_cstr` | 🟢 GhostLF/GhostL with ⊤ outputs |
| look | `a_extract` | 🟢 |
| unifyvar / assignvar | `a_unify`, `a_assign` | 🟢 |
| Algorithmic consistency (fig:alg-consistency) | `a_consis` | 🟢 NEW Δ₁∣Δ₂ tracking |
| Algorithmic subtyping (fig:alg-subtyping) | `a_sub` + `a_sub_flex` | 🟢 |
| Skeleton splitting | `a_split` | 🟢 |
| Algorithmic skeleton inference (fig:alg-skeleton-inference) | `a_pat` | 🟢 |
| Algorithmic type inference (fig:alg-type-inference) | `a_typing` | 🟢 ∀ᾱ.A₀ AbsCheck (step/base), typed Freeze |
| Erasure ⌊·⌋, decorated subtyping/consistency, tag solving (app:decorated-algosub) | `algo/def_decorated.v` (`uskl_to_pskl`, `a_subtag`, `a_consistag`, `a_solvetag(_sub/_eq)`) | 🟢 |
| Metasubstitutions θ : Θ ⇒ Θ' (app:metasubstitutions) | `algo/def_meta.v` (`a_inc`, `a_inc_equiv`, `a_tyequiv`, `⊴`) | 🟢 |
| Decl judgments in algo contexts (app:decl-in-algo-context) | `algo/def_decl_algo.v` (`ad_pat_consis`, `ad_refine_syn`, `ad_refine_pskl`, `ad_wf_pskl` + flex-lookup rules) | 🟡 consistency/refinement layer done; subtyping/typing layer TODO |

## Theorems / lemmas (bottom-up order; ⬜ = to prove, per paper appendix)

**B. consistency-proofs.tex** (§Consistency)
- ⬜ Soundness of decorated consistency
- ✅ Decorating algorithmic consistency (`a_consis_decorate`, `algo/prop_decorate.v`); ⬜ Consistency decoration
- ✅ Soundness of Consistency parts 2–3 (`a_unify_sound` / `a_assign_sound`, `algo/prop_flex.v` — the unifyvar/assignvar halves of thm:sound-consistency); ⬜ part 1 (the aconsis main induction)
- ⬜ Consistency constraint decoration for variables
- ⬜ Completeness of consistency constraint collection & solving (+ for variables)
- ⬜ Soundness of Consistency (Lemma soundConsistency, 3 parts: consis / unifyvar / assignvar)
- ⬜ Completeness and optimality of Consistency (3 parts)

**C. subtyping-proofs.tex** (§Subtyping)
- ⬜ Decorating algorithmic subtyping; Soundness of decorated subtyping
- ⬜ Look decoration; Decorating constraint solving; Constraint solving concatenation
- ⬜ Subtyping decoration (variables → general); Vacuous subtyping decoration
- ⬜ Stability of constraint collection; Look freshness
- ⬜ Decorating instantiation; Soundness of decorated algorithmic subtyping of flexible variables
- ⬜ Theorem: Soundness of subtyping
- ⬜ Complete partial precision; Stability of subtyping under more precise substitution
- ⬜ Completeness of constraint collection & solving (+ for variables); Look completeness
- ⬜ Completeness of flexible-variable subtyping
- ⬜ Theorem: Completeness and optimality of subtyping

**D. proofs.tex** (§Proofs for Algorithms)
- ⬜ Suffix moving; Suffix erasure; Splitting refines
- ⬜ Precision extends skeleton subtyping; Precision preserves refinement
- ⬜ Context precision (+ preserves skeleton inference)
- ⬜ Theorems: Soundness / Completeness+optimality of type inference
- ⬜ Theorems: Soundness / Completeness+optimality of skeleton inference

**A. full-decl-proofs.tex** (declarative metatheory — REBASED onto the synced defs)
- ✅ Soundness/Completeness of syntax-directed rules (`d_sd_typing_sound` / `d_sd_typing_complete`, `prop_syntax_directed.v`, 0 admits)
- ✅ General subsumption; Consistency-Subtyping Transitivity; Subtyping Transitivity; Function Subtyping; Generalised General Subsumption (`prop_general_subsumption.v` D1/D12 + spine, 0 admits; `Print Assumptions` audited in `README.v`)
- Restored chain: `prop_weakening` (d_pat base cases repaired for embedded subtyping), `prop_renaming` + `prop_general_subsumption` (compiled unchanged), `prop_skeleton` (lean extraction: the 18-block dependency closure the equivalence needs; the pre-restart skeleton-safety machinery — incl. the now-false `pskl_to_tskl_is_tskl`, a casualty of the `is_tskl` sync fix A1 — stays in `prop_skeleton.v.legacy` for the later paper-faithful redo), `prop_syntax_directed` (base cases of `d_pat_subst_unit` repaired; obsolete `is_base_term` helper dropped)

# Part 2: Progress log (most recent first)

## 2026-07-12 (c) — refine metatheory + benchmark acceptance tests

`algo/prop_refine.v` (all Qed): refine weakening/Δ-monotonicity,
`ad_refine_syn_refl_inh` / `ad_refine_pskl_refl`, and
`ad_pat_consis_refl_erase` (the GhostR subsidiary induction) — the W3
reflexivity inputs of the appendix-B soundness proof.

`algo/test_examples.v`: ENCODING CHECK per user request — the appendix
benchmark examples (fig:comparison-table-QL/-new) mechanized as full
algorithmic derivations `Θlib ⊢ₐ[TI;□] e ⦂ B ⊣ Θ'` with concrete result
types/contexts.  Covered: A1, A2, A4, A5, A10a, A10b, C2, E2b (Int/Bool
as rigid tvars, Int×Bool Church-encoded — the paper's "Ch." column).
Deferred rows (List-based, pair-constructor, freeze): encoding works,
derivations are just large — see the file header.  NEXT still: appendix
B part 1 (`aconsis` soundness main induction; needs W2
`ad_refine_*_fold_def` + extending `a_unify_sound` with refine-shaped
conclusions), then Soundness of decorated consistency.

## 2026-07-12 (b) — flexible-variable soundness complete (thm:sound-consistency 2–3)

`algo/prop_flex.v` (1056 lines, all Qed): `a_unify_sound` and
`a_assign_sound` with their full support stack — ⊴ cons-congruences and
prefix machinery for the `Θ₀∣Ξ` split, definition-unfolding/folding
(`a_tyequiv_subst_def`, `ad_pat_consis_fold_def`), `a_guess_mono_consis`,
binds-monotone weakening of the Θ-level judgments, and the wf bookkeeping
(`a_wf_aenv_strip_mid/_move_decl/_mid_def_inv`).  Also
`docs/PAPER-GAPS.md` (canonical paper-flagged findings registry; rule 2
points there).  NEXT: appendix B part 1 — the `aconsis` soundness main
induction, then Soundness of decorated consistency.

## 2026-07-12 — decl restoration complete (except prop_safety)

`prop_stability` (incl. `d_typing_order_irrel`, 0 admits) and
`prop_annotation` (1 pre-existing app-case admit) restored;
`prop_skeleton` gained the repaired `subst_var` family.  The only decl file
still `.legacy` is `prop_safety` — the skeleton-safety development whose
`pskl_to_tskl` decorated witnesses are invalidated by sync fix A1; it gets
the paper-faithful redo.  Build 🟢, 7/7 flagship `Print Assumptions`
Closed.

## 2026-07-11 (b) — meta/decl-algo layer, first Qed, ⊴-algebra, notations

- `algo/def_meta.v` (metasubstitutions, `a_tyequiv`, `a_inc`/`⊴`) and
  `algo/def_decl_algo.v` (decl judgments over Θ with flex lookups:
  `⊢ₚₛᵃ`/`⊨ₛᵃ`/`⊢ᵣᵃ`/`⊢ᵣₚᵃ`, Δ as `atoms` to align with `a_consis`).
- **First lemma Qed**: `a_consis_decorate` = paper "Decorating algorithmic
  consistency" (`algo/prop_decorate.v`), with the `pskl→uskl` embedding kit.
- `algo/prop_inc.v`: ⊴-algebra — `msubst_*_id`, `a_suffix_app`,
  `a_inc_refl_gen` ⇒ `a_isub_refl`, `a_isub_weaken_suffix` (all Qed).
- Notation retrofit of `def_decorated.v`/`def_decl_algo.v` (ground rule 1);
  ground rules 1–3 added to CLAUDE.md.
- `a_wf_ptyp`/`a_wf_pskl` made REAL scoping judgments (`a_binds_tvar` moved
  to `algo/def_extra.v`); `a_inc__flex_def` gained the paper-PROSE side
  condition (θ maps to well-formed monotypes in the target,
  algorithmic.tex:123) — this is what makes identity increases keep
  flexible variables and defined-variable transport provable.
- Transport + transitivity Qed (`prop_inc.v`): `a_inc_binds_tvar/_flex/
  _flex_def`, `a_inc_binds_tvarish`, `a_tyequiv_weaken`, `a_tyequiv_isub`
  (stability of ≡), `a_inc_strengthen_suffix_src`, `a_inc_suffix_target`,
  `a_inc_trans` ⇒ `a_isub_trans`.
- NEXT: stability of `ad_pat_consis`/`ad_refine_*` under ⊴ (uses the
  transport kit), `a_unify`/`a_assign` soundness (paper
  thm:sound-consistency parts 2–3), then "Soundness of decorated
  consistency" (Δ₁/Δ₂-generalized, per the paper's proof sketch).

## 2026-07-11 — def_decorated.v + clean PROGRESS

`algo/def_decorated.v` written from `appendices/decorated-algosub.tex`:
erasure `uskl_to_pskl`, `uskl_ghost_free`, `a_tags_sort` (the `Θ ⊢^N
tags{Ψg}{ψg}` premise), `a_consistag` (Δ₁∣Δ₂ + Ψ), `a_subtag` (incl. both-δ
ForallL with look + fresh-Ψg decoration), tag solving `a_solvetag_sub/_eq` +
`a_solvetag`.  Build 🟢.  Old PROGRESS.md archived to
`docs/PROGRESS-legacy-2026-07.md`.

## 2026-07-10 — RE-MECH restart against the finalized paper

Paper finalized (merge `8dfafca`); clean restart per the three-step plan:
(1) decl defs synced with the paper — inconsistencies flagged in
[`docs/REPORT-remech-decl-sync.md`](docs/REPORT-remech-decl-sync.md); fixes:
`is_tskl` untagged-∀ case removed (ψ requires every quantifier tagged),
`d_tags_skl` restricted to ψ's grammar, `d_pat` restructured to the paper's
embedded-subtyping P-Unit/P-Var/P-Anno (no `d_pat__sub` / `is_base_term`).
(2) `frost/algo/def_extra.v` REWRITTEN from `full-algo-spec.tex`: new
`Δ₁∣Δ₂` tracking in `a_consis`, no `refresh`, `□`-RHS Vacuous rules,
GhostLF/GhostL solve rules with `⊤.` outputs, `∀ᾱ.A₀`-input
AbsCheck/AbsAnnoCheck (step/base), Freeze with type input, `a_guess` =
paper's `guess[N]`, `a_sub_flex` (ex-`a_broom`), `Assign-UnivGhost-Id`.
(3) proofs to be redone bottom-up following the paper's appendices; the
pre-sync proof files were moved to `*.v.legacy` (git-tracked, out of the
build) for incremental rebasing.
**Build 🟢 GREEN** (`make coq`).
