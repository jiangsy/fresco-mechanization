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

## 2026-07-13 (e) — aconsis-soundness main induction: 11/14 cases proved

`a_consis_sound_aux` (prop_consis_sound.v): statement finalized; 11 of
14 cases Qed and committed — Ghost, Unit, Rigid, Arrow, UnivGhost,
UnivGhost2, UnivGhostR, GhostR, Flex, FlexL, FlexR.  The flex cases
needed several new lemmas (unify symmetry + subjects-are-flexible,
assign-subject-is-flexible, exact rigid transport, lc- and
guardedness-preservation of refinement).  The 3 ∀-cases (ForallInh,
ForallSyn, UnivGhost1) are admitted; ForallInh is ~95% drafted (saved
to scratchpad) — only a refinement-side embedding-form rewrite in its
synth component is still being worked out.  Partial commits per user
direction (admits are WIP; no case is false).

## 2026-07-13 (d) — main-induction infrastructure COMPLETE

`a_assign_preserves_wf` (0d7333a) — the last wf-preservation blocker
(the Arrow case of the main induction chains `a_wf_aenv Θ1`) — plus its
support (mono_ptyp_wf, a_wf_aenv_uniq, a_guess_mono_flex_binds,
a_wf_aenv_prepend_flex/_strip_prefix, a_assign_new_avoids_F +
a_assign_notin) and `ad_wf_pskl_ftv_tvarish` (247e0e7).  Every
supporting lemma of the aconsis-soundness main induction is now Qed.

Worked out the full ∀-case assembly on paper (ForallInh step-by-step,
recorded in memory `remech-aconsis-main-induction-crux` with the
finalized lemma statement).  What remains is: 3 small "strip a shared
rigid head" lemmas (`a_isub_strip_tvar` via a_inc_tvar_inv + uniqueness,
`no_flex_dep_strip`, `faf_strip`) and the 14-case assembly itself —
transcription against the recorded recipe, no new design.

## 2026-07-13 (c) — main-induction prelude: helpers + wf transport/preservation

Toward the aconsis-soundness main induction (all Qed, prop_consis_sound.v):
close/erasure commutation (`bskl_to_pskl_close`), `a_assign_subject_binds`,
`ad_wf_pskl_reassoc` (move a Δ-var into the context as a rigid, to open
∀-binders in well-formed skeletons), F-monotonicity of the hygienic
refine judgments, `a_wf_ptyp_isub` / `a_wf_pskl_isub` (wf transport along
⊴), the `a_wf_aenv` inversion lemmas, and `a_unify_preserves_wf`.

Refined the statement design (recorded in memory
`remech-aconsis-main-induction-crux`): the two refinement components use
LOCAL F (F=Δ1 for the synth component, F=Δ2 for the pskl component — NOT
Δ1∪Δ2, which breaks Ghost's comp-4 hole side condition); the ∀-case
assembly is strip → rename → F-weaken in that order; and `a_wf_aenv Θ1`
must be a conclusion because the Arrow case chains it into the second
sub-derivation's IH.  REMAINING: `a_assign_preserves_wf` (the Ξ-split +
βs-block + new-def reconstruction) then the 14-case induction itself.

## 2026-07-13 (b) — invariant-preservation package COMPLETE

`no_flex_dep` / `flex_above_free` (Δ-names sit above and differ from
every non-rigid entry) with their split/extension algebra and the two
preservation theorems `a_assign_preserves_inv` / `a_unify_preserves_inv`
(cbd8152): Assign-SkipRigid's occurs condition discharges each
Δ-variable as its entry is walked, the positional invariant makes every
Δ-variable walked by the time Assign-SolveM fires, and the used-name
freshness keeps the guessed names off Δ; unifyvar's only new
definitions are its hatted, Δ-free subjects.  Every prerequisite of the
part-1 main induction (statement, 14 cases) is now Qed — next session
runs the induction itself.

## 2026-07-13 — unifyvar/assignvar prose-completions IMPLEMENTED (user-directed)

Per the user's design call (used-name set, not full-context visibility;
cofinite quantification a la the worklist mechanization's
a_wl_red__sub_arrow2 does not fit because the created names escape into
the output context): `a_flex_tvar` premises on `a_unify__flex_l/_flex_r`;
`a_assign` now carries a used-name set F accumulated by the
entry-walking rules, with `Assign-SolveM` requiring `uniq β̄` and
`dom β̄` fresh from `F ∪ {α̂} ∪ dom(Ξ,Θ0)`.  Paper-shaped judgment =
the F=∅ notation, so the consis rules and decorated defs are textually
unchanged.  Full build green (a_assign_sound generalized over F; two
test sites discharge the new premises).  REMAINING before the part-1
main induction: the invariant-preservation package (no_flex_dep +
flex_above_free positional invariant + preservation through
unify/assign) — design recorded in memory.

## 2026-07-12 (g) — Θ-side renames + a finding on the part-1 invariant

`ad_refine_{syn,pskl}_f_rename_ctx` (7cc630b): the ForallSyn/UnivGhost1
cases build tophole_fill-shaped components with the binder kept rigid in
Θ, so their per-instance transport renames the Θ entry (mid-position).

FINDING (docs/PAPER-GAPS.md, new PROSE-COMPLETION entry): the part-1
augmented solution's "no flexible variable depends on Δ1/Δ2" invariant
is preserved by assignvar via Assign-SkipRigid's occurs condition, but
by unifyvar ONLY via the paper's hatted-metavariable convention —
Flex-Flex-Skip' has no occurs condition, so the mech's unconstrained
`a_unify__flex_l/_flex_r` admit derivations that capture a rigid bound
above the defined variable (ill-scoped `β̂ := X`).  Mech completion
plan (same category as the Assign-SolveM sorted-τ fix): flex-bound
premises on the payload side of flex_l/flex_r; guess^TY β̄-freshness on
Assign-SolveM; then the invariant-preservation lemmas for unify/assign,
and the main statement gains `Δ1∪Δ2 ⊆ Θ0-rigids` + the no-dep premise/
conclusion pair.  THEN the 14-case induction.

## 2026-07-12 (f) — renaming layer + primed ports: part-1 prelude COMPLETE

Crux 2 resolved (5ea381c, ba14da5, 8e0b350): `ad_pat_consis_rename_tvar`
(binder's Θ-entry, mid-position), `ad_refine_{syn,pskl}_f_rename`
(Δ-side, `add Y (remove α Δ)`; fills invariant since α is in the
hygiene set), `ad_wf_pskl_rename_tvar`, subst/ftv-vs-embedding
equations.  Primed ports: `_f_delta_mono`, `_f_refl(_inh)`, `_f_isub`,
and `ad_pat_consis_refine_{syn,pskl}_f_mono` (hygiene inherited from
the painted side + definitions — the paper's no-flex-depends-on-Δ
problem invariant).  Every ingredient of the part-1 main induction is
now Qed; NEXT session: the 14-case induction itself (assembly recipe
in memory note remech-aconsis-main-induction-crux).

## 2026-07-12 (e) — fill-hygienic refinement scaffolding (∀-case crux 1)

`ad_refine_syn_f` / `ad_refine_pskl_f` in prop_consis_sound.v: the
refinement judgments with a set F forbidden in ghost fills (only the
hole rules gain a side condition), plus `*_f_strip` (drop the opened
ForallInh/ForallSyn binder's rigid entry from Θ given it is in F and Δ
— the paper's implicit "by definition of refinement" strengthening;
fills avoid it by hygiene, variable occurrences use Δ, definitions sit
below it), `*_f_forget`, and `ad_wf_pskl_strip_tvar`.  The main
induction will run primed with F := Δ1 ∪ Δ2.  REMAINING for part 1:
primed copies of refl/Δ-mono/⊴-stability; tvar-rename lemmas for
`ad_pat_consis`/`ad_refine_*_f` (crux 2: the ∀-cases' per-α coloured
witness — close the witness at one fresh α, rename per instance); then
the 14-case induction.

## 2026-07-12 (d) — appendix B part 1 support layer (prop_consis_sound.v)

The pieces the flex cases of the aconsis-soundness main induction need
(all Qed): `a_unify_sound_consis` (part 2 restated declaratively — the
paper's Flex case reading; subjects are always variables by
`a_unify_var_inv`, so the conclusion is stated over any binds-monotone
extension Θ' of the output with the subjects tvar-ish, which is how the
skip cases re-assemble the context — NO definition folding needed),
`ad_pat_consis_refine_syn_mono` / `_refine_pskl_mono` (consistency at a
monotype painting implies both refinement components — the paper's
"flex vars don't depend on Δ" steps for Flex/FlexL/FlexR),
`ad_pat_consis_fold_def_q_mono` (Q-side definition folding at
monotypes), plus mono-painting equations and `a_wf_aenv_binds_def_mono`.
NEXT: the 14-case main induction (statement: ⊴ ∧ ∃ coloured witness Q̃
with ⌊Q̃⌋ = Q, consis (syn P ≈ Q̃), refine-syn (inh P0 ⊳ Q̃), refine-pskl
(P ⊳ Q) — the paper's `bid Q` colouring is built inductively:
ForallInh paints the binder inh, ForallSyn syn), using prop_stability's
⊴-transport and prop_refine's reflexivity lemmas.

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
