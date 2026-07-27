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

## 2026-07-27 (later) — P6-Cv PREMISE-FREE: `pskl_no_hole P0` removed (paper-faithful statement)

`a_solve_eq_complete_var` / `_gen` no longer carry the mech-only
`pskl_no_hole P0` side condition; still `Qed` and "Closed under the global
context".  The enabler is the **bag split** `aenv_split` (binds-iff +
dom-eq + disjointness, `a_wf_aenv Θr` explicit) replacing the list
equation `Θ = Θtv ++ Θr`: the equation forced the ForallSyn binder into
Θtv (the consistency rule prepends it to Θ), hence the aenv→Δr refinement
transport, hence the premise.  With the bag, `Θr_ih := (X~tvar)++Θr`
makes the tophole_fill body the IH's refinement premise verbatim, and
holey `P0` flows to the per-row SolE-VacuousR columns — the paper's
per-node `P0 = Hole` dispatch.  §6(t)'s "split-B impossible" was an
artifact of the equational representation.  Dead kit deleted
(`bskl_no_hole`, `ad_refine_syn_aenv_to_delta(_mid)`); WF-SIDE-CONDITIONS
entry flipped to REMOVED/historical; consequently P6-Cs needs no
`P0 = □ ∨ no_hole` disjunct and the Task A accumulated-skeleton invariant
(`prop_accum_no_hole.v`) is supporting kit rather than a requirement.


## 2026-07-27 — P6-Cv CLOSED: `a_solve_eq_complete_var` axiom-free, 0 admits

`a_solve_eq_complete_var` and `a_solve_eq_complete_var_gen` are `Qed` and
"Closed under the global context" (`Print Assumptions`), in the new file
`frost/algo/prop_look_complete_var.v`.  This finishes P6-Cv (the variable
case of consistency-constraint solving completeness, consistency-proofs.tex:
1180) — the last of the 15 consistency cases, `forall_syn_tagged`, and its
three Pi-rows.

Kit that closed it (see DESIGN-completeness-subtyping.md §6(u)):

- **split-A** for the ForallSyn IH: `Θtv_ih := (X~tvar)++Θtv`, `Θr_ih := Θr`
  (X stays at the front of the fixed IH aenv), giving the tight family
  premise `dom Θr` — matching the already-closed `forall_inh_tagged`.
- **`ad_partial_precise_rename_tvar`** (new): an aenv-tvar rename for
  `ad_partial_precise`, which builds the `ad_ppre__tophole_fill` cofinite
  family (binder in the AENV) from a single IHX instance.
- **`pskl_no_hole P0`** side-condition on `_gen` + corollary (registered in
  WF-SIDE-CONDITIONS.md): needed because `inh(□) = bskl_hole`, so the
  ForallSyn refinement transport `ad_refine_syn_aenv_to_delta` (moving the
  ∀-binder into Δr) needs `bskl_no_hole`.
- the three rows: ⊤◇ (UnivGhost, `tophole_both` + tophole_fill/rename),
  □ (GhostL, `hole_l` + tophole_fill/rename), ∀ (ForallGhost,
  `all_l_tophole` + Δ-var FOLD + `ad_ppre__forall`).

## 2026-07-25 (later) — P6-Cv at 10/15 cases; GhostG/topholeg/flex/ghost-absurd closed; Arrow blocked on the flex-P0 statement decision

`a_solve_eq_cv_ghostg` Qed (no size induction — both sides forced to □) +
mono-paint tags kit + topholeg kit (all migrated, axiom-free).  Main
induction now closes ghostg, hole/tophole/tophole_inh/tophole_drop (absurd:
tag-sorted ψa has no plain ghosts — `is_tskl` inversion), flex_l (target
switch to the definition's paint + main IH + `ad_ppre__flex_r` fold),
flex_r (refinement transport), topholeg (KEY continuation; `is_sskl` kit
discharges the paper's P0=□/Ψa=∅ special case; `a_solve_eq_hole_subject_inv`
pins the □-subject sub-output).  Remaining: arrow + 4 ∀-cases.  ARROW
BLOCKED: the drafted statement admits `cex_p6_flex_counterpart.v` verbatim
(re-verified incl. `delta_def_fresh`) — needs a statement-level decision
(P0-side reachability premise vs inlining Cv into Cs); see DESIGN §6(j).

## 2026-07-25 — P6-Cv Var case CLOSED (a_solve_eq_cv_mono / a_solve_eq_cv_var); delta_def_fresh side condition

`a_solve_eq_cv_var` Qed, axiom-free, as the `τ = X` instance of a MONO-target
generalization `a_solve_eq_cv_mono` (target = painting of a mono ptyp; the
defined-flex target chains live in an `a_def_chain` relation whose inversions
ride the premise derivations, not the size measure).  ~25 supporting lemmas in
`algo/prop_look_complete.v` (paint inversions, chain transports, chain-based
subject inversions, the two refinement→precision bridges).  The P6-Cv statement
gained the `delta_def_fresh Δ Θ` hypothesis — a NECESSARY wf-side-condition
(Δ-free statement refuted; registered WF-SIDE-CONDITIONS §7, DESIGN
§6(i)).  Main-induction Unit + Var cases wired and closed in the dev scratch;
13 consistency cases remain.  Perf: two hangs diagnosed and fixed (fsetdec on
an evar `Δr` goal at the bridge call sites → pin `with (Δr := empty)`;
`ltac:(lia)` elaborating before its named arg pins `n` → prior assert).

## 2026-07-25 — the nonflex{P0} repair REFUTED at depth (machine-checked); repair redirected

Tried the proposed -var repair (a `nonflex{P0}` premise) in the mech before
committing to it in the paper — and it fails: `cex_p6_var_nonflex_insufficient`
(cex_p6_flex_counterpart.v, Qed axiom-free) reruns the refutation with
`P0 = 1 → β̂` (nonflex HOLDS) — the Arrow case recurses on P0's pieces, and a
flexible piece opposite the ρ-leaf reproduces the failure one level down.
Key insight from the failed experiment: at ρ = identity (the P = α crux, the
only place the paper instantiates the -var lemma directly) the configuration
is premise-unsatisfiable — the falsity is an artifact of the ρ-generalization
forgetting that flexible counterpart pieces cannot cover ρ-substituted
positions.  Redirected repair (next to validate): extend the positional side
condition to P0 — no flexible variable at or covering a ρ-position —
maintained by the same X-postdates-everything freshness argument.
PAPER-GAPS addendum + paper note amended (remech-paper).

## 2026-07-24 (e) — SE-FlexR widened to the paper's context-free reading (encoding-infidelity fix)

`a_solve_eq__flex_r` demanded `binds α abind_flex_mono Θ` (UNDEFINED
flexibles only); the paper's FlexR (full-algo-spec.tex:1374) is
context-free — `nonflex P` is its only premise, so it fires on ANY
hatted variable, defined or not.  The narrowness was an INDEPENDENT
falsifier of the completeness statements (distinct from the (d)
counterexample, which uses an undefined flexible): a defined flexible
nested in a structural counterpart (`P0 = unit → β̂`, `β̂ := unit ∈ Θ0`)
makes the solve stuck in the mech but succeed on paper, with all other
premises satisfiable — and it would have survived any repair of the
paper-level gap.  Premise widened to `a_flex_tvar Θ α`; fallout was
confined to prop_look_complete.v's ctx-change/strengthen/weaken/rename
helpers (adapted); the soundness stack needed ZERO edits (restriction →
relaxation only adds derivations, and the decorated twin SEq-FlexR was
already context-free).  Full `make coq` green; `a_sub_sound_thm` still
Closed under the global context.

## 2026-07-24 (d) — P6 BLOCKED: the -var completeness lemmas REFUTED (machine-checked)

While drafting P6-Cv's statement, the Pi × P0 case grid exposed a subcase
every paper case analysis skips: the solve counterpart `P0` can be a
FLEXIBLE VARIABLE whose θ-image supplies the constructor that the
refinement-premise inversion "exposes".  Concrete configuration
(`Θ0 = X,α̂`; `θ = [α̂ ↦ unit→unit]`; `ψa = X→unit`; `ρ = [X ↦ unit]`;
`Pi = X→unit`; `P0 = α̂`; `Q = unit→unit`) satisfies every premise of
`lemma:complete-consistency-constraint-collection-solving-var`
(consistency-proofs.tex:1181; same for the subtyping twin at
subtyping-proofs.tex:1696) — including the positional side condition —
while the conclusion is unsatisfiable: FlexR forces `Pa = α̂` and the
precision `θa(α̂) ⊑ᵖ X→unit` fails for every `θa ≡ θ`.  Machine-checked
Qed axiom-free: `frost/algo/cex/cex_p6_flex_counterpart.v` (refutes for
arbitrary `Pa`, `θa`, Δ, tag set).  PAPER-GAPS entry added; DESIGN
§6 (d) has the candidate repairs (both change statements → need
sign-off).  LE-FlexR is never used in either completeness appendix —
the flexible-counterpart subcase is a systematic blind spot of the
5-lemma cluster.  Related: mech `a_solve_eq__flex_r` is narrower than
the paper's context-free FlexR (undefined flexibles only).

Statement-neutral kit delivered (Qed, prop_look_complete.v):
`a_solve_eq_hole_subject_inv`, `uskl_rho_weaken`, `binds_mid_drop`,
`ad_partial_precise_strengthen_tvar(_mid)`, `a_solve_eq_wf`; plus
`a_tyequiv_def_free_eq` / `a_inc_equiv_flex_pin` in the cex file.

## 2026-07-24 (c) — P6 started: ρ-relation decided (+ corrected), leaf/freshness kit Qed

New file `frost/algo/prop_look_complete.v` (all Qed, axiom-free;
`p6_leaf_var` = Closed under the global context).  The paper's ρ is the
RELATION `uskl_rho` (refl + congruences + replace-leaf; DESIGN §7
DECISION block).  DESIGN CORRECTION: the paper's positional side
condition on P_i is load-bearing — counterexamples v4/v5 (DESIGN §7)
show Δ-membership + precision alone admit ⊤◇-wrapped/def-chained leaf
positions that break the conclusion — and is RECOVERED as the lemma
`ad_ppre_delta_var_inv` from freshness of the replaced variables
(Δ-membership, rigid binding, θ-image-/Θ-definition-/⊤◇-shielded-ftv
avoidance via the new `pskl_shielded_ftv`).  Kit: solve-cluster
ctx-change/strengthen/weaken/rename + shielded-output bound, msubst
avoidance lemmas, `is_sskl` painting/refine-hole/consis-tags-empty
helpers, and the packaged -var leaf case `p6_leaf_var`.  Statement
decision: the -var lemmas conclude with θ itself (no θa existential).
NEXT: `uskl_rho` per-constructor inversions, then P6-Cv's main
induction (DESIGN §6 2026-07-24 (c) has the full map).

## 2026-07-24 (b) — P5b-ii step (3) QED: precision-substitution closed

**`ad_pat_sub_precise_upre` (paper `lemma:precision-substitution`) is Qed,
axiom-free** (commit f5b3e72; `Print Assumptions` closed; `make coq`
green) — fuel-PRESERVING precision-substitution over the tag-hygienic
mirror, in ⊑ᵤ-form.  Completed this pass: the remaining six per-rule
⊑ᵤ-transports (Arrow; ForallL tagged/untagged — the crux, via cofinite
body-⊑ᵤ + `uskl_precise_subst` + `subst_bskl_in_uskl_intro` + recursion
at `Ψsup ∖ Ψ'`; UnivGhostL/LG incl. the keepg→L root; FlexMono with the
flex_r root via `binds_unique`) and the 12-case main assembly.  All P5
milestones are now closed except two deferred bridges: the subst-form
corollary (`S[Pa/α] ⊑ᵤ S[ψa/α]`, built when P7b needs it) and the
`_n → _g` tag-renaming freshening (only P7c consumes it).  PAPER-GAPS
gained two entries on `lemma:precision-substitution`: `fresh Ψ'` must be
GLOBAL freshness (the local reading is false via an Arrow-split
scenario), and the "straightforward induction" hides a motive
generalization (⊑ᵤ) plus a fuel-accounting repair
(non-incrementing UnivGhostL/LG/FlexMono).  NEXT: P6.

## 2026-07-24 — P5b-ii (2') Qed + step-(3) infrastructure Qed (⊑ᵤ track)

Executed DESIGN §5.4 through (2') and most of (3)'s infrastructure, all
Qed axiom-free (commits b925723, 0eb95ff, a3da6b7):

- `prop_consis_precise.v`: the ⊑ᵤ relation `uskl_precise`
  (refl + congruences + refinement-mirroring ghostier-LHS rules; no
  tophole_fill mirror — ⊑-targets are inh-paintings), its kit
  (psi_cong / ftag_sub / ftag_rep / lc_l / **subst-compatibility** /
  **embedding** of plain precision against a decorated target), and
  **(2') `ad_pat_consis_precise_upre`** via `consis_split_transport`
  + 7 per-shape transporters.
- `def_decl_algo_sub_hyg.v` (NEW): tag-hygienic fuel mirror
  `ad_pat_sub_g` — ForallL instantiation tags fresh from the subject's
  syntactic tags; fuel: leaves any-n, UnivGhostL/LG/FlexMono
  non-incrementing, Arrow/ForallR/ForallL increment (makes
  precision-substitution fuel-preserving under ⊤◇-wrapping/flex-folding).
- `prop_sub_complete.v`: `_g` helper layer (erasure, psi_cong, ftag-sub
  invariant, wrap_tophole, fold_flex, concrete_target, refl_transport,
  hole_intro) + per-rule ⊑ᵤ-transports for UnivGhostR / Ghost / GhostG —
  the inner-⊑ᵤ-induction pattern (rebuild-via-(2'), same-fuel peels,
  flex_r subject-unfold) is validated end-to-end.

Remaining for (3): Arrow / ForallL(×2, the subst-compat crux) /
UnivGhostL(G) / FlexMono transports + the 12-case main assembly — fully
scripted in DESIGN §6's 2026-07-24 entry (incl. the 4 proof-engineering
rules learned).  PAPER-GAPS entries deferred until (3) is Qed.

## 2026-07-23 (b) — P5b-ii step (2) Qed + consis-precision refactor + §5.4 plan

Completeness-of-subtyping precision-substitution, consistency half DONE:

- NEW `frost/def_tags.v` — `ftag_in_uskl`, the syntactic ε-tag collector
  (leaf module; tags are plain atoms so lngen generates none).
- NEW `frost/algo/prop_consis_precise.v` — the consistency
  subject-precision metatheory, all Qed axiom-free: the general tag/wf
  helper kit and the crux lemmas (1a)/(1b)/(1) MOVED out of
  `prop_sub_complete.v` (which keeps P5a + P5b-i only), plus NEW
  `ftag` kit, `d_tags_skl_ftag`, `ad_pat_consis_ftag_sub`
  (tag ctx ⊆ subject tags), `ad_pat_consis_precise_var_case`, and the
  step-(2) target **`ad_pat_consis_precise_subst`** — substituting the
  more-precise `Pa` for the decorated instantiation `ψa` in a
  consistency SUBJECT preserves consistency, tag context dropping by
  `Ψa` (15-case induction; the paper's `fresh Ψ'` rendered as
  disjointness from the residual ctx AND the subject's other tags).
- Design findings (DESIGN-completeness-subtyping.md §5.4): the paper's
  ForallL `fresh Ψ'` is GLOBAL freshness — the plain fuel mirror makes
  step (3) FALSE under tag collisions, so (3) needs a tag-HYGIENIC
  mirror `ad_pat_sub_g` (+ deferred renaming-based freshening bridge);
  and the subst-form is too weak for its own ForallL crux — (3) runs
  over a subject-precision relation ⊑ᵤ (leaf = precision-replace,
  congruence elsewhere; subst-compatibility closes the crux).
- `make coq` green; flagship `Print Assumptions` unchanged.

## 2026-07-13 (g) — decorated-consistency soundness 12/18 (WIP)

`a_consistag_sound_aux` (lemma:sound-decorated-consistency): the
parallel of the main induction over the tagged judgment `a_consistag`
(18 rules), threading the tag context Ψ into the declarative
consistency component.  12 cases Qed — the 10 structural ones plus
Flex/FlexL (structurally identical to the ordinary versions).  New
helpers `ftvar_in_pskl_uskl_to_pskl`, `ad_pat_consis_psi_cong`.
Admitted (6, with real subtleties recorded in memory): FlexR (a_assign
only sees the tag-erased ⌊S⌋ˢ) and the 5 ∀-cases (tag threading in the
binder).  Templates: the ordinary flex/∀ cases in a_consis_sound_aux.

## 2026-07-13 (f) — aconsis-soundness main induction COMPLETE (thm:sound-consistency part 1)

`a_consis_sound_aux` (all 14 cases Qed, axiom-free — "Closed under the
global context") + the paper-shaped corollary `a_consis_sound`
(Δ-contexts empty, forgets the fill-hygiene scaffolding via `*_f_forget`
to land the plain `⊢ᵣᵃ`/`⊢ᵣₚᵃ` refinements).  The 3 ∀-cases used the
strip→rename→fmono / rename_ctx assembly; the flex cases needed
`a_unify_sym` + `a_unify_subjects_flex`, `a_assign_subject_flex`,
`a_isub_binds_tvar`, and lc-/guardedness-preservation of refinement.
README.v indexes a_unify_sound / a_assign_sound / a_consis_sound (all
three flagships of thm:sound-consistency, parts 1–3).  Statements use
the paper-shaped notations.  NEXT in appendix B: Soundness of DECORATED
consistency (composes a_consis_decorate with these), then completeness.

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
