# Frost Mechanization — Progress

Coordination file for the Phase 2 + Phase 3 push. Two sections:

- **[Part 1: Paper → Mechanization mapping](#part-1-paper--mechanization-mapping)** — per-lemma status, statements, locations.
- **[Part 2: Daily progress](#part-2-daily-progress)** — session-by-session closure log.

**Spec:** [`docs/superpowers/specs/2026-05-10-frost-phase23-design.md`](../docs/superpowers/specs/2026-05-10-frost-phase23-design.md)

## Status (current — 2026-05-20 split-syntax faithfulness audit)

**Build:** 🟢 GREEN (`make coq -j 4`).

**Audit scope requested:** flagship statements only, especially
general/generalised subsumption and algorithmic soundness/completeness.

**Headline verdict:** the current Coq files compile against the latest
split syntax, but several flagship statements are **scaffolding rather
than faithful paper mechanizations**.

| Flagship | Paper claim | Current Coq name | Faithfulness |
|---|---|---|---|
| D1 General subsumption | `Γ ⊢[TI] M ⦂ syn{A}` and `Γ ⊢[M] syn{A} ⊑ bid{B}` imply `Γ ⊢[M] M ⦂ bid{B}` | `d_typing_general_subsumption`, `d_typing_general_subsumption_via_gen` | 🟡 **faithful statement shape, proof admitted**. Current statement quantifies `A : ptyp`, assumes `Γ ⊢[TI] e ⦂ ptyp_to_btyp_syn A`, and subtypes from `ptyp_to_utyp_syn A`; no erased/repainted arbitrary `btyp` remains. |
| D12 Generalised General Subsumption | `FN^n TI` typing plus mode/type compatibility plus generalized subtyping implies `FN^n M` typing | `d_typing_general_subsumption_gen` | 🟡 **close but incomplete**. Uses `is_fn_n_ti` and `mode_fn_n_subst`, which matches `FN^n`; generalized subtyping now uses native `gutyp` for the paper's generalized unresolved `bid{T}`. Missing explicit paper premise `skmod[TY] (FN^n TI) bid{A}` and relies on scaffold `d_sub_gen`. Proof is admitted. |
| Algorithmic type inference soundness | If the algorithm answers a type-inference question, its output is a solution | `a_typing_sound` | 🔴 **not faithful**. Current `a_typing` has one permissive constructor and current `a_transfers` relates any algorithmic context to any declarative context. |
| Algorithmic type inference completeness/minimality | If a solution exists, the algorithm returns a minimal solution | `a_typing_complete` | 🔴 **not faithful**. Current statement is only declarative-to-algorithmic existence; it does not mention paper questions, solutions, metasubstitution factorization, consistency of outputs, or minimality. |
| Algorithmic subtyping soundness/completeness/minimality | If a solution exists, `a_sub` returns the minimal solution | `a_sub_sound`, `a_sub_complete` | 🔴 **not faithful**. Current `a_sub` is reflexive-only, while `a_sub_sound`/`a_sub_complete` use simplified declarative shadows and omit the paper's question/solution/minimality structure. |
| Algorithmic skeleton inference soundness/completeness | Algorithmic skeleton inference returns a safe/most informative solution | `a_pat_sound`, `a_pat_complete` | 🔴 **not faithful** for the same reason: permissive placeholder rules and no solution/minimality relation. |

**Current admit count:** 36 total under `frost/`.  This is not a
proof-completeness audit; it is a statement faithfulness audit.

**Next faithful-statement work:**

1. Add the missing D12 mode/type compatibility premise over the split
   category (`mode_typ_compat` currently lives over `ptyp`; D12 needs a
   native condition for `btyp` or a documented erasure-based bridge).
2. Replace algorithmic placeholders with the real paper questions,
   solution relations, metasubstitution/factorization, and minimality
   predicates before claiming soundness/completeness.
3. Rebuild `a_transfers` so it is an actual projection from algorithmic
   contexts to declarative contexts, not the current universal relation.

**Hard-proof finding (2026-05-20/21):** the first apparent
counterexample was a **mechanization translation issue**, not a core
calculus issue.  The scaffolded generalized subtyping/consistency layer
used `btyp`, which both lost ε-tags and allowed top-level inherited
forall on the left of `Infer`/`Check`/`ForallR`.  The paper's generalized
consistency works over generalized unresolved types.  The mechanization
now has a native `gutyp` category for that grammar, and
`d_sub_gen__infer_gen`, `d_sub_gen__check_gen`, and
`d_sub_gen__forall_r` use synthesized/unresolved `utyp_to_gutyp C` on
entry.  The non-paper `d_consis_gen__embed`,
`d_consis_gen__refl_plain`, and `d_sub_gen__embed` shortcut rules have
been removed; ordinary cases now have to go through the native
generalized rules.  `d_sub_gen_top_inherited_lhs_impossible` checks that
`gutyp_all_inh ...` can no longer appear as a top-level generalized
subtyping LHS.

**Remaining hard-proof issue:** generalized `Arg` still permits
bidirectional arrow components, as the paper's generalized proof
requires.  Closing `d_sub_gen_trans` now needs generalized
consistency/subtyping composition for those bidirectional components
and the native generalized `ForallL` cases.  That is a
proof-generalization/support-lemma issue unless a smaller counterexample
is found in the arrow/forall-left cases.

**Proof push update:** trying `d_sub_gen_trans` directly no longer
stops on top-level inherited forall.  After removing the non-paper
embedding shortcuts, the next required theorem is a native generalized
composition lemma for `d_consis_gen`/`d_sub_gen`, covering `Arg` and
`ForallL` directly.  This classifies the current blocker as a missing
generalized support theorem, not as the earlier translation bug.

## Historical status (pre split-syntax audit; retained for archaeology)

The following section describes the older unified-`typ`/δ-cascade state
and is no longer the current status of the repository.

**Flagship theorems (D1 / D12):** ⚠️ **NOT** "Closed under the global
context" post-δ. `Print Assumptions` on
`d_typing_general_subsumption_via_gen` and `_gen` lists **8 axioms**
(was 10 after Phase 0; 4 nominally closed in Phases 1A-1C, but
`d_sub_mono_RHS_eq` + `d_consis_LHS_mono_wf` re-surfaced via
`d_sub_gen_trans_forall_l_untagged_helper`'s residual admit chain
— see Phase 1.G entry for the corrected count).

**Phase 1.G summary (2026-05-17):** TODO plan to close the remaining
axioms has fundamental blockers — Pattern A's `d_consis_subst_typ_with_ttyp`
is unsound when subst'd var has multiple occurrences (ε-tag linearity
violation, also a paper-level gap in B.3 ForallL). Pattern B option (a)
doesn't compose at D12 (no source of `mono_typ Bhead` for poly body types).
Inline at D12 has the same blocker as SPLIT. Both require either
expressivity restriction OR a paper-faithful redesign of ε-tags as
binders. **Foundation `d_consis_gen_syn_inh_erase_eq` added** for future
work but doesn't drop axioms by itself.

**Closed in Phases 1A-1C (4 axioms):**
- `d_sub_gen_trans` — was fully Admitted; now Qed mod its helper
  (replaced by `d_sub_gen_trans_forall_l_untagged_helper` which itself
  has 1 residual admit, see below).
- `d_consis_gen_trans` — was wholesale-admitted; now Qed with added
  `is_typ T` precondition (rules out the unreachable
  `typ_all_etag → typ_all_col colour_inh` composition; call sites supply
  via `d_wf_typ_is_typ`).
- `d_consis_extends_d_consis_gen` — was wholesale-admitted; now Qed.
- `d_sub_mono_RHS_eq` + `d_consis_LHS_mono_wf` — auto-dropped from the
  axiom list as a side effect of closing `d_sub_gen_trans` (they were
  pulled in only via that lemma's chain).

**Remaining 6 axioms (structural):**

**Pattern A — "non-nil Δ' for __forall_l_untagged" (3 axioms):**
1. `d_sub_gen_trans_forall_l_untagged_helper` — closes for ph mono
   (Δ' = nil); admits when ph contains ε-tags (Δ' ≠ nil).
2. `d_consis_gen_extends_d_sub_nil` — 1 sub-case admit at the new
   `d_sub__forall_l_untagged`. Same Δ' issue.
3. `d_consis_sub_trans` (paper B.3) — 1 sub-case admit at the new
   `d_sub__forall_l_untagged`. Signature DOES handle non-nil Δ via
   Permutation, so this might be closable with a `d_consis_subst_typ`
   helper. Most tractable of the three.

**Pattern B — provably-false via SPLIT-helper dependence (3 axioms):**
4. `d_consis_syn_inh_mono` — provably false; used in 4 SPLIT-helper sites.
5. `d_consis_gen_syn_inh_mono` — provably false; same pattern, gen variant.
6. `d_consis_gen_lhs_syn_eq` — provably false; used in 8 SPLIT-helper sites.

**Strategy for remaining work:**
- Pattern A: unblocker is a `d_consis_gen_subst_typ` lemma (substitute a
  wf type for a free var in d_consis_gen — generalization of existing
  `d_consis_subst_mono` to non-mono substitutes). Add it once, close
  all 3 admits.
- Pattern B: requires restructuring the SPLIT helpers
  (`d_typing_abs_value_to_subsumption_split_d_sub` and its anno variant)
  to derive mono/equality via the structural equation
  `syn_color T1 = inh_color_t Ahead` (invariant 3, intact) instead of
  routing through the broken d_consis chain. T2 side needs a
  polymorphic-body-aware variant.

**Alternative direction (separate effort):** paper-faithful translation
of Lemma B.2 (Consistency Transitivity) and B.3 (Consistency-Subtyping
Transitivity) as **more general** versions (handling arbitrary Δ via
Permutation, matching the paper signatures). The current mechanized
versions over-restrict to nil Δ, which is why some compositions don't
fit. The paper-faithful versions would subsume both Pattern A and
several Pattern-B-adjacent uses.

**Pre-refactor flagship status (commit `8701b4a`)**: both Qed and "Closed under the global context", zero axioms.

**Admit counts (frost/decl/):** 15 base admits (pre-refactor) + **18 new
admits from the δ-encoding refactor** (commits `0bf2815` + δ-cascade
Phase 0). Of the 18 new:
- **8 are PROVABLY FALSE post-refactor** (lemma's conclusion now
  contradicts the new rule's behaviour — needs precondition strengthening,
  not just proof completion):
  - `d_consis_LHS_mono_wf` / `_is_typ_mono`
  - `d_sub_LHS_mono_wf` / `_mono_RHS_eq`
  - `d_consis_empty_eq`
  - `d_consis_gen_lhs_syn_eq`
  - `d_consis_syn_inh_mono` (newly surfaced in Phase 0)
  - `d_consis_gen_syn_inh_mono` (newly surfaced in Phase 0)
- **3 are wholesale-admitted** with original body preserved as
  `(* ... *)` for re-introduction: `d_consis_compose`,
  `d_consis_gen_trans`, `d_consis_extends_d_consis_gen`.
- **1 is a structurally-reachable new case requiring proof restructure:**
  `d_sub_gen_trans` `__forall_l_untagged` inner case at `mode_fn m`
  (surfaced in Phase 0; paper's proof inducts on first d_sub, mechanization
  inducts on `is_fn_n_ti m1` and lacks the matching IH).
- Remaining 6 are sub-case admits with spec links.

See [`docs/superpowers/specs/2026-05-17-delta-encoding-refactor-design.md`](../docs/superpowers/specs/2026-05-17-delta-encoding-refactor-design.md)
and the 2026-05-17 (δ-refactor) entry in Part 2 below.

**Pre-refactor admit categories (still apply to baseline):**
- Phase 2.E skeleton inference (D6, D7) — 2 admits
- Phase 2.D research-grade (stability S1/S2, expressiveness E1) — 6 admits in `prop_typing.v`
- Phase 2.D narrowing / type subst — 3 admits in `typing/prop_weakening.v`
- Post-refactor false helper (lemma is FALSE under new rule set; kept with explanatory comment for now) — 1 admit (`d_consis_gen_narrow_consis` re-encoding gap, see also `d_typing_narrow_consis`)
- Paper-flagged (D3) + colour-tag translation (`d_sub_complete_mono`) — 2 admits in `prop_sub_sound.v`
- `d_typing_gen_lift_mono` __app — 1 admit (was no longer reachable pre-refactor; broken via `Hbody_at_tc` refactor). The non-gen sibling `d_typing_lift_mono_mut` / `d_typing_lift_mono` was deleted 2026-05-17 (zero callers).

**Admit counts (frost/algo/):** 6 admits — all Phase 3.B/C HEADLINE soundness/completeness theorems.

## TODOs (δ-cascade closure — next-session priorities)

Tracked here so the next session has a clean hand-off without scanning the daily log.

### Critical path to D1/D12 "Closed under the global context"

The 6 leaking axioms split into two patterns, each needing one structural fix:

**Pattern A — non-mono ph in `__forall_l_untagged` (3 axioms):**
- [ ] **Add `d_consis_subst_typ_with_ttyp`** (generalize `d_consis_subst_mono` from `mono_typ B` to `d_wf_ttyp Δ_ph Γ2 ph`; output Δ becomes `Δ_outer ++ Δ_ph` with disjointness). ~150-line induction on d_consis with ε-tag bookkeeping per constructor case. Add at the same location as `d_consis_subst_mono` in `subtyping/prop_basics.v`.
- [ ] **Close `d_consis_sub_trans` non-mono case** (1 admit at `subtyping/prop_consis_sub_trans.v:208` `__forall_l_untagged` branch). Mechanical given the subst lemma.
- [ ] **Close `d_sub_gen_trans_forall_l_untagged_helper` non-mono case** (1 admit at `typing/prop_subsumption_aux.v:~445`). Mechanical given the subst lemma.
- [ ] **Close `d_consis_gen_extends_d_sub_nil` non-mono case** (1 admit at `typing/prop_subsumption_aux.v:~225` `__forall_l_untagged` branch). Mechanical given the subst lemma.

**Pattern B — SPLIT-helper provably-false deps (3 axioms):**
- [ ] **Add `d_consis_gen_syn_inh_erase_eq`** (gen variant of the Phase 1.F lemma — same proof structure, applied to `d_consis_gen` rules).
- [ ] **Solve the T2-mono blocker.** Two viable options:
  - **(a) Add `mono_typ Bhead` precondition** to all 4 SPLIT helpers (`d_typing_abs_value_to_subsumption_split[_d_sub]` and `_abs_anno_value_*`). D12 supplies via `d_sub_gen__refl_mono`-derived mono. Cascade D12 to compute mono at all 3 `m_new` branches (currently only computed at `m_new = mode_tc`; need new logic at `mode_ti` and `mode_fn _`).
  - **(b) Restructure `Hbody_at_tc` construction** in D12 to not require `d_sub_gen__refl_mono` on potentially-poly `B` — would require a non-`refl_mono` IH lift, likely via `d_sub__check` + body's d_consis. Deeper restructure.
  - Recommendation: try (a) first — more mechanical.
- [ ] **Refactor 4 SPLIT helpers** to use Phase 1.E's `syn_color_eq_inh_color_mono` (for T1 side; works via `Heq_LHS : syn_color T1 = inh_color_t Ahead → inh_color (erase Ahead)`) and Phase 1.F's `d_consis_syn_inh_erase_eq` (for T2 side; gives `T2 = A2'` ctyp equality replacing the broken `d_consis_lhs_syn_eq`). Mono of T2 comes from option (a) or (b) above.
- [ ] **Verify** all references to `d_consis_syn_inh_mono`, `d_consis_gen_syn_inh_mono`, `d_consis_lhs_syn_eq`, `d_consis_gen_lhs_syn_eq` in SPLIT helpers are gone, then those 4 lemmas can stay Admitted-but-unused (no longer appear in `Print Assumptions`).

### Verification gate

After Pattern A + Pattern B fixes:

- [ ] `Print Assumptions d_typing_general_subsumption_via_gen` → `Closed under the global context`.
- [ ] `Print Assumptions d_typing_general_subsumption_gen` → `Closed under the global context`.
- [ ] Update PROGRESS.md status banner: 🟢 GREEN + flagship theorems closed.
- [ ] Update the 4 provably-false lemma entries in Part 1 to reflect their now-unused status.

### Out of scope (separate effort)

The pre-refactor admits in `prop_typing.v` (E1, S1/S2), `typing/prop_weakening.v` (narrowing), and `subtyping/prop_sub_sound.v` (`d_sub_complete_mono`, `d_sub_no_guess_uniqueness`) remain research-grade — not affected by the δ cascade.

## Status legend

- 🟢 fully closed — Qed with paper-faithful statement (modulo trivial wf preconditions)
- 🟡 partial / narrowed — Qed but with substantive precondition strengthening
- 🟠 admitted — research-grade or paper-flagged; rationale documented inline
- ⚠️ paper-flagged — paper statement itself sketchy; counter-example noted
- 🔴 not mechanized — subsumed, deferred, or out of scope
- n/a — variant of another mechanized statement

**Rule:** A proof with `Admitted.` is NOT done. Track-level claims must be falsifiable by `grep -c "Admitted\." <file>` — non-zero means not 🟢.

---

# Part 1: Paper → Mechanization mapping

Click any `file:LINE` to jump to the formal definition.

## Score

Counts against paper-stated signatures only. A `d_wf_denv Γ` precondition that makes the paper's implicit wf-context assumption explicit is NOT counted as narrowing; substantive shape restrictions (e.g. `is_typ A`) ARE counted as narrowing.

- Paper-stated lemmas (excluding "n/a" duplicates): **23**
- 🟢 fully closed: **4** (D4, D5, A1, A2/A3)
- 🟡 partial / narrowed: **5** (D1/D12 statements compile but proofs are admitted in the split-syntax scaffold; D2 is narrowed; D9/D10 are native split-syntax statements but still admitted)
- 🟠 admitted (HEADLINE): **6** (D6, D7, A8, A9, A11, A12, A13)
- ⚠️ paper-flagged: **1** (D3)
- 🔴 not mechanized: **7** (D11, A4, A5, A6, A7, A10, A14)
- n/a: **3** (D8, D13, D14)

## Declarative metatheory (`paper/sections/declarative.tex`, `paper/sections/syntax-directed.tex`)

Mech statements use the notations from [`frost/decl/notations.v`](frost/decl/notations.v):
`Γ ⊢[ M ] e ⦂ A` for `d_typing`, `Γ ⊢[ M ] e ⇨ P` for `d_pat`, `Δ ⨟ Γ ⊢[ M ] T ⊑ A` for `d_sub`, `Δ ⨟ Γ ⊨ T ≈ A` for `d_consis`, `Γ ⊢ A ≤ B` for `d_shallow_sub`, `Ψ ⨟ Γ ⊢ₛₖ P` for `d_wf_skel`, `Ψ ⨟ Γ ⊢ᵣ P ▸ Q` for `d_refine`, `Ψ ⨟ Γ ⊢ᵣ P ⊳ Q` for `d_refine_syn`. The "gen" relations (`d_typing_gen`, `d_consis_gen`, `d_sub_gen`) and `d_wf_typ` have no dedicated notation — application form used.

Paper labels resolved to file:line in the auto-managed block at end of file (regenerate with `python3 scripts/sync_paper_refs.py --md`). Lemmas without a `\label{...}` in the paper source carry a plain `paper:LINE` ref + a `(no label)` marker.

| # | Paper lemma | Mech & paper statement | Status |
|---|---|---|---|
| D1 | [Lemma 3.1: General subsumption][lemma:general-subsumption] | **Mech:** `d_typing_general_subsumption_via_gen` [`prop_general_subsumption.v`](frost/decl/typing/prop_general_subsumption.v):<br>`d_wf_denv Γ → Γ ⊢[ mode_ti ] e ⦂ ptyp_to_btyp_syn A → nil ⨟ Γ ⊢[ m ] ptyp_to_utyp_syn A ⊑ B → Γ ⊢[ m ] e ⦂ B`<br>**Paper:** `If Γ ⊢_TI M ⇒ syn{A} and Γ ⊢_M syn{A} ≤ bid{B}, then Γ ⊢_M M ⇒ bid{B}` (LaTeX: `\typp[\TI]{\Gamma}{M}{\syn{A}}`, `\typsub[\M]{\Gamma}{\syn{A}}{\bid{B}}`, `\typp[\M]{\Gamma}{M}{\bid{B}}`) | 🟡 Faithful split-syntax statement shape; proof currently `Admitted`. The previous erased/repainted `ptyp_to_utyp_syn (btyp_to_ptyp B)` form has been removed. |
| D2 | Soundness of subtyping (paper [declarative.tex:1101](../paper/sections/declarative.tex#L1101), no `\label`) | **Mech:** `d_sub_sound` [`prop_sub_sound.v`](frost/decl/subtyping/prop_sub_sound.v):<br>`is_typ A → nil ⨟ Γ ⊢[ mode_tc ] A ⊑ B → Γ ⊢ A ≤ B`<br>**Paper:** for `mode_tc` subtyping, the conclusion is shallow-subtypeable. | 🟡 narrowed with `is_typ A` so LHS is `typ_all_col` flavour (matches `d_shallow_sub` shape) |
| D3 | No guessing of polytypes (paper [declarative.tex:1108](../paper/sections/declarative.tex#L1108), no `\label`) | **Mech:** `d_sub_no_guess_uniqueness` [`prop_sub_sound.v:215`](frost/decl/subtyping/prop_sub_sound.v#L215):<br>two instantiations `ph1`, `ph2` of same `d_sub` derivation imply `ph1 = ph2`<br>**Paper:** intuition that the polytype guessing `ph` in `d_sub__forall_l_tagged` is uniquely determined. | ⚠️ paper-flagged — counter-example inlined (`ph` can absorb into nested `forall_l_tagged` chains); paper revision suggested |
| D4 | Refinement preserves wf (paper [declarative.tex:1386](../paper/sections/declarative.tex#L1386), no `\label`) | **Mech:** `d_refine_preserves_wf` [`prop_wellformed.v:766`](frost/decl/prop_wellformed.v#L766):<br>`Ψ ⨟ Γ ⊢ₛₖ P → Ψ ⨟ Γ ⊢ᵣ P ▸ Q → Ψ ⨟ Γ ⊢ₛₖ Q` (coloured variant `d_refine_syn_preserves_wf` also Qed) | 🟢 |
| D5 | Preservation of skeleton wf (paper [declarative.tex:1976](../paper/sections/declarative.tex#L1976), no `\label`) | **Mech:** `d_pat_preserves_skel_wf` [`prop_skeleton.v:128`](frost/decl/prop_skeleton.v#L128):<br>`Γ ⊢[ mode_tc ] e ⇨ P → d_wf_denv Γ → nil ⨟ Γ ⊢ₛₖ P` | 🟢 narrowed via `d_pat_*_preserves_wf` with `is_syn_skel P` side hypothesis |
| D6 | Validity of skeleton inference (paper [declarative.tex:1987](../paper/sections/declarative.tex#L1987), no `\label`) | **Mech:** `d_pat_validity` [`prop_skeleton.v:154`](frost/decl/prop_skeleton.v#L154):<br>`Γ ⊢[ m ] e ⇨ P → d_wf_denv Γ → (∃ A, Γ ⊢[ m ] e ⦂ A) → ∃ B, Γ ⊢[ m ] e ⦂ B ∧ nil ⨟ Γ ⊢ᵣ P ▸ B` | 🟠 depends on refinement reflexivity (guarded skeletons) + anti-symmetry with `d_typing__sub` |
| D7 | Safety of skeleton inference (paper [declarative.tex:1992](../paper/sections/declarative.tex#L1992), no `\label`) | **Mech:** `d_pat_safety` [`prop_skeleton.v:180`](frost/decl/prop_skeleton.v#L180):<br>`(∃ A, Γ ⊢[ m ] e ⦂ A) → d_wf_denv Γ → ∃ P, Γ ⊢[ m ] e ⇨ P ∧ (∀ B, Γ ⊢[ m ] e ⦂ B → nil ⨟ Γ ⊢ᵣ P ▸ B)` | 🟠 universal "refines every type" — needs principal-skeleton construction (join under refinement) |
| D8 | General Subsumption (syntax-directed, paper [syntax-directed.tex:3](../paper/sections/syntax-directed.tex#L3), no `\label`) | (same as D1) | n/a — duplicate of D1; mech has one declarative system |
| D9 | [Lemma B.2: Consistency Transitivity][thm:consist-transitivity] | **Mech:** `d_consis_compose` [`prop_consis_trans.v`](frost/decl/subtyping/prop_consis_trans.v):<br>`Δa ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A → Δb ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B → list_disjoint Δa Δb → ∃ Δc, Permutation Δc (Δa ++ Δb) ∧ Δc ⨟ Γ ⊨ C ≈ B`<br>**Paper:** `If ⊨[Δ₁] Γ T ≈ T' and ⊨[Δ₂] Γ T' ≈ A, then ⊨[Δ₁,Δ₂] Γ T ≈ A` (LaTeX: `\typconsis[\Delta_1]{\Gamma}{\bid{T}}{\bid{T'}}`, `\typconsis[\Delta_2]{\Gamma}{\bid{T'}}{\bid{A}}`, `\typconsis[\Delta_1, \Delta_2]{\Gamma}{\bid{T}}{\bid{A}}`) | 🟡 Native split-syntax scaffold for synthesized middle `A : ptyp`; proof currently `Admitted`. It no longer erases/repaints an arbitrary `btyp`. |
| D10 | [Lemma B.3: Consistency-Subtyping Transitivity][thm:consist-subtyping-transitivity] | **Mech:** `d_consis_sub_trans` [`prop_consis_sub_trans.v`](frost/decl/subtyping/prop_consis_sub_trans.v):<br>`Δ ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A → Δ' ⨟ Γ ⊢[ M ] ptyp_to_utyp_syn A ⊑ B → list_disjoint Δ Δ' → ∃ Δc, Permutation Δc (Δ ++ Δ') ∧ Δc ⨟ Γ ⊢[ M ] C ⊑ B`<br>**Paper:** `If ⊨[Δ₁] Γ T ≈ T' and ⊢[M;Δ₂] Γ T' ⊑ A, then ⊢[M; Δ₁,Δ₂] Γ T ⊑ A`. | 🟡 Native split-syntax scaffold for synthesized middle type; proof currently `Admitted`. It no longer erases/repaints an arbitrary middle `btyp`. |
| D11 | [Lemma B.4: Subtyping Transitivity][thm:subtyping-transitivity] | **Mech support:** `d_sub_gen_trans` [`prop_subsumption_aux.v`](frost/decl/typing/prop_subsumption_aux.v):<br>`nil ⨟ Γ ⊢ᵍ[ m1 ] G1 ⊑ B2 → nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ] btyp_to_gutyp B2 ⊑ B3 → nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ] G1 ⊑ B3` | 🟠 proof currently `Admitted`; after fixing top-level generalized LHS shapes, the remaining work is generalized composition through `Arg` arrow components. |
| D12 | Generalised General Subsumption (paper Lemma B.5, [syntax-directed.tex:343](../paper/sections/syntax-directed.tex#L343), no `\label`) | **Mech:** `d_typing_general_subsumption_gen` [`prop_general_subsumption.v`](frost/decl/typing/prop_general_subsumption.v):<br>`d_typing_gen m_orig Γ e B1 → is_fn_n_ti m_orig → d_wf_denv Γ → d_sub_gen (mode_fn_n_subst m_orig m_new) nil Γ (btyp_to_gutyp B1) B2 → d_typing_gen (mode_fn_n_subst m_orig m_new) Γ e B2`<br>**Paper:** `If ⊢_FN[n] TI Γ M ⇒ bid{A}, ⊢_TY (FN[n] TI) bid{A}, and ⊢_FN[n] M Γ bid{A} ⊑ bid{B}, then ⊢_FN[n] M Γ M ⇒ bid{B}` (LaTeX: `\typp[\FN[n]~\TI]{\Gamma}{M}{\bid{A}}`, `\skmod[\TY]{{\FN[n]}~\TI}{\bid{A}}`, `\typsub[\FN[n]\M]{\Gamma}{\bid{A}}{\bid{B}}`, `\typp[\FN[n]\M]{\Gamma}{M}{\bid{B}}`) | 🟡 Close statement shape, proof currently `Admitted`. Missing explicit counterpart of `skmod[TY] (FN^n TI) bid{A}`; depends on `d_sub_gen_trans`. |
| D13 | [Lemma B.6: Soundness of Syntax-directed Rule][thm:typing-syn-soundness] | — | n/a — mech only has the bidirectional declarative system |
| D14 | [Lemma B.7: Completeness of Syntax-directed Rule][thm:typing-syn-completeness] | — | n/a |

## Algorithmic metatheory (`paper/sections/algorithmic.tex`, `paper/sections/proofs.tex`)

| # | Paper lemma | Mech & paper statement | Status |
|---|---|---|---|
| A1 | [Lemma D.2: Stability][lemma:stability] | **Mech:** `stability_d_typing` [`prop_soundness.v:620`](frost/algo/prop_soundness.v#L620) + 8 siblings:<br>`aenv_extends Θ0 Θ1 → a_transfers Θ0 Γ0 → a_transfers Θ1 Γ1 → Γ0 ⊢[ m ] e ⦂ A → Γ1 ⊢[ m ] e ⦂ A` (same shape for `_d_wf_typ`, `_d_consis`, `_d_sub`, `_d_pat_consis`, `_d_pat_sub`, `_d_refine`, `_d_refine_syn`, `_d_pat`)<br>**Paper:** "All statements in this paper are stable" — for every judgment `J` and `Θ₀ ≤ Θ₁`, `Θ₀ ⊢ J ⇒ Θ₁ ⊢ J`. | 🟢 9 of 9 |
| A2 | [Lemma D.3: Structural rules][lemma:structural] | **Mech:** `d_typing_suffix_moving_singleton` [`prop_typing.v`](frost/decl/prop_typing.v) + `d_pat_suffix_moving_singleton`:<br>`Γ1 ++ y~b ++ Γ2 ⊢[ m ] e ⦂ A → y ∉ dom Γ1 → Γ1 ++ Γ2 ++ y~b ⊢[ m ] e ⦂ A`<br>**Paper:** SuffixMoving rule — moving a binding past a suffix preserves typing. | 🟢 narrowed to single-binding move; full n-binding form needs free-vars-of-context machinery |
| A3 | [Lemma D.4: Splitting refines][lemma:split-refine] | **Mech:** `d_refine_arrow_split` [`prop_skeleton.v:25`](frost/decl/prop_skeleton.v#L25) + 7 siblings (`_all_plain_split`, `_hole_split`, `_tophole_split`, syn-painted variants):<br>`Ψ ⨟ Γ ⊢ᵣ typ_arrow P1 P2 ▸ Q → ∃ Q1 Q2, Q = typ_arrow Q1 Q2 ∧ Ψ ⨟ Γ ⊢ᵣ P1 ▸ Q1 ∧ Ψ ⨟ Γ ⊢ᵣ P2 ▸ Q2`<br>**Paper:** `If Θ₀ ⊢ split[P₀][P₁] ⇒ Θ₁, then Θ₁ ⊢ inh{P₀} fillsyn inh{P₁}` (LaTeX: `\mov{\Theta_0}{\split[P_0][P_1]{}}{\Theta_1}`, `\Theta_1\vdash\inh{P_0}\fillsyn\inh{P_1}`) | 🟢 8 of 8 |
| A4 | [Lemma D.5: Consistency extends subtyping][lemma:consis-sub] | — (NOT mechanized; distinct from D10/B.3) | 🔴 D.5 is stated over algorithmic `allsub` / `consistent`, distinct from D10/B.3 (declarative `d_consis` + `d_sub`). `d_consis_sub_trans` (D10) is NOT a mechanization of D.5; earlier docs conflated the two. Paper: `If Θ ⊢ consistent(P, P') and ⊢_{N,M} Θ P ⊑ Q, then ⊢_{N,M} Θ P' ⊑ Q`. |
| A5 | [Lemma D.6: Substitution preserves safety][lemma:safety-preservation] | — | 🔴 paper proof is "obvious — θ monotype only"; corollary of typ-subst preservation (itself admitted) |
| A6 | [Lemma D.7: Substitution preserves informativeness][lemma:informativeness-preservation] | — | 🔴 same |
| A7 | [Lemma D.8: More information does not harm][lemma:more-informative-skeletons] | — | 🔴 redundant with D1 (general subsumption) — not stated separately. Paper: `If ⊢[M] Θ M ⇒ bid{A} and bid{A'} ≼ bid{A}, then ⊢[M] Θ M ⇒ bid{A'}` (LaTeX: `\typp[\M]{\Theta}{M}{\bid{A}}`, `\bid{A'}\morepoly\bid{A}`). |
| A8 | [Theorem E.4: Soundness of type inference][thm:sound-type-inference] | **Mech:** `a_typing_sound` [`prop_soundness.v:748`](frost/algo/prop_soundness.v#L748):<br>`a_typing m Θ0 P0 e A Θ1 → a_transfers Θ0 Γ0 → a_transfers Θ1 Γ1 → Γ1 ⊢[ m ] e ⦂ A`<br>**Paper:** Given a type inference question `(Θ₀; M; P; M)`, if `⊢_{M;P} Θ₀ M ⇒ A ⇒ Θ₁`, then `(Θ₀ ≤ Θ₁; A)` is a solution. | 🟠 HEADLINE — depends on `a_consis_sound`, `a_unify_sound`, `a_assign_sound`, `a_pre_sub_sound`, `a_split_sound`, `a_guess_mono_sound` (not yet stated) |
| A9 | [Theorem E.5: Completeness and minimality of type inference][thm:complete-type-inference] | **Mech:** `a_typing_complete` [`prop_completeness.v:327`](frost/algo/prop_completeness.v#L327):<br>`Γ ⊢[ m ] e ⦂ A → ∀ Θ0 P0, a_transfers Θ0 Γ → a_wf_typ Θ0 P0 → ∃ Θ1, a_typing m Θ0 P0 e A Θ1 ∧ a_transfers Θ1 Γ`<br>**Paper:** dual to A8 — given a solution `(Θ₀ ≤[θ] Θ; B)`, the algorithm finds a minimal one. | 🟠 HEADLINE — dual to A8; same auxiliary family |
| A10 | [Lemma 4.13: Connection of informativeness][lemma:connection-informativeness] | — | 🔴 not attempted; depends on a precise `morepoly` definition. Paper: for `P` and `Q` safe skeletons of `M`, if `P ≼ Q` then every `inh{Q} fillsyn bid{B}` with `Θ ⊢_M M ⇒ bid{B}` lifts to an `inh{P} fillsyn bid{A}`. |
| A11 | [Theorem 4.15: Soundness of skeleton inference][thm:sound-skeleton-inference] | **Mech:** `a_pat_sound` [`prop_soundness.v:716`](frost/algo/prop_soundness.v#L716):<br>`a_pat m Θ0 P0 e P Θ1 → a_transfers Θ0 Γ0 → a_transfers Θ1 Γ1 → Γ1 ⊢[ m ] e ⇨ P` | 🟠 HEADLINE — mutual with A8 |
| A12 | [Theorem 4.16: Completeness of skeleton inference][thm:complete-skeleton-inference] | **Mech:** `a_pat_complete` [`prop_completeness.v:209`](frost/algo/prop_completeness.v#L209):<br>`Γ ⊢[ m ] e ⇨ P → ∀ Θ0 P0, a_transfers Θ0 Γ → a_wf_typ Θ0 P0 → ∃ Θ1 Q, a_pat m Θ0 P0 e Q Θ1 ∧ a_transfers Θ1 Γ` | 🟠 HEADLINE — mutual with A9 |
| A13 | [Theorem 4.19: Soundness/Completeness/Minimality of subtyping][thm:sound-subtyping] | **Mech:** `a_sub_sound` [`prop_soundness.v:661`](frost/algo/prop_soundness.v#L661) + `a_sub_complete` [`prop_completeness.v:135`](frost/algo/prop_completeness.v#L135) | 🟠 HEADLINE — five auxiliary completeness/soundness lemmas blocked. `a_sub_decidable_existential` is Qed in vacuous-disjunct form (documents the obligation without fabricating a proof). |
| A14 | [Lemma 4.21: Soundness and completeness and minimality of unification][thm:sound-unification] | — | 🔴 `a_unify` defined in `algo/def_extra.v`; no standalone soundness lemma stated (consumed via A13 / A8 chains) |

## Mechanization-only support lemmas

These don't appear as separate paper lemmas but are load-bearing for the mech. Listed so a reviewer can see what infrastructure the paper proofs depend on. Statements use the same Coq notations as the Declarative table above (`Γ ⊢[ M ] e ⦂ A`, `Δ ⨟ Γ ⊨ T ≈ A`, etc.).

| Mech lemma | Status | File:line | Purpose |
|---|---|---|---|
| `d_typing_embed_gen` | 🟢 | [`def_gen.v`](frost/decl/typing/def_gen.v) | `d_typing → d_typing_gen` embedding (structural induction) |
| `d_typing_gen_collapse` | 🟠 | [`def_gen.v`](frost/decl/typing/def_gen.v) | `d_typing_gen → d_typing`; current statement remains admitted and cannot rely on the false "all gen-sub LHS embed into utyp" bridge |
| `d_sub_gen_top_inherited_lhs_impossible` | 🟢 | [`def_gen.v`](frost/decl/typing/def_gen.v) | checks the repaired generalized subtyping rules: inherited forall cannot be a top-level LHS; the earlier counterexample was a translation bug in the scaffold |
| `d_sub_gen_weakening` / `_head` | 🟢 | [`prop_subsumption_aux.v`](frost/decl/typing/prop_subsumption_aux.v) | weakening for the generalized subtyping scaffold |
| `d_consis_gen_weakening` / `_head` | 🟢 | [`prop_subsumption_aux.v`](frost/decl/typing/prop_subsumption_aux.v) | weakening for generalized consistency |
| `d_sub_gen_trans` | 🟠 | [`prop_subsumption_aux.v`](frost/decl/typing/prop_subsumption_aux.v) | generalized transitivity; still admitted, now blocked on generalized consistency/subtyping composition for `Arg` |
| `d_typing_pat_weakening` / `_ctx_morph` | 🟢 | [`prop_weakening.v`](frost/decl/typing/prop_weakening.v) | full 18-case weakening + context morphism (mutual) |
| `d_typing_pat_preserves_wf` | 🟢 | [`prop_wellformed.v`](frost/decl/prop_wellformed.v) | full 18-case wf preservation (mutual) |
| `d_typing_sub_compose` | 🟢 | [`prop_subtyping.v`](frost/decl/prop_subtyping.v) | helper for D1's `__sub` case; proof closes using D10's nil corollary |
| `d_typing_pat_subst_typ_mut` | 🟠 | [`prop_weakening.v:644`](frost/decl/typing/prop_weakening.v#L644) | mutual type subst; blocked on `d_sub_subst` / `d_refine_syn_subst` / `d_pat_*_subst` (not yet stated) |
| `d_typing_narrowing` | 🟠 | [`prop_weakening.v:668`](frost/decl/typing/prop_weakening.v#L668) | reduces to D1; gated on `d_typing_general_subsumption` non-base cases |
| `d_typing_narrow_consis` / `_gen_narrow_consis` | 🟠 | [`prop_weakening.v:713`](frost/decl/typing/prop_weakening.v#L713), [`def_gen.v:1083`](frost/decl/typing/def_gen.v#L1083) | post-ctyp re-encoding: `__var` returns raw bound type; old `syn_color_t`-equality insufficient |
| `d_typing_swap_mono` / `_app_restructure` / `_order_irrel_adj` | 🟠 | [`prop_typing.v:77,107,153`](frost/decl/prop_typing.v) | Stability S1/S2 + order-irrelevance; need `d_typing`-inversion through `d_pat` (research-grade) |
| `E1_intro` / `E1_elim` / `E1_roundtrip` | 🟠 | [`prop_typing.v:218,237,247`](frost/decl/prop_typing.v) | Expressiveness benchmark (Church-encoded existentials); gated on `d_typing_pat_subst_typ_mut` |
| `d_sub_complete_mono` | 🟠 | [`prop_sub_sound.v:173`](frost/decl/subtyping/prop_sub_sound.v#L173) | reviewer-suggested completeness vs monotype-only shallow subtyping; forall_r/forall_l colour-flavour mismatch |
| ~~`d_consis_lhs_is_inh_for_typ` / `d_consis_gen_LHS_syn_color_mono` / `d_consis_LHS_is_utyp_when_RHS_syn_color` / `d_sub_not_lhs_typ_all_col`~~ | — | (deleted 2026-05-17) | All four were post-refactor FALSE under the new `__forall_syn` rule. Removed along with their dead caller chain (the two `d_typing_abs[_anno]_value_to_subsumption` umbrellas + the two `_d_sub` helpers + `is_inh_typ_syn_color_mono`) — none of those had callers outside `prop_subsumption_aux.v`. |

## Per-file admit summary

`frost/decl/` admit counts in this table are historical outside the
currently touched split-syntax files.  The current D1/D12 path now
centres on `def_gen.v`, `prop_subsumption_aux.v`,
`prop_general_subsumption.v`, and the two consistency-transitivity
files:

| File | Count | Admitted lemmas |
|---|---|---|
| `prop_typing.v` | 6 | `d_typing_swap_mono`, `d_typing_app_restructure`, `d_typing_order_irrel_adj`, `E1_intro`, `E1_elim`, `E1_roundtrip` |
| `typing/prop_weakening.v` | 3 | `d_typing_pat_subst_typ_mut`, `d_typing_narrowing` (D1 done; blocked on `d_sub_complete`), `d_typing_narrow_consis` |
| `typing/def_gen.v` | 1 | `d_typing_gen_collapse` |
| `typing/prop_subsumption_aux.v` | 1 | `d_sub_gen_trans` |
| `typing/prop_general_subsumption.v` | 2 | `d_typing_general_subsumption_gen`, `d_typing_general_subsumption` |
| `subtyping/prop_consis_trans.v` | 1 | `d_consis_compose` |
| `subtyping/prop_consis_sub_trans.v` | 1 | `d_consis_sub_trans` |
| `prop_subtyping.v` | 1 | `d_typing_sub_compose` |
| `subtyping/prop_sub_sound.v` | 2 | `d_sub_complete_mono`, `d_sub_no_guess_uniqueness` (paper-flagged) |
| `prop_skeleton.v` | 2 | `d_pat_validity`, `d_pat_safety` |

`frost/algo/` (6 admits — all Phase 3.B/C HEADLINEs):

| File | Count | Admitted lemmas |
|---|---|---|
| `prop_soundness.v` | 3 | `a_sub_sound`, `a_pat_sound`, `a_typing_sound` |
| `prop_completeness.v` | 3 | `a_sub_complete`, `a_pat_complete`, `a_typing_complete` |

---

# Part 2: Daily progress

Session-by-session closure log. Most recent first.

## 2026-05-17 — δ-cascade Phase 1.H (rule added + foundation lemmas + scope of remaining work)

**What this session did.**

1. **Added paper-missing rule `d_consis_gen__forall_syn_tagged_both`** to
   `d_consis_gen` (matches paper's `ForallTagSyn` at δ=ε case from
   syntax-directed.tex, which the δ-refactor had omitted). The rule
   gives `typ_all_etag ε T ≈ typ_all_etag ε A` with Δ unchanged.

2. **Updated all case-analysis sites** (~10 lemmas) to handle the new
   constructor case via inversion / vacuous discharge / structural recursion.

3. **Added 2 helper conversion lemmas:**
   - `is_typ_syn_color_imp_inh_color`: is_typ is invariant under syn ↔ inh re-paint.
   - `is_typ_inh_color_imp_syn_color`: dual.

4. **Added `d_consis_gen_refl_wf_ttyp`** (refl on tagged ph via new rule).
   KEY INSIGHT: output Δ = nil even for tagged ph because the new rule
   keeps Δ unchanged through tagged-∀ peeling. This breaks the apparent
   counting/linearity issue at variable-substitution positions.

5. **Proved `d_consis_gen_subst_typ_with_ttyp`** (substitution lemma).
   Substitutes tagged ph for X in d_consis_gen with output Δ unchanged
   (no `Δ ++ N × Δ_φ` multiplication). The lemma is the foundation for
   closing Pattern A.

6. **Stated `d_consis_gen_sub_trans`** (B.3 gen) as Admitted skeleton +
   `_nil` corollary.

7. **Updated `d_consis_gen_preserves_wf`** with `is_typ B` precondition;
   cascade through `d_sub_gen_preserves_wf` (with `is_typ A` precondition);
   added `d_sub_gen_preserves_is_typ` as research-grade Admitted helper.

8. **Documented `d_consis_gen_to_d_consis`** as research-grade Admitted for
   the new rule case (no d_consis counterpart per declarative.tex).

**Current axiom count: 10**
- 8 pre-existing (Pattern A × 3, Pattern B × 3, misc × 2).
- 2 new admits introduced (`d_sub_gen_preserves_is_typ`, `d_consis_gen_to_d_consis`).

**Net 0 closure this session** — all the foundation work is in place,
but the actual close of Pattern A admits requires more work, scoped below.

### Remaining work to close D1/D12

The dependency tree is deeper than initially visible:

1. **Prove `d_consis_compose`** (paper B.2, currently wholesale admitted).
   Needs cofinite-rename arguments for 3 new compositional sub-cases
   introduced by `__forall_inh_untagged` (per the existing TODO note in
   `prop_consis_trans.v:87-94`). Multi-day work.

2. **Prove `d_consis_gen_compose`** (B.2 gen variant). Mirror of (1) over
   d_consis_gen, plus new rule case. Provable but ~200 lines.

3. **Prove `d_consis_gen_sub_trans`** (B.3 gen, body). Uses (2) for the
   __arg case and the new substitution lemma for __forall_l_*. ~150 lines.

4. **Close Pattern A admits via gen B.3 + embed:**
   - `d_consis_sub_trans` non-mono — replace use with gen version.
   - `d_sub_gen_trans_forall_l_untagged_helper` non-mono — similar.
   - `d_consis_gen_extends_d_sub_nil` non-mono — similar.

5. **Inline D12 m_new=mode_tc** to remove SPLIT helper dependence
   (Pattern B). Replace SPLIT helper calls with structural inversion of
   Hsub_gen + structural peeling for poly-body lift using new rule.
   Pattern B's broken lemmas become orphaned.

6. **Verify** Print Assumptions on D1/D12 reports "Closed under the
   global context".

**Estimated effort:** 1-2 full sessions of focused work on (2)-(4) alone,
assuming (1) is tackled in parallel. (5) is a separate ~1-day refactor.
Total: 3-5 sessions to full closure.

**Build is 🟢 green this session.** All edits compile; the foundation
work is committed in the codebase.

## 2026-05-17 — δ-cascade Phase 1.G (paper-audit: missing rule + cascade scope)

**What this session did.**

1. **Audited paper vs mech rule-faithfulness for d_consis_gen.** Found
   that the mechanization is missing **one rule from syntax-directed.tex's
   d_consis_gen figure**: the `δ=ε` case of `ForallTagSyn`
   ([syntax-directed.tex:99-105](../paper/sections/syntax-directed.tex#L99))
   which relates `typ_all_etag ε T ≈ typ_all_etag ε T'` (tagged on both
   sides, same ε, Δ unchanged). The δ-refactor entry (2026-05-17) added
   `__forall_inh_untagged` (the δ=· case of `ForallTagInh`) but missed
   the δ=ε case of `ForallTagSyn` — they should have been added together.

2. **Verified scope of the gap.** d_consis (declarative.tex Fig 6) does
   NOT have this rule per paper — its `ForallSyn` rule has RHS
   `syn{∀α. A}` (UNTAGGED, no δ subscript). d_pat_consis similarly. So
   the missing rule is exclusively in d_consis_gen.

3. **Corrected axiom count.** `Print Assumptions` reports **8 axioms**
   (not 6 — banner was stale). `d_sub_mono_RHS_eq` and
   `d_consis_LHS_mono_wf` are back in the chain via
   `d_sub_gen_trans_forall_l_untagged_helper`'s residual admit.

### Why the missing rule matters

Without `d_consis_gen__forall_syn_tagged_both` (the missing δ=ε case of
ForallTagSyn), there's **no way to derive `d_consis_gen Δ Γ φ φ` for
tagged φ** — d_consis_gen has tagged LHS rules (`__forall_inh_tagged`,
`__forall_syn_tagged`) that pair tagged-LHS with COLOUR-painted-RHS, but
no tagged-RHS rule. This makes the substitution lemma
`d_consis_gen_subst_typ_with_ttyp` (the gen analogue of what Pattern A
needs) impossible to prove at variable positions when ph is tagged.

With the missing rule added: at a `__var X` position, substituting `X ↦ φ`
yields `d_consis_gen Δ_φ Γ φ φ` derivable by peeling matching tagged ∀'s
on both sides via the new rule, bottoming out at unit/var/arrow. Output Δ
is `Δ_φ` (not N copies), so **no linearity violation** — the "counting"
worry was a red herring; with the right rule the derivation builds the
correct Δ structurally.

### Cascade scope (assessed, not yet implemented)

Adding the rule to d_consis_gen breaks **`d_consis_gen_preserves_wf`**
(and transitively `d_sub_gen_preserves_wf`, `d_typing_gen_preserves_wf`),
because its conclusion `d_wf_typ Γ B` cannot hold when B is
`typ_all_etag ε A` (d_wf_typ has no constructor for typ_all_etag — only
typ_all_col). Cascade scope:

1. **Define `d_wf_btyp`** — a unified wf-predicate covering both
   colour-painted (`typ_all_col`) AND tagged (`typ_all_etag`, with
   linearity tracking) shapes. Matches the paper's `bid{T}` grammar
   ([syntax-directed.tex:14-19](../paper/sections/syntax-directed.tex#L14)):
   `bid{T} ::= unit | α | bid{T1}→bid{T2} | syn{∀^ε α.}bid{T} |
   syn{∀α.}bid{T} | inh{∀α.}bid{T}`.

2. **Reformulate `d_consis_gen_preserves_wf`** to conclude
   `d_wf_btyp Γ B` (with appropriate Δ tracking).

3. **Reformulate `d_sub_gen_preserves_wf` / `d_typing_gen_preserves_wf`**
   similarly. d_sub_gen's `__arg` produces arrows with bid-shape
   components, so its preservation also needs `d_wf_btyp`.

4. **Update all consumers** of these preservation lemmas — every site
   that currently expects `d_wf_typ` from a gen-relation needs either
   `d_wf_btyp` or an explicit narrowing to `d_wf_typ` (which is the
   restriction "no tagged components").

5. **Reformulate `d_consis_sub_trans` (paper B.3)** over `d_consis_gen`
   instead of d_consis. The mechanization currently states B.3 on non-gen
   d_consis, but the paper's B.3 is in syntax-directed.tex which is about
   the generalised relation. The reformulation makes the new tagged-tagged
   rule available for the substitution lemma's var case.

6. **Close the 3 Pattern A admits** (`d_consis_sub_trans` non-mono case,
   `d_sub_gen_trans_forall_l_untagged_helper` non-mono case,
   `d_consis_gen_extends_d_sub_nil` non-mono case) using the new
   substitution lemma.

Pattern B (the SPLIT helpers' `d_consis_syn_inh_mono` etc.) is a
SEPARATE issue from the missing rule — it's about lifting body from
mode_ti to mode_tc when the body type is poly, which doesn't directly
benefit from the new rule. Pattern B needs its own design pass.

### Status this session

**Reverted in-progress edits** to def_gen.v after discovering the cascade
scope mid-implementation. Build remains 🟢 green. The audit finding +
cascade plan are documented above. **No axiom drop this session.**

The PROPER fix (steps 1-6 above) is a multi-day effort and warrants its
own design spec before implementation. Recommend starting with step 1
(define `d_wf_btyp`) and propagating in a controlled sequence.

## 2026-05-17 — δ-cascade Phase 1.F (erase-eq lemma; user-suggested option (b) clarified)

**Commit:** `a461bb9`.

**What this session did.** User suggested option (b): "Add a stronger
d_consis-inversion lemma proving `d_consis ... (syn_color T2) (inh_color
A2') → syn_color T2 = inh_color A2'` under wf conditions."

**Finding.** The literal form is **provably FALSE post-δ** — the new
`d_consis__forall_inh_untagged` rule allows
`d_consis Δ Γ (typ_all_col colour_syn T') (typ_all_col colour_inh A')`,
i.e. `syn_color (ctyp_all T'_ctyp)` on LHS and `inh_color (ctyp_all A'_ctyp)`
on RHS. These differ in colour (`colour_syn` vs `colour_inh`) — the typ
equality fails.

**Closest viable form (Qed):** the **erase weakening**, added to
`prop_consis_trans.v`:

```coq
Lemma d_consis_syn_inh_erase_eq : forall Γ Δ T A,
    Δ ⨟ Γ ⊨ T ≈ A ->
    is_syn_typ T ->
    is_inh_typ A ->
    erase T = erase A.
```

Provable because [erase] discards colour information — for the
`__forall_inh_untagged` case, both `erase (typ_all_col colour_syn _)`
and `erase (typ_all_col colour_inh _)` give `ctyp_all (erase body)`.
The cofinite IH on the body + `open_ctyp_wrt_ctyp_inj` + `erase_ftvar`
closes that case. Other cases close via shape exclusion
(`is_syn_typ` excludes `typ_all_etag`; `is_inh_typ` excludes
`colour_syn`).

**At call sites,** applying gives `erase (syn_color T2) = erase
(inh_color A2') ⟹ T2 = A2'` (ctyp equality, via `erase_syn_color` /
`erase_inh_color` round-trips). Suitable for `subst`.

**Why this doesn't yet drop axioms.** Wiring into SPLIT helpers
requires also solving the T2-mono blocker: even with `T2 = A2'`,
deriving `mono_typ (syn_color T2)` needs either:

- Adding `mono_typ Bhead` to the SPLIT helper signature (cascades to
  D12, requires D12 to establish mono of body type at all m_new
  branches; D12 has `HwfB` at `m_new = mode_tc` but not at others).
- A different construction of `Hbody_at_tc` that doesn't require
  `d_sub_gen__refl_mono` on potentially-poly `B` (would change D12's
  internal IH usage).

Both options are substantive cascading restructures — planned for next
session.

**Axiom count: still 6** (no drop this session; foundation lemma added
for follow-up).

## 2026-05-17 — δ-cascade Phase 1.D + 1.E (partial close + foundation)

**Commits:** `25d99cb` (Phase 1.D), `0e5010c` (Phase 1.E).

**Phase 1.D** — closed the mono-ph half of `d_consis_sub_trans`'s
`__forall_l_untagged` admit:

- Moved 3 helpers to `prop_wellformed.v` (shared use across subtyping/
  and typing/): `d_wf_ttyp_nil_d_wf_typ`, `d_wf_ttyp_nil_mono_typ`,
  `d_wf_typ_open_with_ttyp_nil`.
- In `prop_consis_sub_trans.v`'s `__forall_l_untagged` case: inversion
  of Hc gives `__forall_syn_tagged` (vacuous via HwfT) and `__forall_syn`
  (productive). For Δ' = nil (ph mono), uses `d_consis_subst_mono` on
  Hc's cofinite body, composes with IH on inner d_sub, re-applies
  `d_sub__forall_l_untagged` with Δ' := nil. Non-mono ph case still
  admitted (needs d_consis substitution over `d_wf_ttyp`).

**Phase 1.E** — added foundation for SPLIT-helper refactor:

- New lemma `syn_color_eq_inh_color_mono` (in `prop_basic.v`): the
  ctyp-domain analog of `inh_color_t_eq_syn_color_mono`. Given
  `syn_color T = inh_color A` + `d_wf_typ Γ (syn_color T)`, derives
  `mono_typ (syn_color T)`. Closes via structural disagreement between
  syn_color (colour_syn) and inh_color (colour_inh) on `ctyp_all`.
- Not yet wired into SPLIT helpers. Wiring requires threading several
  structural equations through 4 SPLIT-helper proofs (the chain:
  `Heq_LHS : syn_color T1 = inh_color_t Ahead` + `HA1_eq : inh_color A1'
  = inh_color_t Ahead` → `syn_color T1 = inh_color A1'`). Planned
  follow-up Phase 1.F.

**Axiom count:** still 6 — d_consis_sub_trans appears in
Print Assumptions because the non-mono ph sub-case still leaks, and
the 3 SPLIT-helper-dependent provably-false admits still need wiring.

## 2026-05-17 — δ-cascade Phase 1A/1B/1C (4 axioms closed, 10 → 6)

**Commits:** `530796c` (Phase 1A), `cccfca0` (Phase 1B), `1829862` (Phase 1C).

**Phase 1A** — partial close of `d_sub_gen_trans`'s `__forall_l_untagged`
inner case:

- Moved bridge lemmas (`d_consis_gen_to_d_consis_syn_lhs`,
  `d_consis_gen_to_d_consis`, `d_sub_gen_to_d_sub`) from
  `prop_general_subsumption.v` into `def_gen.v` so they're available to
  `prop_subsumption_aux.v`. All three were already Qed; move was clean.
- Added helper `d_sub_gen_trans_forall_l_untagged_helper` in
  `prop_subsumption_aux.v` that handles the new
  `d_sub__forall_l_untagged` case in `d_sub_gen_trans`'s `mode_fn m`
  branch. Paper-faithful: inducts on the inner d_sub (matching
  syntax-directed.tex:323-338's ForallL induction in Subtyping
  Transitivity).
- Helper handles the ph-mono sub-case (rule's `Δ' = nil`); admits the
  non-mono sub-case (Δ' ≠ nil) — that requires generalising trans to
  non-nil outer Δ.
- `d_sub_gen_trans` itself now Qed; uses the helper for the previously
  fully-admitted case.

**Phase 1B** — closed two wholesale-admitted lemmas:

- `d_consis_gen_trans` (paper B.2 / Lemma D9 at nil Δ): added `is_typ T`
  precondition that rules out the unreachable
  `__forall_syn_tagged × __forall_inh_untagged` composition (whose result
  shape `typ_all_etag → typ_all_col colour_inh` has no d_consis_gen
  producer at nil Δ — the only producer is `__forall_inh_tagged` at
  `(ε :: Δ_body)`). All call sites supply is_typ via
  `d_wf_typ_is_typ` from their d_wf_typ premises.
- `d_consis_extends_d_consis_gen`: parallel restoration. Added the
  `__forall_inh_untagged` case (inverts d_consis_gen's RHS-syn
  matching). Threads is_typ through to its `d_consis_gen_trans` calls.

Side-effect: `d_sub_mono_RHS_eq` and `d_consis_LHS_mono_wf` dropped from
the `Print Assumptions` list — they were transitively reachable only
via `d_sub_gen_trans`'s previously-admitted chain.

**Phase 1C** — documentation refinement on
`d_consis_gen_extends_d_sub_nil`'s residual `__forall_l_untagged` admit
clarifying the two sub-blockers (substitution lemma + non-nil trans).

**Axiom count:** 10 (after Phase 0) → 6 (after Phase 1C).

**Remaining 6 axioms** split into two structural patterns — see [Status
banner above](#status-current--2026-05-17-after-δ-cascade-phases-0--1a--1b--1c)
for the breakdown and the strategic options for finishing the closure.

## 2026-05-17 — δ-cascade Phase 0 (build green, 4 leaking axioms documented)

**Plan:** [`docs/superpowers/plans/2026-05-17-delta-encoding-admit-cleanup.md`](docs/superpowers/plans/2026-05-17-delta-encoding-admit-cleanup.md)

**What this session did.** Restored the green build that was halted at
`prop_subsumption_aux.v:395` since commit `0bf2815` (the WIP δ-refactor).
Added missing sub-case bullets / disjunctive-pattern branches for the
new constructors across the case-splitting proofs they broke:

- `prop_subsumption_aux.v`:
  - `d_sub_gen_trans` (mode_fn m / __embed): added `*` bullet for
    `d_sub__forall_l_untagged`. Inner case at `mode_fn m` requires
    actual proof (paper inducts on first d_sub, mechanization inducts
    on `is_fn_n_ti m1` — IH not aligned). Lemma now `Admitted.`
  - `d_consis_syn_inh_mono` + `d_consis_gen_syn_inh_mono`: added bullets
    for `d_consis__forall_inh_untagged`. **Conclusion `mono_typ (syn_color T)`
    is FALSE on `ctyp_all T` input** — the OLD invariant ("syn-LHS ↔ inh-RHS
    d_consis ⇒ LHS mono") no longer holds. Both lemmas now `Admitted.`
  - `d_typing_abs_value_to_subsumption_split_d_sub` +
    `d_typing_abs_anno_value_to_subsumption_split_d_sub`: added missing
    `d_sub__forall_l_untagged` case (vacuous via outer-shape mismatch).
- `prop_general_subsumption.v`:
  - `d_consis_gen_to_d_consis_syn_lhs` + `d_consis_gen_to_d_consis`:
    added new constructor case (mirrors `d_consis__forall_inh_untagged`).
- `prop_typing.v`:
  - `d_typing_app_reorder`: extended inversion patterns by one branch
    (`d_sub` now has 6 constructors).

**Findings about what's required to close D1 / D12 again.** The 4 leaking
axioms (above) and the 12 other δ-NEW admits share a coupled dependency
on the three broken invariants (4: "syn-LHS↔inh-RHS d_consis ⇒ mono",
5: "d_consis empty Δ ⇒ LHS=RHS", 6: "d_sub mode_fn _ wf LHS ⇒ arrow shape").
Each shortcut lemma's call sites use its conclusion as a load-bearing
equation in downstream proof steps; refactoring individual call sites
doesn't compose. Closing D1 / D12 again requires either:
- (a) Restructuring the SPLIT helpers + `d_sub_gen_trans` to be
  polymorphic-body-aware without leaning on the broken shortcuts
  (paper's proof structure: induct on first d_sub, IH on body), OR
- (b) Adding precondition restrictions at the entry points (e.g. force
  mono binding types at D12's `__abs` call site), cascading upward.

Neither is a single-session change. Phase 0 leaves the codebase in a
clean intermediate state with full documentation.

**Plan updates.** The phase-1+ tasks in
[`docs/superpowers/plans/2026-05-17-delta-encoding-admit-cleanup.md`](docs/superpowers/plans/2026-05-17-delta-encoding-admit-cleanup.md)
have been revised with the feasibility analysis from this session.

## 2026-05-17 — δ-encoding refactor (WIP, commit `0bf2815`)

**Spec:** [`docs/superpowers/specs/2026-05-17-delta-encoding-refactor-design.md`](../docs/superpowers/specs/2026-05-17-delta-encoding-refactor-design.md)

**Motivation.** The paper's `\sublab{ForallL}` rule (declarative.tex:923–930) and four
analogues (declarative.tex:946, 954, 1814, 1837, 1845) allow the potential tag
`δ ∈ {·, ε}`. The post-`typ_all_plain` refactor (2026-05-15) dropped the
`δ = ·` cases with a note "not paper-faithful" — they ARE paper-faithful.
The gap surfaced when trying to generalise `d_typing_order_irrel_adj` to
the n-quantifier version: with `typ_all_col` bindings, `d_sub` at `mode_fn _`
has no instantiation rule, so the typing antecedent is vacuous.

**What changed.**
- **5 new rule constructors** (mechanization/frost/decl/def_extra.v):
  - `d_sub__forall_l_untagged` (LHS `typ_all_col colour_syn`)
  - `d_consis__forall_inh_untagged`
  - `d_pat_sub__forall_l_untagged`
  - `d_pat_consis__forall_inh_untagged`
  - `d_pat_consis__forall_syn_untagged`
- **2 predicate-grammar gaps fixed** (frost/def_extra.v): `is_utyp__pall`
  and `is_uskel__pall` add the `typ_all_col colour_syn` case (paper's
  utyp grammar `T ::= unit | α | T → T | syn{∀^δα.T}` covers both
  `δ = ε ↦ typ_all_etag` and `δ = · ↦ typ_all_col colour_syn`).
- **Rules grouped by paper rule** (tagged + untagged adjacent), not
  appended-last. Easier manual audit per user preference.
- **Notations inlined** via `Reserved Notation` + `where` clauses on 7
  judgments (`d_wf_skel`, `d_wf_ttyp`, `d_wf_tskel`, `d_consis`, `d_sub`,
  `d_pat_consis`, `d_pat_sub`), so rule bodies are paper-faithful in
  one glance. `decl/notations.v` pared down accordingly.

**Cascade.** 13 files modified, +986/−261 lines. ~15 lemmas patched
with new case bullets (mechanical); **16 new `Admitted`s** introduced
in 12 lemmas. Of those:
- **6 admits flag PROVABLY-FALSE lemmas** (conclusion no longer holds
  because the new rule's LHS-colour permissiveness breaks the lemma's
  shape-discrimination):
  - `d_consis_LHS_mono_wf`, `d_consis_LHS_is_typ_mono`
  - `d_sub_LHS_mono_wf`, `d_sub_mono_RHS_eq`
  - `d_consis_empty_eq`
  - `d_consis_gen_lhs_syn_eq`

  These need **precondition strengthening** (e.g. exclude `is_utyp__pall`,
  add `is_typ A` on conclusion side), not just proof completion.
- **3 wholesale admits** with original body preserved as `(* ... *)`
  for re-introduction once the cascade is restructured:
  `d_consis_compose`, `d_consis_gen_trans`,
  `d_consis_extends_d_consis_gen`.
- Remaining 7 are sub-case admits with spec links.

**Build state.** RED — stops at `prop_subsumption_aux.v:395` (one
mechanical `*` bullet away from advancing to the next failure). Remaining
patching scope: estimated 20–50 more bullet additions across
`prop_general_subsumption.v`, `prop_typing.v`, and possibly Phase 3
algo files.

**Flagship-theorem risk.** D1 / D12 (`d_typing_general_subsumption_via_gen`
and `_gen`) almost certainly no longer "Closed under the global
context": both rely transitively on `d_consis_gen_trans` (WHOLESALE
admit). `Print Assumptions` re-check is gated on the build coming back
green.

**Audit.** Independent verifier-agent pass (post-commit) confirmed
rule correctness vs paper, found 5 of the 6 provably-false admits not
enumerated in the original spec, and flagged the D1/D12 closure risk.

**Next steps.** (1) Finish mechanical bullet patching to get build
green. (2) Re-verify `Print Assumptions` on flagship theorems. (3)
For each provably-false lemma, decide between strengthening the
precondition vs restating. (4) Then resume n-arg permutation lemma
work (the original motivation).

## 2026-05-17 — D1 / D12 axiom elimination + B.3 rename

**Commit:** `64545d1` — "mech: eliminate both D1/D12 transitive axioms (2 → 0)"

`Print Assumptions d_typing_general_subsumption_via_gen` now reports **"Closed under the global context"**.

- **Axiom 1 closed** (`d_consis_sub_trans`, paper Lemma B.3): added `d_wf_typ Γ T` premise + new helper `d_consis_RHS_syn_color_eq` (mirror of `d_consis_gen_RHS_syn_color_eq`). Rules out the unsound `typ_all_etag` LHS that the post-refactor `d_consis__forall_syn` rule otherwise admits. Caller `d_typing_sub_compose` discharges the premise via `d_typing_pat_preserves_wf`.
- **Axiom 2 closed** (`d_typing_gen_lift_mono __app`): broken via `Hbody_at_tc` parameter on the 6 TC SPLIT helpers in `prop_subsumption_aux.v`. Internal `lift_mono` calls replaced by `apply Hbody_at_tc`. D12 constructs `Hbody_at_tc` from its own `IHbody` (`H1`) at `m_new := mode_tc` with `d_sub_gen__refl_mono` on the mono body type. The 2 direct `lift_mono` calls in `prop_general_subsumption.v` also replaced by `IHbody` at `m_inner`. `d_typing_gen_lift_mono` itself remains Admitted but is no longer transitively reachable from D12.
- **Renamed** `d_consis_extends_d_sub` → `d_consis_sub_trans` (and `_nil` / `_gen_nil` variants) to match paper B.3 title "Consistency-Subtyping Transitivity". Earlier docs conflated paper D.5 (proofs.tex, `lemma:consis-sub`, algorithmic) with paper B.3 (syntax-directed.tex, `thm:consist-subtyping-transitivity`, declarative); A4 entry now correctly marks D.5 as not mechanized.

## 2026-05-17 — File split + doc audit (commits e47fa82, b576d58, 01c5545)

- Split `prop_typing.v` → `prop_typing/{weakening,gen,abs_subsumption,mono_subsumption,d12}.v` and `prop_subtyping.v` → `prop_subtyping/{basics,consis_compose,consis_extends,sub_sound}.v` for faster iteration.
- Moved axiom audit from `README.v` into `PROGRESS.md`.
- Closed `d_consis_LHS_is_utyp_when_RHS_syn_color` callsites by rewriting through `d_consis_gen_RHS_syn_color_eq` (3 → 2 transitive axioms).

## 2026-05-16 — Bridge extraction + helper closure

Multi-commit push closing the D12 body case-by-case:

| Commit | Axioms before → after | What closed |
|---|---|---|
| `7676aa0` | 5 → 3 | `d_consis_compose_nil_RHS` + helper |
| `4be042e` | 6 → 5 | `d_consis_extends_d_consis_gen`, `d_consis_gen_RHS_syn_color_eq`; `d_consis_LHS_syn_color_mono` restated with mono premise |
| `4008695` | 8 → 6 | `_ti` SPLIT helper variants closed |
| `8b46742` | — | **D12 fully Qed in its proof body** (4 `__abs` / `__abs_anno` × `m_orig` admits closed) |
| `ab87e38` | — | D12 `__app` case closed via `d_consis_gen_refl_is_typ` |
| `28e5212` | — | 6 HmonoT extraction admits (SPLIT helper bodies) |
| `c110ebb` | — | Added `d_consis_syn_inh_mono` helper for mono extraction in new world |

## 2026-05-15 — typ_all_plain refactor (re-encoding pass)

- `4a7653c`: cascade GREEN — `typ_all_plain` refactor complete (build green).
- `7bd8962` / `9c92f5e` / `3cef0ac` / `56bf54c` / `ec52c3a` / `acfbd03`: WIP series — separate plain forall (ctyp) from decorated typ, then repair each file post-refactor.

The re-encoding pass introduced bulk admits (~14 new during rewrite); subsequent repair passes closed most. This pass split the syntactic role of plain-forall (`ctyp_all`) from the decorated polymorphic types (`typ_all_col` + `typ_all_etag`), enabling the colour discipline that drives the D1/D12 closure.

## Earlier (Phase 2 base)

- `bcf2749`: added `README.v` — paper-to-Coq theorem index.
- `7a41888`: closed `d_typing_abs_anno_value_to_subsumption` (Qed).
- `f05e276`: closed `d_typing_abs_value_to_subsumption` (Qed).
- `be06d5b`: removed 3 unused unsound lemmas; added SPLIT helpers for D12 abs/abs_anno.
- `80ccb23`: closed `d_sub_LHS_mono_wf` + `d_consis_extends_d_sub` (then-name; now `d_consis_sub_trans`).
- `023a711`: closed `d_consis_to_d_sub_gen`.

## Earlier retrospective: Lemma 3.7 (`d_pat_preserves_skel_wf`) — worked example of the colour-discipline closure pattern

**Status: Qed-closed** at the paper-faithful signature
([`d_pat_preserves_skel_wf`](frost/decl/prop_skeleton.v):
`d_pat mode_tc Γ e P → d_wf_denv Γ → d_wf_skel nil Γ P` — no extra
premises). Closure took several iterations and bottomed out at a
*methodological* insight rather than a structural patch — see
[DESIGN.md §6 — Proof debugging methodology](DESIGN.md).

**What looked like the obstacle (it wasn't).** The
`d_pat_consis__univ_ghost_inh1` rule recurses on Γ-extension while
`d_wf_skel__all_col` recurses on Ψ-extension. At a `typ_tophole`
boundary, Ψ gets stripped while Γ survives. So a derivation that
introduces α into Γ during d_pat_consis can produce an output ∀α.P
where the wf-check (which rebinds α in Ψ) fails because α is under a
tophole. A concrete counter-example exists at the standalone-rule
level: input `TopHole.(Hole → Unit)`, output
`∀α. TopHole.(α → Unit)` — d_pat_consis derives it, wf rejects it.
This was diagnosed as a "paper-level Γ↔Ψ tension" needing rule
changes.

**What the actual obstacle was.** The d_pat_consis rule *can* derive
the bad shape **in isolation**, but the *only* contexts in the typing
system that invoke d_pat_consis are `d_pat_sub__infer` and
`d_pat_sub__univ_ghost_r`, both of which carry `is_syn_skel P` as an
explicit rule premise. `is_syn_skel` rejects `typ_all_col colour_inh`
at the top — exactly the shape the counter-example produces. So the
bad derivation can be *built*, but it **can never be plugged into a
typing-context use of d_pat_consis.** The paper's informal proof of
Lemma 3.7 implicitly relied on this contextual constraint.
Mechanically, the fix is to surface it on the helper lemma:

```coq
Lemma d_pat_consis_preserves_wf :
    d_pat_consis Δ Γ SS P -> is_skel SS -> wf(SS) ->
    is_syn_skel P ->                                    (* the call-site contract *)
    wf(P).
```

The previously-admitted `__univ_ghost_inh1` case closed by inversion
of `is_syn_skel` on the output.

**The shape of the fix.**

1. `d_pat_consis_preserves_wf` and `d_pat_sub_preserves_wf` strengthened
   with `is_syn_skel P` (call-site contract surfaced).
2. `d_wf_denv__skel` strengthened with `is_skel P` (already true of
   every constructor of dbind_skel-entries; we made it explicit).
3. Auxiliary lemmas: `d_pat_sub_implies_is_syn_skel` (mode_tc /
   mode_ti), `d_pat_base_mode_ti_is_skel` (d_pat output for base
   terms at mode_ti).
4. Mutual `d_typing_pat_preserves_wf` conditions its d_pat side on
   `(m = mode_tc ∨ m = mode_ti)` — implementation detail.
5. **`d_pat_preserves_skel_wf` corollary at mode_tc, no extra
   premises** — matches the paper's signature exactly.

The top-level paper-facing lemma carries no new premises. The
premises appear only on internal helpers, where they reflect the
colour discipline the paper proof's narration was already using.

**Related: "P2/P3 paper inconsistency" — RESOLVED (was a parsing
bug).** An earlier read of paper rules at `declarative.tex:1626` and
`:1635` interpreted them as producing `(typ_tophole typ_hole) → Q` and
`(typ_tophole A) → Q` respectively, concluding the rules produced
shapes that fail wf. That was a **precedence misreading**. In math
notation, `TopHole.X → Y` parses as `TopHole.(X → Y)` (binder
right-associative, like `∀x. P → Q ≡ ∀x.(P → Q)`). The actual rules
produce `typ_tophole (typ_arrow typ_hole Q)` /
`typ_tophole (typ_arrow A Q)` — both bodies are arrows, hence
guarded, hence wf. **No paper inconsistency.**

## Phase 1 (definitions only)

🟢 Complete (commit `6b5f7c3`, 2026-05-10). Every paper rule from `paper/sections/declarative.tex` has a corresponding `Inductive` constructor in `mechanization/frost/decl/def_extra.v`; full clean build; no `Admitted`. Bug audit performed and 9 fixes applied. Mutual block reduced to just `d_typing` ↔ `d_pat`.

## Phase 3 status (post 2026-05-17)

**3.A Algorithmic defs** (`frost/algo/def_extra.v`): 🟢 done. ~140 constructors across 16 inductives.

**3.B Algo soundness** (`frost/algo/prop_soundness.v`): 🟡 scaffolding only. 3 admits: `a_sub_sound`, `a_pat_sound`, `a_typing_sound` (HEADLINE — depend on `a_consis_sound`, `a_unify_sound`, `a_assign_sound`, `a_pre_sub_sound`, `a_split_sound`, `a_guess_mono_sound` not yet stated). All 9 stability lemmas Qed.

**3.C Algo completeness** (`frost/algo/prop_completeness.v`): 🟡 scaffolding only. 3 admits: `a_sub_complete`, `a_pat_complete`, `a_typing_complete` (HEADLINE — dual to 3.B). `a_sub_decidable_existential` Qed in vacuous-disjunct form.

<!-- BEGIN paper-refs (auto-generated by scripts/sync_paper_refs.py) -->
[thm:sound-type-inference]: ../paper/sections/algorithmic.tex#L686 "Theorem E.4: Soundness of type inference"
[thm:complete-type-inference]: ../paper/sections/algorithmic.tex#L693 "Theorem E.5: Completeness of type inference"
[lemma:connection-informativeness]: ../paper/sections/algorithmic.tex#L976 "Lemma 4.13: Connection of informativeness"
[thm:sound-skeleton-inference]: ../paper/sections/algorithmic.tex#L1017 "Theorem 4.15: Soundness of skeleton inference"
[thm:complete-skeleton-inference]: ../paper/sections/algorithmic.tex#L1024 "Theorem 4.16: Completeness of skeleton inference"
[thm:sound-subtyping]: ../paper/sections/algorithmic.tex#L1087 "Theorem 4.19: Soundness, completeness, and minimality of subtyping"
[thm:complete-subtyping]: ../paper/sections/algorithmic.tex#L1088 "Theorem 4.19: Soundness, completeness, and minimality of subtyping"
[thm:sound-unification]: ../paper/sections/algorithmic.tex#L1329 "Lemma 4.21: Soundness and completeness and minimality of unification"
[thm:complete-unification]: ../paper/sections/algorithmic.tex#L1330 "Lemma 4.21: Soundness and completeness and minimality of unification"
[lemma:general-subsumption]: ../paper/sections/declarative.tex#L575 "Lemma 3.1: General subsumption"
[lemma:stability]: ../paper/sections/proofs.tex#L16 "Lemma D.2: Stability"
[lemma:structural]: ../paper/sections/proofs.tex#L21 "Lemma D.3: Structural rules"
[lemma:split-refine]: ../paper/sections/proofs.tex#L34 "Lemma D.4: Splitting refines"
[lemma:restricted-subtyping]: ../paper/sections/proofs.tex#L43 "lemma:restricted-subtyping"
[lemma:consis-sub]: ../paper/sections/proofs.tex#L52 "Lemma D.5: Consistency extends subtyping"
[lemma:safety-preservation]: ../paper/sections/proofs.tex#L906 "Lemma D.6: Substitution preserves safety"
[lemma:informativeness-preservation]: ../paper/sections/proofs.tex#L918 "Lemma D.7: Substitution preserves informativeness"
[lemma:more-informative-skeletons]: ../paper/sections/proofs.tex#L932 "Lemma D.8: More information does not harm"
[thm:consist-transitivity]: ../paper/sections/syntax-directed.tex#L152 "Lemma B.2: Consistency Transitivity"
[thm:consist-subtyping-transitivity]: ../paper/sections/syntax-directed.tex#L165 "Lemma B.3: Consistency-Subtyping Transitivity"
[thm:subtyping-transitivity]: ../paper/sections/syntax-directed.tex#L254 "Lemma B.4: Subtyping Transitivity"
[thm:typing-syn-soundness]: ../paper/sections/syntax-directed.tex#L561 "Lemma B.6: Soundness of Syntax-directed Rule"
[thm:typing-syn-completeness]: ../paper/sections/syntax-directed.tex#L578 "Lemma B.7: Completeness of Syntax-directed Rule"
<!-- END paper-refs -->
