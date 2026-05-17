# Frost Mechanization — Progress

Coordination file for the Phase 2 + Phase 3 push. Two sections:

- **[Part 1: Paper → Mechanization mapping](#part-1-paper--mechanization-mapping)** — per-lemma status, statements, locations.
- **[Part 2: Daily progress](#part-2-daily-progress)** — session-by-session closure log.

**Spec:** [`docs/superpowers/specs/2026-05-10-frost-phase23-design.md`](../docs/superpowers/specs/2026-05-10-frost-phase23-design.md)

## Status (current — 2026-05-17, after δ-cascade Phase 0)

**Build:** 🟢 GREEN. δ-cascade Phase 0 (this session) added missing
bullet placeholders for the new constructors (`d_sub__forall_l_untagged`,
`d_consis__forall_inh_untagged`, `d_consis_gen__forall_inh_untagged`)
across the case-splitting proofs the δ-refactor broke. All `admit.`
placeholders are documented inline.

**Flagship theorems (D1 / D12):** ⚠️ **NOT** "Closed under the global
context" post-δ. `Print Assumptions` on
`d_typing_general_subsumption_via_gen` and `_gen` now lists 4 axioms,
all introduced by the δ refactor:

1. `d_sub_gen_trans` — new `__forall_l_untagged` inner case at `mode_fn m`.
   The `is_fn_n_ti m1` induction doesn't provide an IH at the same
   `mode_fn m` for the body composition; needs proof restructuring to
   match the paper's induction-on-d_sub style (syntax-directed.tex:323-338).
2. `d_consis_syn_inh_mono` — **provably false** post-δ. The
   `__forall_inh_untagged` rule admits `syn_color (ctyp_all C) ≈ inh_color
   (ctyp_all D)` consistencies, breaking the shortcut "syn-LHS ↔ inh-RHS
   d_consis ⇒ LHS mono". Used in 4 SPLIT-helper call sites.
3. `d_consis_gen_syn_inh_mono` — parallel provably-false case for
   d_consis_gen.
4. `d_consis_gen_lhs_syn_eq` — **provably false** post-δ. The
   `__forall_inh_untagged` rule means LHS colour_syn ↔ RHS colour_inh
   (not equal). Used in 8 SPLIT-helper call sites for the
   `A = syn_color T` subst.

Re-closing D1 / D12 requires either (a) restructuring the SPLIT helpers
and `d_sub_gen_trans` to be polymorphic-body-aware without leaning on
the broken shortcuts, or (b) adding precondition restrictions at the
entry points (potentially cascading to D12's signature). This is a
multi-session effort. See plan: [`docs/superpowers/plans/2026-05-17-delta-encoding-admit-cleanup.md`](docs/superpowers/plans/2026-05-17-delta-encoding-admit-cleanup.md).

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
- 🟢 fully closed: **7** (D4, D5, D9, D10, D12, A1, A2/A3)
- 🟡 partial / narrowed: **2** (D1 — Qed wrapper; D2 — narrowed via `is_typ A`)
- 🟠 admitted (HEADLINE): **6** (D6, D7, A8, A9, A11, A12, A13)
- ⚠️ paper-flagged: **1** (D3)
- 🔴 not mechanized: **7** (D11, A4, A5, A6, A7, A10, A14)
- n/a: **3** (D8, D13, D14)

## Declarative metatheory (`paper/sections/declarative.tex`, `paper/sections/syntax-directed.tex`)

Mech statements use the notations from [`frost/decl/notations.v`](frost/decl/notations.v):
`Γ ⊢[ M ] e ⇒ A` for `d_typing`, `Γ ⊢[ M ] e ⇨ P` for `d_pat`, `Γ ⊢[ M ; Δ ] T ⊑ A` for `d_sub`, `Δ ⨟ Γ ⊨ T ≈ A` for `d_consis`, `Γ ⊢ A ≤ B` for `d_shallow_sub`, `Ψ ⨟ Γ ⊢ₛₖ P` for `d_wf_skel`, `Ψ ⨟ Γ ⊢ᵣ P ▸ Q` for `d_refine`, `Ψ ⨟ Γ ⊢ᵣ P ⊳ Q` for `d_refine_syn`. The "gen" relations (`d_typing_gen`, `d_consis_gen`, `d_sub_gen`) and `d_wf_typ` have no dedicated notation — application form used.

Paper labels resolved to file:line in the auto-managed block at end of file (regenerate with `python3 scripts/sync_paper_refs.py --md`). Lemmas without a `\label{...}` in the paper source carry a plain `paper:LINE` ref + a `(no label)` marker.

| # | Paper lemma | Mech & paper statement | Status |
|---|---|---|---|
| D1 | [Lemma 3.1: General subsumption][lemma:general-subsumption] | **Mech:** `d_typing_general_subsumption_via_gen` [`prop_general_subsumption.v:794`](frost/decl/typing/prop_general_subsumption.v#L794):<br>`d_wf_denv Γ → Γ ⊢[ mode_ti ] e ⇒ A → Γ ⊢[ m ; nil ] A ⊑ B → Γ ⊢[ m ] e ⇒ B`<br>**Paper:** `If Γ ⊢_TI M ⇒ syn{A} and Γ ⊢_M syn{A} ≤ bid{B}, then Γ ⊢_M M ⇒ bid{B}` (LaTeX: `\typp[\TI]{\Gamma}{M}{\syn{A}}`, `\typsub[\M]{\Gamma}{\syn{A}}{\bid{B}}`, `\typp[\M]{\Gamma}{M}{\bid{B}}`) | 🟡 Qed wrapper. Bridge: `d_typing_embed_gen` (Qed) · `d_typing_general_subsumption_gen` / D12 (Qed) · `d_typing_gen_collapse` (Qed). **Closed under the global context** as of 2026-05-17. |
| D2 | Soundness of subtyping (paper [declarative.tex:1101](../paper/sections/declarative.tex#L1101), no `\label`) | **Mech:** `d_sub_sound` [`prop_sub_sound.v`](frost/decl/subtyping/prop_sub_sound.v):<br>`is_typ A → Γ ⊢[ mode_tc ; nil ] A ⊑ B → Γ ⊢ A ≤ B`<br>**Paper:** for `mode_tc` subtyping, the conclusion is shallow-subtypeable. | 🟡 narrowed with `is_typ A` so LHS is `typ_all_col` flavour (matches `d_shallow_sub` shape) |
| D3 | No guessing of polytypes (paper [declarative.tex:1108](../paper/sections/declarative.tex#L1108), no `\label`) | **Mech:** `d_sub_no_guess_uniqueness` [`prop_sub_sound.v:215`](frost/decl/subtyping/prop_sub_sound.v#L215):<br>two instantiations `ph1`, `ph2` of same `d_sub` derivation imply `ph1 = ph2`<br>**Paper:** intuition that the polytype guessing `ph` in `d_sub__forall_l_tagged` is uniquely determined. | ⚠️ paper-flagged — counter-example inlined (`ph` can absorb into nested `forall_l_tagged` chains); paper revision suggested |
| D4 | Refinement preserves wf (paper [declarative.tex:1386](../paper/sections/declarative.tex#L1386), no `\label`) | **Mech:** `d_refine_preserves_wf` [`prop_wellformed.v:766`](frost/decl/prop_wellformed.v#L766):<br>`Ψ ⨟ Γ ⊢ₛₖ P → Ψ ⨟ Γ ⊢ᵣ P ▸ Q → Ψ ⨟ Γ ⊢ₛₖ Q` (coloured variant `d_refine_syn_preserves_wf` also Qed) | 🟢 |
| D5 | Preservation of skeleton wf (paper [declarative.tex:1976](../paper/sections/declarative.tex#L1976), no `\label`) | **Mech:** `d_pat_preserves_skel_wf` [`prop_skeleton.v:128`](frost/decl/prop_skeleton.v#L128):<br>`Γ ⊢[ mode_tc ] e ⇨ P → d_wf_denv Γ → nil ⨟ Γ ⊢ₛₖ P` | 🟢 narrowed via `d_pat_*_preserves_wf` with `is_syn_skel P` side hypothesis |
| D6 | Validity of skeleton inference (paper [declarative.tex:1987](../paper/sections/declarative.tex#L1987), no `\label`) | **Mech:** `d_pat_validity` [`prop_skeleton.v:154`](frost/decl/prop_skeleton.v#L154):<br>`Γ ⊢[ m ] e ⇨ P → d_wf_denv Γ → (∃ A, Γ ⊢[ m ] e ⇒ A) → ∃ B, Γ ⊢[ m ] e ⇒ B ∧ nil ⨟ Γ ⊢ᵣ P ▸ B` | 🟠 depends on refinement reflexivity (guarded skeletons) + anti-symmetry with `d_typing__sub` |
| D7 | Safety of skeleton inference (paper [declarative.tex:1992](../paper/sections/declarative.tex#L1992), no `\label`) | **Mech:** `d_pat_safety` [`prop_skeleton.v:180`](frost/decl/prop_skeleton.v#L180):<br>`(∃ A, Γ ⊢[ m ] e ⇒ A) → d_wf_denv Γ → ∃ P, Γ ⊢[ m ] e ⇨ P ∧ (∀ B, Γ ⊢[ m ] e ⇒ B → nil ⨟ Γ ⊢ᵣ P ▸ B)` | 🟠 universal "refines every type" — needs principal-skeleton construction (join under refinement) |
| D8 | General Subsumption (syntax-directed, paper [syntax-directed.tex:3](../paper/sections/syntax-directed.tex#L3), no `\label`) | (same as D1) | n/a — duplicate of D1; mech has one declarative system |
| D9 | [Lemma B.2: Consistency Transitivity][thm:consist-transitivity] | **Mech:** `d_consis_compose` [`prop_consis_trans.v`](frost/decl/subtyping/prop_consis_trans.v):<br>`Δa ⨟ Γ ⊨ T ≈ A → Δb ⨟ Γ ⊨ A ≈ B → list_disjoint Δa Δb → ∃ Δc, Permutation Δc (Δa ++ Δb) ∧ Δc ⨟ Γ ⊨ T ≈ B`<br>**Paper:** `If ⊨[Δ₁] Γ T ≈ T' and ⊨[Δ₂] Γ T' ≈ A, then ⊨[Δ₁,Δ₂] Γ T ≈ A` (LaTeX: `\typconsis[\Delta_1]{\Gamma}{\bid{T}}{\bid{T'}}`, `\typconsis[\Delta_2]{\Gamma}{\bid{T'}}{\bid{A}}`, `\typconsis[\Delta_1, \Delta_2]{\Gamma}{\bid{T}}{\bid{A}}`) | 🟢 mod Permutation — arrow case interleaves segments; paper writes "Δ1, Δ2" as set union |
| D10 | [Lemma B.3: Consistency-Subtyping Transitivity][thm:consist-subtyping-transitivity] | **Mech:** `d_consis_sub_trans` [`prop_consis_sub_trans.v:105`](frost/decl/subtyping/prop_consis_sub_trans.v#L105):<br>`Δ ⨟ Γ ⊨ T ≈ A → Γ ⊢[ M ; Δ' ] A ⊑ B → list_disjoint Δ Δ' → (M = mode_ti → Δ = nil) → d_wf_typ Γ T → ∃ Δc, Permutation Δc (Δ ++ Δ') ∧ Γ ⊢[ M ; Δc ] T ⊑ B`<br>**Paper:** `If ⊨[Δ₁] Γ T ≈ T' and ⊢[M;Δ₂] Γ T' ⊑ A, then ⊢[M; Δ₁,Δ₂] Γ T ⊑ A` (LaTeX: `\typconsis[\Delta_1]{\Gamma}{\bid{T}}{\bid{T'}}`, `\typsub[\M][\Delta_2]{\Gamma}{\bid{T'}}{\bid{A}}`, `\typsub[\M][\Delta_1, \Delta_2]{\Gamma}{\bid{T}}{\bid{A}}`) | 🟢 Qed in paper-faithful form. Side conditions are encoding artefacts (`list_disjoint` + Permutation for set-union, `Δ = nil` for `d_sub__infer` rigidity, `d_wf_typ Γ T` to rule out non-wf `typ_all_etag` LHS via [`d_consis_RHS_syn_color_eq`](frost/decl/subtyping/prop_consis_sub_trans.v#L28)). |
| D11 | [Lemma B.4: Subtyping Transitivity][thm:subtyping-transitivity] | — | 🔴 not separately mechanized; subsumed by D12 (`d_sub_gen_trans` is Qed and powers D12's `__sub` case) |
| D12 | Generalised General Subsumption (paper Lemma B.5, [syntax-directed.tex:343](../paper/sections/syntax-directed.tex#L343), no `\label`) | **Mech:** `d_typing_general_subsumption_gen` [`prop_general_subsumption.v:107`](frost/decl/typing/prop_general_subsumption.v#L107):<br>`d_typing_gen m_orig Γ e A → is_fn_n_ti m_orig → d_wf_denv Γ → d_sub_gen (mode_fn_n_subst m_orig m_new) nil Γ A B → d_typing_gen (mode_fn_n_subst m_orig m_new) Γ e B`<br>**Paper:** `If ⊢_FN[n] TI Γ M ⇒ bid{A}, ⊢_TY (FN[n] TI) bid{A}, and ⊢_FN[n] M Γ bid{A} ⊑ bid{B}, then ⊢_FN[n] M Γ M ⇒ bid{B}` (LaTeX: `\typp[\FN[n]~\TI]{\Gamma}{M}{\bid{A}}`, `\skmod[\TY]{{\FN[n]}~\TI}{\bid{A}}`, `\typsub[\FN[n]\M]{\Gamma}{\bid{A}}{\bid{B}}`, `\typp[\FN[n]\M]{\Gamma}{M}{\bid{B}}`) | 🟢 Qed, **closed under the global context** as of 2026-05-17. All 14 case-rules (4 base × 3 sub × 2 abs flavours + __app + structural) Qed. Routes through SPLIT helpers in [`prop_subsumption_aux.v`](frost/decl/typing/prop_subsumption_aux.v) which take an `Hbody_at_tc` premise constructed from D12's own IHbody — breaks the lift_mono ↔ D12 cycle. |
| D13 | [Lemma B.6: Soundness of Syntax-directed Rule][thm:typing-syn-soundness] | — | n/a — mech only has the bidirectional declarative system |
| D14 | [Lemma B.7: Completeness of Syntax-directed Rule][thm:typing-syn-completeness] | — | n/a |

## Algorithmic metatheory (`paper/sections/algorithmic.tex`, `paper/sections/proofs.tex`)

| # | Paper lemma | Mech & paper statement | Status |
|---|---|---|---|
| A1 | [Lemma D.2: Stability][lemma:stability] | **Mech:** `stability_d_typing` [`prop_soundness.v:620`](frost/algo/prop_soundness.v#L620) + 8 siblings:<br>`aenv_extends Θ0 Θ1 → a_transfers Θ0 Γ0 → a_transfers Θ1 Γ1 → Γ0 ⊢[ m ] e ⇒ A → Γ1 ⊢[ m ] e ⇒ A` (same shape for `_d_wf_typ`, `_d_consis`, `_d_sub`, `_d_pat_consis`, `_d_pat_sub`, `_d_refine`, `_d_refine_syn`, `_d_pat`)<br>**Paper:** "All statements in this paper are stable" — for every judgment `J` and `Θ₀ ≤ Θ₁`, `Θ₀ ⊢ J ⇒ Θ₁ ⊢ J`. | 🟢 9 of 9 |
| A2 | [Lemma D.3: Structural rules][lemma:structural] | **Mech:** `d_typing_suffix_moving_singleton` [`prop_typing.v`](frost/decl/prop_typing.v) + `d_pat_suffix_moving_singleton`:<br>`Γ1 ++ y~b ++ Γ2 ⊢[ m ] e ⇒ A → y ∉ dom Γ1 → Γ1 ++ Γ2 ++ y~b ⊢[ m ] e ⇒ A`<br>**Paper:** SuffixMoving rule — moving a binding past a suffix preserves typing. | 🟢 narrowed to single-binding move; full n-binding form needs free-vars-of-context machinery |
| A3 | [Lemma D.4: Splitting refines][lemma:split-refine] | **Mech:** `d_refine_arrow_split` [`prop_skeleton.v:25`](frost/decl/prop_skeleton.v#L25) + 7 siblings (`_all_plain_split`, `_hole_split`, `_tophole_split`, syn-painted variants):<br>`Ψ ⨟ Γ ⊢ᵣ typ_arrow P1 P2 ▸ Q → ∃ Q1 Q2, Q = typ_arrow Q1 Q2 ∧ Ψ ⨟ Γ ⊢ᵣ P1 ▸ Q1 ∧ Ψ ⨟ Γ ⊢ᵣ P2 ▸ Q2`<br>**Paper:** `If Θ₀ ⊢ split[P₀][P₁] ⇒ Θ₁, then Θ₁ ⊢ inh{P₀} fillsyn inh{P₁}` (LaTeX: `\mov{\Theta_0}{\split[P_0][P_1]{}}{\Theta_1}`, `\Theta_1\vdash\inh{P_0}\fillsyn\inh{P_1}`) | 🟢 8 of 8 |
| A4 | [Lemma D.5: Consistency extends subtyping][lemma:consis-sub] | — (NOT mechanized; distinct from D10/B.3) | 🔴 D.5 is stated over algorithmic `allsub` / `consistent`, distinct from D10/B.3 (declarative `d_consis` + `d_sub`). `d_consis_sub_trans` (D10) is NOT a mechanization of D.5; earlier docs conflated the two. Paper: `If Θ ⊢ consistent(P, P') and ⊢_{N,M} Θ P ⊑ Q, then ⊢_{N,M} Θ P' ⊑ Q`. |
| A5 | [Lemma D.6: Substitution preserves safety][lemma:safety-preservation] | — | 🔴 paper proof is "obvious — θ monotype only"; corollary of typ-subst preservation (itself admitted) |
| A6 | [Lemma D.7: Substitution preserves informativeness][lemma:informativeness-preservation] | — | 🔴 same |
| A7 | [Lemma D.8: More information does not harm][lemma:more-informative-skeletons] | — | 🔴 redundant with D1 (general subsumption) — not stated separately. Paper: `If ⊢[M] Θ M ⇒ bid{A} and bid{A'} ≼ bid{A}, then ⊢[M] Θ M ⇒ bid{A'}` (LaTeX: `\typp[\M]{\Theta}{M}{\bid{A}}`, `\bid{A'}\morepoly\bid{A}`). |
| A8 | [Theorem E.4: Soundness of type inference][thm:sound-type-inference] | **Mech:** `a_typing_sound` [`prop_soundness.v:748`](frost/algo/prop_soundness.v#L748):<br>`a_typing m Θ0 P0 e A Θ1 → a_transfers Θ0 Γ0 → a_transfers Θ1 Γ1 → Γ1 ⊢[ m ] e ⇒ A`<br>**Paper:** Given a type inference question `(Θ₀; M; P; M)`, if `⊢_{M;P} Θ₀ M ⇒ A ⇒ Θ₁`, then `(Θ₀ ≤ Θ₁; A)` is a solution. | 🟠 HEADLINE — depends on `a_consis_sound`, `a_unify_sound`, `a_assign_sound`, `a_pre_sub_sound`, `a_split_sound`, `a_guess_mono_sound` (not yet stated) |
| A9 | [Theorem E.5: Completeness and minimality of type inference][thm:complete-type-inference] | **Mech:** `a_typing_complete` [`prop_completeness.v:327`](frost/algo/prop_completeness.v#L327):<br>`Γ ⊢[ m ] e ⇒ A → ∀ Θ0 P0, a_transfers Θ0 Γ → a_wf_typ Θ0 P0 → ∃ Θ1, a_typing m Θ0 P0 e A Θ1 ∧ a_transfers Θ1 Γ`<br>**Paper:** dual to A8 — given a solution `(Θ₀ ≤[θ] Θ; B)`, the algorithm finds a minimal one. | 🟠 HEADLINE — dual to A8; same auxiliary family |
| A10 | [Lemma 4.13: Connection of informativeness][lemma:connection-informativeness] | — | 🔴 not attempted; depends on a precise `morepoly` definition. Paper: for `P` and `Q` safe skeletons of `M`, if `P ≼ Q` then every `inh{Q} fillsyn bid{B}` with `Θ ⊢_M M ⇒ bid{B}` lifts to an `inh{P} fillsyn bid{A}`. |
| A11 | [Theorem 4.15: Soundness of skeleton inference][thm:sound-skeleton-inference] | **Mech:** `a_pat_sound` [`prop_soundness.v:716`](frost/algo/prop_soundness.v#L716):<br>`a_pat m Θ0 P0 e P Θ1 → a_transfers Θ0 Γ0 → a_transfers Θ1 Γ1 → Γ1 ⊢[ m ] e ⇨ P` | 🟠 HEADLINE — mutual with A8 |
| A12 | [Theorem 4.16: Completeness of skeleton inference][thm:complete-skeleton-inference] | **Mech:** `a_pat_complete` [`prop_completeness.v:209`](frost/algo/prop_completeness.v#L209):<br>`Γ ⊢[ m ] e ⇨ P → ∀ Θ0 P0, a_transfers Θ0 Γ → a_wf_typ Θ0 P0 → ∃ Θ1 Q, a_pat m Θ0 P0 e Q Θ1 ∧ a_transfers Θ1 Γ` | 🟠 HEADLINE — mutual with A9 |
| A13 | [Theorem 4.19: Soundness/Completeness/Minimality of subtyping][thm:sound-subtyping] | **Mech:** `a_sub_sound` [`prop_soundness.v:661`](frost/algo/prop_soundness.v#L661) + `a_sub_complete` [`prop_completeness.v:135`](frost/algo/prop_completeness.v#L135) | 🟠 HEADLINE — five auxiliary completeness/soundness lemmas blocked. `a_sub_decidable_existential` is Qed in vacuous-disjunct form (documents the obligation without fabricating a proof). |
| A14 | [Lemma 4.21: Soundness and completeness and minimality of unification][thm:sound-unification] | — | 🔴 `a_unify` defined in `algo/def_extra.v`; no standalone soundness lemma stated (consumed via A13 / A8 chains) |

## Mechanization-only support lemmas

These don't appear as separate paper lemmas but are load-bearing for the mech. Listed so a reviewer can see what infrastructure the paper proofs depend on. Statements use the same Coq notations as the Declarative table above (`Γ ⊢[ M ] e ⇒ A`, `Δ ⨟ Γ ⊨ T ≈ A`, etc.).

| Mech lemma | Status | File:line | Purpose |
|---|---|---|---|
| `d_typing_embed_gen` | 🟢 | [`def_gen.v`](frost/decl/typing/def_gen.v) | `d_typing → d_typing_gen` embedding (structural induction) |
| `d_typing_gen_collapse` | 🟢 | [`prop_general_subsumption.v:766`](frost/decl/typing/prop_general_subsumption.v#L766) | `d_typing_gen → d_typing` (uses `d_sub_gen_to_d_sub` + `d_consis_gen_to_d_consis`) |
| `d_sub_gen_to_d_sub` | 🟢 | [`prop_general_subsumption.v:730`](frost/decl/typing/prop_general_subsumption.v#L730) | gen → sub bridge for subtyping |
| `d_consis_gen_to_d_consis` | 🟢 | [`prop_general_subsumption.v:705`](frost/decl/typing/prop_general_subsumption.v#L705) | gen → sub bridge for consistency (uses base d_consis with __forall_inh added) |
| `d_consis_gen_RHS_syn_color_eq` | 🟢 | [`def_gen.v`](frost/decl/typing/def_gen.v) | wf + RHS = syn_color ⇒ LHS = syn_color, Δ = nil |
| `d_consis_RHS_syn_color_eq` | 🟢 | [`prop_consis_sub_trans.v:28`](frost/decl/subtyping/prop_consis_sub_trans.v#L28) | non-gen mirror of above; new helper added 2026-05-17 |
| `d_consis_sub_trans_nil` | 🟢 | [`prop_consis_sub_trans.v:206`](frost/decl/subtyping/prop_consis_sub_trans.v#L206) | narrowed (nil/nil) form of D10 |
| `d_consis_sub_trans_gen_nil` | 🟢 | [`def_gen.v`](frost/decl/typing/def_gen.v) | D10 analogue with `d_sub_gen` on the second relation |
| `d_consis_gen_trans` / `d_sub_gen_trans` | 🟢 | [`def_gen.v`](frost/decl/typing/def_gen.v) | transitivity of gen relations (D12's `__sub` mode-changing case) |
| `d_sub_gen_arrow_refl_inner` | 🟢 | [`prop_subsumption_aux.v`](frost/decl/typing/prop_subsumption_aux.v) | refl on mono arrow ⇒ refl on return |
| `d_typing_pat_weakening` / `_ctx_morph` | 🟢 | [`prop_weakening.v`](frost/decl/typing/prop_weakening.v) | full 18-case weakening + context morphism (mutual) |
| `d_typing_pat_preserves_wf` | 🟢 | [`prop_wellformed.v`](frost/decl/prop_wellformed.v) | full 18-case wf preservation (mutual) |
| `d_typing_gen_preserves_wf` / `d_sub_gen_preserves_wf` | 🟢 | [`def_gen.v`](frost/decl/typing/def_gen.v) | gen analogues of preservation |
| `d_typing_abs[_anno]_value_to_subsumption_split[_d_sub]` | 🟢 | [`prop_subsumption_aux.v`](frost/decl/typing/prop_subsumption_aux.v) | SPLIT helpers (4) used by D12 __abs / __abs_anno; take `Hbody_at_tc` premise constructed by caller from IHbody |
| `d_typing_abs[_anno]_value_to_subsumption_split_ti` | 🟢 | [`prop_subsumption_aux.v`](frost/decl/typing/prop_subsumption_aux.v) | TI variants of SPLIT helpers (no lift_mono needed) |
| `d_typing_sub_compose` | 🟢 | [`prop_subtyping.v`](frost/decl/prop_subtyping.v) | helper for D1's `__sub` case; uses `d_consis_sub_trans` with `d_wf_typ` from `d_typing_pat_preserves_wf` |
| `d_typing_pat_subst_typ_mut` | 🟠 | [`prop_weakening.v:644`](frost/decl/typing/prop_weakening.v#L644) | mutual type subst; blocked on `d_sub_subst` / `d_refine_syn_subst` / `d_pat_*_subst` (not yet stated) |
| `d_typing_narrowing` | 🟠 | [`prop_weakening.v:668`](frost/decl/typing/prop_weakening.v#L668) | reduces to D1; gated on `d_typing_general_subsumption` non-base cases |
| `d_typing_narrow_consis` / `_gen_narrow_consis` | 🟠 | [`prop_weakening.v:713`](frost/decl/typing/prop_weakening.v#L713), [`def_gen.v:1083`](frost/decl/typing/def_gen.v#L1083) | post-ctyp re-encoding: `__var` returns raw bound type; old `syn_color_t`-equality insufficient |
| `d_typing_swap_mono` / `_app_restructure` / `_order_irrel_adj` | 🟠 | [`prop_typing.v:77,107,153`](frost/decl/prop_typing.v) | Stability S1/S2 + order-irrelevance; need `d_typing`-inversion through `d_pat` (research-grade) |
| `E1_intro` / `E1_elim` / `E1_roundtrip` | 🟠 | [`prop_typing.v:218,237,247`](frost/decl/prop_typing.v) | Expressiveness benchmark (Church-encoded existentials); gated on `d_typing_pat_subst_typ_mut` |
| `d_sub_complete_mono` | 🟠 | [`prop_sub_sound.v:173`](frost/decl/subtyping/prop_sub_sound.v#L173) | reviewer-suggested completeness vs monotype-only shallow subtyping; forall_r/forall_l colour-flavour mismatch |
| `d_typing_gen_lift_mono` | 🟠 | [`prop_subsumption_aux.v:548`](frost/decl/typing/prop_subsumption_aux.v#L548) | `__app` requires function arg-type mononess (not derivable from rule); **NOT reachable from D1/D12** (broken via `Hbody_at_tc` parameter on SPLIT helpers, 2026-05-17). The non-gen sibling `d_typing_lift_mono_mut`/`_lift_mono` was deleted 2026-05-17 (zero callers, same gap). |
| ~~`d_consis_lhs_is_inh_for_typ` / `d_consis_gen_LHS_syn_color_mono` / `d_consis_LHS_is_utyp_when_RHS_syn_color` / `d_sub_not_lhs_typ_all_col`~~ | — | (deleted 2026-05-17) | All four were post-refactor FALSE under the new `__forall_syn` rule. Removed along with their dead caller chain (the two `d_typing_abs[_anno]_value_to_subsumption` umbrellas + the two `_d_sub` helpers + `is_inh_typ_syn_color_mono`) — none of those had callers outside `prop_subsumption_aux.v`. |

## Per-file admit summary

`frost/decl/` (15 admits total — was 20; -5 on 2026-05-17: 4 false admits + the dead-code `d_typing_lift_mono_mut`/`_lift_mono` pair):

| File | Count | Admitted lemmas |
|---|---|---|
| `prop_typing.v` | 6 | `d_typing_swap_mono`, `d_typing_app_restructure`, `d_typing_order_irrel_adj`, `E1_intro`, `E1_elim`, `E1_roundtrip` |
| `typing/prop_weakening.v` | 3 | `d_typing_pat_subst_typ_mut`, `d_typing_narrowing` (D1 done; blocked on `d_sub_complete`), `d_typing_narrow_consis` |
| `typing/def_gen.v` | 1 | `d_typing_gen_narrow_consis` |
| `typing/prop_subsumption_aux.v` | 1 | `d_typing_gen_lift_mono` (__app obstruction; not reachable from D1/D12) |
| `subtyping/prop_consis_sub_trans.v` | 0 | (was 1 — `d_typing_lift_mono_mut`/`_lift_mono` pair deleted 2026-05-17: zero callers, same __app gap as the gen sibling) |
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
