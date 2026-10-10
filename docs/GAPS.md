# GAPS — the managed list of paper gaps

This is the short, current registry of every finding about the Fresco paper, its reference implementation, and the mechanization's fidelity to it. Each item has a stable ID and one current status.
Date: 2026-10-10. Every entry was re-verified against the current tree (proof_fresco `main`, HEAD eb43ec1) and the current paper (impredicative @ d10a4460, which includes f484dde3's threaded-Ξ `SolE-FlexR` and `Flex-SkipTmVar`).
[`PAPER-GAPS.md`](PAPER-GAPS.md) keeps the long-form history and arguments. Entries cite its line numbers as `PG:<line>` and [`WF-SIDE-CONDITIONS.md`](WF-SIDE-CONDITIONS.md) as `WF:<line>`.
Citation conventions:
- `paper:<file>:<line>` is under `impredicative/paper/sections/` (appendix files are under `appendices/`).
- `impl:type.ml:<line>` is `paper/artifact/implementation/lib/type.ml` at d10a4460.
- Mechanization paths are repo-relative.

The 2026-10-10 rule-faithfulness pass has landed (G-56); the entries it touched are updated.

## Summary

| Kind \ Status | LIVE | UNCERTAIN | RESOLVED BY AUTHORS | MOOT | RETRACTED |
|---|---|---|---|---|---|
| False as stated | 5 | – | 2 | – | 4 |
| Proof-step gap | 11 | – | – | 1 | 1 |
| Missing lemma | 5 | – | – | – | – |
| Missing side condition | 7 | – | 1 | – | 1 |
| Ambiguity / non-determinism | 7 | 1 | 1 | – | – |
| Prose completion | 12 | – | – | 1 | – |
| Implementation issue | 2 | 2 | – | – | – |
| Encoding note (mech-only) | – | – | – | 14 | 1 |
| Mechanization to-do (ours) | 6 | 1 | – | – | – |
| **Total (86)** | **55** | **4** | **4** | **16** | **7** |

Sections: A = 21 · B = 14 · C = 12 · D = 1 · E = 4 · F = 7 · G = 27 (settled). The one-line settled entries in G are counted by their original kind.

---

## A. Live — for the authors: statements false as stated, and proof-step gaps

### G-01 Optimality of unification/assignment is false with syntactic binder entries in ⊑
- **Kind**: False as stated · **Status**: LIVE
- **Paper**: information increase `Θ,x:P ⊑ Θ',x:θP,Ξ` (paper:algorithmic.tex:111-115). Parts 2 and 3 of thm:complete-consistency (paper:full-algo-spec.tex:1556-1572). The paper's own source comment at :1574-1586 admits the problem, and `\input{optimality-cex}` is commented out.
- **Mechanization**: `a_inc__var` / `a_inc__var_skl` accept the payload up to ≡ (fresco/algo/def_meta.v:238-249), in the style of Gundry–McBride–McKinna. `complete_mu` is Qed (fresco/algo/consis/prop_completeness_consis.v:8060).
- **Evidence**: cex/cex_assign_optimal_syn_middle.v `cex_syn_middle_optimality_false` (:360). The same instance factors under the semantic rule (`cex_zeta_semantic`, :320). Both are Qed.
- **Ask for the authors**: Adopt the semantic premise `Θ' ⊢ P' ≡ θP` in the term-binder rule of ⊑ (a draft is in appendices/optimality-cex.tex). The same gap is in Gundry's thesis.
- **Source**: PG:1971

### G-02 The two-condition solution notions are too weak, so thm:complete-consistency is false as stated
- **Kind**: False as stated · **Status**: LIVE
- **Paper**: the solution definition and thm:complete-consistency use two conditions (paper:full-algo-spec.tex:1491-1500, :1556-1574). The proof uses an augmented three-condition version (paper:consistency-proofs.tex:2253-2263). thm:complete-subtyping's generalisation also uses two conditions (paper:subtyping-proofs.tex:3072-3083), and it invokes the consistency theorem at :3157, :3189, :3304 and :3356.
- **Mechanization**: `a_consis_complete` takes the third condition, subject refinement (fresco/algo/consis/prop_completeness_consis.v:8115-8124). Subtyping takes it only at the consistency leaves, via `sub_complete_concl` (fresco/algo/sub/prop_completeness_sub_gen.v:166) and `ad_pat_sub_fuel`. Taking it at the root makes UnivGhostR, ForallL and ForallR vacuous.
- **Evidence**: cex/cex_ad_pat_join_not_leaf_valid.v (`cap_consis`, `cap_no_join`). Root-level vacuity: cex/cex_p7_univ_ghost_r_vacuous.v and cex/cex_p7_third_premise_forall.v. All are Qed.
- **Ask for the authors**: State the solution notions with the subject refinement: at the root for consistency, and at the consistency leaves for subtyping. Alternatively, restrict the two-condition form to hole-free subjects.
- **Note**: The fragments disagree. Triage of PG:2164 called it MOOT, on the grounds that the consistency prose (paper:declarative.tex:2071-2073) already implies the third condition. Triage of PG:3197 called it LIVE, because the theorem's statement does not carry it. LIVE is kept here. It is the same root cause as G-36.
- **Source**: PG:2164, PG:3197; docs/ghost-capture.tex

### G-03 The paper's own TODO "concrete P₀ ⇒ subtyping RHS is P₀" is false
- **Kind**: False as stated · **Status**: LIVE (the TODO comment is still in the source)
- **Paper**: paper:subtyping-proofs.tex:3252-3254 (`% WT: … TODO: optional: check this`), in thm:complete-subtyping's ForallR case.
- **Mechanization**: proves the ≡ version: `a_consis_concrete_output_equiv` and `a_sub_concrete_output_equiv` (cex/probe_sub_concrete_rhs.v:150, :241).
- **Evidence**: cex/cex_p7_concrete_rhs.v `p7_concrete_rhs_is_false` (Qed). The witness is P₀ = 1→1, P = α̂→1, RHS = α̂→1.
- **Ask for the authors**: Delete the TODO, or restate it as `Θ₁ ⊢ P₀ ≡ P₀'`, which is what the proof already uses (:3249-3251).
- **Source**: PG:3090

### G-04 The check rows pin the body's result to the split codomain B, which is unsatisfiable
- **Kind**: False as stated (the rule is too strong) · **Status**: LIVE
- **Paper**: TI-AbsCheck / TI-AbsAnnoCheck write `⊢[TC][B] M ⦂ B` (paper:full-algo-spec.tex:351-355, :362-366). When B is flexible and the body is a λ or an application, the body cannot return B itself. The paper's own completeness proof concludes with the body's B₁. The implementation ignores the body's type (impl:type.ml:1432-1448).
- **Mechanization**: the body's result is a free `B1`, and the rule concludes `A → B1` (`a_typing__abs_check_base`, `_anno_check_base`, fresco/algo/def_rules.v:1943, :1965).
- **Evidence**: argument plus implementation behaviour. `a_typing_complete` is Qed only with the free B1.
- **Ask for the authors**: Give the body premise a fresh output `B₁` and conclude `∀ᾱ.A→B₁`.
- **Source**: PG:4092 (:4099)

### G-05 lemma:constraint-collection-stable-substitution is false without a Barendregt condition
- **Kind**: False as stated. The fragment called it a prose completion, but the unconditional statement is refuted by a machine-checked counterexample.
- **Status**: LIVE
- **Paper**: lemma:constraint-collection-stable-substitution (paper:subtyping-proofs.tex:506-522). It has no freshness premise, and its proof is "straightforward induction".
- **Mechanization**: both directions were deleted in efc8707. See G-53.
- **Evidence**: cex/cex_look_subst_stable_leak.v `look_subst_stable_unconditional_is_false` (Qed). A ∀-opener leaks into 𝒞, and substituting it for β breaks re-derivation.
- **Ask for the authors**: Add `ftv Q ⊆ {α} ∪ ftv(Θ)` (or say "by Barendregt"). Where Q is a ForallL guess this cannot be a context bound, so read the outputs up to rigid renaming.
- **Source**: PG:3343

### G-06 Ξ-strengthening is proved by solving Ξ away, not by direct induction
- **Kind**: Proof-step gap · **Status**: LIVE (both statements are true)
- **Paper**: lemma:suffix-erasure (paper:proofs.tex:38-46, "Straightforward induction"). The "context strengthening" step in the ForallR case of lemma:sound-decorated-subtyping (paper:subtyping-proofs.tex:1310). In both places ForallL may instantiate with Ξ-variables that never reach the conclusion.
- **Mechanization**: fresco/algo/prop_suffix_erase.v covers all six judgements (e.g. `ad_sd_typing_strip_suffix` :1525). For subtyping: `ad_pat_sub_fuel_strip_suffix` and `ad_pat_sub_fuel_subst_flex` (fresco/algo/sub/prop_soundness_subtag.v:1758, :1306).
- **Evidence**: the lemmas above (Qed).
- **Ask for the authors**: Replace both one-line proofs with the generalisation `Θ,Ξ ⊢ J ⟹ Θ ⊢ θJ`, which also rewrites the ForallL witnesses. Say why it is needed.
- **Source**: PG:1164, PG:2203

### G-07 lemma:precision-preserves-refinement needs a nested induction plus wf
- **Kind**: Proof-step gap · **Status**: LIVE
- **Paper**: paper:proofs.tex:80-89 ("Straightforward induction on the refinement derivation")
- **Mechanization**: `ad_refine_syn_trans` and `ad_precise_preserves_refine` (fresco/algo/prop_precise.v:545, :570) are Qed and assume the result is well-formed (`⊢ₚₛ ⌊Q⌋`). The proof is an outer induction on the second derivation and an inner induction that peels UnivGhost/Flex steps.
- **Evidence**: Qed. The earlier claim that the lemma is false without wf is RETRACTED, because its counterexample died with the faithful Ghost rule (51122ada). Whether it holds without wf is open.
- **Ask for the authors**: Sketch the real induction, and say that it uses the wf presupposition (paper:declarative.tex:1424).
- **Source**: PG:1749

### G-08 thm:complete-consistency: three induction subjects that do not combine
- **Kind**: Proof-step gap · **Status**: LIVE
- **Paper**: the proof inducts on the declarative derivation in §1 (paper:consistency-proofs.tex:2588), on Θ₀ in §2 (:2300), and on Θ₀|Ξ in §3 (:2443). Each has a witness where its measure does not decrease. UnivGhostR in §1 recurses on the identical derivation.
- **Mechanization**: one lexicographic measure μ = (V, n, t, k), where V is skeleton size as the solution sees it (fresco/algo/consis/prop_completeness_consis.v:21, :146-154). `complete_mu` is Qed.
- **Evidence**: `complete_mu`. The witnesses are in docs/DESIGN-completeness-measure.md (argument).
- **Ask for the authors**: State one well-founded measure, e.g. solution-normalised skeleton size, then |Θ₀|.
- **Source**: PG:2074

### G-09 thm:complete-consistency §1: the flexible cases are one sentence
- **Kind**: Proof-step gap · **Status**: LIVE
- **Paper**: paper:consistency-proofs.tex:2591-2592 ("handled by the other two parts"). The sentence hides two obligations. First, a bridge from a consistency solution to a unification/assignment solution. Second, recovering the precision `θ₁α̂ ⊑ Q`, which §2 and §3 do not conclude.
- **Mechanization**: `consis_complete_step` (fresco/algo/consis/prop_completeness_consis.v:7664), using `consis_refine_mono_tyequiv` and `tyequiv_mono_consis` (fresco/algo/prop_mono_bridge.v:204, :487).
- **Evidence**: `complete_mu` (Qed).
- **Ask for the authors**: Spell out the Flex, FlexL and FlexR cases, including the bridge and the precision step.
- **Source**: PG:2122

### G-10 thm:complete-consistency §3: no proof that the assignment walk never gets stuck
- **Kind**: Proof-step gap · **Status**: LIVE
- **Paper**: paper:consistency-proofs.tex:2443-2585. The skip cases are dismissed with "follows from IH and context weakening" (:2581). No rule covers a rigid head β ∈ ftv P. Assign-SolveM's occurs check, and the fact that guess^TY returns a monotype, are assumed.
- **Mechanization**: `assign_complete_step` (fresco/algo/consis/prop_completeness_consis.v:4528) uses `ad_pat_consis_rigid_ftv_rev_scoped` (:2211). The unscoped version of that lemma is false.
- **Evidence**: `complete_mu` (Qed).
- **Ask for the authors**: Add the escape/scope argument for the rigid-head case, and discharge Assign-SolveM's premises.
- **Source**: PG:2139

### G-11 lemma:precision-substitution's motive must be generalised
- **Kind**: Proof-step gap · **Status**: LIVE
- **Paper**: paper:subtyping-proofs.tex:1666-1694 ("a straightforward induction … would not result in any type mismatch"). Three things go wrong. ForallL on ψa's own quantifier escapes the motive `S[ψa/α]`. Height preservation needs fuel at rule granularity. The tag-context residual must be pinned.
- **Mechanization**: decorated subject precision ⊑ᵤ (`uskl_precise`, fresco/algo/consis/prop_consis_precise.v:470). The result is `ad_pat_sub_precise_upre_fuel` (fresco/algo/sub/prop_completeness_sub_precise.v:1537).
- **Evidence**: Qed.
- **Ask for the authors**: Use the generalised motive, or at least name the ForallL-on-ψa case.
- **Source**: PG:2280

### G-12 The -var lemma's ForallInh/ForallSyn subcases (P_i = □, ∀◇) break Δ bookkeeping
- **Kind**: Proof-step gap · **Status**: LIVE (the statement is true)
- **Paper**: lemma:complete-consistency-constraint-collection-solving-var (paper:consistency-proofs.tex:1187), at :1328-1347 and :1392-1411. The IH can only run at Δ, but the ∀-precision rule needs the result at Δ,β. Getting there would need Δ-weakening, which is not admissible.
- **Mechanization**: `a_solve_eq_complete_var_gen` (fresco/algo/sub/look/prop_eq_var.v:514) puts the refinement at Δr, the descent binders. The silent "removing β as necessary" becomes `ad_partial_precise_rename_tvar` (:111).
- **Evidence**: `a_solve_eq_complete_var` (:3401, Qed).
- **Ask for the authors**: Generalise the refinement premise to Δ_r ⊇ the descent binders, or supply the transport argument.
- **Source**: PG:2449

### G-13 P6-Sv's UnivGhostLG case omits the P_i = □ subcase
- **Kind**: Proof-step gap · **Status**: LIVE (the statement is true)
- **Paper**: paper:subtyping-proofs.tex:2190-2207 ("P_i must have a top-level ∀◇"). P-Ghost ignores the target's shape, so P_i = □ is possible. The consistency twin does list □.
- **Mechanization**: the □ row is in fresco/algo/sub/look/prop_sub_var.v (lemmas at :85-:164). The flexible P_i case is vacuous (`ad_ppre_mono_paint_dot_univ_ghost_absurd`, prop_solve_ext.v:1536).
- **Evidence**: `a_solve_sub_complete_var` (prop_sub_var.v:1336, Qed).
- **Ask for the authors**: Write "P_i is □ or ∀◇P_i′" and add the □ subcase.
- **Source**: PG:2769

### G-14 P6-Ss's ForallL step needs θψ_b = ψ_b, which fails for legitimate θ
- **Kind**: Proof-step gap · **Status**: LIVE (the theorem is true)
- **Paper**: lemma:complete-constraint-collection-solving (paper:subtyping-proofs.tex:2213), ForallL case at :2590-2660. The step at :2617-2626 needs `θ(S′[ψ_b/β]) = (θS′)[ψ_b/β]`.
- **Mechanization**: the induction is generalised over an accumulated rigid substitution ρ: `a_looksub_solve_complete_gen` (fresco/algo/sub/look/prop_sub_cstr.v:827). P6-Cs is generalised the same way.
- **Evidence**: cex/cex_p6ss_inc_compat.v (`id_inc_dom_overlap`, `def_subst_theta_is_legit`; Qed). It shows that no side condition on θ repairs the step.
- **Ask for the authors**: Redo ForallL with a ρ-generalised IH (absorb `[ψ_b/β]` into ρ at a fresh rigid β), or restrict the lemma to ι-like θ.
- **Source**: PG:2929

### G-15 AbsCheck proof: the shape enumeration misses rigid variables and flex chains
- **Kind**: Proof-step gap · **Status**: LIVE
- **Paper**: paper:proofs.tex:839-840 and :1075-1076 ("the only possible shapes are ∀ᾱ.A′→B′ and ∀ᾱ.α̂").
- **Mechanization**: the rigid case is refuted by `refine_var_arrow_flex_def` (fresco/algo/typing/prop_completeness_typing.v:2945) and `a_split_rigid_var_absurd` (fresco/algo/typing/prop_rigidity.v:703). For flex chains, `mono_refine_arrow_inv` (prop_completeness_typing.v:2900) gives `θα̂ ≡ τ1→τ2`.
- **Evidence**: Qed.
- **Ask for the authors**: Add the rigid-variable exclusion. Say that θα̂ is an arrow only up to ≡.
- **Source**: PG:4154 (:4170)

### G-16 AbsCheck subcase 2 extends θ with non-monotype images
- **Kind**: Proof-step gap · **Status**: LIVE
- **Paper**: paper:proofs.tex:916-917 ("extending θ with β̂↦A and γ̂↦B"), and the same at :1169-1170. Images must be monotypes (paper:algorithmic.tex:123-126).
- **Mechanization**: θ is extended with the τ1 and τ2 from `mono_refine_arrow_inv`. `τ1 ≡ A` and `τ2 ≡ B` are recovered via `ad_refine_syn_inh_tyequiv`.
- **Evidence**: `a_typing_complete` (Qed).
- **Ask for the authors**: Use the monotype decomposition of θα̂ as the witness, and state the two equivalences as obligations.
- **Source**: PG:4154 (:4195)

### G-17 Skeleton-inference completeness uses three unstated facts
- **Kind**: Missing lemma · **Status**: LIVE
- **Paper**: paper:proofs.tex:2006 ("consistency of syn{A} with bid{A}"), :1915 ("reflexivity of context precision"), and ⟨27⟩ ≈:1927 (θ′ extends to binder-extended contexts).
- **Mechanization**: `ad_pat_consis_syn_bid`, `ad_ctx_precise_refl` and `a_inc_id_msubst_unique` (fresco/algo/pat/prop_completeness_pat.v:1601, :1330, :920).
- **Evidence**: Qed.
- **Ask for the authors**: State the three facts as lemmas. Precision reflexivity needs context payloads that are fully well-formed skeletons, not just in scope.
- **Source**: PG:969 (items 2–3)

### G-18 `guess^TY`'s refinement property is used as if it were definitional
- **Kind**: Missing lemma · **Status**: LIVE
- **Paper**: thm:sound-type-inference, Abs case (paper:proofs.tex:454).
- **Mechanization**: `a_guess_mono_refine` (fresco/algo/typing/prop_soundness_typing.v:845, Qed). It needs a Δ parameter, and `⫯.P` is dropped.
- **Evidence**: Qed.
- **Ask for the authors**: State it as a lemma, with Δ.
- **Source**: PG:1225 (item 2)

### G-19 "Preservation of refinement under type equivalence" is asserted but never stated
- **Kind**: Missing lemma · **Status**: LIVE
- **Paper**: thm:sound-skeleton-inference, AbsAnno case (paper:proofs.tex:1578). The Freeze case of thm:sound-type-inference also uses it.
- **Mechanization**: `a_consis_chk_annot_refine` (fresco/algo/pat/prop_soundness_pat.v:1727, Qed). It decouples the consistency context from the refinement Δ.
- **Evidence**: Qed (`a_pat_sound`).
- **Ask for the authors**: State the lemma (in the refinement-target or the ≡ form) and derive the other form from it.
- **Source**: PG:1288

### G-20 AbsCheck subcase 2: split completeness and scope preservation are unstated lemmas
- **Kind**: Missing lemma · **Status**: LIVE
- **Paper**: paper:proofs.tex:902-913 and :1155-1166 ("Assuming fresh β̂, γ̂, we have ⑬"; "well-scoped at the positions").
- **Mechanization**: `a_split_complete_tc` (fresco/algo/typing/prop_completeness_typing.v:2977). Scope: fresco/algo/typing/prop_scope.v (`a_typing_scope_tvar_nil` :2296, `_tm_nil` :2308).
- **Evidence**: Qed.
- **Ask for the authors**: State split completeness at TC and the scope invariant as lemmas.
- **Source**: PG:4154 (:4219)

### G-21 Decidability is implied by the paper's motivation but never proved
- **Kind**: Missing lemma · **Status**: LIVE
- **Paper**: there is no termination or decidability statement. The motivation is set against undecidability results (paper:overview.tex:80, introduction.tex:463, declarative.tex:852).
- **Mechanization**: termination lemmas `e_sub_order_total` and `e_consis_order_total` (fresco/ext_algo/prop_termination.v:1708, :1430). Deciders `e_typing_dec` and `d_typing_infer_dec` (fresco/ext_algo/prop_run_corollaries.v:226, :515). `fresco_infer` is in README.v. The old caveat "negative branch stops at e_typing" is outdated, closed by `a_typing_rel_e`.
- **Evidence**: README.v `Print Assumptions` closed.
- **Ask for the authors**: State termination/decidability as a theorem with a measure sketch:
  - instantiations are bounded by the inherited skeleton;
  - `nall P₁ ≤ nall P₀`;
  - the head ∀-chain shrinks at SI-ForallL.
- **Source**: PG:4267

---

## B. Live — for the authors: missing side conditions / ambiguity in the rules

### G-22 Collection: a leaked ∀-opener may collide with a flexible variable invented elsewhere
- **Kind**: Missing side condition · **Status**: LIVE (f484dde3 did not touch these rows)
- **Paper**: LS-Arrow and LE-Arrow run both halves at one context (paper:full-algo-spec.tex:1065-1071, :1127-1133). The Look/extract step has the same problem (:1001-1008). LS-ForallR, LE-ForallInh and LE-UnivGhost* leak openers into 𝒞, while LE-FlexR, SolE-FlexR and the final guess draw names fresh only for their own context.
- **Mechanization**: `ftv 𝒞₁ ∩ dom Ξ₂ = ∅` plus its mirror on `a_looksub__arrow` and `a_lookeq__arrow` (fresco/algo/def_rules.v:659-692, :744-747). Two guards on `a_extract__solve` (:1098-1140). All are theorems in ext_algo (`e_looksub_lookeq_cstr_old`, fresco/ext_algo/prop_look.v:199; `e_guess_block_fresh`, prop_guess.v:195).
- **Evidence**: cex/probe_extract_conflated_opener.v (`probe_cross_half_guard_is_necessary`, `probe_fold_stuck_deconflated`; Qed).
- **Ask for the authors**: Add the cross-half condition to both arrow rows, or state once that all invented names come from one global supply. The implementation's `counter` (impl:type.ml:588) already does this.
- **Source**: PG:40, PG:4439

### G-23 Collection ∀-rows lack the absence-first guard `α ∈ ftv(subject)`
- **Kind**: Ambiguity / non-determinism · **Status**: LIVE
- **Paper**: LS-ForallR / LS-ForallL (paper:full-algo-spec.tex:1057, :1073) and LE-ForallInh / LE-ForallSyn / LE-UnivGhost1 (:1135, :1142, :1156) do not exclude LS/LE-Absent (:1029, :1098). Only LE-FlexR (:1117) has the guard.
- **Mechanization**: the guard is on five rows (fresco/algo/def_rules.v:651, :698, :755, :763, :774) and is admissible (`a_looksub_forall_r_adm`, fresco/algo/sub/prop_looksub.v:477).
- **Evidence**: `e_looksub_lookeq_absent_pins` (fresco/ext_algo/prop_look.v:264, Qed). The refutations were deleted when the guard landed (eabf308).
- **Ask for the authors**: Add `α ∈ ftv(subject)` to the five rows. It rejects no answer, only a derivation that wastes a name. The implementation tests Absent first (impl:type.ml:579, :680).
- **Source**: PG:117

### G-24 U-FlexL/U-FlexR overlap U-GhostR/U-Ghost at a ◇–flexible cell
- **Kind**: Ambiguity / non-determinism · **Status**: LIVE
- **Paper**: U-FlexL / U-FlexR carry only `nonflex` (paper:algorithmic.tex:755-767; full-algo-spec.tex:1665-1679). At pattern ◇ and subject α̂, U-GhostR keeps Θ while U-FlexL solves α̂ to a fresh β̂.
- **Mechanization**: `P0 <> pskl_ghost` / `P <> pskl_ghost` on `a_consis__flex_l/_r` (fresco/algo/def_rules.v:1477-1486). The decorated twins `a_consistag__flex_l/_r` carry it too since the 2026-10-10 rule pass (the paper's decorated rules are inherited unchanged).
- **Evidence**: cex/probe_inc_more_general.v shows the two answers are equally general, so nothing is lost for soundness or optimality. cex/probe_consis_ghost_flex.v and cex/probe_pat_presents_hole_flex.v show the cell is reachable. All are Qed.
- **Ask for the authors**: Add `P₀ ≠ ◇` / `P ≠ ◇`, or state the rule priority. This matches `join_sk`'s ghost-first arms (impl:type.ml:146-154). It is a determinism fix, not a soundness fix.
- **Source**: PG:230, PG:4382

### G-25 SI-Ghost lacks `M ≠ TI`
- **Kind**: Missing side condition · **Status**: LIVE
- **Paper**: SI-Ghost is an axiom at every M (paper:full-algo-spec.tex:849-853). Its neighbour SI-UnivGhostL (:855-860) has `M ≠ TI`.
- **Mechanization**: `M <> mode_ti` on `a_sub__ghost` (fresco/algo/def_rules.v:1637-1639).
- **Evidence**: cex/probe_sub_ghost_ti.v now proves only that the guarded rule does not derive the bad judgement. That the paper's rule derives it rests on argument and on the implementation, which matches only `Fun _ | Check _` (impl:type.ml:1007-1011).
- **Ask for the authors**: Add `M ≠ TI`. Better, make `P₀ = sk_of_mode(M)` a standing invariant, because the bad cell also arises one arrow down.
- **Source**: PG:293

### G-26 SolS-ForallR / SolS-Vacuous lack match-order exclusions
- **Kind**: Ambiguity / non-determinism · **Status**: LIVE
- **Paper**: SolS-Vacuous (paper:full-algo-spec.tex:1272) and SolS-ForallR (:1283-1287) exclude no subject. They overlap SolS-Var / SolS-ForallL, and the two derivations differ by one spent opener.
- **Mechanization**: `peel_l_off` and `solve_l_off` premises (fresco/algo/def_rules.v:868-873, :886-902; fresco/def_shapes.v:394-397).
- **Evidence**: argument only. The refutation was deleted on repair (5e2384f).
- **Ask for the authors**: Mirror `solve_sub`'s order (impl:type.ml:510-560): SolS-ForallR's subject is not a variable, a ∀ or a ⫯, and SolS-Vacuous's subject is not a ∀ or a ⫯. See G-54 for SolS-ForallR's subject sort.
- **Source**: PG:398

### G-27 LE-UnivGhost2 overlaps LE-FlexR at a flexible counterpart
- **Kind**: Ambiguity / non-determinism · **Status**: LIVE
- **Paper**: LE-UnivGhost2 (paper:full-algo-spec.tex:1163-1169) requires only `guarded{P′}`, and a flexible β̂ is guarded. LE-FlexR (:1117-1123) fires on the same cell, and the two answers differ in both block and constraints.
- **Mechanization**: `flex_r_off Θ P'` on `a_lookeq__univ_ghost2` (fresco/algo/def_rules.v:779-786).
- **Evidence**: argument only. The probes were deleted on repair (2e50ba4).
- **Ask for the authors**: Add "P′ is not a flexible variable" to LE-UnivGhost2. This matches `constr_collect_eq`, which tries LE-FlexR first (impl:type.ml:585-650).
- **Source**: PG:458

### G-28 LS-ForallL lacks the ForallR-priority guard, so collection is not deterministic
- **Kind**: Ambiguity / non-determinism · **Status**: LIVE
- **Paper**: LS-ForallL and LS-UnivGhostL (paper:full-algo-spec.tex:1073-1087) have no guard, unlike SI-ForallL (:835-847). At subject `∀_.α`, target `∀_.1`, mode TC, the two derivations collect different closed constraints.
- **Mechanization**: `forall_r_off m P'` on `a_looksub__forall_l` and `__univ_ghost_l` (fresco/algo/def_rules.v:695-716). Lemma E.17 needed the guard at five sites.
- **Evidence**: argument only. `cex_looksub_not_det.v` was deleted on repair (c97869e).
- **Ask for the authors**: Add "LS-ForallR does not apply" and redo Lemma E.17's ForallR/ForallL/UnivGhostL steps. Otherwise, stop speaking of *the* collected constraints. The implementation tries LS-ForallR first (impl:type.ml:692).
- **Source**: PG:577

### G-29 The repaired SolE-FlexR still lacks `nonghost{P}` and overlaps SolE-GhostL
- **Kind**: Missing side condition (ambiguity) · **Status**: LIVE
- **Paper**: SolE-FlexR (paper:full-algo-spec.tex:1388-1393) has only `nonflex{P}`, and `\nonflex` means just "non-flex" (macro.tex:625). At `◇ ∼ α̂`, SolE-GhostL (:1328) returns α̂, while SolE-FlexR returns a fresh α̂₁. The -var lemmas' P_i = □ subcases silently assume the first answer.
- **Mechanization**: `nonghost_pskl P` on `a_solve_eq__flex_r` (fresco/algo/def_rules.v:997). `a_solve_eq_ghost_subject_inv` (fresco/algo/sub/look/prop_rsubst.v:876) depends on it.
- **Evidence**: argument. The implementation matches the ghost rows first (impl:type.ml:411-470).
- **Ask for the authors**: Add `nonghost(P)` to SolE-FlexR, or define non-flex to exclude ◇ and ∀◇.
- **Source**: PG:3844 (:3883); docs/refutations.tex §status ¶3

### G-30 The suffix-discarding check rows need `uniq(Ξ,Θ)` and "Ξ ∉ result"
- **Kind**: Missing side condition · **Status**: LIVE
- **Paper**: TI-AbsCheck and TI-AbsAnnoCheck (paper:full-algo-spec.tex:348-367) drop the body's suffix Ξ. The appeal to suffix-erasure assumes Ξ is fresh and absent from the result.
- **Mechanization**: both conditions are premises on the four `a_typing__abs{,_anno}_check_{step,base}` rows (fresco/algo/def_rules.v:1931-1985). Completeness discharges them via fresco/algo/typing/prop_scope.v.
- **Evidence**: argument (neither condition is derivable). `a_typing_sound` and `a_typing_complete` are Qed with them.
- **Ask for the authors**: State both conditions on the four rows, or say in prose that a checking body's suffix is fresh for the result.
- **Source**: PG:3963

### G-31 TI-Abs must require `uniq(ᾱ, Θ₁)` on guess^TY's block
- **Kind**: Missing side condition · **Status**: LIVE
- **Paper**: TI-Abs (paper:full-algo-spec.tex:329-336). guess^TY's arrow row draws both halves at one Θ, so ᾱ may repeat.
- **Mechanization**: `uniq (αs ++ Θ1)` on `a_typing__abs` (fresco/algo/def_rules.v:1854). ext_algo derives it.
- **Evidence**: argument.
- **Ask for the authors**: Add the premise, or say that guess^TY's blocks are globally fresh (see also G-22).
- **Source**: PG:3963 (:4002)

### G-32 TI-AbsAnnoCheck's result domain should be the split's A′
- **Kind**: Missing side condition (rule correction) · **Status**: LIVE
- **Paper**: paper:full-algo-spec.tex:358-367 concludes `∀ᾱ.A→B` from `A′ ∼ A`. Soundness would need `inh⌈A′⌉ ⊳ ⌈A⌉`, but consistency transports the other way.
- **Mechanization**: `a_typing__abs_anno_check_base` concludes `A' → B1` (fresco/algo/def_rules.v:1965-1985).
- **Evidence**: argument. `a_typing_sound` is Qed with this form.
- **Ask for the authors**: Conclude `∀ᾱ.A′→B`, or flip the premise to `A ∼ A′`.
- **Source**: PG:3963 (:4013)

### G-33 sd-App needs the appendix's fourth type-equivalence premise
- **Kind**: Missing side condition · **Status**: LIVE
- **Paper**: paper:full-algo-spec.tex:117 says only freezing and the annotated lambdas need ≡. The AT-App step of the soundness proof needs it for App too (paper:proofs.tex:601).
- **Mechanization**: `Θ ⊢ B1 ≡ᵗ A2` on `ad_sd_typing__app` (fresco/algo_decl/def_typing.v:251-270).
- **Evidence**: `a_typing_sound` (Qed).
- **Ask for the authors**: Add `Θ ⊢ A ≡ A′` to sd-App, or prove that typing transports along ≡ at TC.
- **Source**: PG:1225 (item 1)

### G-34 ForallL's "`Ψ′` fresh" must mean global freshness, including the subject's tags
- **Kind**: Ambiguity / non-determinism (wording) · **Status**: LIVE for the paper (its wording is unchanged); settled in the mechanization
- **Paper**: Sub-ForallL (paper:declarative.tex:1018, :1938; prose :1115 "unique and fresh"). Under the local reading, lemma:precision-substitution (paper:subtyping-proofs.tex:1667-1683) is false, because Arrow splits Ψ and so lets a tag be reused.
- **Mechanization**: `Ψ' ∩ Ψ = ∅` and `Ψ' ∩ ftag(subject) = ∅` in all four subtyping judgements (fresco/decl/def_rules.v:421, :436; fresco/algo_decl/def_subtyping.v:91-102). CST goes through `d_sub_tagsin` / `d_sub_freshen` (fresco/decl/prop_tag_swap.v).
- **Evidence**: argument only.
- **Ask for the authors**: Say that Ψ′ is fresh for the tag context and for every tag in the subject.
- **Note**: PG:746's header reads "RESOLVED". That refers to the mechanization only.
- **Source**: PG:746, PG:2251

### G-35 Information increase's flex rule admits a θ that moves a surviving α̂
- **Kind**: Ambiguity / non-determinism (definition) · **Status**: LIVE (low priority; no theorem depends on it)
- **Paper**: the flex rule of ⊑ (paper:algorithmic.tex:96-101) requires only `Θ′ ⊢ τ`, so `[(α̂,⟨⟩)] ∷ [α̂] ⊑ [α̂]` is derivable.
- **Mechanization**: `a_inc` stays faithful to the paper. The ρ-route of G-14 does not need the invariant.
- **Evidence**: cex/cex_p6ss_inc_compat.v `inc_moves_survivor` (Qed).
- **Ask for the authors**: Decide whether to require `α̂ ∈ dom Θ′ ⟹ Θ′ ⊢ θα̂ ≡ α̂`.
- **Source**: PG:2929 (:2985)

---

## C. Live — for the authors: prose completions and well-formedness presuppositions ("state it")

### G-36 Skeleton consistency presupposes refinement; this is load-bearing and stated only in prose
- **Kind**: Prose completion (not derivable from the rules) · **Status**: LIVE
- **Paper**: paper:declarative.tex:2071-2073 ("requires … the refinement judgement Γ ⊢ ⌊S⌋ ⊳ P"). It is absent from the consistency figure (:1966-2045), and the counterpart wf presupposition (:1593-1596) is also only in prose.
- **Mechanization**: the join `d_consis_join` / `ad_consis_join` (fresco/algo_decl/def_consis_refine.v:254) is the premise of every consistency leaf of `d_pat_sub` / `ad_pat_sub` and their `_fuel` twins. `d_pat_to_ad` is hypothesis-free. The closed completeness corollaries are stated over the paper's `⊢ˢ` and `⊢` (`a_typing_complete_sd_infer`, fresco/algo/typing/prop_closed.v:298).
- **Evidence**: cex/cex_ad_pat_join_not_leaf_valid.v (`cap_consis`: the rules derive `∀X.◇ ∼ ∀ˢX.X`; `cap_no_refine`) and cex/cex_d_pat_bridges_false.v (`cap_d_pat_excluded`). Root placement is refuted by cex_p7_univ_ghost_r_vacuous.v and cex_p7_third_premise_forall.v. All compile.
- **Ask for the authors**: Put the presupposition into the figures at the consistency leaves, not at the root (ghost-capture.tex (R-a)), or index consistency by Δ ((R-b)). Without it the rules type `x:∀α.◇ ⊢ x ⦂ ∀ˢα.α`, which no run produces.
- **Source**: PG:1066 (supersedes PG:1121); WF:138-208; docs/ghost-capture.tex

### G-37 "It is easy to extend them" (declarative rules in algorithmic contexts) is a conservativity lemma
- **Kind**: Prose completion · **Status**: LIVE. PG:848's "holds in one direction only" is outdated: both directions now hold.
- **Paper**: paper:full-algo-spec.tex:97-115.
- **Mechanization**: fresco/algo_decl/prop_conserv.v (`ad_pat_to_d` :962, `ad_sd_typing_to_d` :1012, `d_pat_to_ad` :1515, `d_sd_typing_to_ad` :1569).
- **Evidence**: Qed.
- **Ask for the authors**: State the lemma: for a flexible-free Θ, the ad judgement equals the d judgement, and ≡ collapses to =. Note that the soundness corollary closes the output context with `ζ ∷ Θ₁ ⊑ ·`.
- **Source**: PG:848

### G-38 Completeness proofs assume annotations are rigid (flexible-free)
- **Kind**: Prose completion · **Status**: LIVE
- **Paper**: paper:proofs.tex:680 ("annotations A contain no flexible variables"). P-Anno (:1761-1773) gives no argument, and the problem definition (paper:algorithmic.tex:392) gives only scope.
- **Mechanization**: a rigidity premise on the completeness theorems (`msubst_ptyp_rigid_id`, fresco/algo/pat/prop_completeness_pat.v:354). `a_typing_tc_rigid_output` (fresco/algo/typing/prop_rigidity.v:1072) shows the premise cannot be weakened.
- **Evidence**: Qed.
- **Ask for the authors**: Put "annotations mention only rigid variables of Θ₀" into the problem/theorem statements, and give the P-Anno argument.
- **Source**: PG:969 (item 1)

### G-39 Sort-by-metavariable discipline; the two figures disagree on SI-ForallR's subject
- **Kind**: Prose completion (+ ambiguity) · **Status**: LIVE
- **Paper**: SI-Check `guarded{A,B}` (paper:full-algo-spec.tex:799-804). SI-ForallR writes the subject as `A` (:806-811), but the decorated mirror writes `S` (paper:decorated-algosub.tex:62-66). LS-Check and LS-ForallR write `A` and `B` (full-algo-spec.tex:1047-1062).
- **Mechanization**: `pskl_ghost_free` premises (fresco/algo/def_rules.v:1544, :1555, :625, :646, :881, :896, :940). The LS subject sort is deliberately not imposed, because the structural lemmas are mode-agnostic.
- **Evidence**: both directions of subtyping are Qed with these premises.
- **Ask for the authors**: Say that A and B positions are ghost-free, and reconcile SI-ForallR's subject sort across the two figures.
- **Source**: PG:1399 (points 1, 3). Point 2 is G-54.

### G-40 Completeness of subtyping: the subject must be ghost-free at the TY sort
- **Kind**: Prose completion (external sort condition) · **Status**: LIVE
- **Paper**: thm:complete-subtyping (paper:algorithmic.tex:1455). The problem `(Θ₀;N;M;P₀;P)` does not sort P by N.
- **Mechanization**: `NM = TY -> uskl_ghost_free R'` on `a_sub_complete` (fresco/algo/sub/prop_completeness_sub.v:1209-1212). It cannot be derived from the join, because `__arrow`'s domain and `__infer` accept ghosts.
- **Evidence**: argument.
- **Ask for the authors**: State that at N = TY the problem's P is a type. This is G-39's discipline applied to the theorem.
- **Source**: WF:586-630

### G-41 Skeleton inference's base rows need counterpart wf; no output-wf theorem is stated
- **Kind**: Prose completion + Missing lemma · **Status**: LIVE
- **Paper**: "wf of M and bid{P}, as well as skmod" (paper:declarative.tex:1593-1596) is stated per judgement. P-Unit, P-Var and P-Anno (:1630-1650) carry neither. lemma:context-precision-skeleton (paper:proofs.tex:128) and the Sub case use precision at base leaves, which needs `Θ ⊢ ⌊Q⌋`. The paper never proves that algorithmic outputs are well-formed.
- **Mechanization**: `⊢ₚₛ ⌊Q⌋` (the counterpart's wf) on `d_pat__unit/__var/__anno` and `ad_pat__unit/__var/__anno`; since the 2026-10-10 rule pass P-Anno no longer carries the annotation's `⊢ₚ A`, matching the paper (fresco/algo_decl/def_typing.v:90-119). Output-wf theorems `a_consis_output_wf` and `a_sub_output_wf` (fresco/algo/prop_wf_preservation.v:114, :1001).
- **Evidence**: `ad_refine_syn_output_not_wf` (cex/cex_refine_not_transitive.v:125) shows that wf cannot be propagated top-down past P-App.
- **Ask for the authors**: Say that the presupposition holds at every sub-derivation, or put it on the base rules. Add the output-wf lemma for consistency and for subtyping.
- **Source**: PG:4052; WF:229-240

### G-42 The subtyping solution needs the counterpart well-formed in the solution context
- **Kind**: Prose completion · **Status**: LIVE (minor)
- **Paper**: thm:complete-subtyping's Check case (paper:subtyping-proofs.tex:~3180-3200). The solution definition (paper:full-algo-spec.tex:1400-1413) does not require `Θ₁ ⊢ P₁`.
- **Mechanization**: `Θ ⨟ ∅ ⊢ₚₛ ⌊Q⌋` on `a_sub_complete` (fresco/algo/sub/prop_completeness_sub.v:1208) and on `a_sub_complete_check` (fresco/algo/sub/prop_completeness_sub_gen.v:1113). It is consumed by `ad_refine_syn_trans`.
- **Evidence**: argument. Since 2026-10-08 the Ghost rule no longer checks its fill, so wf is not free even at P₀ = ◇.
- **Ask for the authors**: Add "P₁ well-formed in Θ₁" to the subtyping and consistency solution notions.
- **Source**: PG:3321; WF:557-584

### G-43 P6-Cs needs ψa scoped and the consistency subject well-formed
- **Kind**: Prose completion · **Status**: LIVE. Without the subject-wf condition the lemma is false as stated (machine-checked).
- **Paper**: lemma:complete-consistency-constraint-collection-solving (paper:consistency-proofs.tex:921). No wf is stated for ψa or for the subject `κS[ψa/α]`.
- **Mechanization**: `ftvar_in_uskl ψa [<=] dom Θ` and `Θ ⨟ ∅ ⊢ₚₛ ⌊(κS)[ψa/α]⌋` on `a_lookeq_solve_complete` (fresco/algo/sub/look/prop_eq_cstr.v:5201, premises ~:5235, ~:5243). The first follows from the SolE-FlexR repair, because guess payloads must be scoped.
- **Evidence**: cex/cex_p6cs_subject_wf.v `p6cs_without_subject_wf_is_false` and `p6cs_fires_when_the_subject_is_wf` (Qed; the subject is ∀◇(∀◈⟨⟩)). The ψa condition rests on argument.
- **Ask for the authors**: Add both to the lemma's premises, as instances of "all inputs well-formed".
- **Source**: WF:492-555. README.v:220 says this is in PAPER-GAPS.md, but it is not (see G-58).

### G-44 P6's "same rigid variable in the same position" is rendered as freshness
- **Kind**: Prose completion · **Status**: LIVE
- **Paper**: paper:consistency-proofs.tex:1215-1217 and paper:subtyping-proofs.tex:1732. A WT comment there says the property holds by construction.
- **Mechanization**: there is no positional predicate. `a_solve_eq_complete_var` (fresco/algo/sub/look/prop_eq_var.v:3401) carries a freshness pack instead (`rsubst_fresh Δρ Θ κ`, `Δρ ⊆ Δ`, `delta_def_fresh Δ Θ`). The positional fact is recovered by `ad_ppre_delta_var_inv` (fresco/algo/sub/look/prop_rsubst.v:369). P6-Sv's `pskl_shielded_ftv` condition (fresco/algo/sub/look/prop_sub_var.v:695, :809) has not been compared with the paper's wording.
- **Evidence**: argument. The v4/v5 counterexamples have no file. cex_p6cs_rsubst_delta_vacuous.v shows that the stronger `Δρ ∩ dom Θ₀ = ∅` is vacuous.
- **Ask for the authors**: State the positional condition formally, or replace it with the freshness facts it stands for.
- **Source**: WF:283-309; fresco/algo/sub/look/prop_rsubst.v:31-45, :363

### G-45 Information increase's flex-def rule lacks the θ-image wf condition
- **Kind**: Prose completion · **Status**: LIVE (minor; the prose states it)
- **Paper**: the rule at paper:full-algo-spec.tex:31-35 has only `Θ′ ⊢ τ′ ≡ θτ`. The prose at paper:algorithmic.tex:123-126 says "well-formed monotypes in Θ′".
- **Mechanization**: `a_wf_ptyp Θ' τ'` and `mono_ptyp τ'` on `a_inc__flex_def` (fresco/algo/def_meta.v:222-229).
- **Evidence**: argument (lookup stability fails without it).
- **Ask for the authors**: Put `Θ′ ⊢ τ′` (monotype) on the rule in the figure.
- **Source**: PG:1468

### G-46 Identity metasubstitutions must preserve flexible entries
- **Kind**: Prose completion · **Status**: LIVE (minor; the prose states it)
- **Paper**: paper:algorithmic.tex:135-137 (prose only).
- **Mechanization**: `a_isub`'s second component (fresco/algo/def_meta.v:264).
- **Evidence**: argument.
- **Ask for the authors**: Define `⊑ι` formally with the preservation clause.
- **Source**: PG:1478

### G-47 Well-formedness presuppositions the paper already states, carried as hypotheses (informational)
- **Kind**: Prose completion · **Status**: LIVE, informational; nothing is missing from the paper
- **Paper**:
  - refinement presupposes wf of both sides (paper:declarative.tex:1424);
  - precision is refinement, so the same holds for the target in lemma:precision-sub (paper:proofs.tex:70);
  - all algorithmic inputs are well-formed (paper:algorithmic.tex:233, :915; paper:full-algo-spec.tex:1478);
  - a solution maps into well-formed monotypes of Θ′ (paper:algorithmic.tex:123-126).
- **Mechanization**: these are hypotheses on lemma statements, not rule premises. Examples: `ad_refine_syn_trans`, `ad_precise_extends_pat_sub` (fresco/algo/sub/prop_completeness_sub_precise.v:1848), `a_sub_sound`, and `a_consis_complete` (`⊢ Θ` of the competing target, :8121).
- **Evidence**: `ad_refine_syn_output_not_wf` (cex/cex_refine_not_transitive.v:125). The refinement rules alone derive `∀◇(□→□) ⊳ ∀α.∀◇(α→α)`, whose output is ill-formed, so the presupposition filters derivations.
- **Ask for the authors**: none. Optionally say that the refinement presupposition is load-bearing.
- **Note**: PG:1793's triage called this MOOT, and the WF-doc triage called it LIVE-informational. Both describe the same state.
- **Source**: PG:1793; WF:29-136, :242-281

---

## D. Open questions (UNCERTAIN) — what exactly needs checking

### G-48 SI-Check: does `\aconsis[B]{Θ₀}{A}{B}{Θ₁}` pin the consistency output to B?
- **Kind**: Ambiguity / non-determinism (likely a typesetting slip) · **Status**: UNCERTAIN
- **Paper**: SI-Check (paper:full-algo-spec.tex:799-804) and its decorated version (paper:decorated-algosub.tex:54-59). By macro.tex:1002-1016 the macro reads as input B, subject A, output B. The output-free abbreviation is at full-algo-spec.tex:1455-1457 (commented out at paper:algorithmic.tex:635-637). The proof's Check case (paper:subtyping-proofs.tex:3187-3192) produces a free output P₀′ and argues P₀′ ≡ P₀, which is the abbreviation reading.
- **Mechanization**: `a_sub__check` leaves the output free (fresco/algo/def_rules.v:1528). `a_subtag__check` argues that pinning it is unsound (fresco/deco_algo/def_decorated.v:214-235). The implementation returns the join's output (impl:type.ml:1021-1024).
- **To check**: whether SI-Check becomes underivable under the literal reading at `A = α̂→1, B = 1→1`, where U-FlexL returns α̂→1 (cf. `cex_consis`, cex/cex_p7_concrete_rhs.v). Also whether `A = α̂, B = ()` breaks. Neither is machine-checked.
- **Ask for the authors**: Say which reading is intended. If it is the abbreviation, drop `[B]` and restore the abbreviation's definition.
- **Source**: PG:3146; fresco/deco_algo/def_decorated.v:225-231

Other UNCERTAIN items: G-50 and G-51 (implementation) and G-54 (SolS-ForallR sort, ours to settle first).

---

## E. Reference implementation issues

### G-49 NEW: SI-Flex-Skip drops the term/lock binding it walks past, causing a crash
- **Kind**: Implementation issue · **Status**: LIVE (introduced by impl commit d10a4460)
- **Paper**: Flex-SkipTmVar re-attaches `x:P` (paper:full-algo-spec.tex:914-920). The mechanization's `a_sub_flex__skip_tm_var` does too (fresco/algo/def_rules.v:1704).
- **Implementation**: in `sub_flex`, the arm `| Marker | BVar _ | Lock _ -> … add_binding Marker` (impl:type.ml:1074-1078) pops a `BVar` or `Lock` and pushes back a `Marker`.
- **Evidence**: fresh build of d10a4460. `let f = fun x -> x 1` passes. These crash with `Failure("get_type_context: internal error")`:
  - `fun y -> fun f -> (fun z -> z) (f 1)`
  - `fun x -> fun y -> (fun z -> y) (x 1)`
  - `fun y -> fun x -> (fun z -> y) (x 1)`
  - `fun x -> (fun z -> x) (x 1)`

  The fix `| (Marker | BVar _ | Lock _) as bind -> … add_binding bind` makes all of them pass, and `test.sh` stays at 0/25 failures (verified in scratch builds).
- **Ask for the authors**: Apply that one-line fix.
- **Source**: new (2026-10-10), found while re-testing PG:2727 and PG:3395

### G-50 The old `broom_flex_poly` witness is now ACCEPTED, against the July decision
- **Kind**: Implementation issue · **Status**: UNCERTAIN
- **Paper**: Flex-SkipTmVar (paper:full-algo-spec.tex:914-920). The witness is `let g = fun f -> f (k args)` with `args : list (∀b.b→b)`.
- **Implementation**: the crash is fixed by d10a4460's new SI-Flex-Skip arm. A fresh build accepts the program (rc = 0). The stale 2026-10-08 binary still crashes.
- **Mechanization**: `a_sub_flex__skip_tm_var/_skl` (fresco/algo/def_rules.v:1704-1712). The mechanization's verdict on the witness has not been computed.
- **To check**: on 2026-07-28 the authors decided that the program "should be REJECTED". Either that decision, or the declarative analysis behind it, needs revisiting. Running the ext_algo runner on the witness would settle the mechanization's side.
- **Ask for the authors**: Should `fun f -> f (k args)` type? If not, the new path accepts too much.
- **Source**: PG:2727 (and :2690-2706)

### G-51 The implementation's `is_wf_` ignores the ∀◇ / Δ discipline
- **Kind**: Implementation issue · **Status**: UNCERTAIN
- **Paper**: SI-ForallL's `Θ₀,Ξ ⊢ P₁` (paper:full-algo-spec.tex:841) is the disciplined skeleton wf, which clears Δ under ∀◇.
- **Implementation**: `is_wf_` (impl:type.ml:50-63) treats `UGhost p` as `is_wf_ gamma p`, with no Δ and no guardedness. It is used at :988 for SI-ForallL.
- **Mechanization**: `a_sub__forall_l` takes the disciplined `(Ξ++Θ0) ⨟ ∅ ⊢ₚₛ P1`. Soundness needs it, because the conversion fails at `∀α.∀◇(α→α)`.
- **To check**: whether an instantiation that violates the discipline can actually reach SI-ForallL.
- **Ask for the authors**: Make `is_wf_` follow the ∀◇ rule, or argue that P₁ never contains a ∀◇ that captures a ∀-variable.
- **Source**: WF:326-395

### G-52 U-Flex-Flex-Assign passes `join_sk` its arguments swapped
- **Kind**: Implementation issue · **Status**: LIVE (still present at d10a4460; argued benign, not proved)
- **Paper**: Flex-Flex-Assign has subject α̂ and input β̂ (paper:full-algo-spec.tex:1732-1738). The mechanization follows the paper (fresco/algo/def_rules.v:1355-1357).
- **Implementation**: impl:type.ml:314-320 calls `join_sk (subst α̂) (subst β̂)`, but `join_sk` takes the input first (:146-182). U-Assign-Assign (:356-360) uses the paper's order.
- **Evidence**: argument. The swap is benign by mirror symmetry, since Δ₁ = Δ₂ = ∅ and Q is discarded. `a_consis_sym` was never mechanized.
- **Ask for the authors**: Swap the two arguments at impl:type.ml:317-318.
- **Source**: PG:1640, PG:1680

---

## F. Mechanization to-dos (ours, not the paper's)

### G-53 Restore the deleted paper lemma `a_looksub_lookeq_subst_stable` / `_rev`
- **Kind**: Mechanization to-do · **Status**: LIVE
- **What**: both directions of lemma:constraint-collection-stable-substitution (see G-05) were deleted as "unused" in efc8707 (2026-10-07). They still have "kept on purpose" banners at fresco/algo/sub/prop_looksub.v:680-745. The keep rule in CLAUDE.md (a paper lemma with no consumer) applies.
- **Dangling citations**: fresco/algo/sub/look/prop_sub_cstr.v:137 and :2299 (`a_looksub_subst_stable_rev`, "Qed"); fresco/deco_algo/prop_decorate_sub.v:2287 and :2463. The ForallL rows now use `a_looksub_lookeq_subst_gen_size` (prop_decorate_sub.v:2596).
- **Do**: restore both lemmas from efc8707^, with the Barendregt premise, then `make coq`.

### G-54 SolS-ForallR's left-hand `A`: a slip, or a real restriction?
- **Kind**: Mechanization to-do (ambiguity) · **Status**: UNCERTAIN
- **Paper**: SolS-ForallR (paper:full-algo-spec.tex:1283-1287) writes the left-hand side as `A`, a type.
- **Mechanization**: reads it as `P`, with no subject sort (fresco/algo/def_rules.v:886-902). The argument is that `◇ ≼TC ∀β.B` is reachable, because LS-Var emits `sub_TC(∀β.B)` while the pattern is still ◇, and SolS-GhostL needs a guarded B.
- **Implementation**: sides with the paper. impl:type.ml:535 guards the rule with `is_type a`, so `Ghost` vs `Check (∀…)` falls through to `UnifyError` (:559).
- **Do**: check whether that cell is reachable in the implementation. If it is, report an implementation incompleteness. Otherwise sort the mechanization's rule and re-prove. Then ask the authors.
- **Source**: PG:1399 (point 2)

### G-55 Decorated FlexL/FlexR now carry the `≠ ◇` guard
- **Kind**: Mechanization to-do · **Status**: DONE (2026-10-10 rule pass, `c76b344`)
- **What**: `a_consistag__flex_l/_r` (fresco/deco_algo/def_decorated.v) gained `P0 <> pskl_ghost` / `P <> pskl_ghost`, as the plain rules have (G-24). Decoration gets it from the plain rule; decorated soundness lost its ◇ cases.

### G-56 Rule-faithfulness pass (2026-10-10)
- **Kind**: Mechanization to-do · **Status**: DONE
- **Done** (merged, full build green): `d_sub__arg` / `d_pat_sub__arg` / `d_sub_tagsin__arg` → `__arrow`; the redundant `is_ityp` premise dropped from `d_sub__forall_r` and the `d_sd_typing` / `ad_sd_typing` ∀-step rows (now lemmas `d_sub_tc_is_ityp`, `d_sd_typing_tc_abs{,_anno}_is_ityp`); P-Anno's annotation wf dropped from `d_pat__anno` and `ad_pat__anno` (the sd-Anno prose completion stays on `ad_sd_typing__anno` only, PG:923); the Ghost fill-wf premise dropped from ALL five Ghost rows (decl and `ad`).
- **Consequence for statements**: `a_consis_complete` and P6-Cs / P6-Ss / P6-L now take the counterpart's wf `{{ Θ ⨟ empty ⊢ₚₛ ⌊Q⌋ }}a` — the paper's presupposition (WF-SIDE-CONDITIONS §2a). `a_sub_complete`, `a_pat_complete`, `a_typing_complete` and the closed corollaries are unchanged.
- **Also**: `a_scope_pskl` is no longer an inductive judgement; it is the Definition `lc_pskl P /\ (forall α, α ∈ ftv P -> a_binds_tvar α Θ)` (proved equivalent first), kept only where a proof genuinely has scoping and not the disciplined `a_wf_pskl` (the C-Arrow output inside consistency completeness).

### G-57 Register the P6-Cs subject-wf refutation in PAPER-GAPS.md
- **Kind**: Mechanization to-do · **Status**: LIVE
- **What**: README.v:220 says `cex_p6cs_subject_wf.v` is recorded in PAPER-GAPS.md, but it is only in WF-SIDE-CONDITIONS.md:512-555. Either add a PAPER-GAPS entry or fix README's pointer. The finding is G-43.

### G-58 Stale pointers and dead cex citations
- **Kind**: Mechanization to-do · **Status**: LIVE
- **Deleted cex files still cited**: these were removed when their guards landed (24917bb, ed58e48, 2e50ba4, c97869e, 5e2384f, eabf308):
  - `cex_looksub_not_det.v`
  - `probe_extract_supply_drift.v`
  - `probe_extract_flexr_ug2_drift.v`
  - `probe_solve_sub_forall_r_drift.v`
  - `probe_sub_supply_drift.v`
  - `probe_bcore_ug2_flexr.v`

  They are cited at:
  - fresco/def_shapes.v:344, :389
  - fresco/ext_algo/def_look.v:50-51
  - prop_sub_complete.v:40-42
  - prop_extract_det.v:47-49, :2266
  - prop_look.v:258
  - prop_look_pair.v:10, :71
  - PAPER-GAPS.md:458 and other sections
- **Renamed or gone, still cited in PAPER-GAPS.md**:
  - `probe_pat_presents_ghost_flex.v` is now `…_hole_flex.v` (PG:230).
  - `alpha_stack_looksub` (PG:577) is retired.
  - `cex_p7_shield_double_occ.v` and `probe_double_occ_run.v` are gone.
  - `e_extract_solve_guard` (PG:4439) is gone.
  - `fresco/algo/prop_sub_concrete_rhs.v` is now `cex/probe_sub_concrete_rhs.v` (PG:3090).
  - `ad_pat_sub_strip_suffix` is now `ad_pat_sub_fuel_strip_suffix`.
- **Wrong PAPER-GAPS line or § pointers**:
  - fresco/algo/sub/prop_looksub.v:706 cites PG:2257; it should be PG:3017.
  - fresco/algo/sub/prop_looksub.v:710 cites PG:2567; it should be PG:3343.
  - fresco/algo/prop_precise_recover.v:11 cites "§9.1" and fresco/algo/consis/prop_completeness_consis.v:359 cites "§9.2". Both sections are in docs/DESIGN-completeness-measure.md, not PAPER-GAPS.md.
- **Stale comment**: fresco/algo/consis/prop_completeness_consis.v:356-365 says the stuck-check ingredients are "NOT supplied", but they are discharged at :4540-4546.
- **Stale def_rules line numbers**: fresco/ext_algo/def_consis.v:5 and :35, and fresco/ext_algo/def_look.v:17 (`a_sub__forall_l`'s `uniq` is now ~:1605).
- **README.v:211-215 paper lines**:
  - P5 :1664 → :1667
  - Cv :1180 → :1187
  - Cs :920 → :921
  - Sv :1696 → :1699
  - Ss :2202 → :2213
  - L :2730 → :2749
- **Leftovers**: cex/probe_flexr_neutralises_p6.v still mentions `sub_shield`.

### G-59 Stale statements in WF-SIDE-CONDITIONS.md, ghost-capture.tex, refutations.tex and PAPER-GAPS.md headers
- **Kind**: Mechanization to-do · **Status**: LIVE
- **WF-SIDE-CONDITIONS.md**:
  - Dead paths: `algo/prop_consis_complete.v`, `algo/prop_look_complete{,_var}.v`, `fresco/algo/prop_sub_complete_thm.v`, `prop_sub_complete_dispatch.v`, `fresco/algo/cex/…` (now `cex/`), `algo/def_decorated.v:96` (now fresco/deco_algo/def_decorated.v:71), and `algo/def_rules.v:164`.
  - Dead names: `a_{consis,unify,assign}_solution` and `ad_pat_sub_precise_upre_gv` (now `_fuel`).
  - It still describes `sub_shield` as a residual.
  - Its paper:declarative.tex citations are off by 2-3 lines (e.g. :1427 → :1424, :2074 → :2072).
  - §1a omits `ad_precise_extends_pat_sub`'s extra `⊢ₚₛ ⌊Q⌋` and TY ghost-freeness.
- **ghost-capture.tex**:
  - It says `d_sd_typing_to_ad` has no hypothesis, but it still takes `d_wf_denv Γ` and term wf.
  - "28/28 Print Assumptions" should be 34.
  - It cites commit 2cb0179 on `remech`.
  - The R-TopHoleKeep "explicit guarded{bid Q}" remark (~l.597-603) is obsolete.
- **refutations.tex**:
  - `fresco/algo/cex/…` paths should be `cex/…`.
  - `a_sub_sound_thm` is now `a_sub_sound`.
  - "`Ψ′ fresh` as `Ψ′∩Ψ = ·`" is now global (since 2026-08-11).
  - "Still outstanding: `flex_apart`/`sub_shield`" is settled.
  - `run_exists_at_correct_instantiation` no longer exists.
- **PAPER-GAPS.md headers**:
  - PG:746 says "RESOLVED", but the paper's wording is still live (G-34).
  - PG:848 says "one direction only", but both directions now hold (G-37).
  - PG:1749 still says "FALSE without wf", which is retracted.
  - PG:3032 is moot.

---

## G. Settled — resolved by the authors, moot, or retracted

Resolved by the authors:
- **G-60** SolE-FlexR discarded the accumulated pattern, which refuted Look completeness and Thm 4.6. Repaired in fc03787b and f484dde3: threaded Ξ, returns guess^TY(P) (paper:full-algo-spec.tex:1388-1393; impl d10a4460). `a_sub_complete` is unconditional. PG:3640, PG:3844; docs/refutations.tex. The follow-on is G-29.
- **G-61** P6-Sv was false under the keep-α̂ SolE-FlexR (its ForallL descent built the excluded configuration). Resolved by the same repair. `a_solve_sub_complete_var` is Qed and needs no shield. PG:2505
- **G-62** The flexible subtyping walk had no rule for a term-variable head. Resolved by Flex-SkipTmVar (f484dde3, paper:full-algo-spec.tex:914-920). cex_p7_flex_walk_tm_var.v refutes only the old rule set. PG:3395. The implementation follow-up is G-49.
- **G-63** P6-Ss ForallR: LS-ForallR lets 𝒞 mention the bound β. The authors clarified (2026-07-29) that scoping is checked separately at the use site (paper:full-algo-spec.tex:841). PG:2821
- **G-64** Assignment optimality needs `dom Ξ ⊆ ftv P`. The paper already had this in its problem definition (paper:full-algo-spec.tex:1520-1524, since 90383752). RETRACTED. PG:2056

Retracted (our own claims):
- **G-65** Our P6 counterexamples at a flexible P₀ (-var lemmas; Cv/Sv probes). They died with the SolE-FlexR repair. PG:1331, PG:2325; refutations.tex §status ¶5
- **G-66** "Refinement is not transitive". Its counterexample relied on the mechanization's old Ghost rule, which demanded a well-formed fill (retracted 2026-10-08). PG:1749, PG:1793
- **G-67** Sub-Infer precision "read off the consistency premise". This was a misreading: the paper invokes thm:complete-consistency. PG:3160
- **G-68** Source-level "incompleteness on programs" (`pipe (λg. g arg)`). The declarative system rejects the program too, so this is a §2.9 limitation. PG:3727
- **G-69** Closed-pair refutation of thm:complete-subtyping. The probe used the wrong mode. PG:3825
- **G-70** A `pskl_no_ghost P0` premise on P6-Cv completeness. Removed on 2026-07-27. WF:425-490

Moot (mechanization bugs fixed, or encoding notes):
- **G-71** The two-slot `∼` in Flex-Flex-Assign and Assign-Assign is consistency, not unifyvar. This was a mechanization bug (fixed 2026-07-14); the paper was right. PG:1489, PG:1571
- **G-72** Hatted-metavariable and "fresh β̄" conventions rendered as premises. These are admissible (the eleven `*_no_loss` lemmas, fresco/algo/prop_swap.v §13b). PG:1571, PG:1907
- **G-73** Metasubstitution was a sequential fold. Fixed; the paper says finite map. PG:1728
- **G-74** Decorated FlexR had an over-general subject. Mechanization bug, fixed. PG:1864
- **G-75** Assign-SolveM needs a monotype. The paper's τ already says so. PG:1893
- **G-76** Definition-sync findings from the restart. This is a pointer only (docs/REPORT-remech-decl-sync.md). PG:2197
- **G-77** Decorated ForallL quantifies its decoration as a cofinite tag family. Equivalent modulo renaming. PG:2231
- **G-78** The `flex_apart` premise was missing `fa_rsubst_var`. The whole `flex_apart` / `sub_shield` tower was deleted (2026-10-10). PG:3032
- **G-79** sd-Anno annotation wf. The paper puts wf on no sd rule, so only the mechanization was inconsistent (see G-56). PG:923
- **G-80** ForallL "WLOG guarded P₀" is a join permutation. The paper's sentence is right, and the mechanization's cost has been paid. PG:3574
- **G-81** Solve binder rows and arrow siblings need freshness and threading. The paper's solve judgement is context-free and Barendregt covers it. The D-fragment called this "LIVE as an encoding choice"; it is classified MOOT here. The related global-supply wording is G-22. PG:3844 (:3916)
- **G-82** Typing binder rows are exists-fresh, not cofinite. This is purely a locally-nameless matter. PG:4092 (:4125)
- **G-83** Guardedness of a kept ∀◇ comes from wf. The mechanization has matched the paper since 2026-10-08. WF:210-227
- **G-84** `a_tags_sort` drops the context. Scope is restored at the call sites (settled design). WF:397-406
- **G-85** Mode compatibility on the decoration lemmas. This is the paper's own problem definition. WF:408-423
- **G-86** Payload-wf discipline for skeleton term entries. Now a theorem (`a_wf_aenv_binds_var_skl_wf`). WF:632-652
