# Frost Re-Mechanization — Progress

Clean restart against the **finalized paper** (branch `re-mech`, paper merge
`8dfafca`).  Ground rules: the paper's definitions and proofs are never
changed; the mechanization follows the paper's proof appendices bottom-up.
Pre-restart history: [`docs/PROGRESS-legacy-2026-07.md`](docs/PROGRESS-legacy-2026-07.md).
Decl↔paper sync findings: [`docs/REPORT-remech-decl-sync.md`](docs/REPORT-remech-decl-sync.md).

Pre-restart proof files used to sit beside their originals as `*.v.legacy`
(git-tracked, excluded from the build).  They were **deleted 2026-08-06**:
each was pinned to the pre-restart declarative definitions and no longer
type-checks (they reference constructors that no longer exist —
`is_base_term__*`, `d_tags_skl__hole`, `is_tskl__all_syn`, …).  Mine them from
git history when re-proving; they are last present at `a81ef2d`.  The two
that carried real unported content are `frost/decl/prop_safety.v.legacy`
(177 Qed / 14 Admitted — `d_pat_total_gen`, `d_pat_safety`, the
`hole_safe`/`skel_safe` engine) and `frost/decl/prop_skeleton.v.legacy`
(139 Qed — the pre-restart skeleton machinery); the nine `frost/algo/*.legacy`
files were `Admitted` scaffolding subsumed by the current algo development.

# Part 1: Paper → mechanization map

## Definitions (all 🟢 compiled)

| Paper | Mechanization | Status |
|---|---|---|
| Syntax (types/terms/skeletons, decl §3) | `frost/language.ott` → `def_ott.v` (`ptyp/btyp/utyp/pskl/bskl/uskl`, `exp`) | 🟢 synced |
| Colour/shape predicates (syn/inh/decorated/guarded/values) | `frost/def_shapes.v` | 🟢 synced (`is_tskl` fixed) |
| `tags{Ψ}{φ}` / `tags{Ψ}{ψ}` | `decl/def_rules.v` `d_tags` / `d_tags_skl` | 🟢 synced (ψ-grammar exact) |
| Typing (fig:decl-typing) | `d_typing` | 🟢 |
| Syntax-directed typing (§3.3) | `d_sd_typing` | 🟢 |
| Subtyping + consistency (fig:decl-subtyping-consistency) | `d_sub`, `d_consis` | 🟢 |
| Skeleton wf / refinement (§3.5) | `d_wf_pskl/uskl`, `d_refine_syn` | 🟢 |
| Skeleton inference (fig:decl-skeleton-inference) | `d_pat` | 🟢 restructured to embedded-subtyping base rules |
| Skeleton subtyping/consistency (fig:decl-skeleton-subtyping-consistency) | `d_pat_sub`, `d_pat_consis` | 🟢 |
| Algorithmic contexts/suffixes (§5.1) | `algo/def_rules.v` `aenv/abind/a_suffix` | 🟢 rewritten |
| `skmod[TY]/[SK]` on input skeletons | `a_ty_mode_compat`, `a_sk_mode_compat` | 🟢 |
| guess^TY / guess^N (LaTeX `\guessMono`/`\guess`) | `a_guess_mono`, `a_guess` | 🟢 |
| Constraint collection (fig:poly-info-extraction) | `a_looksub`, `a_lookeq` | 🟢 no-refresh, □-Vacuous |
| Constraint solving (fig:constraint-solving) | `a_solve_sub`, `a_solve_eq`, `a_solve_cstr` | 🟢 GhostLF/GhostL with ∀◇ outputs |
| look | `a_extract` | 🟢 |
| unifyvar / assignvar | `a_unify`, `a_assign` | 🟢 |
| Algorithmic consistency (fig:alg-consistency) | `a_consis` | 🟢 NEW Δ₁∣Δ₂ tracking |
| Algorithmic subtyping (fig:alg-subtyping) | `a_sub` + `a_sub_flex` | 🟢 |
| Skeleton splitting | `a_split` | 🟢 |
| Algorithmic skeleton inference (fig:alg-skeleton-inference) | `a_pat` | 🟢 |
| Algorithmic type inference (fig:alg-type-inference) | `a_typing` | 🟢 ∀ᾱ.A₀ AbsCheck (step/base), typed Freeze |
| Erasure ⌊·⌋, decorated subtyping/consistency, tag solving (app:decorated-algosub) | `algo/def_decorated.v` (`uskl_to_pskl`, `a_subtag`, `a_consistag`, `a_solvetag(_sub/_eq)`) | 🟢 |
| Metasubstitutions κ : Θ ⇒ Θ' (app:metasubstitutions) | `algo/def_meta.v` (`a_inc`, `a_inc_equiv`, `a_tyequiv`, `⊴`, and the application family `msubst_{ptyp,btyp,pskl,uskl_syn}`) | 🟢 |
| Decl judgments in algo contexts (app:decl-in-algo-context) | `algo_decl/def_consis_refine.v` (`ad_pat_consis`, `ad_refine_syn`, `ad_refine_pskl` + flex-lookup rules); `algo_decl/def_subtyping.v` (`ad_pat_sub`, `ad_pat_sub_fuel`, `ad_partial_precise`); `algo_decl/def_typing.v` (`ad_pat`, `ad_sd_typing`) | 🟢 COMPLETE 2026-08-06.  The typing layer that section D needs landed: `ad_pat` (skeleton inference) and `ad_sd_typing` (SYNTAX-DIRECTED typing — the appendix ports that one, not `d_typing`).  Per the appendix, NO new rule was needed (every type-level lookup happens inside the embedded subtyping/consistency/refinement premises, which already carry their flexible rows); what was added are the appendix's THREE explicit type-equivalence premises, on `sd-Freeze`, `sd-AbsAnnoCheck` and `sd-AbsAnno`.  `abind_to_pskl` (the `dbind_to_pskl` mirror) added to `algo/def_rules.v` |

## Theorems / lemmas (bottom-up order; ⬜ = to prove, per paper appendix)

**B. consistency-proofs.tex** (§Consistency) — ALL PROVED (status audited 2026-07-28; every `algo/` file is admit-free)
- ✅ Soundness of decorated consistency (`a_consistag_sound_aux`, `algo/prop_consis_sound.v`)
- ✅ Decorating algorithmic consistency (`a_consis_decorate`, `algo/prop_decorate.v`); ✅ Consistency decoration (`algo/prop_decorate_sub.v`, consistency-proofs:88)
- ✅ Soundness of Consistency, all three parts: part 1 `a_consis_sound` / `a_consis_sound_aux` (`algo/prop_consis_sound.v`, the aconsis main induction), parts 2–3 `a_unify_sound` / `a_assign_sound` (mutual bundle `a_assign_unify_consis_sound`)
- ✅ Consistency constraint decoration for variables (`algo/prop_decorate_sub.v`, consistency-proofs:606)
- ✅ Completeness of consistency constraint collection & solving: `a_lookeq_solve_complete` (P6-Cs, `algo/prop_look_complete_cstr.v`) and `a_solve_eq_complete_var` (P6-Cv, `algo/prop_look_complete_var.v`) — both axiom-free; P6-Cs carries one paper-external wf side condition whose necessity is machine-checked (`algo/cex/cex_p6cs_subject_wf.v`, docs/WF-SIDE-CONDITIONS.md)
- ✅ Completeness and optimality of Consistency, all three parts (`a_consis_complete` / `complete_mu` / `assign_complete_step`, `algo/prop_consis_complete.v`)

**C. subtyping-proofs.tex** (§Subtyping)
- ✅ Decorating algorithmic subtyping (`a_sub_decorate` / `a_sub_decorate_bundle`, `algo/prop_decorate_sub.v` + `algo/prop_soundness_sub.v`); Soundness of decorated subtyping (`a_subtag_sound_bundle`, `algo/prop_sub_sound.v`)
- ✅ Look decoration (`algo/prop_pat_sub.v` §7); Decorating constraint solving (`algo/prop_soundness_sub.v`); Constraint solving concatenation (`algo/prop_decorate_sub.v` §3, lemma:solvetag-concat)
- ✅ Subtyping decoration (variables → general) (`algo/prop_decorate_sub.v`, subtyping-proofs:175/541); Vacuous subtyping decoration (same file, :483)
- ✅ Stability of constraint collection (`a_looksub_lookeq_subst_stable`); Look freshness (`a_extract_output_fresh`) — both `algo/prop_looksub.v`
- ✅ Decorating instantiation (`a_extract_decorate`, `algo/prop_soundness_sub.v`); Soundness of decorated algorithmic subtyping of flexible variables (the flex half of `a_subtag_sound_bundle`)
- ✅ **Theorem: Soundness of subtyping** (`a_sub_sound`, `algo/prop_soundness_sub.v`, axiom-free)
- ✅ Complete partial precision (`algo/prop_sub_complete.v` P5b, lemma:partial-precision-complete); Stability of subtyping under more precise substitution (`ad_pat_sub_precise_upre`, same file — P5)
- ✅ Completeness of constraint collection & solving **for variables** (subtyping-proofs:1696, P6-Sv) — `a_solve_sub_complete_var` in `frost/algo/prop_look_complete_sub_var.v`, **Qed and axiom-free** (`Print Assumptions`: closed under the global context).  The paper's statement is **FALSE as given**, machine-checked counterexample `frost/algo/cex/cex_p6sv_forall_flex.v` (`p6sv_with_p6cv_premises_is_false`): its own ForallL case builds, from a ρ = IDENTITY instance, the raw-flexible-payload configuration that `cex_p6_flex_freshened.v` rules unreachable on the constraint-collection route.  What is proved is the REPAIRED statement, which adds the positional premise `flex_shield Θ0 Ψ' Δρ P0 ψa` (plus `flex_apart_walk`, and a `binds`-monotone context generalization so Sub-ForallL can run the IH at `Θ,β`).  `flex_shield_excludes_cex` is kept as the regression test tying the premise to the counterexample.  See docs/PAPER-GAPS.md and DESIGN-completeness-subtyping.md §6 (x)–(a3)
- 🟢 Completeness of constraint collection & solving (subtyping-proofs:2202, P6-Ss) — **CLOSED 2026-07-30**, `Qed` + axiom-free — `a_looksub_solve_complete_gen` (ρ-generalized) + the paper's premise-free ρ = identity corollary `a_looksub_solve_complete` in `frost/algo/prop_look_complete_sub_cstr.v`; **11 of 12 rows closed**, ALL TWELVE ROWS closed.  ⚠️ Phase B's planned prerequisite — a sub-side `ad_pat_consis_target_ftv` — is FALSE at `ad_pat_sub_g__forall_l_tagged` even under `is_tskl` (`cex/cex_p6ss_sub_target_ftv.v`); what Sub-ForallR carries instead is a MODE-GUARDED DISJUNCTION (DESIGN §8 (h)), whose right disjunct (`alpha_stack`) is the shape that never descends the target.  Like P6-Sv it is a REPAIRED statement (`sub_shield`).  ⚠️ P6-Cs's `Δρ ∩ dom Θ0 = ∅` premise was VACUOUS — `cex/cex_p6cs_rsubst_delta_vacuous.v` — and is now the ftv-level one.
- ✅ **Look completeness** (subtyping-proofs:2730, P6-L) — **CLOSED 2026-07-30**, `Qed` + axiom-free — `a_extract_complete_gen` in `frost/algo/prop_look_complete_extract.v`.  **P6 IS COMPLETE**: all five of its lemmas (P6-Cv, P6-Cs, P6-Sv, P6-Ss, P6-L) are closed.  The statement is the paper's, with the paper's own PROSE well-formedness of ψa restored on the statement (`Θ ⨟ Δ ⊢ₚₛᵃ ⌊ψa⌋ˢ`, which `ad_partial_precise_complete` needs, plus the precision hole rule's `Δ ∩ ftv ψa = ∅`); the paper's `inc[θ≡θa]{Θ0}{Θ}` appears as the reflexive `a_inc_equiv Θ0 κ κ Θ` beside an a_inc conclusion exhibiting θa as the EXTENSION `κa ++ κ` — the mech's `a_inc_equiv` is positional, so that is where the content lives (same reading as P6-Ss).  One ENCODING FIX was required first: `a_extract` now carries a context and solves at `Ξ ++ Θ0`, not `Ξ` alone — the paper's solve/guess judgments are context-FREE, and handing the solve `Ξ` alone hid Θ0's flexibles from the one context-sensitive rule of the cluster (`a_solve_eq__flex_r`), which made P6-L unprovable.  See DESIGN-completeness-subtyping.md §7.4 / §7.5
- 🟢 Completeness of flexible-variable subtyping (subtyping-proofs:2836, P7a) — **ALL FIVE ROWS CLOSED 2026-08-03**, `Qed` + axiom-free, in `frost/algo/prop_sub_complete_thm.v`: §(F) `a_sub_flex_complete_depend`, §(G) `_skip`, §(I) `_assign`, §(K) `_solve`, §(M) `a_sub_flex_complete_skip_rigid`.  §(I)/§(K) are the CROSS-HALF rows (both re-enter the MAIN judgment, so their IH is the **P7b** motive).  §(M) needed the ⇓-apparatus of §(L0)/§(L1)/§(L) — `a_inc__tvar` shrinks the TARGET, so the IH runs at the truncation `Θ'` and every solution-side premise is ⇓-normalized before being strengthened there; its one obligation beyond the consistency walk's `Assign-SkipRigid` is `ad_precise_downarrow` (`⇓ˢP ⊑ P`), which brings the motive's PRECISION conjunct back from `⇓ᵇQ` to `Q`.  The motive's flexibility premise was STRENGTHENED to `a_flex_tvar Θ0 α` (the walk's own invariant, as in `assign_complete_at`); no downstream statement changed.  The remaining P7 work is the DISPATCHER (§12) plus its STUCK-CHECK.  What follows is the pre-closure record.  TASK 0 (supplying P6-L's `sub_shield` premise at P7b's Sub-ForallL) lives in `frost/algo/prop_sub_shield_supply.v`, all Qed + axiom-free: a mono-ish counterpart (§4, covers a raw FLEXIBLE `P0`), the non-composite shapes (§5), any **flex-free** `P0` (§6, uniformly in ψa and Δρ), and — the generalization that does the real work — any **inh-free counterpart** / any `P0` **with no ∀** (§7/§8: `ad_pat_consis_inh_free_tag_free`, `ad_pat_sub_g_inh_free_tag_free`, `ad_refine_syn_inh_free`, `sub_shield_supply_all_free_p0`).  ⚠️ Residual SETTLED 2026-08-03 and it is NEGATIVE: a `P0` carrying a ∀ below its head is not merely uncovered, it makes `sub_shield` FALSE at a REACHABLE configuration (`cex/cex_p7_shield_realizable.v`, Qed + axiom-free — the full completeness input, the ForallL join node, the fill, and `~ sub_shield` all machine-checked, plus `join_at_Rw_is_forall_l`: no other join rule applies there).  `sub_shield` is a MECH-INVENTED repair premise, so no paper statement is refuted and P6-Sv/P6-Ss stay `Qed`; what is refuted is its NON-POSITIONAL indexing, and the repair is a positional re-indexing replayed through P6-Ss and P7b's two ForallL rows.  Until then P7c's two ForallL cases are BLOCKED (the other ten are not).  DESIGN-completeness-subtyping.md §14.1 / §9.0.2
- 🟡 Theorem: Completeness and optimality of subtyping (subtyping-proofs:3050, P7b/P7c) — **IN PROGRESS**.  Motive locked AND REPAIRED 2026-07-30 (`sub_complete_concl` / `sub_flex_complete_concl` / `a_sub_complete_bundle`, `frost/algo/prop_sub_complete_thm.v`): the join is the LEAF-VALID mirror `ad_pat_sub_gv` (def_decl_algo_sub_hyg.v) carrying the subject refinement at the consistency leaves, with NO root-level third premise — the first-cut root premise was REFUTED as a lockstep condition (machine-checked `cex/cex_p7_univ_ghost_r_vacuous.v` + `cex/cex_p7_third_premise_forall.v`: it lost Sub-UnivGhostR entirely and the head-disagreeing ForallL/ForallR solutions `∀a.a ⩽ unit`, `unit ⩽ ∀a.unit`).  FIVE of P7b's rows closed, Qed + axiom-free — Sub-Ghost, Sub-GhostG, **Sub-Infer**, **Sub-Check** and **Sub-UnivGhostR** (a REAL proof: algorithmic UnivGhostR + the `□`-P0 precision core at the stripped counterpart + a `∀◇`-wrap).  The enabling lemma is `a_inc_equiv_precise_msubst` (precision is stable under equivalent metasubstitutions), with the shared core `a_sub_complete_hole_p0_precision`.  ⚠️ Remaining obligation: transport P5's precision-substitution + the freshening kits to `_gv` for ForallL/ForallR.  See docs/PAPER-GAPS.md and DESIGN §9.1.3 / §1.  ⚠️ The property the paper marks with its own TODO at `:3243` ("input `P_0` concrete ⟹ RHS is `P_0`") is **FALSE** — machine-checked `frost/algo/cex/cex_p7_concrete_rhs.v` (`p7_concrete_rhs_is_false`).  Sub-Check / Sub-ForallR are unaffected: both already argue via the EQUIVALENCE, and BOTH halves of it are proved in `frost/algo/prop_sub_concrete_rhs.v` — `a_consis_concrete_output_equiv` and `a_sub_concrete_output_equiv`, each `Θ1 ⊢ P0 ≡ˢ P'`, both falling out of the SOUNDNESS theorems' refinement conjunct plus `ad_refine_syn_ghost_free_equiv`.  See docs/PAPER-GAPS.md and DESIGN §9.1

**D. proofs.tex** (§Proofs for Algorithms) — STARTED 2026-08-06.  🟢 the
DEFINITIONAL layer is in (`algo_decl/def_typing.v`: `ad_pat`,
`ad_sd_typing`); the lemma/theorem block is teed up with per-item design in
[`docs/HANDOFF-section-d.md`](docs/HANDOFF-section-d.md).
⚠️ Three of these are marked "straightforward induction" in the paper and are
NOT straightforward in the mechanization — reasons recorded per lemma there.
- 🟢 **Suffix moving — CLOSED 2026-08-06**, Qed + axiom-free
  (`algo_decl/ + deco_algo/prop_ctx_mono.v`): `ad_sd_typing_suffix_moving`,
  `ad_pat_suffix_moving`.  ⭐ ONE lemma, not
  five: every `ad_*` judgement reads its context only through `binds` and
  `a_binds_tvar` (itself a disjunction of `binds`), and NOTHING in the layer is
  anti-monotone — the negative side conditions (`a_non_flex`, `a_flex_tvar`)
  live in the ALGORITHMIC judgments.  So one relation `aenv_binds_le` gives
  weakening, exchange and block permutation for `a_wf_ptyp` / `a_wf_pskl` /
  `a_tyequiv` / `ad_pat_consis` / `ad_refine_syn` / `ad_refine_pskl` /
  `ad_pat_sub` / `ad_pat` / `ad_sd_typing` at once.  ⚙ **The mech statement
  needs NO side condition**: the paper's "Ξ does not depend on entries in Θ₂"
  is what keeps the RESULT context well-formed (`Θ ⊢ ctx` orders definitions
  before uses), not what makes the judgement move — a block permutation
  preserves `binds` in BOTH directions.  A dropped premise only strengthens the
  lemma.  ⚠️ TRAP for the rest of section D: `econstructor` on a cofinite rule
  SHELVES the avoid-set evar `?L`, so the premise never reaches the following
  tactic and resurfaces at `Qed` as "incomplete proof" — supply `L` by hand
  (that is also what keeps the file under a second)
- ✅ Suffix erasure — CLOSED 2026-08-06 (all six judgements,
  `algo/prop_suffix_erase.v`).  NOT a `binds`-monotone statement (it must show the
  derivation never LOOKED into Ξ).  ⚠️ **CONFIRMED 2026-08-06 to be needed**
  (the four CHECK rows of `a_typing` DROP the pending suffix from their
  output, unlike `a_pat`'s, which keep it), and **CONFIRMED not to be the
  paper's "straightforward induction on the typing derivation"**: the
  obstruction is `ad_pat_sub`'s `ForallL`, which instantiates with a
  freely-chosen decorated skeleton `ψ` that may mention Ξ, so the recursive
  premise is not Ξ-fresh even when the conclusion is.  Reachable with a
  DEFINED `α̂ ∈ Ξ`.  ⭐ Working route: erase by SOLVING —
  `Ξ ++ Θ ⊢ J ⟹ Θ ⊢ κJ` for a κ solving Ξ into Θ, identity on Ξ-free types
  (five per-judgement transports).  ⚙ `ad_pat_sub`'s own driver
  (`ad_pat_sub_strip_suffix`, prop_pat_sub.v) ALREADY EXISTED — the tree
  solved this at the subtyping layer during the subtyping-soundness
  campaign, with the same ForallL insight recorded in
  `ad_pat_sub_subst_flex`'s header.  🟡 NEW `algo/prop_suffix_erase.v`
  (Qed, axiom-free) adds the layers above it: the substitution kit
  (`subst_abind`/`subst_aenv` + the coercion commutations),
  `a_wf_ptyp`/`a_wf_pskl`, `a_tyequiv`, `ad_refine_syn`, `ad_pat_consis`,
  and the driver `ad_refine_syn_strip_suffix`.
  ⛔ LEFT: `ad_pat` and `ad_sd_typing`, which additionally need
  `ad_pat_sub_subst_mid` in the SUBSTITUTED-CONTEXT style (prop_pat_sub.v's
  version concludes at the un-substituted tail, which does not compose with
  the binder rows that push TERM entries).  The fallback (weaker, read the
  conclusion up to a flexible suffix) is no longer needed.
  docs/PAPER-GAPS.md + HANDOFF §1
- ✅ Splitting refines — CLOSED 2026-08-06, COLOURED (`a_split_refines`,
  prop_soundness_typing.v §11), via `ad_pat_consis_mono_to_refine`.
  Historical route notes: 2 of 3 rows trivial (`ad_refine_pskl_refl`, which
  forces an EXTERNAL wf premise); the `a_split__flex` row is a real proof: its
  premise is a full `a_consis` run.  ⭐ Route scouted: `a_assign_sound` →
  invert `ad_pat_consis__flex_r` (the only applicable rule) → `binds α
  (abind_flex_mono_def τ) Θ1`, leaving a mono-level `≡ˢ ⟹ ⊳` obligation.
  ⚙ 2026-08-06: that last obligation is `consis_mono_join`'s output fed to
  the CONVERSE of `refine_mono_join` (prop_mono_bridge.v).  ⛔ Do not prove
  the converse by induction on `≡ᵗ` — `sym`/`trans` would need refinement
  symmetry and TRANSITIVITY, and transitivity is false
  (`cex/cex_refine_not_transitive.v`); go through `prop_normal.v`'s
  `a_tyequiv_downarrow` normal form, as `a_tyequiv_arrow_inv` does
- ⬜ Precision extends skeleton subtyping — ⚠️ SCOUT FIRST: `P' ⊑ P` admits
  `P' = □`, where the only applicable row is `ad_pat_sub__ghost` (inherited
  painting + `mod_comp_sk`), so the statement may need a side condition
- ✅ Precision preserves refinement — `ad_precise_preserves_refine`
  (`algo/prop_precise.v:585`), Qed, audited in `README.v`
- ⬜ Context precision (+ preserves skeleton inference) — new `⪯ctx` inductive
  + one lemma over `ad_pat`; needs a "same non-variable entries ⟹ preserved"
  context-change lemma for `ad_pat_sub` / `ad_refine_syn` that does not exist
  yet.  GATED on "Precision extends skeleton subtyping" (the `ad_pat__var` row)
- ✅ **Theorem: Soundness of skeleton inference — CLOSED 2026-08-06**,
  `a_pat_sound` (`algo/prop_soundness_pat.v` §5), Qed and *Closed under the
  global context*; all ten `a_pat` rows proved; `Check`ed and audited in
  `README.v`.  Its last piece, AbsAnno's refinement-target transport, is
  `a_consis_chk_annot_refine` (§4) — the paper's inline "preservation of
  refinement under type equivalence", which exists nowhere as a lemma
  (docs/PAPER-GAPS.md).  ⚠️ The statement carries ONE hypothesis beyond the
  paper's list: `a_wf_exp Θ0 e` (the problem definition's "M wf in Θ0").
  WF-SIDE-CONDITIONS pattern
- ✅ **Theorem: Soundness of type inference — CLOSED 2026-08-06**,
  `a_typing_sound` (`algo/prop_soundness_typing.v` §13), Qed and *Closed under
  the global context*; all eleven `a_typing` rows proved; `Check`ed and audited
  in `README.v`.  Carries theorem 1's extra hypothesis, plus ONE extra
  conclusion conjunct (`a_wf_ptyp Θ1 A`, the output type scoped in the output
  context, which `AT-App` consumes).  ⚠️ FOUR rule-level side conditions the
  paper leaves to prose are now stated on `fig:alg-type-inference`
  (docs/PAPER-GAPS.md): the two Barendregt conditions the four suffix-DISCARDING
  check rows need for `lemma:suffix-erasure`, the `uniq` filter `AT-Abs` needs
  on `guess^TY`'s block, and the correction of `AT-AbsAnnoCheck`'s result
  domain.  ⭐ Reader-facing form: `a_typing_sound_infer` / `a_typing_sound_check`
  (algo/typing/prop_closed.v) — the empty context, one per user-facing mode,
  and since 2026-08-10 stated against the paper's own §declarative system
  (`· ⊢ˢ[M] e ⦂ B` and `· ⊢[M] e ⦂ B`) through the conservativity bridge
  `algo_decl/prop_conserv.v`, with the run's output context closed off by a
  metasubstitution the proof BUILDS.
  History of the build-up:
- 🟡 (history) **Theorem: Soundness of type inference — STARTED 2026-08-06**
  (`algo/prop_soundness_typing.v`, NEW; all Qed and axiom-free).  ⭐ The
  `Freeze` ingredient is DONE and was DERIVED from theorem 1's transport, not
  rebuilt: `a_consis_chk_tyequiv` (the paper's "which further gives
  `Θ2 ⊢ B ≡ A`") = the transport + ⭐ `ad_refine_syn_inh_tyequiv`, which says
  **a refinement between two GHOST-FREE paintings IS a type equivalence**
  (refinement's job is filling ghosts; between paintings of plain types only
  the structural rows and the two flexible lookups can fire — exactly `≡ᵗ`'s
  generating set).  Also banked: `a_typing_tm_ge`, `ad_sd_typing_isub_tm`,
  `btyp_syn_painting_inv`, `ad_sd_typing_subst_tm`/`_rename_tm`, and ⭐
  `btyp_inh_painting_inv` (in CHECK mode the colouring is FORCED, which
  removes the need for a TYPE-variable renaming at this layer).
  **2026-08-06 sixth pass — two more prerequisites CLOSED**, both Qed and
  axiom-free: §8 `ad_sd_typing_mod_comp_ty` (⭐ not the SK proof one sort up
  — `mod_comp_ty` is stated on a `btyp` while the premise's target is that
  `btyp`'s SKELETON, so it needs `is_styp_of_btyp_to_bskl` and
  `is_ityp_of_erase_inh`, the second of which genuinely needs local closure,
  supplied by `ad_pat_consis_lc_r` + `lc_btyp_of_lc_bskl_erase`; the `≡ᵗ`
  rows take theirs from `a_tyequiv_lc`, which carries `a_wf_aenv` exactly as
  `d_typing_skmod` carries `d_wf_denv`) and §9 `a_guess_mono_refine` (the
  paper's inline "by definition of `guess^TY`, `Θ1,ᾱ ⊢ inh{P} ⊳ inh{A}`" —
  a SIZE induction, with the ∀ witness going into **Δ**).
  LEFT: suffix ERASURE (see above), COLOURED split-refine, `AT-App`'s
  typing-under-`≡ᵗ` transport at TC, then the eleven-row induction; see
  docs/HANDOFF-section-d.md §7.5
- ✅ **Theorem: Completeness + optimality of skeleton inference — CLOSED
  2026-08-07**, `a_pat_complete` (`algo/prop_completeness_pat.v`), Qed and
  *Closed under the global context*; `Check`ed and audited in `README.v`.
  Nine step lemmas glued by strong induction on `size_exp` (the mech FUSED
  the paper's `P-Sub` into the base rows, so every recursive premise is at a
  strict subterm).  Carries theorem 1's hypotheses, plus the payload-wf
  DISCIPLINE of the TARGET context's skeleton term entries.
- ✅ **Theorem: Completeness + optimality of type inference — CLOSED
  2026-08-08**, `a_typing_complete` (`algo/prop_completeness_typing.v`), Qed
  and *Closed under the global context*; `Check`ed and audited in `README.v`.
  Twelve step lemmas glued by strong induction on the LEXICOGRAPHIC
  `(size_exp e, size_btyp B)`: ten rows recurse at a strictly smaller
  SUBJECT, and only the two ∀-peeling AbsCheck rows recurse at the same
  subject, dropping one `∀` off the declarative result.
  ⭐ Reader-facing form: `a_typing_complete_infer` / `a_typing_complete_check`
  (algo/typing/prop_closed.v) — the empty context, one per user-facing mode,
  with no metasubstitution quantified and the optimality already
  instantiated; each has the declarative derivation as its ONLY premise.
  ⭐ Its two unrecorded prerequisites, both closed here: `a_split_complete_tc`
  — completeness of SPLITTING at check mode, i.e. the paper's AbsCheck
  **subcase 2**, where the split's flexible row has to be BUILT out of a full
  consistency run — and the §6.3#2 SCOPING invariant
  (`algo/prop_ty_scope.v`), which discharges the suffix-discarding rows'
  premise (2).  ⚠️ Three findings on the paper's own AbsCheck proof are
  registered in [`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md) (the shape
  enumeration is incomplete; the subcase-2 metasubstitution extension maps
  a flexible to a NON-monotype; the split run and the scoping step are
  asserted).
- ⚙ §4b's composition gap (completeness consumed a leaf-valid join while
  soundness concluded only the plain one) is CLOSED, and since 2026-08-12 it
  is closed at the SOURCE: the paper's leaf presupposition sits ON
  `ad_pat_sub` itself (`3f08641`), so both sides speak of one relation.  The
  three-relation era — `ad_pat_sub_g` / `_gv` / `_v` and the forgetful map
  `ad_pat_sub_fuel_forget` — is retired; what is left is `ad_pat_sub` and its
  fuel-indexed mirror `ad_pat_sub_fuel`, bridged at the end of
  `algo_decl/prop_ctx_mono.v`.

**A. full-decl-proofs.tex** (declarative metatheory — REBASED onto the synced defs)
- ✅ Soundness/Completeness of syntax-directed rules (`d_sd_typing_sound` / `d_sd_typing_complete`, `prop_syntax_directed.v`, 0 admits)
- ✅ General subsumption; Consistency-Subtyping Transitivity; Subtyping Transitivity; Function Subtyping; Generalised General Subsumption (`prop_general_subsumption.v` D1/D12 + spine, 0 admits; `Print Assumptions` audited in `README.v`)
- Restored chain: `prop_weakening` (d_pat base cases repaired for embedded subtyping), `prop_renaming` + `prop_general_subsumption` (compiled unchanged), `prop_skeleton` (lean extraction: the 18-block dependency closure the equivalence needs; the pre-restart skeleton-safety machinery — incl. the now-false `pskl_to_tskl_is_tskl`, a casualty of the `is_tskl` sync fix A1 — stays in `prop_skeleton.v.legacy` for the later paper-faithful redo), `prop_syntax_directed` (base cases of `d_pat_subst_unit` repaired; obsolete `is_base_term` helper dropped)

# Part 2: Progress log (most recent first)

## 2026-08-15 (h, latest) — ⛔ **SCOUTING RESULT: the EXTRACT level's planned route is REFUTED — the COLLECTION is not deterministic up to renaming, and the root cause is a side condition the paper omits**

§8c.6's next item was to repeat level 3's transport one layer up, which
needs `a_looksub` / `a_lookeq` determinism up to fresh renaming.  It does
not hold.  `cex/cex_looksub_not_det.v` (Qed, axiom-free) exhibits, at
subject `∀_.α`, target `∀_.1`, mode TC, two derivations of the SAME
collection judgement with the same (empty) block and constraint lists
`[≼TC ∀_.1]` vs `[≼TC 1]` — both CLOSED, so no renaming and no swap chain
relates them.  The mechanism: `LS-Var` emits its constraint at the
CURRENT target, so peeling the target (LS-ForallR) and peeling the
subject (LS-ForallL) collect different things, and at a ∀/∀ crossing both
rules apply.

⭐ **Root cause is the paper's own omission** (filed in PAPER-GAPS.md):
`SI-ForallL` carries `guarded{P_0} ∨ P_0 = □` with the paper's own
comment *"avoid overlapping with ForallR; only need in an algorithmic
presentation"* (`full-algo-spec.tex:838`), and `SI-UnivGhostR` carries the
same guard for the same stated reason — but the COLLECTION's `LS-ForallL`
(`:1065`) and `LS-ForallR` (`:1049`) have none.  ⚙ The ALGORITHM is
unaffected: both lists are solvable and the runner commits to ForallR;
what fails is the invariant that the collection's output is determined.
In hindsight the evidence was already in the tree — level 1's reorder
lemma `a_looksub_forall_r_first` is stated with EXISTENTIAL outputs
precisely because re-rooting changes them.

⛔ **(a) WAS THEN TRIED, AND IT BREAKS COMPLETENESS — reverted, evidence
recorded.**  The minimal correct guard is "`LS-ForallR` does not apply"
(the paper's literal `guarded{P'} ∨ P' = □` is too strong: it also blocks
`⫯` and non-ghost-free `∀` targets, where nothing else applies, since
"the target is guarded or ◇" is not an invariant — `LS-Arrow` splits a
guarded arrow target into halves of any shape).  Everything below the
completeness layer absorbs it mechanically: the e-side rule mirrors it,
`prop_swap.v` gains `looksub_no_forall_r_swap`/`_open`, and — the design
working — the RUNNER discharges it from its own dispatch, the three ways
a ForallL branch is reached being exactly the three ways the premise
holds (⚙ via a `Hint Extern` into `lookdec`: it is a constructor PREMISE
`eauto` must solve, not a top-level goal; and `ghost_free_ck_complete`
must MOVE to `def_dec.v`, since `prop_dec.v` sits below the runners).
⛔ It dies at P6: `alpha_stack_looksub`
(`algo/sub/look/prop_sub_cstr.v:373`) proves an α-stack collects the
WHOLE target *undescended, for ANY target and ANY mode*, and its own
header records why that matters — *"Sub-ForallR's stack branch never
invokes LS-ForallR"*.  The guard falsifies it exactly at TC with a
ghost-free ∀ target, i.e. at the counterexample (`∀_.α` IS an α-stack);
repairing it means re-deriving the Sub-ForallR stack branch against a
PEELED target, which changes what P6's solving half is handed.

So the fork now reads: redesign that step of P6, or carry (b)'s
solve-equivalence invariant at the extract level (no rule change, bigger
metatheory, not compositional through `LS-Arrow`).  (b) at least leaves
the closed theorems alone.  ⚠️ It is also a real choice for the paper's
authors, not only a mechanization one — filed in PAPER-GAPS.md.
Awaiting the user.

## 2026-08-15 (g) — ⭐⭐⭐ **§8c.3 LEVEL 3 CLOSED: the CSTR FOLD is complete — the yield mismatch is paid by TRANSPORTING the derivation's tail along the determinism chain**

`prop_run_complete.v` §5 (`e_solve_cstr_run_complete` /
`e_solve_cstr_impl_complete`, axiom-free; file 3,432 → 3,831 lines,
~39 s): a constraint-fold derivation at scoped, covered inputs — plus
`uniq` of its block — means the fold runner does not return `None`.
This is the first level to CONSUME the determinism metatheory, and it
consumes it exactly as §8c.6's recipe predicted: invert the eq-cons row,
kill the head by level 2a's finished lemma, bridge the runner's run back
to an a-side derivation (`e_solve_eq_sound`), read off the aligned
renaming ρ (`a_solve_eq_det`), and transport the derivation's TAIL along
ρ's palindromic swap chain (`a_solve_cstr_swaps` on `chain ρ zs`) so
that its context, subject and constraint list land on the runner's:
`chain_flex_pairs` aligns the two blocks entrywise, `rel_pskl_chain`
turns the derivation's yield into `sv_out r1`, and
`swaps_cstrs_fresh_id` leaves `𝒞'` FIXED (the left column dodges
`ftvar_in_aenv Θd`, the right dodges the supply, the intermediates are
freshly drawn).  ⚠️ `uniq Ξd` is a REQUIRED premise, not a defensive
one — without it the derivation's block need not be a renaming of the
runner's at all; it splits recursively because blocks only append
upward (`uniq_app_1`/`_2`).

What the level ADDED to the plan, and what every level above should
copy:

- ⚠️⚠️ **THE `fsetdec` CLIFF WAS MEASURED, and it decides how the
  motive sets must be WRITTEN.**  On a DISJOINTNESS goal
  (`_ ∩ _ [=] empty` hypotheses, a membership conclusion) `fsetdec`
  costs 0.25 s at 4 set variables, 2 s at 5, and **> 120 s at 6** —
  the fold's first draft spelled its variable set out as
  `ftv P ∪ ftv Q0 ∪ ftv 𝒞'`, which put THREE variables into every
  column-freshness goal and hung the build.  The fix is to hold the
  set OPAQUE (`pose` + `clearbody` + one `HVdef` equation re-opened in
  the four places that look inside), keeping every such goal at ≤ 4.
  ⚙ PURE-SUBSET goals are NOT on this cliff — 9 set variables cost
  0.1 s — so only the disjointness family needs the discipline.
- The n-fold context kit is mechanical (`flex_agree_swaps_left`,
  `ftvar_in_aenv_swaps_subset` — folds of §3a's singles under one
  "every chain pair avoids V" hypothesis, itself `chain_atoms` plus
  the two column-freshness facts), with ONE genuinely new lemma:
  `flex_agree_flex_block`, both sides gaining the SAME flex block at
  the head, so agreement EXTENDS to the block's own atoms — needed
  because `rel_pskl_ftv_r` bounds the transported yield by
  `V ∪ cols_r ρ`, not by `V`.
- The det file gained the four small facts the transport needs and
  nothing in the tree provided: `atoms_fresh_list` (a fresh LIST, by
  iterating `atom_fresh` against a growing avoid-set),
  `uniq_flex_pairs_l_nodup`/`_r_nodup` (the `uniq` premises ARE the
  chain's two `NoDup`s — ⚠️ `map` is metalib's env-map, write
  `List.map`), and `swaps_aenv_uniq`.
- The sind is the smallest of the campaign (ONE doubled premise: the
  eq tail companion, which already sits at the RUNNER's yield), and
  the case bash has only 4 leaves — the sub-with-a-tail leaf closes by
  `inversion Hd` alone (no rule fits).

`make coq` green, README 32/32, zero admits.

## 2026-08-15 (f) — ⭐⭐⭐ **THE YIELD-MISMATCH FORK IS RESOLVED AND ITS METATHEORY LANDED: the solve layer is DETERMINISTIC UP TO FRESH RENAMING**

The §8c.6 design fork is decided — option (a), the USER's call — and
`frost/ext_algo/prop_solve_det.v` (1,177 lines, ~15 s, axiom-free) now
holds what the cstr fold and every composition above it will consume:
`a_solve_eq_det` and `a_guess_mono_det` — two derivations on the same
inputs, at ANY two contexts, produce the same block and yield up to an
aligned fresh-pair renaming.  ⭐⭐ The statement is RELATIONAL
(`rel_pskl ρ V`) because a functional renaming is genuinely absent:
`a_guess_mono__arrow` runs both halves at the same Θ, so one derivation
may guess the SAME flexible for two holes where another guesses two —
column uniqueness is paid only at the TRANSPORT (`rel_pskl_chain`, a
palindromic swap chain through globally fresh intermediates, built
solely from the tree's single-swap primitive).  ⭐ The det lemmas are
HYPOTHESIS-FREE — no flex_agree, no scoping: rule choice is forced by
input shapes, the overlaps produce identical outputs
(`a_solve_eq_var_subject_inv` — the 12-rule matrix has exactly the
var-subject and ghost-corner crossings), and the size induction rebinds
both binder rows to a common fresh opener while `rel_pskl_close` DROPS
the opener from the identity support.  ⚠️ Two >100 s hangs were the
KNOWN evar-set fsetdec trap resurfacing (`eapply rel_pskl_mono` then
un-pinned `apply Hrel`; un-`clear`ed fsetdec beside the size IH) — both
now in §8c.6; a third pitfall: an unimported name inside a `match goal`
body reports "No matching clauses", not an unbound reference.
`make coq` green; the fold's completeness (prop_run_complete §5) is the
next consumer, per the updated §8c.6 recipe.

## 2026-08-15 (e) — ⭐⭐ **§8c.3 LEVEL 2b: the SOLVE block's SUB runner is complete — the LEFT-first reorders paid, via a hoist/wrapper split**

`prop_run_complete.v` §4 (`e_solve_sub_run_complete` /
`e_solve_sub_impl_complete`, axiom-free, file ~30 s): an `a_solve_sub`
derivation at scoped, covered inputs means the sub-solve runner answers —
same `flex_agree` motive as level 2a, reflexive at the run level.  The
level's own price was the dispatch's LEFT-first rule priorities
(type.ml:489-533 peels ∀/⫯ SUBJECTS first, the opposite of the look
walk): `a_solve_sub_tophole_l_first` (strip-first; easy — no swaps, the
ForallR case re-applies at the SAME witness) and
`a_solve_sub_forall_l_first` (ForallL-first).  ⭐⭐ The scouted
∃-context interface for the latter is right, but it CANNOT be proved by
one direct induction — the IH returns an ABSTRACT context, and
re-applying SS-ForallR needs a witness fresh for it, which any
opener-renaming swap re-pollutes.  The resolution:
`a_solve_sub_forall_l_hoist` proves the reorder with the context FIXED
under the strong freshness `β ∉ ftvar_in_aenv Θd` (the look level's
R-first dance then applies verbatim — IH at an interim δ, fixed-context
rebinds, `a_solve_sub_ctx_exchange` as a `ctx_change` instance), and the
wrapper buys that freshness with ONE sanitizing pre-swap `(β δ)` on the
input derivation, delivering the motive facts (incl. `β ∉ dom Θd'`) at
the sanitized context.  The case bash (79 leaves): reorders applied
UNIFORMLY at ∀/⫯ subjects (no inversion), riding rebind
(`a_solve_sub_rebind_r_ctx`) at the ForallR-committing clauses, the
Check clause dropping into the finished §3 eq lemma with premises passed
unchanged, Arrow/GhostLF verbatim from §3d.  ⚠️ Three new traps in
§8c.6: `repeat split` dives into `flex_agree`; `simpl in <one hyp>`
by-clauses fail at COMPOSITE subjects (goal's `ftvar_in_pskl` stays
opaque to `fsetdec` — always `simpl in *`); a finished `_impl_complete`
lemma's implicit result args need their own kill tactic
(`kill_seq_call_g`).  ⛔ Next is the cstr fold's DESIGN FORK (§8c.6) —
decide (a) determinism-up-to-renaming vs (b) composing through the
a-side P5–P7 tower BEFORE writing the fold.  `make coq` green.

## 2026-08-15 (d) — ⭐⭐ **§8c.3 LEVEL 2a: the SOLVE block's eq runner is complete — and the threading levels' interface is settled**

`prop_run_complete.v` §3 (`e_solve_eq_run_complete` /
`e_solve_eq_impl_complete`, axiom-free, file 21 s): a `a_solve_eq`
derivation at scoped, covered inputs means the eq-solve runner answers.
⭐⭐ The design addition over the look template: the solve's ARROW row
threads the CONTEXT with each side's own fresh block, so the motive
carries the derivation's context `Θd` separately, related to the
runner's by `flex_agree V Θd Θr` — agreement of `a_flex_tvar` on the
inputs' variables (SE-FlexR's test is the solve cluster's ONLY
context-sensitive read) — plus a scoped-inputs premise
`V ⊆ ftvar_in_aenv Θd`; junk blocks ride by `flex_agree_push_blocks`
(`a_solve_sub_eq_generated_fresh_set` d-side, `e_solve_sub_eq_block`
r-side), and the §3b rebinds let the context RIDE the swap (no `β == b`
split anywhere).  ⚠️ Two traps: `eapply flex_agree_weaken` FIRST leaves
the set an evar and `fsetdec` under it hangs (>110 s → build agreement
bottom-up with explicit sets); `nonghost_pskl (⫯ _)`/`◇` have no
constructor and need their own `look_absurd` kill.  ⛔ Recorded in
§8c.6: sub-solve next (ForallL-first + strip-first reorders — the
dispatch peels subjects first, OPPOSITE of look); then a real DESIGN
FORK before the cstr fold — the tail runs at the runner's own YIELD,
which `flex_agree` cannot cover; candidate resolutions (determinism-up-
to-renaming vs composing through the a-side P5–P7 tower) are laid out
there.  `make coq` green.

## 2026-08-15 (c) — ⭐⭐⭐ **THE FIRST §8c.3 COMPLETENESS INDUCTION IS CLOSED — the LOOK block's two runners answer wherever a derivation exists**

`prop_run_complete.v` §2 (the file 92 → 1,381 lines, 18.6 s, axiom-free):
`e_lookeq_run_complete` and `e_looksub_run_complete` — an `a_lookeq` /
`a_looksub` derivation whose inputs the supply covers
(`ftvar_in_aenv Θ ∪ {{α}} ∪ ftv P ∪ ftv P' [<=] S0`) means the runner
does not return `None`.  Coverage is the ONLY premise beyond the
derivation, and it re-establishes trivially at every recursive call.
The §8c.6 scouting held: hand strong-induction principles per order
(`e_lookeq_order_sind` / `e_looksub_order_sind`, Section + term-level
`Fixpoint`, every premise doubled with its motive companion — the auto
`_ind` gives no IH through the Arrow conjunction), a runner-dispatch
case bash through the §8c.4 `simp` equations, and ONE swap per binder
row (`a_lookeq_rebind`/`_l`/`_r`, `a_looksub_rebind_l`/`_r`) — the
outputs are requantified existentially, so unlike the `_move` family no
`β ∉ dom Ξ ∪ ftv 𝒞` is owed.  ⭐⭐ The one thing scouting missed: the
runner's ForallR PRIORITY at a ghost-free ∀ target overlaps LS-ForallL /
LS-UnivGhostL in the relation, so a left-rooted derivation must be
REORDERED — `a_looksub_forall_r_first`, structural induction with the
swaps AFTER the IH and `a_looksub_ctx_exchange` gluing the two binder
entries; the eq layer has no overlap because `guarded_pskl` excludes
∀/⫯ heads.  ⚠️ Mechanics for the next levels, recorded in §8c.6: the
`kill_*_call` tactics must run OUTSIDE `match goal` branches
(rename-first scripts); `destruct … eqn:` substitutes the scrutinee into
the pre-asserted `≠ None` hypothesis and the `None` branch closes by
`False_ind _ (Hne eq_refl)`; `Set Implicit Arguments` leaves
under-`open` arguments explicit (pin with `Arguments`).  `make coq`
green.  Next: the solve level, same template.

## 2026-08-15 (b) — ⭐⭐⭐ **ALL TWELVE RUNNER BLOCKS DERIVE THEIR EQUATIONS — `def_consis_impl.v` flipped by the same tagged encoding, and BOTH entry-point exhibits are Qed**

The (a) entry's template applied to the three-way mutual
(`assign`/`unifyvar`/`consistency`): tag `consis_call` (⚠️ `Type`, not
`Set` — the Δ-slots carry metalib's `atoms`), combined order, three-way
`Fixpoint` injection, wrappers.  Consis-specific: the block returns
`consis_result` UNIFORMLY (a tag-dependent result type would extract
through `Obj.magic`; assign/unify rows dummy the join field and the
wrappers repack), the P0 × P matrix is ONE clause with a convoy
double-match in the original first-match order, and `Assign-UnivGhost-Id`
is an inner convoy in the flexible-head clause (the α-test commutes with
the shape test).  **13 equations — one per clause — 117 s, 17.8 MB `.vo`,
every obligation closed on the first run, axiom-free.**  With it the
check-mode entry exhibit is Qed (`prop_run_complete.v`):
`e_typing_run S0 mode_tc nil ⌈unit⌉ exp_unit = Some (unit result)`,
through SI-Check into U-Unit — the end-to-end witness that every runner
is computationally analysable.  Extraction after both flips:
`frost_guess.ml` 3,873 → 3,460 lines, `ocamlc -c` clean, no `Obj.magic` /
`Acc_rect` / `Fix_sub` / `FixWf`.  `make coq` green.  ⭐ Nothing is left
at `equations=no`; §8c.3's order-driven completeness induction has no
blocker left in the runners.

## 2026-08-15 (a) — ⭐⭐ **`def_sub_impl.v` DERIVES ITS UNFOLDING EQUATIONS — the mutual `with` re-encoded as ONE tagged block (user directive), with two measured compile-time traps on the way**

The §8c.4 blocker on the critical path is closed: `e_sub_impl` is
reducible.  `Equations` cannot derive unfolding equations for a mutual
`with` companion (settled, thirty-line reproduction), and the
continuation-hoist alternative is REFUTED at the guard checker (the
checker does not thread subterm specs through the walk's own inner fix —
also a thirty-line reproduction).  What landed is the user's encoding:
`sub_call : Set := sub_call_sub P | sub_call_flex Ξ α`, one block
`e_sub_call_impl` over the tag, `by struct` on a combined single-inductive
order `e_sub_call_order` mirroring `def_order.v` §6, with a mutual
`Fixpoint` injection from the untouched mutual orders and thin
same-signature wrappers `e_sub_impl` / `e_sub_flex_impl` — so
`def_typing_impl.v`, `def_pat_impl.v` and `Extract.v` are byte-identical.
Two traps, both measured and both in handoff §8c.4: (i) the tag must be
the FIRST argument or the case tree cross-multiplies the flex clauses
under the sub clauses' column splits (840 obligations, 30 unclosable);
(ii) clause-pattern dispatch makes `equations=yes` prove one lemma per
case-tree LEAF — 102 equations, 965 s, a 105 MB `.vo` — so the sub side
is ONE clause whose dispatch is term-level convoy matches (each arm binds
the equality the obligation tactic `subst`s), which derives 7 clause
equations in 150 s / 26 MB.  Dispatch order is the reference
implementation's, unchanged (ForallR before ForallL, §8b.1).  Extraction:
`frost_guess.ml` 3,873 → 3,783 lines (the two mutual functions merge into
one tagged function plus wrappers), `ocamlc -c` clean, no `Obj.magic` /
`Acc_rect` / `Fix_sub` / `FixWf`.  `make coq` green, README 32/32,
`Print Assumptions` closed on the impl, its equations, the injection and
`e_sub_run_sound`.  ⛔ Left at `equations=no`: `def_consis_impl.v` only —
and the exhibit below shows it is now THE blocker; this file is the
template for flipping it.

**Later the same day — ⭐ THE ENTRY-POINT COMPLETENESS EXHIBIT IS QED**
(`frost/ext_algo/prop_run_complete.v`, the campaign file of §8c.3/§8c.5):
`e_typing_run_complete_unit_infer` — `e_typing_run S0 mode_ti nil
pskl_hole exp_unit = Some (mk_typing_result S0 nil ptyp_unit)`,
axiom-free, six tactics, every one of them a §8c.4 deliverable
(`simp e_typing_impl`, `cbn`, `unfold e_sub_impl`,
`simp e_sub_call_impl`, `cbn`, `reflexivity`).  A Qed-opaque totality
proof sits in the term, so no plain computation could have done this —
the equations quantify over the domain proof, which is §8c.3's argument
made concrete.  ⚠️ The check-mode twin is stuck exactly at
`e_consis_impl` (no equations), which settles the next move.

## 2026-08-14 (d) — ⭐⭐ **THE COMPLETENESS CAMPAIGN IS RESHAPED — induct on the ORDER; and `algo/prop_swap.v` gains the two equivariance lemmas it never had**

Two things, and the first is why the second was written.

**⭐⭐ (2c)+(2d) SHOULD BE ONE INDUCTION, ON THE ORDER** (handoff §8c.3).
Lifting an `a_*` run to an `e_*` run by structural induction on the `a_*`
derivation does NOT go through: the `a_*` rule opened its binder at its own
`α0`, the `e_*` rule must open at the supply's `α`, so the IH has to be
applied to the TRANSPOSED sub-derivation — which is not a structural
subterm.  The two textbook repairs (a nominal permutation-parameterised
motive; a height-indexed mirror of all fourteen judgements) are both
expensive.  ⭐ The repair is to induct on `e_*_order` instead: the domain
predicates of `def_order.v` are not merely total but CANONICAL — their
premises name `supply_fresh S0` explicitly (`def_order.v:429-433`).  So the
induction is always available (the orders are unconditional), the IHs land
at the runner's committed names, and the `a_*` derivation is only INVERTED
and transposed at each level, by ONE transposition, with the existing
single-swap kit.  ⭐ It also collapses (2c) and (2d): the conclusion can be
the runner's `Some` directly, and the AGREEMENT the ForallR output test
needs is available because the order pins the name.

**`algo/prop_swap.v` §16** — the prerequisite that finding exposed:
`swap_exp` plus `swap_exp_open_var` / `_fresh_id` / `_fvar_notin` /
`_ftvar_notin`, `lc_exp_swap`, `swap_block_ftv_filter`, and ⭐ `a_pat_swap`
and `a_typing_swap`.  §5–§12 covered the whole tower below them; these two
were never written because nothing needed them (`a_pat_complete`
regenerated its cofinite family with `a_pat_rename_tm`, which went with the
exists-fresh conversion).  `prop_completeness_pat.v:885` had already
predicted `a_pat_swap` mirrors the others row by row.  All eight `Closed
under the global context`; `make coq` green, README 32/32.

⚠️ `swap_exp` is not optional — holding the term fixed fails at the binder
rows, whose IH would then need `a <> x` for a binder the ROW chooses.
⚠️ And this is NOT `a_pat_rename_tm` returning: that lemma renamed a type
variable across a run while `x` stayed put and unconstrained; a
transposition moves every atom at once, so no side condition on `x` is
owed.  The ⛔ note at the end of §6 is scoped to its own statement shape.

⚠️ Traps: the boxed-comment quote trap bit again (a quoted phrase inside
`(* … *)` swallows the terminator); `swap_aenv` is a `map`, so
`swap_aenv (Ξ ++ Θ)` and `swap_aenv Ξ ++ swap_aenv Θ` are equal only
PROPOSITIONALLY while the singleton `swap_aenv (x ~ b)` does reduce — fold
the appends back and `exact` stops working; and a positional
`[ t1 | … | tn ]` freshness dispatch is wrong at exactly one row, because
`ftvar_in_exp (exp_abs_anno Aan e)` splits under `simpl` into two
components where `exp_abs e` gives one.  The file now selects by GOAL SHAPE
(`swap_notin_split`).

## 2026-08-14 (c) — ⭐⭐ **COMPLETENESS CAMPAIGN 2a + 2b(part): every runner TEST gains its converse, and the subtyping walk gains the two run-invariants it was missing**

`frost/ext_algo/prop_dec.v` (new, 33 lemmas) and
`frost/ext_algo/prop_run_invariants.v` (new, 8 lemmas) — all
`Closed under the global context`.

**2a — the deciders.**  `def_dec.v` and `def_pat_impl.v` §1 proved their
inventory SOUND ONLY, which is all a soundness-only runner owes.  Once
`None` has to mean UNTYPABLE every `false` must be earned, so each check
owes `<the guard> -> … _ck = true`.  All but one are the same induction
read backwards; `wf_pskl_ck` is the exception on both counts its header
named — FUEL ADEQUACY (the bound `size_pskl P` is the checker's own
structural depth: the ∀ row's descent into `open P1 (pskl_var_f β)` costs
exactly the `S` the `pskl_all_syn` node pays for, ⚠️ state it as an
inequality or it is not its own IH) and THE COFINITE ROW (instantiated at
the checker's `supply_fresh` name by `a_wf_pskl_all_inv_at`).  §6 adds the
nine evidence-carrying DECOMPOSITIONS, so **every test a runner performs —
boolean or not — now has both directions**.  ⚠️ `uniq` is load-bearing in
`lookup_binding` and the two `split_at_key_*`: the scans stop at the FIRST
occurrence and `binds` is an "appears somewhere" predicate.

**2b (part) — the run invariants.**  `e_sub_defs_mono` /
`e_sub_flex_defs_mono`, the twin of `e_consis_defs_mono` the campaign
flagged as missing, plus `e_consis_lc` and `e_sub_lc` / `e_sub_flex_lc`.
⭐ The `e_sub` twin was missing because TERMINATION only needed the
consistency block's (`e_sub_order_total` takes `aenv_defs_mono Θ0` as an
INPUT hypothesis); completeness makes the output side load-bearing, since
`def_typing_impl.v`'s AT-Anno/AT-Freeze rows test `defs_mono_ck` on a
subtyping run's result.  ⚠️ `e_sub_lc` needs `aenv_defs_mono Θ0` —
`Flex-Assign` substitutes a context DEFINITION into the counterpart, so
the counterpart's local closure survives only because the payload is mono.

⛔ Still open in 2b: lc / defs-mono for the `e_pat` and `e_typing` OUTPUTS,
and the relation-side SHAPE facts (ForallR's `Ξ ++ (α~tvar) ++ Θ1`, the abs
rows' binder-marker split, the `⌈⌉`-image readbacks).  Handoff §8c.2.

⚠️ Traps re-paid: the metalib `one` form (a `change`, not `simpl_env`,
bridges cons-form goals to `x ~ b ++ Θ` hypotheses); an intro pattern `_`
on an equation the returned `sig` proof MENTIONS fails with "used in
conclusion"; and `simpl` turns `Flex-Assign`'s substituted VARIABLE into an
`if α == β then … else …` that must be decided before anything downstream
can see a skeleton.

## 2026-08-14 (b) — ⭐⭐ **THE RUNNER'S SOUNDNESS REACHES THE PAPER'S OWN DECLARATIVE JUDGEMENT**

`frost/ext_algo/prop_run_corollaries.v`: two corollaries, one per mode,
composing the four links that already existed — `e_typing_run_sound`
(def_typing_impl.v §5) ∘ `e_typing_sound_init` (prop_typing.v §2) ∘
`a_typing_sound` ∘ the conservativity corollaries
(`algo/typing/prop_closed.v`).  At a closed, well-formed program, if the
EXTRACTED function answers `Some r` then `{{ nil ⊢ˢᵈ[ m ] e ⦂ … }}d` and
`{{ nil ⊢[ m ] e ⦂ … }}d` — the paper's own declarative systems, with the
run's residual flexibles closed off by the metasubstitution `ζ` soundness
hands back.  Both `Closed under the global context`.  The entry supply is
FIXED at `ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e`, which is the
one `e_typing_sound_init` chooses and the reason it is hypothesis-free;
the only side condition left is `{{ nil ⊢ᵉ e }}a`, which is
`a_typing_sound_infer`'s and expected.  ⚠️ SOUNDNESS ONLY — `None` is
still justified by nothing; that is runner completeness, and with
totality it is what yields decidability.  ⚙ Deliberately NOT in
`README.v`: the paper index carries the paper's labelled statements, and
the README-worthy claim on this line is the decidability corollary that
completeness owes.

## 2026-08-14 — ⭐⭐⭐ **PHASE 4 CLOSED: EVERY JUDGEMENT EXECUTES — TODO (2) of the extractable-encoding hand-off is COMPLETE**

The Bove–Capretta runners for all thirteen judgements beyond `guess^TY`
landed (`docs/HANDOFF-extractable-algo-encoding.md` §8b.7): the guard
deciders (`def_dec.v`, soundness-only), the collection
(`def_look_impl.v`), the solving layer and its fold (`def_solve_impl.v`),
the extraction pipeline (`def_extract_impl.v`), the MUTUAL
`assign`/`unifyvar`/`consistency` block (`def_consis_impl.v`), the MUTUAL
subtyping walk (`def_sub_impl.v`, ForallR before ForallL per §8b.1), and
`e_split`/`e_pat`/`e_typing` (`def_pat_impl.v` / `def_typing_impl.v`,
which also carry the two judgements' NEW orders and totality —
unconditional: every walk precondition is TESTED at the call site rather
than threaded as metatheory).  Result shape decided for all partial
runners: `option (sig (spec …))` — soundness-only, rejection-justification
deferred to a determinism pass.  Every `*_run_sound` is Qed and
axiom-free; `extraction/Extract.v` exports all runners and the emitted
OCaml passes `ocamlc -c`.  ⭐ One phase-2 bug surfaced BY the runners and
fixed: `def_order.v`'s ForallL premise pinned the extraction's supply at
`S0` where `e_sub__forall_l` runs it at `add α S0` — invisible to the
(supply-parametric) totality proofs, forced by the runner's double duty
(satisfy the order's premise AND the rule).  The traps paid for
(silent-obligation Equations mode, the cons/`++` simple-apply gap, the
`Forall_app_intro` eauto explosion, `subst`-through-`fix` guard breakage,
catch-all row expansion, `coqc | head` SIGPIPE corruption) are recorded in
§8b.7.

## 2026-08-13/14 — ⭐⭐⭐ **THE TERMINATION CAMPAIGN CLOSED: `e_sub_order_total` UNCONDITIONAL — the subtyping walk and its whole call graph terminate**

**Later on 2026-08-14 the one hypothesis was DISCHARGED**: the consistency
block's totality (`e_consis_order_total`) is proved by the measure
`(W, ndef, size, walk)` with `W := holes + undefined-flexibles` — holes are
the only source of new flexibles (Assign-SolveM's guess block is exactly the
pattern's holes), so any run that grows the context strictly consumed W; the
W-preservation inequality `nundef Θ' + ndef Θ' ≤ nundef Θ + ndef Θ + holes`
chains at the Arrow row and, with ndef-monotonicity, decides the tie/strict
case split.  ⚙ §7.4's prediction that the worklist's `num_etvar`/`split_depth`
machinery would be needed was pessimistic — holes-as-fuel replaces
split-depth, because the guess consumes the whole pattern shape at once.
`e_sub_order_total` now carries NO hypothesis.  The §7.3 finding is FILED in
PAPER-GAPS.md with its mechanized status.  Remaining for TODO (2): phase 4's
runners only, unblocked end to end.  The original entry:

**`make coq` exit 0; zero `Admitted`/`Axiom`; every named theorem `Print
Assumptions`-closed.**  The paper's undischarged decidability argument
(HANDOFF-extractable-algo-encoding.md §7.3: "never guess polytypes out of
thin air" is offered *against* the undecidability of impredicative
polymorphic subtyping, and never proved) is now mechanized for the
subtyping side, over `frost/ext_algo/`'s threaded encoding:

- **The principle as theorems** (`prop_termination.v` §2–§6):
  `e_guess_mono_nall` (the guess copies ∀s, never invents one), carried
  through the WHOLE extraction — `e_extract_nall : nall Q' ≤ nall P'`,
  the instantiation bounded by the INHERITED SKELETON ALONE (sharper than
  planned: the collection deposits only counterpart fragments).
- **The decrease theorem** (§7–§9): the codomain-spine prediction of §8b.2
  REFINED to the head ∀/⫯-chain count `hnall` — a spine count does NOT
  decrease at ForallL (an eq-payload can be ∀-headed); `hnall` does:
  `e_extract_forall_l_hnall`, with both hypotheses the rule's own premises.
- **Bove–Capretta orders for the whole call graph** (`def_order.v`, new):
  one constructor per judgement, shape-conditional premises (partial
  judgements need no failure enumeration; runners invert once).
- **Totality**: collection UNCONDITIONAL; solving/fold/extraction at lc
  inputs (§10–§11); ⭐⭐ `e_sub_order_total` (§13) by the lex measure
  `(fnd_mode M, nall P0, hnall P, ndef Θ, size P, walk)` — with the
  consistency block's totality as its ONE explicit hypothesis
  (unification-style, its own campaign; its orders are defined and its
  defs-mono preservation proved, §12).

Phase 0 (reference-implementation probes, honest weakness notes) and
phase 3 (ForallR-before-ForallL, settled by citation `type.ml:910/958`)
are in HANDOFF §8b.1–8b.2.  Full state and traps: HANDOFF §8b.3–8b.5.

## 2026-08-12 — ⭐⭐⭐ **TWO RELATIONS, AND THE RULES EMBED THE PAPER'S: `ad_pat_sub_v` RETIRED, `_gv` RENAMED `_fuel`**

**`make coq` exit 0; README.v 28/28 `Print Assumptions` closed; no `Admitted`,
no `Axiom`.**

The `ad_pat_sub` family is now exactly **two `Inductive`s and nothing else**:

| | what it is | where it appears |
|---|---|---|
| `ad_pat_sub` | the paper's all-in-one subtyping box, WITH the leaf presupposition | every rule, every statement |
| `ad_pat_sub_fuel` | that plus the completeness measure's fuel index | inside the subtyping-completeness proof |

- ⭐ **`ad_pat_sub_v` IS GONE.**  It was `exists n, ad_pat_sub_fuel n …` — a
  three-line `Definition`, not a relation — and `ad_pat`'s / `ad_sd_typing`'s
  six BASE ROWS embedded it, so **an existential over a proof-measure index sat
  in the specification**.  It was there only because the plain relation lacked
  the leaf datum, so a fuel had to be named (and then hidden) purely to carry
  it.  Those rows now embed `ad_pat_sub` itself.
- ⭐ **`ad_pat_sub_gv` → `ad_pat_sub_fuel`** (653 sites).  `_gv` encoded two
  distinctions that no longer exist — `g` (the retired non-hygienic mirror) and
  `v` (leaf-valid, which the plain relation now carries) — so the name recorded
  history rather than content.  The one thing it adds is the FUEL.  Also
  `_of_gv` → `_of_fuel`, `_to_v` → `_to_fuel`, `ad_pat_sub_precise_upre_gv` →
  `_upre_fuel`, `ad_precise_extends_pat_sub_gv` → `_fuel` (then merged away).
- ⭐ **The seven `ad_pat_sub_v_*` wrappers became PLAIN structural lemmas**,
  by DIRECT induction — `mono`, `subst_mid`, `isub`, `weaken`, `rename_tvar`,
  `rename_paint`, `sk_to_d`.  ⚠️ Five were restored from git, and TWO of the
  five (`isub`, `weaken`) came from a PRE-leaf-premise commit and had to be
  regenerated from their fuelled twins instead — their leaf rows were missing a
  subgoal, which surfaces as `Wrong bullet -: Current bullet - is not finished`.
- ⭐ **`ad_pat_sub_ty_to_d` and `ad_pat_sub_sk_to_d` are now siblings** on the
  plain relation; the fuelled `sk_to_d` is gone.  It had been statable only
  over the mirror — the fuel was never what that proof needed, only the datum.

⭐⭐ **THE FACT THAT MAKES ALL OF THIS MECHANICAL: the two relations differ by
the INDEX ALONE.**  Every premise of `ad_pat_sub_fuel`'s twelve rows lines up
with `ad_pat_sub`'s, in order.  So porting a lemma between them is a statement
change with an UNCHANGED body (only `IHad_pat_sub_fuel` → `IHad_pat_sub`), and
that is how `sk_to_d`, `isub` and `weaken` were produced.

⚙ **Where the two maps survive, and why none of them is a detour**:
`ad_pat_sub_to_fuel` INTRODUCES the measure exactly where a proof is about to
call `a_sub_complete` (three sites in `prop_completeness_typing.v`, three in
`prop_completeness_pat.v`); `ad_pat_sub_of_fuel` drops it where a plain
derivation is wanted.  The single lemma that does both,
`ad_precise_extends_pat_sub`, documents why: precision-substitution must be
fuel-PRESERVING (the completeness ForallL case applies its IH to the
substituted premise), so `_upre_fuel` cannot be stated without the index,
while this statement has no fuel on either side.

## 2026-08-12 — ⭐⭐ **THE FUEL DIRECTION LANDS UNCONDITIONALLY, and the plain relation's structural layer turns out to be DEAD**

**`make coq` exit 0; README.v 28/28 `Print Assumptions` closed; no `Admitted`,
no `Axiom`.**  −561 / +136 lines.

⭐ **`ad_pat_sub_to_v` (algo/sub/prop_soundness_subtag.v): every plain join
ADMITS a fuel.**  With the existing `ad_pat_sub_of_gv` this makes the two
relations INTERDERIVABLE.  It is **unconditional** — any sort, any Θ, no
ghost-freeness — and that is new: it became provable only because
`ad_pat_sub` took on the leaf presupposition earlier the same day.  Before
that the leaf rows had to RECOVER the datum, which needed a ghost-free subject
over a declarative context; now the datum is a PREMISE of the row that needs
it, so every row matches one for one.

⭕ **This CLOSES obstruction (A)** of `docs/HANDOFF-closed-corollaries-
declarative.md` — the `ad_pat_sub → ad_pat_sub_gv` direction `def_subtyping.v`
recorded as "still owed", and the SK sort it left open.  `prop_conserv.v` §13's
`ad_pat_sub_ty_to_v` (~90 lines, TY sort only, ghost-free subject, declarative
context) is RETIRED for it, and `base_row` lost a tactic argument with it.

⚙ **THE FUEL IS THE DERIVATION'S HEIGHT** and the collection is routine —
leaves conclude at any fuel, UnivGhostL/UnivGhostLG/FlexMono do not increment,
and Arrow/ForallR/ForallL each have exactly ONE recursive premise, so no `max`
and no `_fuel_weaken`.  ⚠️ ForallR is COFINITE, so one fuel must serve
infinitely many α while the IH hands back a different one per α: take the IH at
ONE fresh α and regenerate the family at THAT fuel with
`ad_pat_sub_gv_rename_tvar`.  ⚠️ The witness must be fresh for
`ftvar_in_aenv Θ`, NOT `dom Θ` — a flexible's DEFINITION may mention a rigid,
which is the rename's second side condition (new `ftvar_in_aenv_binds_def`,
prop_flex.v).

⭐ **AND THEN THE PLAIN STRUCTURAL LAYER TURNED OUT TO BE DEAD.**
`ad_pat_sub_{subst_flex,subst_flex_def,rename_tvar,strip_suffix}` — ~450 lines
running in parallel with their `_gv` twins — have NO consumer anywhere: every
occurrence in the tree is their own definition or a comment naming them.  Their
users had long since moved to the `_gv` mirrors, which is where the fuel lives.
Deleted.  ⚠️ **A grep that filters out lines STARTING with `(*` does not filter
comment lines that merely MENTION the name** — that is what made them look live
on the first pass; check for `Lemma`/`Qed` boundaries, or just delete and let
the build answer.

So no proof in the tree round-trips through the fuel: `ad_pat_sub_to_v`'s only
consumer is `base_row`, where reaching `ad_pat_sub_v` is the actual content.

## 2026-08-12 — ⭐⭐ **`ad_pat_sub_g` IS DELETED: two relations where there were three**

**`make coq` exit 0; README.v 28/28 `Print Assumptions` closed; no `Admitted`,
no `Axiom`.**  −1505 / +539 lines.

With the leaf presupposition on `ad_pat_sub` itself (previous entry), the
third relation had nothing left to be: `ad_pat_sub_g` was `ad_pat_sub` + fuel
− leaf datum, and every one of its ~20 lemmas duplicated a `_gv` twin.  Gone,
together with `ad_pat_sub_gv_forget`.  What remains is exactly two:
`ad_pat_sub` (paper-faithful `Inductive`, WITH the datum) and
`ad_pat_sub_gv` (that + the completeness measure's fuel).

**⭐ THE ONE GENUINELY NEW OBLIGATION — and it is not where it was expected.**
The plan predicted ~10 look-layer lemmas that CONSTRUCT `_g` and would have to
supply the leaf datum.  **The look layer never constructs `_g`.**  Every `_g`
in `look/prop_sub_var.v`, `look/prop_sub_cstr.v`, `look/prop_extract.v` is a
HYPOTHESIS — the declarative join being simulated — and every conclusion is an
algorithmic `a_looksub` / `a_solve_sub` / `a_extract` fact; every call site
already held a `_gv` and called `ad_pat_sub_gv_forget` to weaken it, so those
migrations were a rename and a deletion.

The obstacle was one level up: P7's two ForallL rows
(`prop_completeness_sub_gen.v`) reshape the join's SUBJECT along `≡ᵘ` before
handing it to the look layer, and the reshaped subject's leaf data cannot be
read off the original's.  So refinement had to be shown stable under the
equational theory on its SOURCE — a fact the tree did not have in any form
(nothing related `a_pskl_tyequiv` to `ad_refine_pskl`):

```coq
Lemma ad_refine_pskl_tyequiv_source : forall Θ0 P P',
  {{ Θ0 ⊢ P ≡ˢ P' }}a -> forall Θ Δ Pt,
    (forall x b, binds x b Θ0 -> binds x b Θ) -> {{ ⊢ Θ }}a ->
    ({{ Θ ⨟ Δ ⊢ᵣₚ P' ⊳ Pt }}ad -> {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Pt }}ad)
    /\ ({{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Pt }}ad -> {{ Θ ⨟ Δ ⊢ᵣₚ P' ⊳ Pt }}ad).
```

⭐ It costs ~140 lines, and three things make it cheap:

- **`a_uskl_tyequiv_erase` does the sort work.**  The datum is stated on the
  ERASURE `⌊R⌋ˢ`, and `≡ᵘ` projects onto the `pskl`-level `≡ˢ` — so no
  uskl-level refinement theory is needed at all.
- **`≡ˢ`'s `__sym` forces a BICONDITIONAL motive**, and `__trans` then
  composes.  Only four rows generate: `__flex_def` is
  `ad_refine_pskl__flex_l` one way and the existing
  `ad_refine_pskl_unfold_def_subject` the other.
- **Each congruence row is an induction on the REFINEMENT, not on the
  equivalence** (`refine_source_{arrow,all,tophole}`): the row that consumes
  the source is unique, and the only other reachable row is `__flex_r`, which
  does not touch the source and is simply peeled and rebuilt.
  ⚠️ `ad_refine_pskl__tophole_fill` runs its premise at `(α ~ tvar) ++ Θ`,
  which is why the statement is generalized over context EXTENSIONS and why
  the tophole helper alone needs `{{ ⊢ Θ }}a` — to rebuild the row at
  `L ∪ dom Θ` and keep the extended context well-formed.

**The rest was mechanical**, in this order (each step compiling on its own):

1. `ad_refine_pskl_tyequiv_source` + its three helpers into
   `prop_completeness_sub_precise.v`, beside
   `ad_refine_pskl_unfold_def_subject`.
2. Two wrappers in `prop_sub_msubst_equiv.v` —
   `ad_refine_pskl_tyequiv_uskl_subject` (via the erasure) and
   `ad_refine_pskl_paint_transport` (the ⊳-mirror of
   `ad_pat_consis_paint_skl_transport`, via `a_tyequiv_pskl`) — then its three
   `≡ᵘ`-layer lemmas converted to `_gv`.
3. `prop_completeness_sub_precise.v`: the 15 twinned `_g` lemmas deleted
   (−1097 lines); `_g_ftag_sub` / `_g_concrete_target` renamed to `_gv`.
4. The look layer, `prop_completeness_sub_gen.v` and `cex/`: renamed, and the
   `ad_pat_sub_gv_forget` calls dropped.
5. The `_g` `Inductive` and `ad_pat_sub_gv_forget` deleted.

⚠️ **THE ONE TRAP, and it bites in three files**: `_gv__arrow` carries the
DOMAIN's leaf refinement BETWEEN the consistency premise and the recursive
one, so it is the single row where the extra premise is not last — every
positional `H0` naming the tag equation `Ψ [=] Ψ1 ∪ Ψ2` in an arrow row
shifts to `H1` (`ad_pat_sub_gv_ftag_sub`, `_gv_concrete_target`,
`a_looksub_solve_complete_gen`).  The LEAF rows are safe: there the new
premise comes last, so `H`…`H3` keep their meanings.

⚙ `cex/` needed the datum at two witnesses and it was free at both: the
configurations `∀ᵗᵃᵍε.#0 ⩽ β` (`cex_p6ss_sub_target_ftv.v`,
`cex_p7_sub_monoish.v`) instantiate the ∀ with the rigid `β` itself, so the
leaf refinement is `β ⊳ β` — `ad_refine_pskl__var`.  The other two cex files
already carried `_gv` twins of their `_g` witnesses, so those `_g` witnesses
were simply dropped.  ⚠️ `right. simpl; auto` does NOT close
`a_binds_tvar β Θ` (a three-way disjunction), and **`auto` does not fail when
it leaves the goal open** — the error surfaces only at `Qed` as "Attempt to
save an incomplete proof".  Use `right; unfold a_binds_tvar; eauto`.

README.v's P5 entry now `Check`s `ad_pat_sub_precise_upre_gv`.


## 2026-08-12 — ⭐⭐ **THE LEAF PRESUPPOSITION GOES ON `ad_pat_sub` ITSELF, and `ad_pat_sub_g_of` DIES**

**`make coq` exit 0; README.v 28/28 `Print Assumptions` closed; no `Admitted`,
no `Axiom`.**

`d_pat_sub` has carried the paper's presupposition on skeleton consistency
(`declarative.tex:2074`) on its consistency-leaf rows since 2026-08-11.
`ad_pat_sub` did not — a separate mirror `ad_pat_sub_gv` carried it instead —
so the paper's own relation and its decl-in-algo twin disagreed, and every
bridge had to detour through the mirror.  The premise is now on
`ad_pat_sub`'s four leaf rows (`__infer`, `__check`, `__univ_ghost_r`, and
`__arrow`'s DOMAIN, which is itself a consistency leaf):

```coq
{{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) }}ad
```

- ⭐ **`ad_pat_sub_g_of : _g -> ad_pat_sub` IS DELETED, and it is now FALSE.**
  A plain fuel derivation has no leaf datum to hand over.  `ad_pat_sub_of_gv`
  is re-proved as a DIRECT induction on `_gv` instead of factoring through
  `ad_pat_sub_gv_forget` + `_g_of`.  Only the leaf-valid mirror reaches the
  plain relation now — which is the point of the change.
- ⭐ **`cex/cex_ad_pat_join_not_leaf_valid.v` §1/§3b RETRACTED, deliberately.**
  `cap_plain` asserted that the capture pair `∀X.◇ ⩽ ∀ˢX.X` IS derivable in
  the plain relation; that is exactly what the change forbids.  The record is
  KEPT, not deleted: §2 (`cap_no_refine`) is the reason the presupposition has
  to be ON THE RULE, and no consistency reasoning recovers it.
- ⭐ **The TY sort pays NOTHING.**  `d_consis_refine_ty`
  (algo_decl/prop_conserv.v): at `N = TY` the datum is REFLEXIVITY, because
  consistency preserves the plain erasure (`d_consis_btyp_erase`) and both
  sort inclusions agree with it (the two new coercion equalities
  `uskl_to_pskl_utyp_to_uskl` / `bskl_to_pskl_btyp_to_bskl` in
  `frost/prop_coercions.v`).  So the TY-sort bridge `d_sub_to_ad` gains only
  a `d_wf_utyp Γ C` hypothesis — the paper's usual EXTERNAL well-formedness
  (docs/WF-SIDE-CONDITIONS.md) — and its one call site, `base_row`, has it for
  free: every base row's subject is the painting of a `ptyp` the row already
  has well-formed (`d_wf_utyp_painting_syn`).
- ⚙ New in `decl/prop_wellformed.v`: `d_wf_utyp_open` (a ∀ body opened at an
  arbitrary well-formed `ph` is well-formed).  It was `d_sub_wf`'s two ForallL
  cases duplicated inline; both now call it, and so do `d_sub_to_ad`'s two.
- ⚙ **FOUR DEAD LEMMAS REMOVED** from `algo/prop_pat_sub.v` —
  `ad_pat_sub_isub`, `ad_pat_sub_weaken`, `ad_pat_sub_psi_cong`,
  `ad_partial_precise_isub`.  Each had exactly one occurrence in the tree: its
  own definition.
- ⚙ `ad_pat_sub_{subst_flex,subst_flex_def,rename_tvar,strip_suffix}` MOVED
  from `algo/prop_pat_sub.v` to `algo/sub/prop_soundness_subtag.v`, beside their
  `_gv` twins — that is where the refinement transports they now need live.
  Both consumers (`prop_suffix_erase.v`, `prop_rename_decl.v`) already import
  it.  ⚠️ In that file bare `guarded_pskl_subst` resolves to
  `prop_looksub.v`'s homonym (it has an extra disequality premise); the one
  wanted is `guarded_pskl_subst_var`.

## 2026-08-11 — ⚙ **`etag` → `tag`; `prop_decorate.v` DELETED into `prop_coercions.v`**

**`make coq` exit 0; README.v 28/28 `Print Assumptions` closed.**

- **`etag` → `tag`**, 689 occurrences: the `e` stood for the ε of the tag
  variable, which the sort names already carry.  `frost/prop_etag.v` →
  `prop_tag.v`, `decl/prop_etag_swap.v` → `prop_tag_swap.v`, and the ott
  constructor `all_etag` → `all_tag` (so `utyp_all_etag` / `uskl_all_etag`
  became `utyp_all_tag` / `uskl_all_tag`; `def_ott.v` / `prop_ln.v`
  regenerate).  ⚠️ The rename is `(?<![A-Za-z])etag`, NOT a plain
  `etag` → `tag`: **`solvetag` contains `etag` as a substring** (`solv`+`etag`),
  and 55 identifiers in the `a_solvetag*` family would have become
  `a_solvtag*`.  `retag` / `retagging` in prose are untouched for the same
  reason.  ⚙ Regeneration was checked idempotent first (`touch language.ott
  && make ott lngen` → zero diff) before editing the grammar.
- **`deco_algo/prop_decorate.v` is gone.**  86 lines, six lemmas, every one of
  them a `pskl_to_uskl` conversion fact — `prop_coercions.v` is the tree's
  single home for those, so they moved into its §1 / §2 / §3 by KIND (the
  file's own organisation), and the 29 `Require`s of the dead file were
  dropped.  ⚠️ The move only became possible after `pskl_to_uskl` ITSELF moved
  from `deco_algo/def_decorated.v` to `frost/coercions.v` — it is a map
  between two of the six sorts, so `coercions.v` was always its home, and its
  inverse `uskl_to_pskl` had already moved there earlier the same day.
  ⚙ `pskl_to_uskl_lc` / `_guarded` went into §3 deliberately: that section is
  inside the file's scoped `Set Implicit Arguments` region, which is what
  keeps their subject implicit as it was in the old file.

## 2026-08-11 — ⚙ **NOTATION SCOPES: the SYSTEM moves off the turnstile and onto a `{{ … }}d` / `{{ … }}ad` / `{{ … }}a` / `{{ … }}da` DELIMITER**

**`make coq` exit 0; README.v 28/28 `Print Assumptions` closed; no `Admitted`, no `Axiom`.**

Every judgement of every system is now written inside a system-tagged brace
pair, and each pair is the delimiter of its own notation scope
(`frost_d_scope` / `frost_ad_scope` / `frost_a_scope` / `frost_t_scope`,
delimited `%d` / `%ad` / `%a` / `%t`).  47 notations were re-declared and
**4 043 use sites** rewritten across 88 files; the tree is unchanged
semantically — no rule, statement or proof was touched.

**Why.** Two earlier passes tried to carry the system ON the turnstile and both
failed the same way: the system mark competed with the marks the judgement
itself needs.  First it was a subscript (`⊢ₐ`), which reads as a sort, and `ᵃ`
meant `a_` in `a_wf_pskl` but `ad_` in `ad_pat_consis`.  Then (2026-08-09) it
was a superscript, which produced three-glyph stacks — `⊢ᵣₚᵃᵈ`, `⊢ₚᵣᵃᵈ`,
`⊢ₛᵃᵈ[` — and forced `ad_sd_typing` to DROP its `ˢ` (leaving a plain `⊢ᵃᵈ[ M ]`)
purely to avoid a third mark.  With the system on the delimiter the turnstile is
free, so one relation's copies across systems differ by the delimiter ALONE:

| before | after |
|---|---|
| `Γ ⨟ Δ ⊢ᵣ Q ⊳ P` / `Θ ⨟ Δ ⊢ᵣᵃᵈ Q ⊳ P` | `{{ Γ ⨟ Δ ⊢ᵣ Q ⊳ P }}d` / `{{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad` |
| `Γ ⊢ˢ[ M ] e ⦂ A` / `Θ ⊢ᵃᵈ[ M ] e ⦂ B` | `{{ Γ ⊢ˢᵈ[ M ] e ⦂ A }}d` / `{{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad` |
| `Γ ⨟ Δ ⊢ₚₛ P` / `Θ ⨟ Δ ⊢ₚₛᵃ P` | `{{ Γ ⨟ Δ ⊢ₚₛ P }}d` / `{{ Θ ⨟ Δ ⊢ₚₛ P }}a` |
| `Γ ⊢ₛ[ M ] e ⦂ P` (skeleton) | `{{ Γ ⊢ˢ[ M ] e ⦂ P }}d` |
| `Θ ⊢ᵗ[ Δ1 \| Δ2 \| P0 \| Ψ ] R ∼˙ Q ⊣ Θ'` | `{{ Θ ⊢[ Δ1 \| Δ2 \| P0 \| Ψ ] R ∼ Q ⊣ Θ' }}da` |

The two axes left on the turnstile: **SUPERSCRIPT = which copy** (bare types,
`⊢ˢ` skeletons, `⊢ˢᵈ` syntax-directed — `ˢ` and `ˢᵈ` are siblings, not a mark
and its refinement) and **SUBSCRIPT = which relation** (`⊢ᵣ`/`⊢ᵣₚ`, `⊢ₚᵣ`,
`⊢ₛ`/`⊢ₑ`, and `⊢ₚ`/`⊢ᵦ`/`⊢ᵤ`/`⊢ₚₛ`/`⊢ᵤₛ` for well-formedness).  The ε-tagged
system drops its dots — `∼˙`/`⩽˙` existed only to stay apart from the
algorithmic `∼`/`⩽`, and `}}da` does that job now (the delimiter was spelled
`}}t` until `93c3624`).

**NOT wrapped**, deliberately: `κ ∷ Θ ⊑ Θ'` (`a_inc`), `Θ ⊴ Θ'` (`a_isub`) and
the conversion / substitution functions.  The delimiter answers "which system?",
and those are meta-level relations with no cross-system twin, so the question
has no answer for them.

Two traps worth recording:

- ⚠️⚠️ **The first slot of a `{{ … }}X` notation must carry NO level
  annotation.**  Metalib already owns `{{ x }}` for the atom-set singleton
  (`Metatheory.v:41`), so every `{{`-prefixed rule shares its prefix; camlp5 can
  only factor rules whose shared prefix uses the same entry, and metalib's is
  plain `constr`.  Annotating it fills the build with
  `notation-incompatible-prefix` warnings and one of the two rules silently
  stops working.  (This is also why McTT-style CUSTOM ENTRIES are unusable
  here: three entries sharing the `{{` opener is a hard parse error, not a
  warning.)
- ⚠️ **`Open Scope` is NOT transitive through `Require Import`**, and a closed
  scope makes Coq report the notation as simply not existing.  So every file
  that DECLARES judgement notations in a scope also opens it; a consumer then
  gets both halves through the same import that made the notation visible.

Also fixed on the way through: the six `comment-terminator-in-string` warnings
(a quoted phrase straddling a banner comment's `*)` — the ASCII quotes became
typographic ones, prose unchanged), and the dead `Δ ⨟ Γ ⊢ᵤ C` reservation in
`decl/def_rules.v`.  ⚙ Docs written before this date quote the old glyphs; the
legend in `frost/notations.v` keeps them as history.

## 2026-08-11 (night) — ⭐⭐⭐ **THE GHOST-CAPTURE REPAIR: two presuppositions the paper states in prose go ON the declarative rules, and TYPE-INFERENCE COMPLETENESS CLOSES OVER `⊢ˢ` / `⊢`**

**`make coq` exit 0; README.v 28/28 `Print Assumptions` closed; no `Admitted`, no `Axiom`.**

The one remaining hypothesis of the entry below (`d_pat_bridges`) turned out to
be **FALSE**, which made `d_sd_typing_to_ad` *vacuous*. Diagnosing why produced
the repair.

- ⭐ **THE DIAGNOSIS.** The leaf-valid datum `Θ ⨟ ∅ ⊢ᵣₚᵃᵈ ⌊R⌋ˢ ⊳ ⌊Q⌋` that
  `ad_pat_sub_gv` carries is **the paper's own presupposition on skeleton
  consistency** — `declarative.tex:2074`, *"skeleton consistency … requires
  well-formedness of `syn{S}` and `bid{P}` under Γ **as well as the refinement
  judgement `Γ ⊢ ⌊S⌋ ⊳ P`**"* — which `docs/WF-SIDE-CONDITIONS.md` §2 had
  recorded as deferred (*"it has not bitten yet"*). It bit.
- ⚠️ **It is NOT derivable from the consistency rules**, and that is the finding
  for the authors: consistency's ∀-rows put the bound rigid into **Γ** while
  refinement's put it into **Δ** and forbid a ghost's fill to mention Δ. At
  subject `∀X.◇` vs counterpart `∀ˢX.X` the rules derive the consistency
  (`cap_consis`) and refinement rejects it (`cap_no_refine`).
- ⭕ Two machine-checked refutations forced the diagnosis and are now
  **retracted by the repair**, at the configuration that produced them
  (`cex/cex_d_pat_bridges_false.v`): the pointwise `d_pat → ad_pat` bridge, and
  the App **package** with the skeleton EXISTENTIALLY quantified — the latter
  because the leaf datum wants the answer's body free of the ∀-bound rigid
  while App's refinement wants it to *be* that rigid.

**What changed** (no published statement altered):

| where | what |
|---|---|
| `decl/def_rules.v` | NEW `d_refine_pskl` — the UNCOLOURED refinement, which the paper defines at `declarative.tex:1516` and the presupposition is stated at; `d_refine_syn` (coloured) cannot serve, the two paintings disagree at a ∀ |
| `decl/def_rules.v` | `d_pat_sub`'s three consistency-bearing rows (`Infer`, `UnivGhostR`, `Arrow`'s domain) gain the presupposition — exactly the rows `ad_pat_sub_gv` decorates |
| `decl/def_rules.v` | `d_pat`'s three base rows gain the counterpart's wf (`declarative.tex:1595`), which `ad_pat` has carried since 2026-08-07 |
| `prop_weakening.v` / `prop_skeleton.v` / `prop_syntax_directed.v` | the `d_refine_pskl` kit: `_weakening`, `_subst_unit`, `_same_tvar`, mirroring `d_refine_syn`'s three |
| `prop_conserv.v` §5 | `d_refine_pskl` ⇄ `ad_refine_pskl` |
| `prop_conserv.v` §7 | `ad_pat_sub_sk_to_d` **deleted** (false now) → `ad_pat_sub_gv_sk_to_d`, from the leaf-valid mirror, which is what `ad_pat` embeds anyway |
| `prop_conserv.v` §7 | NEW `d_pat_sub_to_ad_gv` / `_v` — ⚙ the fuel is easy at SK: `d_pat_sub` has no cofinite row, so no renaming (unlike §13's TY twin) |
| `prop_conserv.v` §15 | ⭐ `d_pat_to_ad` — the bridge that used to be ASSUMED, now a hypothesis-free induction; `d_sd_typing_to_ad` loses its hypothesis |
| `prop_closed.v` | ⭐⭐ `a_typing_complete_sd_infer` / `_sd_check` / `_decl_infer` / `_decl_check` |
| `frost/coercions.v` | `uskl_to_pskl` (+ `⌊·⌋ˢ`) MOVED from `deco_algo/def_decorated.v`, and `uskl_to_pskl_subst` from `prop_decorate_sub.v` — `decl/def_rules.v` is upstream of both and now needs the erasure |

⚙ **Blast radius, measured**: 13 constructor sites for `d_pat_sub`'s three rows
and 10 for `d_pat`'s. Everything else in the 39-file development compiled
untouched — including all four section-D theorems.

⚠️ `a_wf_exp nil e` is a real premise of the completeness corollaries (the same
one soundness takes). On the `ad` side it was free; on the declarative side it
is not, because `d_sd_typing__anno` states no wf for its annotation — the
sd-Anno gap.

Author-facing note, in the paper's own notation:
[`docs/ghost-capture.tex`](docs/ghost-capture.tex)
(`make -f Makefile.ghost-capture` from `docs/`).

## 2026-08-11 (evening) — ⭐⭐ **`d_sd_typing` → `ad_sd_typing` IS PROVED IN GENERAL FORM, reduced to ONE hypothesis**

`d_sd_typing_to_ad` (`algo_decl/prop_conserv.v` §15), over an ARBITRARY Γ:

```coq
d_sd_typing M Γ e B -> d_wf_denv Γ -> a_wf_exp (denv_to_aenv Γ) e ->
d_pat_bridges -> ad_sd_typing M (denv_to_aenv Γ) e B
```

Every rule but App is discharged.  `d_pat_bridges` is obstruction (A), stated:
`forall M Γ e Q, d_pat M Γ e Q -> … -> ad_pat M (denv_to_aenv Γ) e Q`.

⭐ **STATED GENERAL ON PURPOSE.**  At `Γ = ·` both side conditions below are
free, so a closed-only statement would have hidden them — and one of them is a
real finding about the paper's §declarative figure, not bookkeeping:

1. ⚠️ **`d_sd_typing__anno` states NO well-formedness of its annotation**, while
   its four type-carrying siblings (`__abs`, `__abs_anno`, `__abs_check_base`,
   `__abs_anno_check_base`) all state `Γ ⊢ₚ A`, and `ad_sd_typing__anno` demands
   `a_wf_ptyp Θ A`.  It is NOT recoverable from the derivation, so the bridge
   carries `a_wf_exp (denv_to_aenv Γ) e` — the paper's ambient "all inputs are
   well-formed", in exactly the shape the `ad` side EXHIBITS
   (`ad_sd_typing_wf_exp`).  docs/WF-SIDE-CONDITIONS.md.
2. `d_wf_denv Γ`, which only the Var row consults.

⭐ **NEW, and general: the declarative target-lc chain** — `d_consis_lc_btyp`
and `d_sub_lc_btyp` (decl/prop_general_subsumption.v) and
`d_sd_typing_target_lc` (decl/prop_syntax_directed.v), the declarative
counterpart of `ad_sd_typing_target_wf`.  ⚙ These are the `lc` twins of
`d_consis_wf` / `d_sub_wf`: those need the subject WELL-SCOPED and give
well-scopedness back, which is more than a caller who only wants to build an
`a_tyequiv__refl` can pay — and `a_tyequiv__refl` is what the appendix's four
type-EQUIVALENCE premises reduce to over a flexible-free Θ.  Also
`lc_btyp_of_lc_ptyp_erase` (prop_wellformed.v): erasure preserves STRUCTURE, so
it reflects local closure too.

⚙ **Traps**: `subst` after inverting `a_wf_exp` at `sd-AbsAnno` uses the rule's
own `btyp_to_ptyp B1 = A` to eliminate `A`, so the reconstruction must name
`btyp_to_ptyp B1` instead (the "subst eats rule premises" trap again).  And
`ad_sd_typing__freeze`'s premise type `B` is not determined by its conclusion —
`apply` needs `with (B := A)`.

## 2026-08-11 (later still) — ⚙ **`prop_conserv.v` MOVED to `algo_decl/` + `deco_algo/`**, where a `d_` ⇄ `ad_` bridge belongs

The conservativity bridge was filed under `algo/typing/` when it was written,
on the theory that needing `btyp_to_bskl_open` (algo/pat/) and `guarded_pskl_lc`
(algo/sub/) would invert the layering.  ⚠️ It does not, and the file is not part
of the algorithm: it relates the DECLARATIVE system to the decl-in-algo one, so
it belongs to neither, and `algo_decl/` + `deco_algo/` is by CLAUDE.md's own description
"the layer BETWEEN the algorithmic and declarative systems … the bridge the
soundness and completeness proofs both go through".

⭐ Why there is no inversion: the DEFINITION layers point one way
(`algo/def_*` → `algo_decl/ + deco_algo/def_*`, never back), while the PROOF layers
already interleave — `deco_algo/prop_soundness_sub.v` reaches into
`algo/prop_soundness_consis.v`, `algo/prop_pat_sub.v`, `algo/prop_refine.v` and
`algo/prop_stability.v`.  One consumer (`algo/typing/prop_closed.v`) and a dozen
prose references repointed; `frost/coercions.v` already CALLED it
`algo_decl/prop_conserv.v`, which is the tell that it was mis-filed.

## 2026-08-11 (later) — ⭐⭐⭐ **THE UNIFORM READING OF `fresh Ψ'` LANDS: all four subtyping judgements carry GLOBAL tag hygiene, and CST pays for it**

Continuation of the entry below.  `make coq` exit 0, admit-free, axiom-free,
README.v 24/24 `Print Assumptions` closed.  Full write-up:
[`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md) (✅ RESOLVED 2026-08-11) and
[`docs/HANDOFF-closed-corollaries-declarative.md`](docs/HANDOFF-closed-corollaries-declarative.md)
§(B).

### 1. The rule change

`d_sub`, `d_pat_sub` and `ad_pat_sub` now carry, on both `ForallL` rows, the
premise the fuel mirrors `ad_pat_sub_g` / `_gv` already had:

```coq
Ψ' ∩ (ftag_in_utyp (utyp_all_tag ε C)) [=] empty     (* d_sub *)
Ψ' ∩ (ftag_in_uskl (uskl_all_tag ε R)) [=] empty     (* d_pat_sub, ad_pat_sub *)
```

That is the paper's single word *fresh* read GLOBALLY, which is what
`lemma:precision-substitution` needs: the context-local reading does not
survive the **Arrow** split, where the tag context divides but the subject does
not.  Obstruction (B) of the completeness bridge — which bit at the TYPE sort
too, so (A) could not have fixed it — is gone.

### 2. What it cost: ~35 mechanical sites, and two that were not

⭐ **The mechanical ones need ONE fact**, and it is worth having stated in its
strongest form: `ftag_in_utyp_subst_tagfree` / `ftag_in_uskl_subst_tagfree`
(`frost/prop_tag.v` §0) — substituting a TAG-FREE term cannot change a tag.
Every transport either keeps the subject, takes `Ψ' := ∅`, or substitutes a
type variable / `1` / a monotype painting, so it reads off that lemma.

⚠️ **`d_consis_sub_trans_mid`** (CST, paper B.3) was the real one: its ForallL
case transports along `utyp_tag_refines`, where the subject **GAINS** tags, so
the hygiene has to be re-established for a strictly bigger tag set.  §3 below.

⚠️ **`d_sub_prefix_spine_perm`** (`decl/prop_stability.v`) was the second, and
it is small: it PERMUTES an argument spine.  ε tags are order-blind on a spine
and blind to a ∀-prefix (`ftag_spine_utyp_perm`, `ftag_utyp_all_syn_n`), and
`d_sub_fn_all_syn_inv` / `_fnn_` — inversion lemmas — now report the hygiene
premise they were dropping.

### 3. ⭐ The CST repair: COLLECT, then move WHOLESALE

`frost/decl/prop_tag_swap.v` §4–§5 (new, ~250 lines on top of the 2026-08-11
equivariance kit).  The lesson is the shape:

- §3's per-node freshening CANNOT be iterated through an induction.  At a
  ForallL node the IH is tied to the ORIGINAL instantiation `ph`, while
  freshening yields a derivation of a DIFFERENT statement; and the swap cannot
  be applied to the IH's OUTPUT either, because there the instantiation's tags
  and the refined subject's tags sit in the SAME term `T0[ph]`.
- ⭐ So **stop freshening node by node.**  `d_sub_tagsin U` is `d_sub` with
  `Ψ' [<=] U` on the two ForallL rows.  `d_sub_to_tagsin` COLLECTS the bound by
  a plain induction — no freshening anywhere — and `d_sub_freshen` then moves
  `U` off any finite set with ONE chain of transpositions, valid whenever the
  CONCLUSION is tag-free (then no swap touches it).  One swap rewrites the
  whole derivation, so there is no changed statement to feed back.
- ⚙ The twin's `ForallR` is EXISTS-FRESH where `d_sub`'s is cofinite.  The
  collection must produce ONE `U` for the whole rule, and a cofinite premise
  would demand a bound uniform in infinitely many `α`; naming the atom makes
  the collection a one-liner and the forgetful direction pays for it with the
  tree's existing `d_sub_rename_tvar`.

`d_consis_sub_trans_mid_tagsin` (`decl/prop_general_subsumption.v`) is CST over
that twin, against a tag-BOUNDED refinement `utyp_tag_refines_in V` (the added
tags confined to `V`), with one global `U ∩ V [=] ∅` discharging every node's
hygiene at once.  ⚙ **The bound has to be an indexed RELATION**, not the set
inclusion `ftag C' ⊆ ftag Cmid ∪ V` it implies: the inclusion does not survive
descending into a ∀'s body, since `ftag (∀^ε T0)` has already absorbed ε — and
the body is exactly where the ForallL case goes.

Both call sites (`decl/prop_stability.v`, `d_sub_trans_spine`'s infer case)
discharge the new premise by the wholesale freshening: legitimate exactly
there, because the transported derivation runs at the EMPTY tag context with a
PAINTED (hence tag-free) subject.

⚠️ **No paper statement was weakened.**  `d_consis_sub_trans` gains
`Δb [=] empty` — which is the paper's own statement, at `·`; the
general-context form was a mech-internal inductive generalisation and survives
as `d_consis_sub_trans_mid_tagsin`.  `d_sd_typing` / `d_typing` are untouched.

### 4. ⚙ Duplicates removed on the way (the change needed the facts UPSTREAM)

- `ftag_in_uskl (ptyp_to_uskl_syn A) [=] empty` existed **twice**, as
  `ftag_in_uskl_ptyp_syn` (`algo/consis/prop_consis_precise.v`) and
  `ftag_in_uskl_ptyp_to_uskl_syn` (`algo/sub/look/prop_eq_cstr.v`) — and
  prop_eq_cstr.v could see BOTH, which is exactly the resolution hazard
  CLAUDE.md warns about.  One copy now, `ftag_ptyp_to_uskl_syn`, in
  `algo/prop_pat_sub.v` (the earliest file that has `ptyp_to_uskl_syn` and is
  upstream of every consumer), renamed to the conversion-fact convention.
- `frost/prop_coercions.v` gains §5: `ftag_btyp_to_utyp_syn` and
  `ftag_bskl_to_uskl` (a painting invents no tag), plus `ftag_utyp_to_uskl` —
  ⭐ the SORT inclusion, by contrast, KEEPS every tag, which is how the
  conservativity bridge carries the hygiene across the sorts.
  `ftag_in_bskl_to_uskl` was deleted from `prop_consis_precise.v` as its
  duplicate.
- ⭐⭐ **THE ATOM TRANSPOSITION EXISTED TWICE**, in `frost/prop_tag.v` (ε tags)
  and `frost/algo/prop_swap.v` (type variables) — under the **same six names**
  (`swap_atom`, `swap_atoms`, `swap_atom_invol`, `swap_atoms_empty`,
  `swap_atoms_in`, `swap_atoms_notin`), and `algo/prop_pat_sub.v` imports BOTH
  files.  ⚠️ That is the resolution hazard CLAUDE.md warns about, and the two
  `swap_atoms_notin`s were **different facts** (set-fixed vs pointwise).  A
  transposition of two ATOMS knows nothing about ε tags, so the layer now lives
  once, upstream, in `prop_tag.v` §1; `prop_swap.v` imports it and keeps only
  what the TYPE-variable side adds.  `swap_atom_fresh` was renamed to
  `prop_swap.v`'s `swap_atom_other` (one fact, one name) and `prop_swap.v`'s
  own `swap_atoms_notin` was dead.

### 5. ⚙ Dead code the repair left behind, swept

Once §3 landed, the per-node freshening it replaces and everything reachable
only from it went dead.  Deleted, with RESTART NOTEs at both files:
`d_sub_freshen_forall_l` (+ `_aux`, + `swap_atoms_disjoint_keep`, which only
measured it); `d_sub_tagsin_of`, the twin's forgetful direction (CST goes the
other way — it was the round-trip certificate); `d_sub_swap_tag` and
`d_pat_sub_swap_tag` (§3's `d_sub_tagsin_swap_tag` is the same proof with the
`Ψ' ⊆ U` row carried); and with them the whole **`uskl` half** of the ε-swap
kit — `swap_tag_in_uskl` and its nine transport lemmas, plus
`d_tags_skl_swap_tag` / `d_wf_uskl_swap_tag` / `d_pat_consis_swap_tag`.
⚠️ The skeleton half was consumer-less SYMMETRY: the CST repair the file exists
for runs at the TYPE sort.  Re-deriving it is the `utyp` half with
`utyp`/`C` → `uskl`/`R` plus the four ghost constructors.  Also deleted:
`ftag_in_pskl_to_uskl` (`prop_consis_precise.v`), which never had a consumer.

## 2026-08-11 — ⭐ **ε-TAG EQUIVARIANCE PROVED**; `ad_pat_sub_n` retired; `def_decl_algo_sub_hyg.v` merged away

Asked to make `d_sub` and `d_pat_sub` take the same (GLOBAL) reading of the
paper's ForallL side condition `fresh Ψ'` as the `_g` / `_gv` mirrors.  `make
coq` exit 0, 24/24 closed.  Full write-up: [`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md)
(⛔ GAP 2026-08-11) and the hand-off.

⭐ **NEW: `frost/prop_tag.v` + `frost/decl/prop_tag_swap.v`** (~600 lines) —
the primitive that reconciles the two readings.  `fresh` is a statement about
NAMES, so the right primitive is ε-tag EQUIVARIANCE: a TRANSPOSITION of two
tags is an automorphism of `d_tags`, `d_tags_skl`, `d_wf_utyp`, `d_wf_uskl`,
`d_consis`, `d_pat_consis`, `d_sub` and `d_pat_sub`, with **no freshness side
condition** — a one-way rename would need ε₂ fresh for the whole derivation,
and "the tags of a derivation" is not collectable from a `Prop`.  (Same reason
`algo/prop_swap.v` takes equivariance as the renaming primitive for type
variables.)  On top: `d_sub_freshen_forall_l` moves ONE ForallL node's
instantiation out of any finite set, one transposition per offending tag,
measured by `cardinal (Ψ' ∩ S)`.  ⚙ Tag contexts are `atoms`, which has no
image operator, so the set action is characterised by a single
`swap_atoms_spec` and every other fact is a pointwise consequence.

⚠️ **The rule change itself was BACKED OUT.**  Adding `Ψ' ∩ ftag(subject) = ∅`
to `d_sub` / `d_pat_sub` / `ad_pat_sub` is mechanical at ~35 of ~38 sites and
fails at exactly one: `d_consis_sub_trans_mid` (CST, paper B.3), whose ForallL
case transports along `utyp_tag_refines`, where the subject GAINS tags.  ⚠️ It
cannot be repaired locally with the primitive: structural induction ties the IH
to the ORIGINAL instantiation, and freshening yields a derivation of a
different statement — while the swap cannot be applied to the IH's output
either, because there the instantiation's tags and the refined subject's tags
sit in the same term `T0[ph]`.

⭐ **The next step is worked out** (≈150 lines + the CST edit): a tags-BOUND
twin `d_sub_tagsin U` (`Ψ' [<=] U` on the ForallL rules), whose
`d_sub_to_tagsin` is a plain collection induction; its equivariance; a
wholesale freshening valid when the CONCLUSION is tag-free; then CST restated
with `d_sub_tagsin U` + `ftag C' ∩ U [=] ∅`, and its two call sites discharging
that premise by the wholesale freshening.  Five steps, spelt out in the
hand-off.

⚙ **Also landed, and independent**: `ad_pat_sub_n` — the non-hygienic fuel
mirror — and its five bridge lemmas (`ad_pat_sub_of_n`, `_n_succ`, `_n_mono`,
`_n_rename_tvar`, `ad_pat_sub_to_n`; §P5a of
`algo/sub/prop_completeness_sub_precise.v` plus the 64-line inductive) had **no
consumer anywhere in the tree** — §1 of the completeness skeleton named `_n` as
the measure, the development settled on the tag-hygienic `ad_pat_sub_g`, and
nothing came back for it.  Deleted (~290 lines), RESTART NOTEs at both sites.
And `def_decl_algo_sub_hyg.v` was MERGED into `def_subtyping.v`: one topic
(the paper's subtyping box and the mirrors that measure it), and per CLAUDE.md's
DO-NOT-MERGE check the smaller file's only extra dependency was `Lia`.

## 2026-08-10 — ⭐ **THE CONSERVATIVITY BRIDGE: SOUNDNESS AT A CLOSED PROGRAM NOW READS THE PAPER'S §declarative SYSTEM**

Hand-off: [`docs/HANDOFF-closed-corollaries-declarative.md`](docs/HANDOFF-closed-corollaries-declarative.md).

`a_typing_sound_infer` / `a_typing_sound_check` (`algo/typing/prop_closed.v`,
`README.v`) now state their declarative side as `· ⊢ˢ[M] e ⦂ B` **and**
`· ⊢[M] e ⦂ B` — the paper's own §declarative judgments over a declarative
context — instead of `ad_sd_typing` over `nil : aenv`.  `make coq` exit 0,
admit-free, axiom-free, 24/24 `Print Assumptions` closed.

**New: `frost/algo_decl/prop_conserv.v`** (~1300 lines) — the bridge the
paper asserts and never states (`app:decl-in-algo-context`: *"it is easy to
extend them to algorithmic contexts Θ"*).  A declarative context IS a
flexible-free algorithmic one (`denv_to_aenv`), each `ad_` judgment is its
`d_` version plus the flexible-lookup rows, and those are vacuous in the
image — so `ad_ → d_` is a plain induction per judgment (consistency at both
sorts, refinement, subtyping at both sorts, skeleton inference, typing).
Registered in [`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md).  Three things the
paper leaves implicit had to be made explicit:

1. the appendix's four `Θ ⊢ A ≡ B` premises **collapse to `=`** at a
   flexible-free Θ (`a_tyequiv_denv_eq`) — which is why the §declarative
   figure may silently reuse an annotation;
2. the colour-discipline premises `d_sub` states and the fused `typsub^N_M`
   figure omits (`is_styp` on Infer, guardedness + `is_ityp` on Check,
   `is_ityp` on ForallR) are **recovered**, not assumed, at `N = TY`;
3. Δ and Γ **swap roles between the sorts** — the skeleton judgments put a
   bound rigid into Δ, the type ones into Γ (`d_wf_utyp_of_d_wf_uskl`).

⭐ **The step the paper does not mention** is §11: soundness delivers its
derivation at the run's OUTPUT context Θ₁, which still holds flexibles
(`fun x -> x` at `·` gives `Θ₁ = α̂`, answer `α̂ → α̂`).  Since the run starts
at `·`, Θ₁ is a pure suffix, so peeling it with `ad_sd_typing_subst_mid` and
accumulating `solves_flex_of_wf_head`'s solutions **builds** a closing
`ζ ∷ Θ₁ ⊑ ·` together with the derivation at `·` — building it rather than
quantifying over one is what keeps the corollary non-vacuous.  The
corollaries also lost their existential `Bt`: the mode forces the answer's
colouring (`syn{A}` at TI, `inh{A}` at TC).

⚙ Two conversions added: `utyp_to_uskl` (the sort inclusion) and its
retraction `uskl_to_utyp`, in `frost/coercions.v` with their facts in
`frost/prop_coercions.v`.  The `msubst_btyp` facts §11 needs live in
prop_conserv.v — `msubst_btyp` was defined in `algo/def_meta.v` and used by
no proof anywhere, so that is its only home.

### ⭕ STILL OPEN — the COMPLETENESS direction, now blocked TWICE

- **(A) the leaf-valid datum.**  ⭐ The previous session's R0 question is
  SETTLED on its positive side: `d_pat_consis_subject_refine_ghost_free`
  (§12) proves that **at a ghost-free subject the datum is derivable from
  consistency alone**.  So `ad_sd_typing`'s own base rows — which join
  `syn{A}` for a *type* `A` — are never the obstruction; what is left is
  exactly `ad_pat`'s P-Var at a skeleton entry whose `P` has a ghost under a
  ∀, which `ad_pat__abs` may introduce and which typing reaches through App.
  ⚠️ A reachable configuration is still not a refutation: the App rule
  existentially quantifies its skeleton, so refuting the bridge means closing
  over every choice of it.
- **(B) tag hygiene — NEW, and not confined to the skeleton sort.**
  `ad_pat_sub_gv`'s ForallL rows demand the instantiation's tags fresh from
  the SUBJECT's syntactic tags (the mech's rendering of the paper's prose
  `fresh Ψ'` as GLOBAL freshness, which `lemma:precision-substitution`
  needs); `d_sub` / `d_pat_sub` demand freshness from the TAG CONTEXT only,
  and the two come apart at Arrow, where the context splits but the subject
  does not.  Bridging them needs the ε-tag freshening the development
  deferred.  This blocks the TYPE sort too, so (A) alone does not fix it.

⚠️ Putting the leaf datum on `d_sd_typing` forces the same on `d_typing`
(standalone `Sub`) and re-opens all of Phase 2 plus the paper's §declarative
figure — do not take that route without asking.

## 2026-08-10 — ⭐ **CLOSED-PROGRAM COROLLARIES OF THE TWO TYPING THEOREMS**

`a_typing_sound_infer` / `_check` and `a_typing_complete_infer` / `_check`
(algo/typing/prop_closed.v, split out of the completeness file in the same
pass), all Qed and axiom-free, all `Check`ed in
README.v (now 24 entries).  At the empty context the input can only be in one
of the two user-facing modes — INFERENCE at the ghost `□`, CHECKING at a
closed type `⌈A0⌉` — so each flagship splits in two, and three premises go
with the split: `a_wf_aenv nil` is a constructor, `nil ⨟ ∅ ⊢ₚₛᵃ P0` is
`a_wf_pskl__hole` resp. the annotation's own wf, and `a_ty_mode_compat` is
read off the mode.

Completeness sheds two more (shared engine `a_typing_complete_nil`).
`κ ∷ nil ⊑ nil` holds at `κ = nil` (`a_inc__empty` + `a_suffix__nil`), so **no
metasubstitution is quantified at all** and the refinement premise reads at
`P0` itself (new one-liner `msubst_pskl_nil`, beside `msubst_ptyp_nil`).  And
the optimality is applied at the identity increase SOUNDNESS hands back, so
the conclusion collapses to

```coq
exists ζ, ζ ∷ Θ1 ⊑ nil /\ nil ⊢ msubst_ptyp ζ A1 ≡ᵗ B
```

— the run's answer, closed off by ζ, IS the declarative type: it is the most
general derivation, not merely some derivation.

⭐ **Both completeness corollaries end up with the declarative derivation as
their ONLY premise.**  At INFERENCE the refinement premise goes because at `□`
it says only that the declarative result is a SYNTHESISED painting of a
well-formed type, and both halves are read off the derivation
(`ad_sd_typing_mod_comp_ty` + `mod_comp_ty_ti_inv` + `ad_sd_typing_target_wf`);
that needed the SYN mirror of `btyp_inh_painting_inv` — new
`btyp_syn_colouring_inv`, and with it `ptyp_to_btyp_syn_open_var` in
prop_coercions.v, which was missing while its `_inh` twin was not.  At CHECKING
the checked type is the DECLARATIVE RESULT itself, `⌈⌊B⌋⌉`: at `TC` the
colouring is forced (`mod_comp_ty_tc_inv` + `btyp_inh_painting_inv`), so the
refinement at an arbitrary annotation `A0` is REFLEXIVITY at `⌊B⌋` and `A0`
goes with it.  ⚙ Nothing is lost at the empty context — refinement of a
ghost-free painting takes only the structural rows there (the two flexible
rows need a definition in the context, and `·` has none), so `inh{A0} ⊳ ⌊B⌋`
forces `A0 = ⌊B⌋` anyway.

⭐⭐ **AND COMPLETENESS NEEDS NO CONDITION ON THE TERM AT ALL** — so
`a_typing_complete_infer` has the declarative derivation as its ONLY premise.
`ad_sd_typing__anno` was the one rule that put a type into the term WITHOUT
an `a_wf_ptyp Θ A` premise (its four type-carrying siblings all have one),
and its join constrains only the TARGET (`ad_pat_sub_target_wf`), so a
derivation said nothing about the scope of the types its subject mentions.
**The premise is now ON the rule** (algo_decl/def_typing.v,
registered in docs/PAPER-GAPS.md), which is free on the soundness side —
`a_typing_sound` already carries `a_wf_exp Θ0 e`, which stores exactly this
at every annotation — and buys the new

```coq
ad_sd_typing_wf_exp : Θ ⊢ᵃᵈ[ M ] e ⦂ B -> a_wf_exp Θ e
```

(with `a_wf_exp_strip_prefix` / `_strip_tm` / `a_wf_exp_lc` beside it).  Rule
change cost: FIVE construction sites and no induction rewrites —
`prop_ctx_mono` (`a_wf_ptyp_mono`), `prop_rename_decl`
(`a_wf_ptyp_rename_paint`), `prop_suffix_erase` (`a_wf_ptyp_subst_mid`) and
two in `prop_soundness_typing` (`a_wf_ptyp_isub` / `_mono`).  ⚠️ Each of those
also had to renumber the join hypothesis `H0 → H1`.

⚠️ **SOUNDNESS still asks for `a_wf_exp nil e`**, and adding the same premise
to `AT-Anno` would not change that: `a_typing__abs` runs the body under the
flexibles `guess^TY` just invented, and nothing stops a nested annotation
from mentioning one — a run can accept a term whose type variables are not
those of its INPUT context.  It is the paper's own "M is well-formed in Θ₀".

## 2026-08-10 — ⭐ **THE ENTRY-WF SIDE CONDITION IS GONE FROM THE WHOLE TREE**, and the changelog comments with it

`forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps` is no longer
stated ANYWHERE.  On 2026-08-09 it was dropped from the two flagship
completeness statements only, and the `_gen` lemmas and step rows kept
threading it; now every site derives it where it is used, from the
`a_wf_aenv` premise it already has, by `a_wf_aenv_binds_var_skl_wf`.

Swept: `a_pat_sound`, `a_typing_sound` (the question-context copy the earlier
pass left behind), `typing_scope_concl` and both discharge corollaries
(`a_typing_scope_tvar_nil` / `_tm_nil`), `a_pat_output_wf`,
`ad_ctx_precise_refl`, `a_pat_complete_gen` / `a_typing_complete_gen` and all
sixteen step rows — 72 premise lines in five files, plus the ~25 `assert
(Hskl…)` blocks and inline `ltac:` arguments that existed only to feed them.
The two soundness theorems keep `Hskl` as a one-line `pose proof` after
`intros`, because their per-row uses are unchanged.

⚙ `ad_ctx_precise_refl` got shorter, not longer: with the entry's wf ON the
constructor its two term rows read it off `H0` and the other four are
`exact IHHwf`.  ⚠️ `prop_scope.v` reaches
`a_wf_aenv_binds_var_skl_wf` QUALIFIED — it deliberately does not
`Require Import prop_inc_strengthen` (it already dodges two shadowed names
that way).

**Comment sweep, same pass.**  Deleted the comments that only record what the
development used to look like: 32 move/dedupe/rename tombstones ("[X] deleted
<date> (cleanup audit …): an alpha-variant of the one in Y"), and the
historical paragraphs of ~20 mixed blocks (`§10 WHAT THE ASSEMBLY OWES`'s
residual ledger, `prop_completeness_consis.v`'s `HISTORY.` paragraph, the
`flex_shield`-moved-out banner, the four `(formerly …)` file-merge banners).
Kept: `RESTART NOTE`s (CLAUDE.md mandates them), `⚠️ DO NOT MERGE` notes, perf
findings, and every cex/ header — those record findings, not history.

## 2026-08-09 — ⭐ **`a_wf_aenv__var` NOW STORES THE DISCIPLINED SKELETON WF** (`a_scope_pskl` has no rule site left)

`make coq` exit 0; all `Print Assumptions` closed, zero
Axioms/Parameters/Variables/Admitted.  Registry entry updated:
[`docs/WF-SIDE-CONDITIONS.md`](docs/WF-SIDE-CONDITIONS.md) — the section that
had this as a QUEUED CLEANUP now records it as done, with what the note got
wrong.

A context's term entry `x : P` used to carry only `a_scope_pskl Θ P`
(scoping), so the two flagship completeness theorems had to hypothesise
`forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps` for BOTH
their contexts.  The entry now carries `Θ ⨟ empty ⊢ₚₛᵃ P` directly.

⚙ **The obstruction was ORDERING, and it was shallow.**  `a_wf_pskl` was
declared AFTER `a_wf_aenv` in `algo/def_rules.v`, so naming it in the
constructor was a forward reference — which is plausibly why the weak
judgement was introduced at all (`a_scope_pskl` sits immediately before
`a_wf_aenv`).  It depends only on `a_binds_tvar` and `guarded_pskl`, so its
block moved up: 28 lines.

⭐ **The feared new lemma pack was already in the tree.**  The registry
predicted "split/guess outputs are disciplined" would have to be proved.  It
does not: `a_split_wf` already yields `Θ1 ⨟ empty ⊢ₚₛᵃ P` for the split's left
output — exactly what `a_pat__abs` pushes — `a_pat__abs_check` pushes `□`
(`a_wf_pskl__hole`), and `ad_pat__abs` carries the premise on the rule.  So no
row can push a skeleton it cannot justify; that was checked BEFORE starting,
because a row pushing (say) `∀◇□` would have made the constructor
*unprovable* rather than merely tedious.

⚙ Migration shape (22 build rounds, ~30 sites): consumers convert with
`a_scope_pskl_of_wf`, which is also an `#[export] Hint Resolve` — so every
site that discharged an entry's scope through `eauto` needed NO edit.  Only
the `exact H` forms did.  `a_wf_pskl_ftv_tvarish` and
`a_wf_pskl_to_a_scope_pskl` moved out of the two consistency files into
`algo/prop_swap.v` §0: the strengthening makes them needed at the BOTTOM of
the algo order, and prop_flex.v — the topical home, it already holds
`a_wf_pskl_weaken`/`_strip_mid` — IMPORTS prop_swap.v, so that direction is a
cycle.  ⚠️ prop_swap.v has no global `Set Implicit Arguments` **by design**
(its header says why), so §0 scopes its own — without that the moved lemmas
silently gain explicit arguments and their ~70 call sites break as
`match goal` branches that no longer fire.  Retired: `a_wf_pskl_scope`,
pat/prop_soundness_pat.v's private copy of the same conversion.

⚠️ **`a_scope_pskl` CANNOT be deleted**, contrary to the registry's endgame.
It has no rule site now, but 182 statement uses, and the weak form is
genuinely irreducible at one of them: `ad_pat_consis_target_wf` says a
consistency JOIN'S target erases to a *scoped* skeleton and gives nothing
stronger, while `msubst_compose_id_pskl` and `a_inc_equiv_msubst_pskl` are
applied at exactly that subject.  Strengthening `msubst_compose_id_pskl`'s
premise was tried and REVERTED for this reason.  Making the join-target lemma
disciplined is a real proof obligation — its `∀◇` cases would have to
establish guardedness and the Δ-reset — not a rename.

✅ **AND THEN DROPPED (same day).**  `a_pat_complete` and `a_typing_complete`
no longer state the two `binds y (abind_var_skl Ps) -> … ⊢ₚₛᵃ Ps` hypotheses.
The predicted cost — "re-proving every row that consumes them" — did not
materialise: the rows keep threading them through `a_pat_complete_gen` /
`a_typing_complete_gen`, and the FLAGSHIP simply discharges them from its own
`a_wf_aenv` premises with the new `a_wf_aenv_binds_var_skl_wf`
(algo/prop_inc_strengthen.v, beside its `_ftv` sibling: the entry's stored wf
weakened past the entry).  Two external wf side conditions became theorems, and
`README.v`'s ascriptions shrank accordingly.  ⚙ One internal caller
(`a_typing_complete_abs`'s use of theorem 3) had to drop two positional
arguments.  ⛔ Still stated, not swept: the SOUNDNESS theorems' question-context
copy, which is derivable the same way.

## 2026-08-09 (latest) — ⚙ **NOTATION PASS: the system/sort AXES, `⇨` retired, `blk` → `Ξg`**

Notation only — no rule, statement or proof obligation changed; the diff is
inside notated forms plus one variable rename.  Recorded in
[`docs/PROPOSAL-notation-pass.md`](docs/PROPOSAL-notation-pass.md) §5 (the
before/after table) and §6 (what was deliberately left); the canonical legend
now lives in the header of [`frost/notations.v`](frost/notations.v), which
`CLAUDE.md`'s style section points at.

Three defects, all reported by the user:

1. **`⇨` was wrong on most of the rules that used it.**  `d_pat` / `ad_pat` /
   `a_pat` are indexed by an arbitrary mode `M`, and `⇨` claims the term
   SYNTHESISES its skeleton — true only at `M = TI`; at `TC` the skeleton is an
   INPUT.  All three now write `⦂`, with the skeleton sort carried by the
   turnstile subscript: `Γ ⊢ₛ[ M ] e ⦂ P`, `Θ ⊢ₛᵃᵈ[ M ] e ⦂ Q`,
   `Θ ⊢ₛᵃ[ m ; P0 ] e ⦂ Q ⊣ Θ'`.  ⚙ The paper writes its own mode-generic
   typing with a plain colon for exactly this reason (`\typp`,
   `paper/macro.tex:1087`); its `⇛`/`\TTo` marks the SKELETON judgement, not
   synthesis, so the mech's lookalike `⇨` had imported a meaning the paper's
   glyph never carried.
2. **The system marker meant two different systems, and the two axes shared
   one device.**  `ᵃ` was `a_` in `a_wf_pskl` (`⊢ₚₛᵃ`) but `ad_` in
   `ad_pat_consis` / `ad_refine_syn` / `ad_sd_typing` / `ad_pat`; meanwhile
   `a_consis` / `a_sub` / `a_pat` / `a_typing` wrote the SYSTEM as a subscript
   (`⊢ₐ`), which everywhere else means the SORT.  So the algorithmic and the
   decorated turnstiles differed by sub- vs superscript `a` alone.  Fixed by
   one device per axis — **superscript = system** (`⊢` d, `⊢ᵃᵈ` ad, `⊢ᵃ` a,
   `⊢ᵗ` ε-tagged, `⊢ˢ` syntax-directed), **subscript = sort** (bare types,
   `⊢ₛ` skeletons) — and by stating the sort exactly ONCE: as the subscript
   where the system has one relation per sort, as the bracket index `N`/`NM`
   where one relation covers both.  ⭐ That last rule is why `ad_pat_consis`
   and `ad_pat_sub` LOST their `ₛ`: the ad system has no type-sort sibling to
   be told apart from, and `ad_pat_sub`'s `NM` already names the sort — the
   same reason `a_sub` never had one.  Stating it twice is how `⊢ₛᵃ[ TY | … ]`
   came to read as a contradiction.  ⭐ And the same rule one step further:
   `ad_sd_typing` first became `⊢ˢᵃᵈ`, which stacks the VARIANT mark `ˢ` on the
   SYSTEM mark `ᵃᵈ` — the superscript must hold the system and NOTHING else,
   or `ˢᵃᵈ` reads as one opaque system name.  There is no `ad_typing`, so `ˢ`
   had nothing to disambiguate from: it is plain `Θ ⊢ᵃᵈ[ M ] e ⦂ B`, and the
   three copies of typing now differ by the system mark ALONE (`⊢[ M ] e ⦂ A`,
   `⊢ᵃᵈ[ M ] e ⦂ B`, `⊢ᵃ[ m ; P0 ] e ⦂ B ⊣ Θ'`).  `⊢ˢ` survives only in the
   declarative system, where `d_typing` and `d_sd_typing` genuinely coexist.
3. **`blk : aenv` violated the greek-context convention** — and it turned out
   to be a stray ALIAS: the rest of the tree already calls that object `Ξg`
   (`a_guess_mono Θg Pi0 Ξg A`, `algo/sub/look/prop_eq_cstr.v:2212`).  Renamed
   throughout `algo/typing/prop_completeness_typing.v` (92 sites, plus
   `Hwfblk`/`Hftvblk`);
   `Ξg` and not plain `Ξ` because `a_typing_complete_abs` needs BOTH the guess
   block and the output suffix at once, and because `a_decls`'s own
   constructor binds a `Ξ` that `induction` reintroduces.  ⚙ `Hblk` elsewhere
   (`prop_solve_ext.v`, `prop_eq_cstr.v`, `prop_soundness_pat.v`) is a
   hypothesis ABOUT a block, not a context, and `a_tvar_block` is a real
   relation — "block" is legitimate terminology, so those keep their names.

⚙ Sweep mechanics worth keeping: four of the renames are context-SENSITIVE,
because `⊢ₐ[` and `⊢[` are each shared by two judgements that differ only in a
relation symbol several tokens later.  Those need a bounded regex whose middle
forbids every other relation symbol plus `->` / `(*` / `*)` / blank line —
without the guard, a comment block showing an `a_extract` judgement several
lines above a prose `⊑ᵖ[∅]` gets its own turnstile marked (this happened in
`prop_extract.v`).  And the `*_pat` turnstiles must be marked WHILE `⇨` still
distinguishes them from `*_typing`, before `⇨` becomes `⦂`.

⚠️ Counting notation sites with `grep -r` over the build tree inflates the
figure ~4×: `.vo` / `.glob` / `.aux` artifacts contain the notation strings
too, and `*.v.legacy` is not source.  The real size was ~1.7k substitutions in
79 files, not the ~15k a naive `grep -rn | wc -l` reported.

## 2026-08-09 — ⚙ **CLEANUP PHASE 3: `frost/prop_coercions.v`, the `_thm` retirement, `make tidy`, §8.1d, and the algo/ FILE REORG; duplicates 53 → 33**

Continues the post-theorem-4 cleanup audit
([`docs/REPORT-remech-cleanup-audit.md`](docs/REPORT-remech-cleanup-audit.md),
Phase 3 banner).  No rule, statement or proof obligation changed.  Verified by
a CLEAN full rebuild (`make clean && make coq`, exit 0, 97 files): **108/108**
`Print Assumptions` in the tree report `Closed under the global context`, zero
`Axioms:`/`Parameters:`/`Variables:`, zero `Admitted`/`Axiom`.  ⚙ 108 is the
whole-tree figure; the older "39/39" in earlier banners counted a smaller set
and an INCREMENTAL build only emits the reports of the files it rebuilds (98
here), so a clean run is the only way to see them all at once.

- **§5.4 — `frost/prop_coercions.v` (409 lines, 38 lemmas).**  Everything about
  the paint/erase conversions, gathered from ELEVEN files: §1 retractions, §2
  `open`/`open_rec` commutation, §3 `lc` + shape-predicate transport, §4 `ftvar`
  transport.  `coercions.v` is now definitions-only; `prop_basic.v` is the
  predicate layer (ghost-freeness) and `Require Export`s the new file, so its
  ~99 consumers needed no edit.
- ⚠️ **The audit undercounted, because the worst duplication used DIFFERENT
  names.**  `ftvar_in_pskl (ptyp_to_pskl A) [=] ftvar_in_ptyp A` was proved
  **four times** (`ftvar_in_pskl_ptyp_to_pskl`, `ftvar_in_ptyp_to_pskl`,
  `ftvar_ptyp_to_pskl`, `…_local`); the `ptyp_to_btyp_syn` and `btyp_to_ptyp`
  ftvar facts three times each.  A name-keyed scan is blind to all of it.
- ⚠️ **The tree already documented the hazard.**
  `decl/prop_syntax_directed.v`'s `ftvar_paint_btyp_syn_eq` existed only to
  escape a shadow (its comment says so), and by now had **zero uses**.  Deleted.
- **Rule adopted: one fact, one name, one file, in its STRONGEST form.**  Where
  copies differed in strength (`=` / `[=]` / `[<=]`, or general `open` vs its
  variable instance) the strong one is kept and weak uses `rewrite` with it.
- ⚠️ **"Strongest form" is not "most general statement".**  Deleting the
  variable-instance `_open` lemmas in favour of the general ones was WRONG and
  `make coq` caught it: `rewrite`'s matching is syntactic, so the pattern's
  `ptyp_to_btyp_inh ?A2` will not match a bare `btyp_var_f α` — that needs the
  fixpoint unfolded.  Logical subsumption is not rewrite-subsumption.  `_var`
  is now a **one-line corollary** of the general form, not a second induction,
  and the two names make explicit an asymmetry that used to be settled by
  import order (`decl/` wants general, `algo/` wants the variable instance).
- **Naming: the `_thm` suffix is retired** (`a_sub_sound`, `a_sub_complete`,
  `a_consis_complete`, `a_sub_flex_sound`, `a_sub_sound_v`).  It marked nothing
  — no bare name was taken — while `a_pat_sound` / `a_typing_complete` already
  set the no-suffix convention.  Conventions recorded in `CLAUDE.md`.
- **§8.1d closed + 6 more duplicates (39 → 33).**  `prop_completeness_sub_gen.v`
  is flipped onto `algo/prop_completeness_look.v`.  ⚙ TWO checks are needed
  before flipping any consumer and tree-wide collision-freedom is not one of
  them: (1) the consumer must declare no name that a NEWLY-exposed cluster file
  declares, and (2) no cycle — safe here because the three added files are
  EARLIER in the linear chain.  Recorded in the facade header.
- ⚙ **The test for whether a duplicate pair can be deduped IN PLACE**: one
  declaring file must already see the other (direct import or `Export` chain —
  reachability is the wrong test) AND every other consumer must see the
  survivor.  Only 6 of the 13 true duplicates pass; the rest need the lemma
  LIFTED to a common ancestor.  ⚠️ `guarded_pskl_subst_var` and
  `a_wf_aenv_binds_def_mono` look deletable but are not — some consumers see
  only the losing copy, and ADDING an import to fix that is the move that has
  broken this build before.
- **FILE REORG (phase 3c).**  `completeness_look/prop_kit.v` — 6952 lines,
  three concerns, the audit's named source of most duplicate names — is split
  into `sub/look/prop_rho_relation.v` (3286), `sub/look/prop_solve_ext.v`
  (1692) and `sub/look/prop_flex_apart.v` (2103).  "kit" named nothing.
- **`algo/` grouped BY JUDGEMENT**: 35 flat files → 18 flat + `consis/` (4),
  `sub/` (8, with `sub/look/` 8), `pat/` (2), `typing/` (5).  ⚠️ A
  `soundness/` vs `completeness/` split would be FALSE — there is no
  soundness-only file; `prop_soundness_consis.v` is imported by 13
  completeness files, so soundness is kit for completeness.  ⚠️ No `kit/`
  folder either: 9 files whose only shared property is "shared" repeats the
  `prop_kit.v` mistake at directory scale.  27 module paths rewritten.
- `prop_sub_concrete_rhs.v` → `cex/probe_sub_concrete_rhs.v` (zero consumers;
  it is a finding, not machinery).
- ⚠️ **`Set Implicit Arguments` is per-FILE, so splitting a file drops it from
  every half but the first** — third appearance of this trap today, now from
  splitting rather than moving.  ⚙ And the failure is SILENT inside
  `match goal`: a branch whose BODY fails to elaborate is reported only as
  "No matching clauses for match", pointing at a pattern that does match.
- ⚠️ **A stale `.vo` lets a dead import resolve** rather than fail — three
  `cex/` files still imported the deleted `prop_kit` and surfaced only as
  "makes inconsistent assumptions over library".  Run `make tidy` after any
  rename.  ⚙ Cheap pre-build check for a path change: verify every `Require`d
  `src.*` module resolves to a real file.
- **`make tidy`.**  Phase 1's hand sweep regrew (11 `.glob`, 66 `.aux`): `clean`
  globbed only two directory levels and the tree is three deep, and it knew only
  the `scratch_*` prefix.  `tidy` deletes an artifact iff its companion `.v` is
  gone, and PRESERVES the live `.aux` timing data perf passes depend on.


## 2026-08-08 — ⭐⭐⭐⭐ **THEOREM 4 IS CLOSED: `a_typing_complete` (thm:complete-type-inference), Qed + axiom-free**

Section D's last theorem.  `Theorem a_typing_complete`
(`algo/prop_completeness_typing.v`, 4638 lines, zero admits) is `Check`ed
and audited in `README.v`; the `Print Assumptions` count is now 39/39
*Closed under the global context*.

What the last two rows needed, beyond the ten already committed:

- ⭐⭐ **`a_split_complete_tc` — COMPLETENESS OF SPLITTING AT CHECK MODE, a
  lemma the recorded plan assumed was already covered and is not.**
  `a_split_complete` (prop_completeness_pat.v) is stated for `M <> mode_tc`
  and returns the IDENTITY split; at TC the input is a TYPE painting
  `⌈A0⌉`, so `a_split__flex` IS reachable (`a_split_ty_shape`'s "whole
  asymmetry") and the row has to be built.  This is the paper's AbsCheck
  **subcase 2**: from the declarative refinement of `κ⌈A0⌉` to an arrow only
  two shapes of `A0` survive — a syntactic arrow (the identity split) and a
  FLEXIBLE, where two fresh `β̂1`/`α̂1` are invented and SOLVED by a full
  consistency run supplied by `a_consis_complete`, at the monotypes the
  flexible's own `κ`-image decomposes into (NEW `mono_refine_arrow_inv`:
  a monotype painting that refines to an arrow IS an arrow up to `≡ᵗ`,
  by induction on the REFINEMENT, its `flex_l` row unfolding the
  definition).  `unit` / `∀` / a RIGID variable all die on the refinement
  (NEW `refine_var_arrow_flex_def`).  The conclusion is the standard stage
  package — the run, its own identity increase, and a factoring witness `ζ`
  carrying BOTH the binder's `≡ᵗ` (what `a_inc__var` consumes) and the
  codomain's refinement (what the body's IH consumes).
  ⚙ Its ARROW row needs NEW `msubst_compose_inc_id_r` (composing an
  increment with its own source's identity is the increment itself — both
  metasubstitutions enumerate the source's flexibles in the same order).
- `a_typing_complete_abs_check_base` / `a_typing_complete_abs_anno_check_base`
  — the `a_typing_complete_abs` template MINUS the `guess^TY` block (the
  domain comes from the split) PLUS the suffix discard, whose premise (2) is
  discharged by **`a_typing_scope_tm_nil`** (§6.3#2 at the TERM marker).
  The anno row is THREE-staged (split, annotation consistency, body), so its
  optimality is the App row's TRIPLE glue; its consistency is oriented
  SUBJECT = the split's domain, INPUT = the written annotation, the reverse
  of `AT-AbsAnno`'s (docs/PAPER-GAPS.md).
- **The glue** `a_typing_complete_gen`: strong induction on the
  LEXICOGRAPHIC `(size_exp e, size_btyp B)`, `n`/`m`-bounded in theorem 3's
  style.  Ten rows recurse at a strictly smaller SUBJECT (any second
  component is then allowed); only the two ∀-peeling AbsCheck rows recurse
  at the SAME subject, and their IH premise's measure guard
  `size_btyp B' < size_btyp (btyp_all_inh B)` is discharged by
  `size_btyp_open_btyp_wrt_btyp_var`.
- ⚙ The Anno and Freeze rows gained the TARGET context's skeleton-entry
  discipline (`binds y (abind_var_skl Ps) Θ -> Θ ⨟ ∅ ⊢ Ps`), as a row
  hypothesis and inside their IH premise — the glue cannot supply an IH at
  an arbitrary target without it.  Every other row already carried it.

## 2026-08-08 — ⭐⭐⭐ **§6.3 #2 IS CLOSED: the run-result SCOPING invariant (`algo/prop_ty_scope.v`), and the two `_step` completeness rows land on it**

The four suffix-discarding check rows carry premise (2) — *the discarded
suffix `Ξ` does not occur in the run's result* — which
`thm:complete-type-inference` has to DISCHARGE when it builds those rows.
That invariant is now proved, in a new `frost/algo/prop_ty_scope.v`
(2622 lines, zero admits, every result axiom-free):

- `a_sub_sub_flex_scope` — the SUB-level walk, and `a_typing_scope` — the
  TYPING-level walk, both in **scope-propagation** form.  ⚠️ Core
  PRESERVATION (the shape `a_sub_sub_flex_ty_core` / `a_typing_ty_core` use)
  is FALSE once `core_rigid` is relativized to the above-marker region, for
  two independent reasons recorded at the lemmas: `a_sub_flex__assign`
  substitutes the input skeleton, and the check `_base` rows reach
  `a_split__flex` at TC.
- `a_typing_scope_tvar_nil` / `a_typing_scope_tm_nil` — the two `Ξ0 = nil`
  corollaries, where the marker sits at the top of the input (so the
  hypothesis is vacuous) and `suffix_no_rigid_mid` turns the conclusion into
  premise (2) verbatim.
- ⭐ **`a_assign_unify_consis_region`** — a NEW region walk over the
  assignment / unification / consistency bundle, which the `_base` rows'
  `a_split__flex` case genuinely needs: output well-formedness alone covers
  only the `Assign-SolveM` shape, and `a_assign__assign` merges the pending
  suffix into a recursive consistency run whose subject's binding never
  mentions the split's invented flexibles.  The walk says the above-marker
  region never grows and every undefined flexible the payload names lands
  at-or-below the marker — which is the DEPOSIT discipline (`Assign-Depend`
  parks, `Assign-SolveM` deposits at the subject's entry) made formal.
  Specializing the consistency motive to a VARIABLE subject with a
  non-variable payload makes thirteen of the fourteen consistency rows
  vacuous and leaves `a_unify`'s motive literally `True`.

On top of it, `a_typing_complete_abs_check_step` and
`a_typing_complete_abs_anno_check_step` are landed in
`prop_completeness_typing.v` (ten of twelve rows of
`thm:complete-type-inference` now closed).  Both carry the measure guard
`size_btyp B' < size_btyp (btyp_all_inh B)` on their IH premise: those rows
recurse on the SAME subject, so the glue's measure has to be the
lexicographic `(size_exp e, size_btyp B)`.

Still open for theorem 4: the two `_base` completeness rows and the glue.

## 2026-08-08 — ⭐⭐⭐ **THE CHECK-ROW RULE SURGERY: the four suffix-discarding rows repaired against completeness, all six `a_typing` binder rows EXISTS-FRESH, `thm:sound-type-inference` re-proved on the repaired rules**

Theorem 4's check-row work found the four suffix-discarding check rows, as
transcribed from fig:alg-type-inference, incompatible with completeness in
two independent ways (docs/PAPER-GAPS.md, 2026-08-08 entry):

1. **The `_base` body premise's pinned result is unsatisfiable** whenever
   the split codomain is a flexible and the body is itself a lambda (the
   inner run concludes the INNER split's arrow, never the flexible) — yet
   the implementation accepts such programs and never reads the body's
   returned type (type.ml I-AbsCheck).  The paper's own completeness proof
   concludes with the body's `B₁`, not the figure's `B`.  The rules now
   take a free `B1` and conclude `A → B1`; the "Ξ ∉ result" side condition
   moves onto `B1`.
2. **Cofinite binder families are unsatisfiable**: the discarded `Ξ` can
   mention the one binder the run used, so a family sharing `Ξ` has no
   members — verbatim `a_sub__forall_r`'s 2026-07-31 situation.  All six
   binder rows (the four check rows + AT-Abs + AT-AbsAnno, the latter two
   per user direction for uniformity) are now EXISTS-FRESH with Barendregt
   avoid-sets.

Consequences proved, all Qed and axiom-free:
- `a_split_refines_gen` (prop_soundness_typing) — the split refinement
  with an arbitrary refinement of the codomain painting; the flex row goes
  consistency → refinement → `ad_refine_syn_inh_tyequiv` (ghost-free
  painting refinement IS `≡ᵗ`) → subject transport along `≡ˢ`.
- NEW `algo/prop_rename_decl.v` (712 lines): `a_tyequiv_rename_tvar`,
  `ad_pat_rename_tvar`, `ad_sd_typing_rename_tvar` + leaf bridges —
  `thm:sound-type-inference` now receives ONE binder instance and rebuilds
  the DECLARATIVE cofinite families by renaming (type binders; term
  binders keep the existing `ad_sd_typing_rename_tm` route).
- `a_typing_sound` re-proved end to end on the repaired rules (the two
  `_step` cases via the renaming cluster; the two `_base` cases via
  `a_split_refines_gen` and the body's own refinement suffix-stripped).
- The 330-line `a_typing_rename_tm` walker (theorem 4's K6) is DEAD under
  exists-fresh rules and was deleted; the seven landed completeness rows
  now instantiate the binder rules directly.
- Fallout repaired across prop_stability, prop_ty_core (the ty_core check
  cases now pin `B1 = B` through the IH under `core_rigid`),
  prop_soundness_pat (new wf-exp pick lemmas), test/test_examples.
- ⚙ **Build time**: the Abs/AbsAnno rows' binder-rule applications hung
  `prop_completeness_typing.v` (≫40 min on one sentence) for TWO stacked
  reasons: an `eapply … with (x := x); [ … ]` left the rule's context
  arguments as EVARS under the freshness branch's `fsetdec` (pin ALL the
  `with`-arguments), and the freshness goal itself put the row's 12-leaf
  avoid-set hypothesis in `fsetdec`'s scope — the decision procedure is
  exponential in the number of set atoms (~16 here), so even `clear`-scoped
  it needs ≫40 min.  Repair: bullet the application with every context
  argument pinned and close the freshness goal by LINEAR decomposition
  (`solve_notin`, 0.002 s).  The file's total sentence time is now 14.6 s.

## 2026-08-07 — ⭐⭐⭐ **THEOREM 3 IS CLOSED: `a_pat_complete` (thm:complete-skeleton-inference), Qed + axiom-free**

All nine rows and the glue are in `algo/prop_completeness_pat.v`; the theorem
is `Check`ed and `Print Assumptions`-audited in `README.v`.  The induction is
on `size_exp e` alone (P-Sub is FUSED into the base rows), each row a STEP
LEMMA taking its IH as an explicit premise (the P7 factoring).

⭐ **K6 (the binder rows' renaming) closed as a HYBRID**: `a_pat_rename_tm`
swaps the type-level data (contexts and both skeletons — equivariance, so no
freshness is needed for it) and SUBSTITUTES in the term.  ⚠️ The recorded
statement needed one repair: a third freshness premise `b ∉ fvar_in_exp e`
(the NEW name avoids the term) — without it the `AP-Var` rows are a
counterexample (`e = var b` with `b`'s entry in `Θ0` and `a ∉ dom Θ0`).

⭐⭐ **The binder rows' shared skeleton** (AbsCheck / AbsAnnoCheck / Abs /
AbsAnno): ONE fresh binder; the IH once; `a_pat_sound`'s identity increase
decomposes the run's output around the VERBATIM term entry
(`a_inc_var_skl_inv` / `binds_mid_eq` + tm-verbatim); a freshness pack from
the KIND DISCIPLINE (a term-bound atom is never type-level bound, so wf data
cannot mention it — K8); `a_pat_rename_tm` generates the cofinite family from
the instance; and the optimality's three conjuncts strip by K4 +
`a_inc_equiv_strip_var_*_head`.  ⭐ The caller's identity witness reaches the
IH through the run's own because **an identity witness is determined by its
source** (`a_inc_id_msubst_unique`).

⭐⭐ **The two transports the paper leaves implicit** both fell to EXISTING
kit (grep-the-completeness-kits-first paid twice): the Abs domain's
"precision along the metasubstitution equivalence" is
`a_inc_equiv_precise_msubst_flip` + `ad_precise_preserves_refine` +
`msubst_pskl_compose`/`_id`; AbsAnno's and App's two-stage compositions glue
by `a_inc_equiv_glue`, the dom condition by
`a_assign_unify_consis_flex_preserve` (AbsAnno) or the NEW
`a_inc_id_flex_preserve` (App — an identity increase preserves flexibility,
via `a_inc_binds_tvar_rev`).

⭐ New general-purpose pieces beyond the step lemmas: `ad_ctx_precise_refl`
(context precision is reflexive on a PAPER-wf context — the skeleton
entries' payload-wf discipline is a hypothesis, `a_wf_pskl_strengthen`-ed to
each tail), `ad_pat_consis_syn_bid` (a type's SYN painting is consistent
with any of its BID paintings — the paper's "consistency of syn{A} with
bid{A}"), `a_wf_exp_of_tvarish` (theorem 1's `a_wf_exp` from lc + the
rigidity side condition — so theorem 3 carries `lc_exp` only).

⚙ The theorem's hypothesis set beyond the paper (all WF-SIDE-CONDITIONS.md
externals): wf of both contexts + the input skeleton, the payload-wf
discipline of BOTH contexts' skeleton term entries (the solution side is new
— `⪯ᶜᵗˣ`-reflexivity needs it), mode compatibility, `lc_exp`, and the
annotation-rigidity side condition.

⛔ NEXT: theorem 4 (thm:complete-type-inference, proofs.tex:617–1395) — needs
the height-indexed mirror `ad_sd_typing_n` (its `__abs_check_step` recurses
on the SAME term), `a_typing_rename_tm` (same swaps), and §6.3's two open
side conditions.  Then the cleanup debt.

## 2026-08-07 — ⭐⭐ **THEOREM 3's KIT and its THREE BASE ROWS are CLOSED** (NEW `algo/prop_completeness_pat.v`)

`thm:complete-skeleton-inference` is under way.  Its conclusion is factored
as `pat_complete_concl`, in `a_sub_complete`'s own shape.  ⭐ Two
structural simplifications, both consequences of earlier decisions: the mech
FUSED the paper's `P-Sub` into the three base rows, so the induction is on
`size_exp e` ALONE (the paper's lexicographic measure is theorem-4-only); and
`ad_pat_target_wf` is now provable BOTTOM-UP (§5's rule change), so the
statement needs no target-wf hypothesis at all.

Banked, all Qed + axiom-free: K1 `ad_pat_target_wf`, K7 `a_pat_output_wf`,
K2 `a_inc_binds_var_skl_rev`/`_var_typ_rev` (the solution context's term
entry comes from a question-context one — `a_inc`'s term rows are SEMANTIC),
K3a/K3b the painting bridges (`a_pskl_tyequiv_to_uskl`, `a_tyequiv_to_uskl`,
the two msubst commutes) and the three slack lemmas, K4
`a_inc_strip_tm_head` + `a_isub_strip_tm_head` (the paper's "erasing the term
variable", an INDUCTION because of the deposited suffix), K5
`a_split_complete`, and the three base rows `a_pat_complete_unit` / `_var` /
`_anno`.

⭐⭐ The scouting's one open design point is SETTLED: `P-Anno`'s slack is
REFLEXIVE, because an annotation is SOURCE syntax — its type variables are
RIGID, and `a_inc`'s domain is exactly the source's FLEXIBLES.  That rigidity
is theorem 3's ONE side condition about the term.  ⚠️ `dom κ ∩ dom Θ = ∅` is
NOT the right condition — it is false for identity increases.

⛔ LEFT: the induction's six remaining cases (Freeze, Abs, AbsAnno,
AbsCheck, AbsAnnoCheck, App); per-case recipe in memory `remech-theorem3-plan`
and HANDOFF §6.4.

## 2026-08-07 — ⭐⭐⭐ **§5 IS CLOSED: `lemma:context-precision-skeleton` — and the ALGORITHM'S OUTPUTS ARE PROVEN WELL-FORMED (a new foundation)**

Section D §5 (`ad_ctx_precise` + `ad_ctx_precise_pat`, NEW
`algo/prop_precise_sub.v`) is Qed + axiom-free and audited in README.v,
together with the flagged rule-change decision — RESOLVED differently than
recorded:

- ⚠️ the recorded route (wf premise on `ad_pat__app` + top-down propagation)
  is REFUTED by analysis: the non-transitivity cex's capture configuration
  sits inside `P-App`'s own refinement premise, so target-wf cannot reach
  the function premise's domain.  The landing repair puts
  `Θ ⨟ empty ⊢ₚₛᵃ ⌊Q⌋` on the three BASE rows of `ad_pat` — exactly where
  lemma:precision-sub's external counterpart-wf is consumed (this lemma's
  Var case; theorem 3's Sub case).  `ad_sd_typing` unchanged (TY derives wf
  from scope + ghost-freeness).
- ⭐⭐⭐ soundness supplies the premise from a NEW foundation,
  `algo/prop_wf_output.v`: **`a_consis_output_wf`** (the consistency run's
  output is wf — a 14-row induction whose motive pairs wf-at-∅ with a
  `pskl_shielded_ftv`-avoidance of the run's Δ1∪Δ2 trackers, an ftv
  provenance bound, and guardedness propagation; the Ghost/GhostR
  `Δ ∩ ftv` side conditions are exactly what make the close-rows' re-binding
  sound) and **`a_sub_output_wf`** (mutual with the flex walk; context
  surgeries cribbed from `a_subtag_sound_bundle`).  Both Qed + axiom-free.
  The P6 kit supplied the gadget and the strip (`pskl_shielded_ftv`,
  `a_wf_pskl_tvar_to_delta`, `a_wf_pskl_all_of_one`) — the
  grep-completeness-kits-first rule again.
- consumer sweep: prop_ctx_mono / prop_soundness_pat / prop_suffix_erase
  (+ NEW `subst_bskl_to_pskl_eq`) / the cex file; `a_pat_sound`'s base rows
  supply via `a_sub_output_wf`.  Full `make coq` green, all README audits
  Closed.

## 2026-08-07 — ⭐⭐⭐ **§3 IS CLOSED: `lemma:precision-sub` over the LEAF-VALID join — as a 133-line COROLLARY of P5c, not a new induction**

`ad_precise_extends_pat_sub_gv` / `_v` (prop_completeness_sub_precise.v
tail, Qed + axiom-free, FUEL PRESERVED, both sorts).  The planned ~400-line
subject-precision induction was NOT needed: **P5c's precision-substitution
`ad_pat_sub_precise_upre_gv` already IS the transport over `ad_pat_sub_gv`**
— built for P7b's Sub-ForallL, leaf refinements carried through
(`uskl_precise_erase_refine`), fuel preserved by `_gv`'s non-incrementing
admin rows (that fuel discipline was DESIGNED for precision-substitution).
What §3 needed on top is only the BRIDGE `uskl_precise_of_ad_precise`: the
paper's pskl precision (a refinement between two INHERITED paintings) is a
decorated subject-precision `uskl_precise Θ ∅ ⌈P'⌉ᵘ ⌈P⌉ᵘ` — rows map
one-to-one, `tophole_fill` dead (an inh painting is never `bskl_all_syn`),
the `__hole` row's ∀-freeness by `inh_eq_syn_no_forall`, the flex rows by
`mono_inh_eq_syn`.  The corollary instantiates P5c at
`Ψrep = Ψsup = Ψna = ∅` with the identity context map.

⭐ LESSON (now a standing rule): before mirroring a structural lemma to a
new syntactic level, grep the P5–P7 completeness files for an existing
`precise`/`upre`/`transport` — the campaign already built level-crossing
machinery for everything ForallL's ψ-instantiation touches.  The previous
entry's transitivity kit was built before this search; it stays (it is the
pskl-level counterpart the tree lacked) but §3 does not consume it.

⛔ NEXT: §5 `ad_ctx_precise` + `ad_ctx_precise_pat` (Var row consumes
`ad_precise_extends_pat_sub_v`; the other rows use prop_ctx_mono's
`aenv_tbinds_le` `_mono` family), then theorem 3.

## 2026-08-07 — ⭐⭐ **§3's ENGINE: the UNCOLOURED refinement-transitivity kit is Qed** — `ad_refine_pskl_trans_gen` + `ad_precise_preserves_refine_pskl` (prop_precise.v tail)

The first component of `lemma:precision-sub` over the leaf-valid join: the
pskl-level mirror of prop_precise.v's `ad_refine_syn_trans` chain, all Qed
and axiom-free.  `ad_precise_preserves_refine_pskl` is what transports the
`_gv` leaf datum (`Θ ⨟ ∅ ⊢ᵣₚᵃᵈ P ⊳ ⌊Q⌋`) down a precision `P' ⊑ P`.

⭐⭐ **The mirror is NOT row-for-row**: the syn template's ghost-left crux
kills the `__all` row outright (a syn painting has no `bskl_all_inh`), but
the pskl `__all` row FIRES and its inner `__tophole_fill` case composes a
`∀◇`-fill under a `∀ˢ∘∀ˢ` step — which needs the transitivity IH at a
REASSOCIATED context (the ∀-witness moved from Δ into Θ as a rigid).  A
fuel mirror was NOT needed: the statement is GENERALIZED over a context map
(`Hmap` : bindings preserved into `Θx`; `Hsplit` : each source Δ-variable
is still in `Δx` or has become a rigid of `Θx`), so the structural IH is
available at the moved context.  The Δ-freeness propagation
(`ad_refine_pskl_ftv_delta_free`) and the ghost-left package
(`ad_refine_pskl_hole_l`) carry the same map.  Consumers use the plain
instance `ad_refine_pskl_trans` (identity map).

`ad_refine_pskl_of_inh_paintings` drops a precision (refinement of two
INHERITED paintings) to the uncoloured judgement — sound because the pskl
`__hole` fill demands strictly less than the syn one (any wf skeleton vs a
synthesised painting), with `__tophole_fill` dead (an inh painting is never
`bskl_all_syn`) and the flex rows closed by `mono_inh_eq_syn`.

⚙ Traps this cost: Coq 8.20's `induction` on a hypothesis whose context
indices are pinned by other hypotheses AUTO-REVERTS those hypotheses and
re-introduces the variables under FRESH names (`Θx` → `Θ0`) — hypothesis
NAMES survive, so the fix is a type-directed
`match type of Hmap with ... => rename ... end` preamble in the subcases
that name the context; `inversion HwfQr; subst` substitutes the context
variable away entirely (use the new `a_wf_pskl_{arrow,all,tophole}_inv_x`
stable inversions instead).

⛔ NEXT for §3: the `_gv` precision-sub induction itself
(`ad_precise_extends_pat_sub_gv`) — its consis premises transport by
`ad_pat_consis_subject_precise` (prop_consis_precise.v:692, already built),
its leaves by this kit, its `Ψ [=] ∅` by `ftag_in_pskl_to_uskl`; then §5's
`ad_ctx_precise` + `ad_ctx_precise_pat` (the "context-change lemma" §5 asks
for now EXISTS as the `aenv_tbinds_le` `_mono` family in prop_ctx_mono.v).

## 2026-08-07 — ⭐⭐⭐ **SECTION D: §6.2's RULE CHANGE LANDS — the six base rows embed `ad_pat_sub_v`, and both soundness theorems survive AXIOM-FREE**

`make coq` clean; all 33 `Print Assumptions` audits in `README.v` — including
`a_pat_sound` and `a_typing_sound` — still *Closed under the global context*.
The capture configuration is now REJECTED by the rules themselves:
`cex_ad_pat_join_not_leaf_valid.v` §3 flips from `cap_reachable` to
`cap_not_reachable`, the change's own machine-checked witness.

**1. The missing pair is built first** (`prop_suffix_erase.v` §5 / §8,
~270 lines, Qed + axiom-free on the FIRST compile):

- `ad_refine_pskl_subst_mid` — the `ad_refine_pskl` mirror of
  `ad_refine_syn_subst_mid` (:499).  The two judgements' `__hole` rows differ
  (the `bskl` one's fill is a SYNTHESISED painting, the `pskl` one's a plain
  wf fill), so the induction is mirrored, not bridged — and the `pskl`
  `__hole` row is in fact SIMPLER (no painting rewrite), while the `__var`
  row closes by `ad_refine_pskl_refl` + `a_wf_pskl_mono_ptyp`.
- `ad_pat_sub_gv_subst_mid` + `ad_pat_sub_v_subst_mid` — the `_gv` mirror of
  `ad_pat_sub_subst_mid` (:929), fuel carried UNCHANGED; the four leaf rows'
  refinement datum travels by the new lemma, re-shaped by
  `uskl_to_pskl_subst_mono` / `bskl_to_pskl_subst_mono`.  The ForallL rows
  reuse §1h's idiom exactly (`6: exact IH` first — it is what fixes ψ — then
  `simpl; rewrite ftag_in_uskl_subst_mono; assumption` for the hygiene
  premise).

**2. Then the rule change in ONE pass**, exactly as scoped
(hand-off §6.2; the reverted attempt's patch served as the map):
`ad_pat__{unit,var,anno}` and `ad_sd_typing__{unit,var,anno}` now embed
`ad_pat_sub_v <NM> m empty Θ <R> <Q>`.  Consumer sites converted:
`ad_pat_sub_mono` → `_v_mono` (6 in prop_ctx_mono.v, 4 tm-swap rows EACH in
prop_soundness_pat.v and prop_soundness_typing.v), `ad_pat_sub_isub` →
`_v_isub` (3 + 3), `ad_pat_sub_mod_comp_sk` + ⭐ its TY analogue
`ad_pat_sub_mod_comp_ty` recover the plain premise via `ad_pat_sub_of_v`
(3 + 3 — the TY triple was NOT on the attempt's consumer table), the seven
`a_sub_sound` sites in `a_pat_sound` / `a_typing_sound` become
`a_sub_sound_v`, and ⭐ `a_typing_sound`'s `a_wf_ptyp Θ1 A` conjunct
reads the join through `ad_pat_sub_target_wf` — plain again, via
`ad_pat_sub_of_v` (3 sites, also not on the table).  The six
`@ad_pat_sub_subst_mid` base-row sites in `ad_pat_subst_mid` /
`ad_sd_typing_subst_mid` become `@ad_pat_sub_v_subst_mid` — same @-shape,
since the wrapper keeps the plain lemma's quantifier prefix.

⚙ The predicted several-rebuild loop took exactly three: (i)
prop_soundness_typing.v needed `Require Import …prop_soundness_subtag` (a
`Require Import` does not re-export — fourth occurrence of this trap), (ii)
the `mod_comp_ty` triple, (iii) the `target_wf` triple.  Everything else —
including the cex rewrite — compiled on the first attempt.

⛔ NEXT (hand-off §6.3 + the theorem-3 row map): theorem 3
(`thm:complete-skeleton-inference`, proofs.tex:1711–2197), whose Sub case
still wants `lemma:precision-sub` (§3) and §5's `ad_ctx_precise`; then
theorem 4.  The completeness direction now RECEIVES `ad_pat_sub_v` from the
hypothesis derivation's base rows and feeds it to `a_sub_complete`.

## 2026-08-06 — ⭐⭐ **SECTION D completeness: the three SCOUTING questions are settled — the leaf-validity gap is REAL (machine-checked), and `lemma:precision-sub`'s flagged obstruction is DEAD**

Two new files in `cex/`, both compiling; no change to the development yet.

**1. Where `ad_pat_sub_gv` enters — ON THE RULE**
(`cex/cex_ad_pat_join_not_leaf_valid.v`; hand-off §6.2).  `a_sub_complete`
takes its join as the LEAF-VALID `ad_pat_sub_gv`, while `ad_pat` /
`ad_sd_typing` embed the plain `ad_pat_sub`, so a completeness induction
arrives at a base row it cannot use.  The gap is not bookkeeping: at the
CAPTURE configuration (subject `∀X.◇`, counterpart `∀ˢX.X`) the plain join
EXISTS (`cap_plain`), the leaf-valid one does NOT (`cap_no_gv`), and the
configuration is REACHABLE from `ad_pat` as `P-Var` at an entry `x : ∀X.◇`
(`cap_reachable`).  ⭐ The mechanism is the paper's own asymmetry —
**consistency's ∀-rows push the rigid into `Θ` so the ghost's fill may capture
it, refinement's ∀-row pushes it into `Δ` and `ad_refine_pskl__hole`'s fill is
`Δ`-free BY RULE**.

⚙ This is the paper's AUGMENTED consistency-solution notion propagating one
layer up (`a_consis_complete` already carries the same datum at its root;
subtyping carries it at the LEAVES because at the root it is vacuous —
`cex_p7_univ_ghost_r_vacuous.v`).  Consequence: §6.1's soundness-side repair
(make `a_subtag_sound_bundle` conclude `_gv`) is now a hard PREREQUISITE, not
an option — the rule change breaks theorems 1 and 2 until it lands.
Registered in `docs/PAPER-GAPS.md`.

**2. The four rule-level side conditions, from the completeness side**
(hand-off §6.3).  None refuted.  `uniq (Ξ ++ Θ)` is derivable from
`a_typing_sound` + `⊴`; `AT-AbsAnnoCheck`'s split-domain result is free;
`uniq (αs ++ Θ1)` needs a NEW `a_guess_mono` existence lemma with an avoid set
(`prop_flex.v` has only `_decls` / `_generated_fresh` / `_ftv` / `_open_at`);
⚠️ the one to watch is "`Ξ` does not occur in the result type" at the two
`_step` rows, which needs an invariant no lemma states yet ("a TC run's result
type is scoped BELOW any suffix the run deposits").

**5. ✅ The `Check` row's missing lemma is BUILT** — `prop_soundness_subtag.v`
§1a–§1d, Qed and axiom-free, ~180 lines: `ad_refine_pskl_unfold_def_target`,
⭐ `ad_refine_syn_f_inh_wf_transfer`, `refine_transport_arrow` / `_all`, and
`ad_refine_pskl_refine_inh_gen` / `_target`.  ⭐ **It needs TWO FEWER
hypotheses than its consistency twin**: `ad_pat_consis_refine_inh_gen` carries
a Δ-free wf of the source plus "every Δ-variable is Θ-visible", and neither
survives the mirror because **refinement's `__all` extends Δ while
consistency's ∀-rows extend Θ**.  The Δ-RELATIVE wf transfer replaces the
first and the second turns out to have no consumer at all.
⚠️ Trap that cost 97 s per run: `fsetdec` on an EVAR avoid-set does not
terminate — `a_wf_pskl_delta_mono`'s `Δ0` is left an evar by the
Δ-polymorphic `a_wf_pskl_mono_ptyp`, and the wrapper was not needed.
Profile-first paid: imports alone were 0.3 s, so it was never I/O.

## 2026-08-07 — ⭐⭐⭐ **SECTION D: §6.1 IS CLOSED — `a_subtag_sound_bundle` concludes the LEAF-VALID join**

`make coq` clean; every `Print Assumptions` audit still *Closed under the
global context*.  `subtag_sound_concl` / `subtag_flex_sound_concl`'s third
conjunct is now `exists n, ad_pat_sub_gv n NM M Ψ Θ1 R Qt`, and all fifteen
rows are converted.

Row-by-row leaf sources, as landed: `Infer` / `UnivGhostR` →
`ad_refine_pskl_refl` at the wf subject (after
`bskl_to_pskl_pskl_to_bskl_syn`); `Check` → §1a–§1d's
`ad_refine_pskl_refine_inh_target`, transporting the dropped conjunct from the
CONSISTENCY's output `Qt` to `B`; `Arrow` (domain) → the dropped conjunct
DIRECTLY, `⊴`-transported with `ad_refine_pskl_isub`; `ForallR` →
`ad_pat_sub_gv_strip_suffix` + `ad_pat_sub_gv_rename_tvar`; ⭐ `ForallL` ×2 →
ONE WIDER AVOID-SET on `a_tags_sort_decorate_exists` (the decoration is chosen
fresh anyway, so `_gv`'s extra hygiene premise costs only naming the subject's
tags), exactly as §6.1 predicted; the ghost rows and the flex walk pass
through, using `_gv_psi_cong` / `_isub` / `_weaken`.

⚙ Fuel: leaves take `0`; `ForallR` / `Arrow` / `ForallL` conclude at `S n`;
`UnivGhostL(G)` / `FlexMono` / the whole flex walk are NON-incrementing, so
they reuse the IH's `n`.

⚙ Consumers: of the three positional readers, one never touched the join; the
other two recover the plain form with `ad_pat_sub_of_gv`.
`prop_soundness_sub.v` needed the `def_decl_algo_sub_hyg` import added — a
`Require Import` does not re-export.  ⭐ `a_sub_sound`'s own statement is
UNCHANGED (still the plain join, recovered at the call site), deliberately:
its consumers still feed the plain join into `ad_pat` / `ad_sd_typing`.

⛔ **NEXT:** change those two rules to embed `exists n, ad_pat_sub_gv n …`
(§6.2) and hand the `_gv` on from `a_sub_sound` — the last step before
theorems 3 and 4.

**9. ✅ THE `strip_suffix` CHAIN IS COMPLETE — and with it EVERY structural
prerequisite of §6.1** (`prop_soundness_subtag.v` §1h, Qed and axiom-free):
`ad_refine_pskl_subst_flex_def`, `ad_pat_sub_gv_subst_flex_def`, and the
driver `ad_pat_sub_gv_strip_suffix`, plus `bskl_to_pskl_subst_mono` and ⭐
`ftag_in_uskl_subst_mono` (a MONOTYPE's painting is tag-free, so substituting
it cannot add tags — the `ForallL` hygiene premise for the third time).

⚙ All four `_gv` structural mirrors (`psi_cong`, `isub`, `weaken`,
`strip_suffix`), the fuel-preserving `rename_tvar`, and the `Check` row's
`ad_refine_pskl_refine_inh_target` are now in the tree.  What is left of §6.1
is the ATOMIC step: change the two `*_concl` definitions and rewrite the 15
rows.

⚠️ `guarded_pskl_subst` had to be written FULLY QUALIFIED here — the bare name
resolves to prop_looksub.v's homonym, which carries a DISEQUALITY premise.

**8. ✅ The `strip_suffix` chain, UNDEFINED-HEAD half** — `prop_soundness_subtag.v`
§1g, Qed and axiom-free: ⭐ `ad_refine_pskl_subst_flex` (which did not exist in
any form — no `ad_refine_pskl`/`_f` substitution-strip), then
`ad_pat_sub_gv_subst_flex`, plus `bskl_to_pskl_subst_unit` and
`ftag_in_uskl_subst_unit` (substituting `1` cannot change TAGS either).

⛔ **And the chain turned out FIVE lemmas deep, not three.**  The plain driver
`ad_pat_sub_strip_suffix` (prop_pat_sub.v:1158) does not induct on the
judgement — it iterates a SUBSTITUTION strip head-first over Ξ, and its head
**splits on whether the flexible is DEFINED**, calling
`ad_pat_sub_subst_flex_def` (prop_pat_sub.v:1031) in that branch.  So the
DEFINED half (`ad_refine_pskl_subst_flex_def`, `ad_pat_sub_gv_subst_flex_def`)
and the driver itself remain.

**7. ✅ THREE of the FOUR `_gv` STRUCTURAL MIRRORS the bundle's rows consume**
— `prop_soundness_subtag.v` §1f, Qed and axiom-free: `ad_pat_sub_gv_psi_cong`
(the leaf carries no Ψ), `_isub` and `_weaken` (leaf via
`ad_refine_pskl_isub` / `_weaken`, both already in the tree).

⛔ **And the survey that produced them is the session's other finding: §6.1's
conversion is BIGGER than "threading".**  The 15 rows consume four structural
lemmas over `ad_pat_sub`, each needing a `_gv` mirror.  The fourth,
`ad_pat_sub_gv_strip_suffix` (the `ForallR` row), is a THREE-lemma chain with
a missing ingredient: the plain `ad_pat_sub_strip_suffix`
(prop_pat_sub.v:1158) does not induct on the judgement — it iterates
`ad_pat_sub_subst_flex` (prop_pat_sub.v:749, ~120 lines) head-first over Ξ —
and **`ad_refine_pskl_subst_flex` does not exist in any form**.  Details in
HANDOFF §6.1(c).

**6. ✅ `ad_pat_sub_gv_rename_tvar` is BUILT** — `prop_soundness_subtag.v` §1e,
Qed and axiom-free.  §6.1's `ForallR` row needs it because the ALGORITHMIC
subtyping rule is EXISTS-FRESH (one α) while `ad_pat_sub_gv__forall_r` is
COFINITE; the `_gv` version carries the fuel UNCHANGED.  Two new bridges:
`ad_refine_pskl_f_of_plain` (the `__hole` hygiene side condition is vacuous at
`F = ∅`) and ⭐ `ftag_in_uskl_subst_var` — **renaming a TYPE variable cannot
change TAGS**, an EQUALITY, so the local copy is 6 lines and the downstream
`ftag_in_uskl_subst_uskl_in_uskl` was not needed.

⚠️ Four traps, all from moving scratch-proved script INTO the tree — a scratch
file's hint context and name resolution are NOT the target file's: `; auto`
closes a different NUMBER of goals (and the "Wrong bullet" then points at the
NEXT row, not the guilty one); **`guarded_pskl_subst` resolves to
`prop_looksub.v`'s homonym here**, which carries a DISEQUALITY premise (use
`guarded_pskl_subst_var`); `apply` does not present premises in source order,
so `first [ … ]` per goal beats a positional chain; and in the two ForallL
rows the RECURSIVE premise must be discharged FIRST because it is what fixes
`ψ` — otherwise `ψ` is still an evar at the `a_tags_sort` goal.

**4. §6.1's dependency-order blocker is GONE.**  `ad_pat_sub_g_of` (was
`prop_completeness_sub_precise.v`) and `ad_pat_sub_gv_fuel_weaken` (was
`prop_completeness_sub.v`) MOVED to `algo_decl/def_decl_algo_sub_hyg.v`,
joined by the composite `ad_pat_sub_of_gv`.  Both are plain inductions over
the mirrors, so they need nothing that file does not already import — and
`algo/prop_soundness_subtag.v`, which now has to CONCLUDE `_gv`, sits before both
completeness files.  `make coq` clean.

⭐ **And §6.1's row table gained a row it under-estimated**: the `Check` row's
leaf datum is `⌊T⌋ˢ ⊳ ⌊Qt⌋` for the CONSISTENCY's output `Qt`, while the row
re-targets its conclusion to `inh B` (audit-F2 — the output is not literally
`B`).  So it needs the `ad_refine_pskl` MIRROR of
`ad_pat_consis_refine_inh_target` (prop_soundness_subtag.v:366).  `Arrow`'s
domain leaf, by contrast, is direct.

**3. `lemma:precision-sub` — the Ghost row is NOT the obstacle**
(`cex/probe_precision_sub_ghost_row.v`; hand-off §3).  `ad_precise P Q` is
`inh{P} ⊳ inh{Q}`, and `ad_refine_syn__hole`'s fill is a SYNTHESISED painting
while the target is an INHERITED one — the two images meet exactly on the
`pskl_all_syn`-free skeletons.  So `□ ⊑ P` hands back a Θ-well-scoped `P1`
with `inh P = syn P1` (`ad_precise_hole_inv`), which IS `ad_pat_sub__ghost`'s
obligation, and `□ ⊑ ∀X.P` is outright FALSE
(`ad_precise_hole_all_absurd`).  ⚠️ A second candidate counterexample — a
DEFINED flexible subject at `M = TC`, where `ad_pat_sub__flex_mono` is
function-mode only — is also REFUTED: `Sub-UnivGhostR` takes any *guarded*
subject and a variable is guarded (`ps_concl`).  What a full proof still owes
is the Ghost row's `Ψ [=] ∅` (automatic: a `pskl_to_uskl P` subject is
tag-free) and a `mod_comp_sk` transport.

## 2026-08-06 — ⭐⭐⭐ **SECTION D: `thm:sound-type-inference` IS CLOSED** — `a_typing_sound` is Qed and axiom-free, and four side conditions the paper leaves to prose are now on the rules

`make coq` clean; `a_typing_sound` `Check`ed and `Print Assumptions`-audited in
`README.v` beside `a_pat_sound`.  The eleven-row induction
(`algo/prop_soundness_typing.v` §13) is theorem 1's mirror one layer up, with
the SAME two extra hypotheses (`a_wf_exp` + the disciplined skeleton-entry wf)
and `a_ty_mode_compat` in place of `a_sk_mode_compat`.

**⚙ The conclusion carries one conjunct beyond the hand-off's target**:
`a_wf_ptyp Θ1 A`, the output type scoped in the output context.  `AT-App`
consumes it — its third premise runs at input `⌈A⌉`, and nothing else in the
derivation says the FUNCTION's domain is scoped where the argument is checked.
It is the paper's ambient "all inputs are well-formed", threaded; and the four
CHECK rows can now prove it exactly because of the Barendregt premises below.

**⭐ Row by row.**  Rows 1–4 (`Unit`/`Var`/`Anno`/`Freeze`) are theorem 1's with
`a_sub_sound` at the TY sort, plus `btyp_of_erased_ptyp` (a `bskl` whose
erasure is a painting of a TYPE is itself a colouring — the sort bridge the SK
layer did not need).  `Anno`'s two sequential premises thread the skeleton-entry
hypothesis through `a_typing_tm_ge`.  Rows 5/6 (`Abs`/`AbsAnno`) use
`a_split_ty_shape`: AWAY from check mode the split is arrow-or-hole, so
`a_split__flex` — and with it `lemma:split-refine` — is out of reach, exactly as
at theorem 1.  ⭐ `AT-Abs` is the one row with no counterpart: its `guess^TY`
block sits BETWEEN the binder and the context, so the ⊴-peel crosses it with
`a_isub_strengthen_decls_src` (the block is declaration-only), and its
refinement obligation is `a_guess_mono_refine`.  Rows 7–10 are the four CHECK
rows whose output DROPS the pending suffix; they are exactly the ones that need
`ad_sd_typing_strip_suffix` AND `a_split_refines`, because `a_ty_mode_compat`'s
TC row admits any `⌈A⌉` and `a_split__flex` IS reachable there.  ⭐ NO
type-variable renaming for `ad_sd_typing` is needed at the two ∀-peeling rows:
at TC the colouring is FORCED (`btyp_inh_painting_inv`), so the induction
hypothesis is simply re-run at every member of the cofinite family.  Row 11
(`AT-App`) runs theorem 1 on premise 1, inverts the IH's arrow refinement, and
gets the appendix's fourth `≡ᵗ` premise from `ad_refine_syn_inh_tyequiv`.

**⚠️ FOUR RULE CHANGES, all in `algo/def_rules.v`, all documented in
[`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md) and cleanly revertible.**

1. **The four CHECK rows get the paper's two prose side conditions**:
   `uniq (Ξ ++ Θ)` (verbatim `Sub-ForallR`'s own Barendregt premise for its own
   discarded suffix) and "`Ξ` does not occur in the RESULT type".  The paper's
   proof of this very theorem ASSUMES both — "since all variables in Ξ do not
   appear in `inh{B}`" — and ⛔ neither is derivable: a scoping theorem cannot
   supply the second, because at the ∀-peeling rows the body's result may
   legitimately mention flexibles the body created and the rule offers no
   handle saying those were re-deposited BELOW the discarded prefix.
2. **`AT-Abs` gets `uniq (αs ++ Θ1)`**, the consumer-side filter for
   `guess^TY`'s block.  `uniq αs` is NOT derivable (the guess's ARROW row runs
   both halves at the same `Θ`) — this registry already records that for the
   collection walk, where `Sub-ForallL`'s `uniq (Ξ, Θ₀)` filters it downstream.
   `AT-Abs` is the other consumer: it puts the block INTO the context.
3. ⭐ **`AT-AbsAnnoCheck`'s result domain is the SPLIT's `A'`, not the written
   annotation.**  The paper's (commented-out) rule writes `A → B` while
   orienting its consistency `A' ∼ A` — subject the split's domain, input the
   annotation, the REVERSE of `AT-AbsAnno`'s `A ∼ P`.  The two cannot both
   stand: with `A → B` soundness owes `inh⌈A'⌉ ⊳ ⌈A⌉` while the consistency
   run transports the other way, and refinement is neither symmetric nor
   transitive.  `A' → B` is also what the un-annotated `AT-AbsCheck` already
   returns, and it is exactly what the appendix's `≡ᵗ` premise on
   `sd-AbsAnnoCheck` is FOR.
4. (previous pass) `ad_sd_typing__app`'s fourth `≡ᵗ` premise and
   `a_split__flex`'s freshness.

**New in the kit** (`prop_soundness_typing.v` §12): `a_wf_ptyp_of_wf_pskl` /
`_of_scope_pskl` (reading a painting's skeleton well-formedness as a type's),
`a_wf_exp_ftv_dom`, `btyp_of_erased_ptyp`, `a_ty_mode_compat_{hole,arrow}_inv`
+ `a_split_ty_shape`, `a_split_wf` (the split's increase, wf and BOTH
components), `a_guess_mono_wf`, `a_wf_aenv_decls_app`,
`a_isub_strip_var_typ_mid` (the term-entry ⊴-peel that DROPS the suffix — the
`a_isub_strip_tvar_mid` mirror) and `a_wf_ptyp_strip_mid`.

⛔ **Next**: the `ad_pat_sub_gv` composition gap (hand-off §6), then the two
completeness theorems.

## 2026-08-06 — ⭐⭐ **SECTION D: FOUR of theorem 2's five prerequisites are CLOSED — suffix erasure (all six judgements) and split-refine included**

`make coq` clean; everything Qed and axiom-free.

- ✅ **`lemma:suffix-erasure`, all six judgements** (`prop_suffix_erase.v`
  §1–§11).  See the entry below for the SOLVING generalization and the two
  design points that make the lookup rows collapse.  The two the theorem
  quotes are `ad_pat_strip_suffix` and `ad_sd_typing_strip_suffix`.
  §8 re-does `ad_pat_sub`'s transport in the SUBSTITUTED-CONTEXT form
  (prop_pat_sub.v's concludes at the un-substituted tail, which does not
  compose with binder rows that push TERM entries); §9/§10 are `ad_pat` and
  `ad_sd_typing`, whose subject is an EXPRESSION so `subst_ptyp_in_exp`
  enters, and whose colour predicates need the `btyp` mirrors
  `is_styp_subst_mono` / `is_ityp_subst_mono` / `mod_comp_ty_subst_mono`.
- ✅ **`lemma:split-refine`, COLOURED** (`a_split_refines`,
  prop_soundness_typing.v §11).  ⭐ Its enabler is
  `ad_pat_consis_mono_to_refine` (§10) — **a monotype CONSISTENCY is a
  refinement**: once the subject is a monotype painting the two judgements
  have the SAME five rows (`unit`, `var`, `arrow`, the two flexible
  lookups), and everything that distinguishes them is unreachable.
  ⛔ This deliberately replaces the previously-scouted `≡ᵗ ⟹ ⊳` bridge,
  which would have needed refinement symmetry AND TRANSITIVITY — and
  transitivity is FALSE (`cex/cex_refine_not_transitive.v`).
  `consis_mono_sym` supplies the direction change instead.
  ⚠️ Carries a FRESHNESS side condition: `a_split__flex` invents two
  flexibles and the mech's rule records no freshness for them.
- ✅ **`AT-App`'s `≡ᵗ` step — resolved by ADDING THE PREMISE.**
  ⭐ [paper-gap] It was a MISSING APPENDIX PREMISE, not a missing lemma.
  The appendix adds an explicit `≡ᵗ` premise to exactly three
  syntax-directed rules "because in an algorithmic context a flexible may
  stand for either type", then says "we only need to extend freezing and
  annotated lambda rules" — but its own AT-App case needs a fourth, since
  `sd-App` reuses the function's domain BY EQUALITY as the argument's
  checked type.  `ad_sd_typing__app` now carries
  `Θ ⊢ (btyp_to_ptyp B1) ≡ᵗ A2` beside `Θ ⊢ᵃᵈ[TC] e2 ⦂ inh{A2}`.
  ⚙ Ripple: four construction sites, each discharged by the `a_tyequiv`
  transport already sitting beside the one it accompanies.
  ⛔ The alternative (keep the rule, prove the transport) costs an
  `ad_pat_consis` TARGET transport along `≡ᵗ` — both directions at once,
  nested induction, the mirror of `skl_tyequiv_consis_transport`'s SUBJECT
  one — PLUS a mode-indexed generalization over a NEW colour-preserving
  `btyp` equivalence, because `sd-App`'s conclusion type is the function's
  CODOMAIN.  ⚠️ Changing a rule is reserved for the WF-SIDE-CONDITIONS
  pattern, so this is flagged for the authors' call.
- ⚙ **`a_split__flex` now carries its FRESHNESS on the rule.**  The paper
  says "fresh" in prose and the mech's rule recorded nothing, so
  `a_split_refines` could not reach `a_assign_sound` (whose premise is that
  the extended context is well-formed).  Added INPUT-only, against
  `ftvar_in_aenv` rather than `dom`, exactly as `a_guess_mono__hole` does —
  a payload `α̂ ≔ τ` may mention the invented variables and must not.
  WF-SIDE-CONDITIONS pattern, rule-premise variant; no construction sites
  outside the definition, so the ripple is inversion-only.
- ⛔ **LEFT**: the eleven-row induction itself.  HANDOFF §7.5 now carries a
  ROW-BY-ROW plan keyed to `a_pat_sound`'s corresponding rows: eight of the
  eleven have a direct counterpart there, rows 7–10 (the four CHECK ones,
  whose output drops the pending suffix) are the ones needing BOTH new
  lemmas, and `AT-Abs` is the one with no counterpart at all.

## 2026-08-06 — ⭐ **SECTION D: suffix erasure BUILT for four of six judgements — by SOLVING, not by dropping**

New `algo/prop_suffix_erase.v` (§1–§7), Qed and axiom-free; `make coq`
clean.  The repair of `lemma:suffix-erasure`, whose stated proof does not
go through (see the entry below and docs/PAPER-GAPS.md).

**The generalization**: `Θa,α̂,Θ0 ⊢ J ⟹ [τ/α̂](Θa,Θ0) ⊢ [τ/α̂]J`, with the
paper's statement the case where the conclusion's types are Ξ-free.  At
`ForallL` the freely-chosen instantiation ψ becomes `[τ/α̂]ψ` — Ξ-free,
still a decorated skeleton, still the same tags, because τ is a MONOTYPE.

⭐⭐ **Two design points make the rows COLLAPSE instead of needing
transports.**  (1) `solves_flex` demands τ to BE the definition, not merely
to be equivalent to it: then at `flex_def`/`FlexL`/`FlexR` on the
eliminated variable the rule's subject and its unfolding become the SAME
term, so the row disappears.  (2) The substitution is applied to the WHOLE
remaining context, not just the prefix above α̂ — leaving the tail alone is
sound but needs an "α̂ does not occur here" argument at EVERY lookup row,
while substituting uniformly is discharged ONCE, at the driver
(`subst_aenv_fresh_eq` + `a_wf_aenv_ftv_dom`: a well-formed context
mentions only its own domain).

Landed: §1 `subst_abind`/`subst_aenv`; §2 the coercion commutations (⭐ a
MONOTYPE has one colouring, so a single τ serves the `inh` and `syn` rows
of the same derivation); §3 `solves_flex` + `a_wf_ptyp`/`a_wf_pskl` +
`a_wf_ptyp_tbinds_mono` (these judgements read the context only through
`a_binds_tvar`, so they travel along a map of type-level occurrences —
plain `binds`-monotonicity would forbid the payloads to change); §4
`a_tyequiv_subst_mid`; §5 `ad_refine_syn_mono_refl` +
`ad_refine_syn_subst_mid`; §6 `ad_pat_consis_subst_mid` (its `var` row
becomes consistency's REFLEXIVITY on the substituted monotype); §7 the
drivers `ad_refine_syn_strip_suffix` / `a_tyequiv_strip_suffix` +
`solves_flex_of_wf_head`.

⚙⚙ **CORRECTION**: the tree ALREADY had this, one layer down.
`ad_pat_sub_strip_suffix` (prop_pat_sub.v) IS `lemma:suffix-erasure` for
`ad_pat_sub`, and `ad_pat_sub_subst_flex`'s header states the reason
verbatim — "the ForallL witnesses are rewritten too, which is exactly why
this is provable where naive strengthening is not".  So the obstruction is
a REDISCOVERY at the tree level; the PAPER gap stands unchanged.  The whole
`_subst_mono` closure family is reused rather than rebuilt.

⛔ LEFT: `ad_pat` and `ad_sd_typing`.  They additionally need
`ad_pat_sub_subst_mid` in the SUBSTITUTED-CONTEXT style — prop_pat_sub.v's
`ad_pat_sub_subst_flex_def` concludes at the UN-substituted tail (with an
extra "no definition in the tail mentions β" hypothesis), and that shape
does not compose with binder rows that push TERM entries whose payloads the
substitution rewrites.  Their subject is an EXPRESSION, so
`subst_ptyp_in_exp` enters too.

## 2026-08-06 — ⭐ **SECTION D: two more of theorem 2's prerequisites CLOSED — and `lemma:suffix-erasure` is NOT the "straightforward induction" the paper claims**

`algo/prop_soundness_typing.v` §8–§9, both Qed and axiom-free; `make coq`
clean.

**§8 `ad_sd_typing_mod_comp_ty`.**  ⭐ Not `ad_pat_mod_comp_sk` one sort up.
At the SK layer `mod_comp_sk` is stated on a `bskl` — exactly what the
subtyping premise's target IS — so the base rows read the fact off the
premise.  At the TY layer `mod_comp_ty` is on a `btyp` while the premise's
target is that `btyp`'s SKELETON, so two shape bridges are needed:
`is_styp_of_is_sskl_erase` (INFER) and `is_ityp_of_erase_inh` (CHECK).
⚠️ Only the CHECK one needs local closure — `is_sskl` carries lc itself,
whereas `btyp_to_bskl (btyp_var_b n)` and `pskl_to_bskl_inh (pskl_var_b n)`
agree while a BOUND variable is not `is_ityp`.  It is supplied from the
`Check` row's own consistency premise (`ad_pat_consis_lc_r`,
`lc_btyp_of_lc_bskl_erase`).  The other lc source is the appendix's `≡ᵗ`
premises at `Freeze` / `AbsAnnoCheck(→)`: `a_tyequiv_lc` carries
`a_wf_aenv Θ`, because the `flex_def` row hands back a DEFINITION and only
the context says it is a monotype — the same hypothesis `d_typing_skmod`
carries as `d_wf_denv`.  ⭐ The induction never goes under a binder.

**§9 `a_guess_mono_refine`.**  The paper's "By ⑯ and definition of
`guess^TY`, we have `Θ1,ᾱ ⊢ inh{P} ⊳ inh{A}`" (AT-Abs), which exists
nowhere as a lemma.  Filling a ghost with a fresh flexible IS a refinement
step; a universal ghost is DROPPED, so `⫯.P` is `tophole_remove`, not
`tophole_keep`.  ⚙ SIZE induction (source exists-fresh, target cofinite —
the ∀ row goes through `a_guess_mono_open_at`).  ⭐ The statement carries a
**Δ** and the ∀ row puts its witness there, the same decoupling
`ad_refine_syn_target_transport` needed; sound here for the reason it was
unsound there — `__hole`'s fill is Δ-free BY RULE, and guess^TY's fills are
the generated flexibles, which live in Θ.

**⛔ The scouting result that changes the plan: `lemma:suffix-erasure`.**
It IS needed (the four CHECK rows of `a_typing` drop the pending suffix
from their output; `a_pat`'s keep it, which is why theorem 1 dodged it),
and it is NOT "a straightforward induction on the typing derivation".  The
obstruction is `ad_pat_sub`'s `ForallL`: it instantiates with a decorated
skeleton `ψ` the rule chooses freely — `is_tskl__var` admits one that
mentions Ξ — so the recursive premise sits at `open R ψ`, not Ξ-fresh, even
though the conclusion is.  The configuration is reachable with a DEFINED
`α̂ ∈ Ξ`.  Every OTHER route into Ξ surfaces in the types.  ⭐ The route
that works: erase by SOLVING, not dropping — `Ξ ++ Θ ⊢ J ⟹ Θ ⊢ κJ` where κ
solves Ξ into Θ (undefined `α̂ ↦ 1`, defined `α̂ ↦` its definition's image),
which is the identity on Ξ-free types and turns `ψ` into an Ξ-free `κψ`
that is still `is_tskl` + ghost-free + same-tags.  Recorded in
docs/PAPER-GAPS.md and HANDOFF §1, together with a strictly-weaker fallback
(read the conclusion up to a flexible suffix; then suffix MOVING alone
suffices, and the sequential rows still compose via
`(Ξ2 ++ Θ2) ⊴ (Ξ2 ++ Ξ3 ++ Θ3)`).

Also recorded, for the authors: `sd-App` may simply be MISSING a fourth
`≡ᵗ` premise.  The appendix already adds one to `sd-Freeze`,
`sd-AbsAnnoCheck` and `sd-AbsAnno` for exactly the reason `AT-App`'s
"Thus by ⑧ and ⑬" needs a transport the paper never states.

## 2026-08-06 — ⭐ **SECTION D: thm:sound-type-inference STARTED — its `Freeze` ingredient is DERIVED from theorem 1's transport, not rebuilt**

New file `algo/prop_soundness_typing.v`; all Qed and axiom-free; `make coq`
clean.

**⭐ The headline.** `sd-Freeze` carries an explicit `Θ ⊢ B ≡ᵗ A` premise
(one of the appendix's three added premises), and the paper discharges it
with a single clause off thm:sound-consistency — "which further gives
`Θ2 ⊢ B ≡ A`".  The mechanized consistency soundness hands back a REFINEMENT
into the run's own output colouring instead, so the equivalence is recovered
in two steps, and both were already paid for:

1. the refinement-target transport of `prop_soundness_pat.v` §4 turns that
   output colouring into a colouring of the SUBJECT, giving
   `inh(A) ⊳ bid(B)`;
2. ⭐ `ad_refine_syn_inh_tyequiv`: **a refinement between two GHOST-FREE
   paintings IS a type equivalence.**  Refinement's whole job is filling
   ghosts; between paintings of plain types the only rows that can fire are
   the structural ones and the two flexible lookups — which is exactly the
   generating set of `≡ᵗ`.  Δ plays no part, because `a_tyequiv__all` binds
   nothing in Θ, so the ∀ row goes straight through.

That is `a_consis_chk_tyequiv`, and it is the "derive it from the transport,
do not rebuild it" the previous entry's hand-off asked for.

**Also banked**: `a_typing_tm_ge` (reverse tm-verbatim for `a_typing`; its
`AT-Abs` row additionally crosses the `guess^TY` block, which
`a_guess_mono_decls` says is flexible-only); `ad_sd_typing_isub_tm`
(stability under `⊴` + tm-verbatim — the ∀-peeling rows push a RIGID entry,
so they use `a_isub_cons_tvar`); `btyp_syn_painting_inv` (a colouring whose
painting is synthesised is the all-synthesised one — how `sd-Freeze`'s
`ptyp_to_btyp_syn B` shape is read off the IH's `◇ ⊳ bid(B)`);
`a_tyequiv_isub_le`.

**Also banked, second pass**: `ad_sd_typing_subst_tm` / `_rename_tm` (the
term-variable renaming the six term-binder rows need; its App row
substitutes into the embedded SKELETON-inference premise, which is what
`ad_pat_subst_tm` is for), and ⭐ `btyp_inh_painting_inv`:

**⭐ IN CHECK MODE THE COLOURING IS FORCED**, which REMOVES an item from the
hand-off's list.  The two ∀-peeling rows (`AT-AbsCheck`/`AT-AbsAnnoCheck`
`_step`) are cofinite in a RIGID α, so the naive route to their declarative
counterparts wants a TYPE-variable renaming for `ad_sd_typing` — which would
mean renaming lemmas for every judgement it embeds.  It is not needed: those
rows run at TC, where `mod_comp_ty B mode_tc` is `is_ityp B` and an inherited
type has only ONE colouring, so the IH's colouring at each α is already
`ptyp_to_btyp_inh` of its erasure — exactly the `open … (btyp_var_f α)` shape
the rule wants.  Only the TERM-binder rows need a renaming.

**LEFT** (HANDOFF §7.5): `ad_sd_typing_mod_comp_ty` — its `unit`/`var`/`anno`
rows want a TY analogue of `ad_pat_sub_mod_comp_sk` plus two shape bridges
(`is_sskl (btyp_to_bskl B) -> is_styp B`, `btyp_to_bskl B =
pskl_to_bskl_inh P -> is_ityp B`), and its `freeze` row wants `lc_ptyp A` off
the rule's `≡ᵗ` premise; then the eleven-row induction, whose one genuinely
new row is `AT-Abs` (it deposits the `guess^TY` block between the binder and
the context, so the ⊴-peel has to cross it).

## 2026-08-06 — ⭐⭐⭐ **SECTION D: `thm:sound-skeleton-inference` IS CLOSED** — `a_pat_sound` is axiom-free, and the paper's un-stated "preservation of refinement under type equivalence" is supplied

`make coq` clean.  `Print Assumptions a_pat_sound` = **Closed under the
global context**; the theorem is now `Check`ed and audited in `README.v`
beside `a_sub_sound`.

The last piece was `a_consis_chk_annot_refine` — AbsAnno at the ARROW split
shape, i.e. the step the paper writes as one clause, "by preservation of
refinement under type equivalence", and never states as a lemma.  It is a
TARGET TRANSPORT: `a_consis_chk_sound` hands back the consistency and the
refinement at one context, so only the refinement's TARGET has to be
re-coloured into a painting of the annotation.

**⛔ The dead end, recorded because it costs the most to discover.**  Do NOT
induct on `a_consis`: its ∀ rows bind the fresh witness in **Θ** while
refinement's `__all` binds it in **Δ**, which is exactly what
`ad_refine_syn_f`'s hygiene set exists to manage — that route re-does
consistency soundness.

**⭐⭐ The three things that made the declarative-layer route go through:**

1. **The two contexts must be DECOUPLED** (`Θc` for the consistency,
   `Θr ⨟ Δ` for the refinement, tied by a definitions-visible condition and a
   flexibles-visible one).  With one shared Θ the `__all` row cannot be closed
   in either direction: moving the CONSTRUCTED output back (Θ → Δ) is
   **unsound**, because `ad_refine_syn__hole`'s fill is Δ-free BY RULE while
   the transport's fills are `ptyp_to_pskl A` for the sub-annotations, which
   do mention the witness.  Decoupled, both ∀ rows land exactly where their
   own rule puts the binder and NO context move is needed anywhere.
2. **The `__hole` row needs an OCCURRENCE lemma**
   (`ad_pat_consis_subject_ftv`): a free variable of a type-painting SUBJECT
   either survives into the consistency's TARGET, or is a flexible, or escapes
   into a definition's body.  The rule wants its fill well-formed at EMPTY Δ —
   the annotation must be Δ-FREE — while the invariant only gives "in Δ or a
   tvar of Θr"; at `__hole` the target is a synthesised painting well-formed
   at empty Δ, so all three disjuncts land in `dom Θr`, and a Δ-bound ∀
   witness (fresh for Θr) is excluded.
3. **The two flexible rows are sound because A DEFINITION IS A MONOTYPE**,
   hence uniquely coloured (`btyp_to_bskl_mono_syn`) — that is what forces the
   recursive answer to be exactly the synthesised painting
   `ad_refine_syn__flex_l` / `__flex_r` demand.

**The kit** (`prop_soundness_pat.v` §4a–§4f): coercion identities incl.
`btyp_to_bskl_mono_syn`; `a_wf_pskl_delta_to_ctx` (Δ→Θ for skeleton wf, the
safe direction); ⭐ `ad_refine_syn_rename_delta` (renaming a Δ-member —
supplies `__all`'s cofinite family from its one fresh witness); ⭐
`ad_pat_consis_subject_ftv`; ⭐ `ad_refine_syn_rename_tvar` in MID-CONTEXT
form, with `a_wf_pskl_rename_tvar` and the `a_tvar_block` predicate (the
`__tophole_fill` row stacks binders on Θ, so the renamed slot is not at the
head) — supplies `__tophole_fill`'s family; then `transport_hole_answer`,
`ad_refine_syn_target_transport` and the lemma itself.

⚙ **Build the `≡ᵗ` reading from this transport, do not rebuild it**:
thm:sound-type-inference's `Freeze` case invokes exactly the same fact ("which
further gives `Θ2 ⊢ B ≡ A`").

⚙ **New traps** (HANDOFF §7.4): under `Set Implicit Arguments` a lemma's later
universals can go implicit while one of them stays explicit — inside a nested
induction, use `@`-application with `_` for the inferable prefix.  For an
inner `induction Href`, `revert` everything mentioning the refinement's
context/Δ first, `remember` the target, `revert` its equation, and give an
explicit `as [...]` pattern; state any auxiliary fact AFTER the `remember`, or
it picks up the abstracted target and becomes a premise of every inner IH.
A `- bullet is not finished` with nothing focused means an `auto` failed to
apply a ∀-quantified IH whose first premise is a context EQUATION.

## 2026-08-06 — ⭐ **SECTION D: the open lemma's kit starts landing, and its design is CORRECTED** — the ∀ rows force the two contexts apart

Three more lemmas Qed and axiom-free in `algo/prop_soundness_pat.v`
(§4a–§4c); `make coq` clean; `a_pat_sound` unchanged, still exactly one
axiom.  This entry is about `a_consis_chk_annot_refine`, the one axiom.

**⭐ THE CORRECTION.**  The previous pass's plan had the target transport
share ONE context between the consistency and the refinement.  That does not
work at the `__all` row: the consistency premise lives at `(α~tvar),Θ` and
the refinement premise at `Θ ⨟ α,Δ`, and moving the CONSTRUCTED output back
(Θ → Δ) is **unsound** — `ad_refine_syn__hole`'s fill is Δ-free BY RULE, so a
fill mentioning α cannot survive the move, and in the transport the fills are
exactly `ptyp_to_pskl A` for the sub-annotations, which do mention α.  The
repair is to DECOUPLE the two contexts (`Θc` for the consistency, `Θr ⨟ Δ`
for the refinement) and relate them by two conditions — definitions of `Θc`
visible in `Θr`, and every `Θc`-tvar either in `Δ` or a tvar of `Θr`.  Then
BOTH ∀ rows land exactly where their own rule puts the binder and **no
context move is needed anywhere**: `__all` keeps α in Δ, `__tophole_fill`
puts it in Θr.  Full statement + per-row map in
`docs/HANDOFF-section-d.md` §7.3 and the file's §4 header.

**⭐ The second correction: the `__hole` row needs an OCCURRENCE LEMMA.**
`ad_refine_syn__hole` demands `Θr ⨟ ∅ ⊢ₚₛᵃ (ptyp_to_pskl A)` — A must be
Δ-FREE — while under a ∀ the invariant only gives "in Δ or tvar-ish in Θr".
The upgrade is: a free variable of a type-painting SUBJECT either survives
into the consistency's TARGET or escapes through a DEFINITION.  At `__hole`
the target is `pskl_to_bskl_syn P` with `Θr ⨟ ∅ ⊢ₚₛᵃ P`, so all disjuncts
land in `dom Θr`, and a Δ-bound ∀ witness (fresh for Θr) is excluded.

**Banked this pass:**

- §4a coercion identities, incl. ⭐ `btyp_to_bskl_mono_syn`: **a monotype has
  only one colouring**.  That is what lets the two flexible rows rebuild —
  a definition `α̂ ≔ τ` is a monotype, so whatever colouring the recursive
  call produces for it IS the synthesised painting `__flex_l` / `__flex_r`
  demand.
- §4b `a_wf_pskl_delta_to_ctx` — the Δ→Θ move for skeleton well-formedness
  (the safe direction; the refinement analogue is NOT sound, see above).
- §4c ⭐ `ad_refine_syn_rename_delta` — renaming a Δ-member of a refinement.
  This is what turns the `__all` row's ONE fresh witness into the cofinite
  family the rule demands.  Its `__hole` and flexible rows are the
  interesting ones: `α ∉ dom Θ` makes the fill and the definitions invisible
  to the substitution, so the payloads are untouched.

**LEFT** (HANDOFF §7.3): the occurrence lemma; a Θ-renaming for
`ad_refine_syn` in mid-context form (the `__tophole_fill` row's family, with
§4c as the template) plus its `a_wf_pskl` renaming; then the transport
itself, after which the axiom is three lines.

## 2026-08-06 — ⭐⭐⭐ **SECTION D: `thm:sound-skeleton-inference` IS ASSEMBLED** — all ten `a_pat` rows proved, one isolated open lemma left

`a_pat_sound` (`algo/prop_soundness_pat.v` §5) is **Qed**; `make coq` clean.
`Print Assumptions a_pat_sound` lists exactly ONE axiom — the isolated
`a_consis_chk_annot_refine` — and every new support lemma is *Closed under the
global context*.

**What landed (the four hand-off items, in order):**

1. `a_pat_tm_ge` — the reverse tm-verbatim invariant for `a_pat` itself
   (`aenv_tm_le_via_binder_ge` is the mirror of prop_stability's
   `aenv_tm_le_via_binder`; it needs NO `a_suffix` premise, because the
   pending suffix is crossed on the SOURCE side where a lookup is only
   weakened).  With `a_pat_tm_le` this says a run's term entries are the SAME
   at input and output — which is what sustains the disciplined-wf hypothesis
   through App's and AbsAnno's sequential premises.
2. `a_wf_aenv_strip_tm_mid` (+ the new `a_scope_pskl_mono` in
   `prop_ctx_mono.v`) — dropping a term entry from the MIDDLE of a well-formed
   context.  ⭐ The content: no payload can mention a term KEY type-wise —
   every payload is checked by `a_wf_ptyp` / `a_scope_pskl`, both term-blind,
   so both transport along `aenv_tbinds_le_strip_tm`; freshness only shrinks.
3. The **⊴-peel** at the Abs rows (`a_isub_peel_var_skl_mid` /
   `a_isub_peel_var_typ_mid`): from `(x:P),Θ1 ⊴ Ξ,(x:P),Θ2` conclude
   `Θ1 ⊴ Ξ,Θ2`.  ⭐ Two findings.  (i) The conclusion must be stated AT
   `Ξ ++ Θ2`, not at `Θ2`: the definition-preservation component of `⊴` maps
   into the whole target, and a definition of `Θ1` could a priori be found in
   the pending suffix — at `Ξ,Θ2` that is not a problem (the peeled entry is
   dropped by PAYLOAD SHAPE, no freshness needed), at `Θ2` it would need a
   freshness fact the statement does not carry.  (ii) The κ-component peels
   by `a_inc_var_skl_inv` + a `uniq`-mid list-surgery lemma (`uniq_mid_eq`)
   and re-grows the suffix by the new `a_inc_weaken_suffix_target`
   (= `a_inc_refl_gen` ∘ `a_inc_trans`) — there was no target-weakening lemma
   for `a_inc`.
4. The **ten-row induction**.  Var(typ) needed the new
   `a_wf_aenv_binds_var_typ_wf` (the `a_wf_aenv_binds_def_wf` mirror) +
   `a_wf_ptyp_to_wf_pskl`; App reads its second premise's input wf off
   `ad_refine_syn_hole_l_target_wf` and its syn-painting shape off
   `ad_refine_syn_syn_l` at `P := □`; the four binder rows go
   suffix-moving (`ad_pat_suffix_moving`) then exists-fresh→cofinite
   (`ad_pat_rename_tm`).

**⭐ `ad_pat_mod_comp_sk` is provable standalone** — the `mod_comp_sk` premise
of `ad_pat__abs` / `__abs_anno` does NOT force strengthening the theorem's
conclusion.  The two Abs rows carry it, the base rows read it off their
subtyping premise (`ad_pat_sub_mod_comp_sk`), Freeze and App invert theirs,
and the two Check rows get their codomain's `is_sskl` from the IH and their
domain's from the rule's own `a_wf_ptyp` — no local-closure side condition
is needed anywhere.

**⛔ THE ONE OPEN LEMMA**, isolated and honestly marked:

    a_consis_chk_annot_refine : a_consis_chk Θ0 A P Θ1 -> … ->
      exists B, btyp_to_ptyp B = A /\
        Θ1 ⨟ ∅ ⊢ᵣᵃᵈ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B)

It is AbsAnno at the ARROW split shape only (the HOLE shape answers with the
all-synthesised painting `ptyp_to_btyp_syn A` and is proved).  The paper
asserts it inline — "by preservation of refinement under type equivalence" —
and it exists nowhere as a lemma.  ⭐ **The route is now concrete** (full plan
in the file's §4 header): it is a TARGET TRANSPORT provable on the
DECLARATIVE layer alone, by a NESTED induction (outer on `ad_pat_consis`,
inner on `ad_refine_syn`), and every row has an answer.  Going back through
`a_consis` instead is a dead end — its ∀ rows bind the fresh α in Θ while
refinement's bind it in Δ, which is exactly what `ad_refine_syn_f`'s hygiene
set exists to manage, so that route re-does consistency soundness.  Two small
new lemmas are needed: `ad_refine_syn_delta_to_ctx` (the Δ→Θ direction only —
a weakening, and the reverse is neither true nor needed) and the
monotype-colouring collapse `mono_ptyp (btyp_to_ptyp B) → btyp_to_bskl B =
ptyp_to_bskl_syn (btyp_to_ptyp B)`, which is what makes the `flex_l`/`flex_r`
rows rebuild.  ⚙ The same fact, read as consis-to-`≡ᵗ`, is what
thm:sound-type-inference's Freeze case needs — build ONE of the two and
derive the other.

⚙ **Session traps.** A bare `subst` will happily consume the erasure equation
`bskl_to_pskl Qt = Q` (its RHS is a bare variable), CLEARING it — use
`subst m` / `subst P0 P Q0` in the split-shape case splits.  `eapply` on
`a_wf_aenv_strip_tm_mid` leaves the peeled binding an evar, so `intros []`
on `~ abind_is_ty ?b` fails: put the `a_wf_aenv` goal first
(`eapply …; [ | exact H ]; intros []`).  `simpl_env in H |- *` is not accepted
— write the two calls.  And `simpl in Heq` unfolds metalib's `one`, which
then breaks any `match goal` pattern written with `~`; prove the shape facts
by `inversion Heq; subst; first [reflexivity | assumption]` instead.

## 2026-08-06 — ⭐⭐ **SECTION D: the whole support kit for thm:sound-skeleton-inference is Qed** — tm-verbatim stability, term-var renaming, and the split-shape analysis that retires split-refine + transitivity for theorem 1

`make coq` clean, no admits, all new lemmas Closed under the global context.
Three files: `algo_decl/ + deco_algo/prop_ctx_mono.v` (reworked),
`algo/prop_stability.v` (extended), `algo/prop_soundness_pat.v` (NEW — §1–§3
kit; the theorem assembly is next, per-case routes in
`docs/HANDOFF-section-d.md` §7).

1. ⭐ **`a_split_sk_shape`**: under `skmod{SK}` the split is the ARROW or HOLE
   row only (no `skmod{SK}` rule for a flexible input), so
   thm:sound-skeleton-inference needs NEITHER lemma:split-refine NOR
   refinement transitivity — the composed refinement is one `__arrow` of a
   reflexivity + IH, or one `__hole` over the IH's syn-painting inversion.
   Both hard prerequisites the hand-off feared are TYPE-inference-only.
2. ⭐ **The paper's "stability" (proofs.tex:19-26) is a real gap, and the
   repair is the TM-VERBATIM invariant**: `⊴` preserves a term entry only up
   to `≡ᵗ` (`a_inc__var`'s semantic-entries relaxation), so the typing
   judgements do NOT transport along `⊴` alone.  The algorithm never rewrites
   a term entry — now proved in BOTH directions across the whole cluster
   (assign/unify/consis, sub/sub_flex, split, pat, typing): forward `*_tm_le`
   (prop_stability.v), reverse `*_tm_ge` (prop_soundness_pat.v §3a; suffixes
   are `a_decls`, so output term entries all come from the input).
   `ad_pat_isub_tm` = stability under `⊴` + tm-verbatim, no ≡-slack needed.
3. **The ctx-monotonicity kit is now TERM-BLIND where it can be**
   (`aenv_tbinds_le`, prop_ctx_mono.v §1b): every judgement except
   `ad_pat`/`ad_sd_typing` reads only type-level entries, so their `_mono`
   lemmas take the weaker relation — and the paper's "refinement judgements
   are stable under dropping term variables" is the `strip_tm` instance,
   for free (§6 corollaries).
4. **Term-variable renaming for `ad_pat`** (`ad_pat_subst_tm` /
   `ad_pat_rename_tm`): the exists-fresh → cofinite bridge the Abs cases
   need — context-surgery form (the renamed KEY moves, payloads cannot
   mention term keys), all type-level premises by the term-blind kit.
5. `a_wf_exp` (the problem definition's "M well-formed in Θ0" — annotations
   only), `pskl_to_uskl_via_bskl_syn`, `a_sk_mode_compat` inversions,
   `ad_pat_sub_mod_comp_sk` (SK-sorted subtyping targets satisfy
   `skmod{SK}`).
6. ⚠️ FOUND: `a_wf_aenv__var` stores only `a_scope_pskl` where the paper's
   `Θ ⊢ ctx` requires `Θ ⊢ P` — the `AP-Var(skl)` soundness case needs the
   disciplined wf, so the theorem carries it as a hypothesis
   (WF-SIDE-CONDITIONS pattern; hand-off §7 has the exact statement).
   ⛔ ONE open lemma identified for AbsAnno: refinement-target transport
   along type-level consistency (the paper's inline "preservation of
   refinement under type equivalence", proofs.tex:1578) — also needed by
   theorem 2's Freeze case; build once for both.

## 2026-08-06 — ⚙⚙ **HOUSEKEEPING: the pre-restart `.legacy` corpus deleted, `def_tags`+`predicates` folded into `def_extra`, `algo_decl/` + `deco_algo/` promoted, and two more renames retired into the SWAP kit**

`make coq` clean; README.v still audits **28 × Closed under the global
context**.  No statement of any paper-facing theorem changed — this is a
deletion/refactor pass only.  Net: **−12 164 / +597 lines** across 93 files
(of which ≈10 600 deleted lines are the `.legacy` corpus and ≈1 000 are Coq
proof text that the equivariance kit made redundant).

### 1. The `*.v.legacy` corpus is gone (11 files, ≈10 600 lines)

They were pinned to the PRE-RESTART declarative definitions and no longer
type-check against the current ones — they reference constructors that do not
exist any more (`is_base_term__*`, `d_tags_skl__hole`, `d_tags_skl__tophole`,
`is_tskl__all_syn`, `pskl_subsumes__*`).  Nine `frost/algo/*.legacy` files
were `Admitted` scaffolding (`def_question`, `prop_lemmas`,
`prop_soundness`, `prop_completeness`, `prop_decorated`, …) fully subsumed by
the current algo development.  The two that carry real unported content are
`decl/prop_safety.v.legacy` (177 Qed / 14 Admitted — `d_pat_total_gen`,
`d_pat_safety`, the `hole_safe` / `skel_safe` engine) and
`decl/prop_skeleton.v.legacy` (139 Qed).  ⚙ **Both are recoverable from git at
`a81ef2d`** — mine them there when the paper-faithful skeleton-safety redo
starts.  Deleting `d_sub_rename_var` (below) also retired
`prop_renaming.v`'s "NON-tvar binder relabel" section, whose stated purpose
was to discharge the `sub` case of `d_typing_rename_var` — a lemma that only
ever existed in `prop_safety.v.legacy`.

### 2. `def_tags.v` + `predicates.v` folded into `frost/def_shapes.v`

The three-way split bought nothing: every consumer imported all three, and the
two smaller files held 6 predicates that were **exact duplicates** of ones
already in `def_extra.v`.  Dropped as dead duplicates: `mono_btyp`,
`mono_utyp`, `is_inh` (= `is_ityp`), `is_ttyp_utyp` (= `is_ttyp`),
`is_syn_bskl` (= `is_sskl`), `no_forall_bskl`.  ⭐ `is_syn` was the SAME
inductive as `is_styp` under a different constructor prefix and was the only
duplicate with live uses — unified onto `is_styp` at 22 sites, and the
identity-in-disguise `is_styp_is_syn` deleted with its 6 call sites.
`ftag_in_uskl` moved over verbatim.  `frost/README.v` (a 0-byte file) deleted.

### 3. `algo_decl/` + `deco_algo/` promoted out of `algo/` to `frost/algo_decl/ + deco_algo/`

It is not part of the algorithm: it is the ε-tagged BRIDGE that soundness and
completeness both route through.  Module path `src.frost.algo.decorated_algo.*`
→ `src.frost.decorated_algo.*`, 44 files touched.  The CLAUDE.md directory map
was rewritten to match reality (it still listed the pre-2026-08-06 file names).

### 4. ⭐ Two more substitution-shaped renames retired into the equivariance kit

DESIGN.md §4.3's campaign converted the ∀ rows to exists-fresh
**rename-lemma-first**; the swap kit (`algo/prop_swap.v`) later showed those
renames are corollaries of equivariance.  Two of the four clusters are now
actually converted, with **every consumer untouched** — the rename lemmas keep
their statements verbatim and only their proofs change:

| cluster | was | is |
|---|---|---|
| guess | `a_guess_mono_rename_tvar{,_size}`, 150 lines of size induction | `a_guess_mono_swap` + `swap_ptyp_as_subst`, 12 lines inside `a_guess_mono_open_at` |
| look | `a_looksub_lookeq_rename_tvar_size`, **528 lines** | `a_looksub_lookeq_swap` + the three bridges, 2 × 12 lines |

The enabling additions are three "a swap IS the rename when the TARGET is
fresh" bridges: `swap_ptyp_as_subst` and `swap_aenv_as_rename` (prop_swap.v —
the context one covers the KEY and the PAYLOAD, since `ftvar_in_aenv` counts
both) and `swap_cstrs_as_subst` (prop_looksub.v, where `subst_cstrs` lives).
⭐ **Why the size induction disappears entirely**: a substitution can COLLAPSE
two names, so every binder row had to split three ways (source = binder /
target = binder / neither) and the "target = binder" branch re-freshened,
producing a non-subderivation — hence the measure.  A transposition is a
BIJECTION, so there is no collapse, no split, and no measure.

Deleted as dead in the same pass: `a_looksub_rename_tvar_keep`,
`a_lookeq_rename_tvar_keep`, `a_lookeq_rename_var`, `a_solve_sub_rename_var`,
`a_solve_eq_rename_var` (already swap-derived wrappers nobody called),
`guarded_pskl_rename`, `d_sub_rename_var` + `d_consis_rename_var` +
`d_wf_utyp_rename_var`, and the helpers that only the deleted size induction
used (`ftv_subst_var_keep`, `subst_var_pskl_neq_var`, `rename_aenv_same`,
`subst_cstrs_app`).  Also `frost/ltac_utils.v`'s unused `inst_cofinites` /
`discharge_category`, `prop_general_subsumption.v`'s `nbauto`, and four unused
`auc_*` projections in `prop_consis_rename.v`.

### 4b. ⚙ Both flagship STATEMENTS lose `ad_refine_syn_f`

`a_sub_sound` and `a_sub_complete` both mentioned `ad_refine_syn_f`
at `F = ∅`.  `F` is consistency soundness' ghost-fill hygiene set
(prop_soundness_consis.v §"Fill-hygienic refinement"), a proof device: the ∀
cases must move an opened binder from Θ into the refinement's Δ, and a naive
strip is unsound because a ghost FILL could mention it, so the variant forbids
`F` in ghost fills.  At `F = ∅` the `__hole` side condition is vacuous and the
two judgments are **inter-derivable** — `ad_refine_syn_f_forget` and
`ad_refine_syn_f_of_plain` were both already Qed — so this was scaffolding
leaking into two paper-facing statements.  Both now read the plain
`Θ ⨟ ∅ ⊢ᵣᵃᵈ … ⊳ …`.  ⭐ For COMPLETENESS this is not cosmetic: `_f` sat in a
HYPOTHESIS, and being the stronger of the two it was gratuitously weakening
the theorem.  The internal machinery still runs on `_f`; only the statements
changed.  The one non-README consumer, `a_sub_concrete_output_equiv`, drops
its `ad_refine_syn_f_forget` wrapper.

⛔ **What this does NOT touch — `ad_pat_sub_gv`.**  That one is an argued
repair, not scaffolding.  `_gv → _g` (`ad_pat_sub_gv_forget`) exists; the
CONVERSE is the paper gap itself — the leaves' subject refinement is the third
solution condition of the AUGMENTED thm:complete-consistency, not derivable
from the paper's two (the capture configuration `(P0 = ◇, P = ∀X.◇, Q = ∀X.X)`
passes both) and not statable at the root (refinement is lockstep;
`cex_p7_univ_ghost_r_vacuous.v` + `cex_p7_third_premise_forall.v`).  Below it
sit `_g → _n → ad_pat_sub`: `ad_pat_sub_g_of`, `ad_pat_sub_of_n` and
`ad_pat_sub_to_n` are Qed, and the missing `_n → _g` TAG-FRESHENING bridge is
DEFERRED by DESIGN §5.4 (≈300 lines; only the paper-facing corollary consumes
it), after which DESIGN:166 requires transporting it to `_gv`.

⚠️ **The two flagships therefore still do not COMPOSE**: soundness *concludes*
plain `ad_pat_sub`, completeness *assumes* `ad_pat_sub_gv`.  Soundness produces
strictly less than completeness consumes.

⭐ **BUT THE MISSING CONTENT IS ALREADY PROVED — the fix is threading, not new
mathematics.**  `_gv`'s leaf premise is `Θ ⨟ ∅ ⊢ᵣₚᵃᵈ ⌊R⌋ˢ ⊳ ⌊Q⌋` (the subject's
erasure refines to the leaf counterpart).  That is *literally* the last
conjunct both consistency-soundness results already export:

| | last conjunct |
|---|---|
| `a_consis_sound` (:5598) | `Θ1 ⨟ ∅ ⊢ᵣₚᵃᵈ P ⊳ P'` |
| `a_consistag_sound_aux` (:4650) | `ad_refine_pskl_f Δ2 Θ1 Δ2 ⌊R⌋ˢ P'` |

So the route to composition is to strengthen `a_subtag_sound_bundle` /
`a_sub_sound` to CONCLUDE `ad_pat_sub_gv` — i.e. stop DROPPING a conjunct
the leaves already hand back — rather than to derive `_gv` from an arbitrary
declarative join, which is refuted.  ⚙ The one real cost is that `_gv` is
FUEL-indexed, so soundness would have to produce an `exists n`
(`ad_pat_sub_to_n` is the precedent).

### 5. ⛔ What was NOT retired, and why

`a_assign_unify_consis_rename_tvar` (prop_consis_rename.v §8, **591 lines**)
stays.  Its three consumers are `a_consis_decorate_size`'s ∀ rows (§10), which
rebuild a cofinite `a_consistag` family from the run's one binder and need the
output context's suffix `Θt` back **UNCHANGED**.  The swap instead returns
`swap_aenv α β Θt`, so equating the two needs `α ∉ ftvar_in_aenv Θt` — a scope
fact §8 currently sidesteps with its `tvar_prefix` / F-protection argument
(§5) and which no existing lemma supplies (`a_wf_aenv` would give it, but §8
runs on `uniq` alone).  Retiring it is a redesign of §10's three rows, not a
cleanup.  `a_looksub_rename_var` (the LOOKED-FOR variable, §6) also stays and
is NOT swap-derivable: its statement keeps `Θ` fixed while `α` is a flexible
IN `Θ`, so the transposition is not the identity there.  The DECLARATIVE and
DECORATED layers keep their renames outright — there is no swap kit over
`d_*` / `ad_*`, and their targets are cofinite relations with no outputs to
leak into.

## 2026-08-06 — ⭐⭐ **THE ALGORITHMIC RULES NOW CARRY THEIR SORT DISCIPLINE** (typ vs skl), and the tree builds 37% faster

`make coq` clean; README.v still audits **28 × Closed under the global
context**, so both directions of subtyping stay closed and unconditional.

### 1. The problem

The algorithmic judgements all range over ONE category (`pskl`), but the
paper's rules are sorted *by metavariable*: `A`/`B` mark positions the
grammar only ever fills with a TYPE, `P`/`Q` admit a full skeleton.
`SI-Check` is the clearest case — `\guarded{A,B}` — and nothing in the rule
forces ghost-freeness; the letter carries it.  A Coq `Inductive` has no such
notion, so the mech was silently more liberal than the paper everywhere.

### 2. What landed

`pskl_ghost_free` (the "is a type" predicate) moved from
`algo/prop_pat_sub.v` up to [`frost/def_shapes.v`](frost/def_shapes.v) so the
RULES can use it, with the syntactic closure kit (open / close / subst / swap
/ `ptyp_to_pskl` round-trip, `ghost_free_auto`) in
[`frost/prop_basic.v`](frost/prop_basic.v).  Premises added:

| rule | premise |
|---|---|
| `a_sub__check` | subject **and** target |
| `a_sub__forall_r` | target `∀α.B` |
| `a_looksub__check`, `a_looksub__forall_r` | target |
| `a_solve_sub__check`, `a_solve_sub__forall_r`, `a_solve_sub__ghost_l` | target |
| `a_subtag__check`, `a_subtag__forall_r`, `a_solvetag_sub__check`, `a_solvetag_sub__forall_r` | target |

Consistency, `assignvar`, `unifyvar`, `a_typing` and `a_pat` needed nothing —
the paper writes `P`/`Q`/`τ` throughout, and `a_typing` already outputs a
`ptyp`.

The TARGET premises cost nothing: they are read off `skmod{TY}`
(`a_ty_mode_compat_tc_ghost_free`), which every completeness lemma already
carries.  `SI-Check`'s SUBJECT premise needed a new transport chain in P7 —
the motive's TY-sort `uskl_ghost_free R'` moves across `≡ᵘ`
(`a_uskl_tyequiv_ghost_free`), reflects back through the metasubstitution
(`msubst_pskl_ghost_free_inv`) and then through the erasure
(`uskl_ghost_free_to_pskl`).

### 3. Three findings, all in [`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md)

- **The two figures disagree on `SI-ForallR`'s subject** — plain rule `A`,
  decorated mirror the skeleton `S`.  Only the target is mechanized.
- **`SolS-ForallR`'s LHS `A` is a slip**: its own premise is dischargeable by
  `SolS-GhostL`, whose LHS is `◇`.  Sorting it would leave `◇ ≼TC ∀β.B` with
  no rule, and that is reachable (`∀α.α` against a ∀-target).
- **`LS-Check`/`LS-ForallR`'s subject is TRUE but not free.**  Those rows are
  TY-reachable only, so the subject IS a type — but the collection's
  structural lemmas are mode-agnostic and two of them substitute an ARBITRARY
  skeleton into the subject (`a_looksub_lookeq_subst_stable`,
  `a_looksub_lookeq_subst_gen_size`); the latter's consumer feeds it the
  node's guess, which at the SK sort carries ghosts.  ⛔ Not mechanized;
  it would mean threading `skmod` through the whole structural kit.

### 4. ⚙ Build time: 970 s → 608 s serial, and one file 20×

Profiled with `Set Ltac Profiling` against the `.aux` per-proof timings
(which already record every proof's cost — no rebuild needed to find hot
spots).  Two `fsetdec` misuses, both the hazard CLAUDE.md already names:

| site | cost | fix |
|---|---|---|
| `prop_flex.v`, 3× `assert (ftvar_in_aenv ((x~tvar) ++ Θ) [=] add x …) by (simpl; fsetdec)` | 160 s | hoisted `ftvar_in_aenv_cons_tvar` up from `prop_looksub.v` and applied it |
| `prop_flex.v`, `clear - Hfr Hb0Ξ Hup Fr Hc2. fsetdec` (5 hyps, one a 7-way `pick fresh` union) | 46 s | derive the three ATOMIC facts from one small hypothesis each first |

`prop_flex.v` 133 s → 4.4 s.  **It is an EARLY dependency, so this is on the
critical path of every rebuild.**  ⭐ And the sort premises paid for
themselves: `prop_soundness_sub.v` fell 96 s → 14.2 s, its
`dec_ext_solve_eq_step_size` (76 s) dropping below 3 s — the premises PRUNE
impossible rows out of that induction.

⚙ **Lesson for the next perf pass**: the `.aux` files hold `proof_build_time`
per proof.  Aggregate them BEFORE rebuilding anything; then label individual
`fsetdec` calls with `time "F1" fsetdec` to find the single call that
dominates.  Guessing from `grep` for unscoped `fsetdec` would have missed
both of these — one was already `clear -`-scoped, just not narrowly enough.

### 5. Also fixed (pre-existing)

`cex/probe_payload_reachability.v` had a dangling `Require` on
`algo/prop_sub_shield_supply.v`, deleted by the shield deprecation
(`2a1c380`); its stale `.vo` had been masking the break.  The one-line
`pskl_all_free` it needed is now inlined there.

## 2026-08-05 — ⭕⭕ **THE SHIELD LAYER IS FULLY DEPRECATED**

`make coq` clean.  With subtyping completeness unconditional, the entire
mech-invented shield apparatus and the counterexample record built around it
are deleted.  **Nothing outside `cex/` ever depended on any of it**, and the
cluster was self-contained (`def_flex_shield` ← its five users).

DELETED (Coq text at `11349c5`):

| file | lines | what it was |
|---|---|---|
| `cex/def_flex_shield.v` | 526 | `flex_shield`, its transport kit, `flex_shield_excludes_cex` |
| `cex/cex_p7_shield_realizable.v` | 560 | the over-strength argument for the non-positional `sub_shield` |
| `cex/cex_p7_shield_double_occ.v` | 449 | the double-occurrence configuration; its refutation was already retracted **and reversed** |
| `cex/cex_p7_shield_forall_flex.v` | 170 | the ∀-over-flexible stuck shape; its `sub_shield` conclusion already retracted |
| `cex/regr_p7_shield_arrow.v` | 113 | regression that `flex_apart`'s two base rows cover the arrow shapes |
| `cex/probe_double_occ_run.v` | 97 | the `main_forall` refutation — retracted 2026-08-05 |
| `cex/cex_p6sv_forall_flex.v` | 45 | the P6-Sv counterexample that started the saga — retracted by the repair |

≈ 1960 lines.  Every one of these was either RETRACTED by the authors'
repaired `SolE-FlexR` or a statement about a premise that no longer exists.

⭐ KEPT, and de-shielded: `cex/cex_p7_sub_monoish.v`.  Its headline
`p7_sub_monoish_counterpart_is_false` is a general fact about the SUBTYPING
JOIN, not about the shield — the subtyping-side analogue of
`ad_pat_consis_monoish_counterpart` is FALSE, because consistency's ∀ rules
require the counterpart to be a quantifier too while subtyping's ForallL
INSTANTIATES, so a tagged-∀ subject can face a mono-ish counterpart directly.
That asymmetry outlived the layer it was written for; the header now states it
on its own terms.

⚠️ Docs (`DESIGN-completeness-subtyping.md`, the hand-offs) still narrate the
shield saga and cite the deleted files.  That is deliberate — they are the
history, and the commit is named in each deletion.  This log entry is the
index into it.


## 2026-08-05 — ⭐⭐⭐ **SUBTYPING COMPLETENESS IS UNCONDITIONAL.  `a_sub_complete` GOES INTO README.v**

`make coq` clean, every `.v` fresh, README's audit is 28 ×
`Closed under the global context` with no axioms.

**`a_sub_complete_bundle_holds` and `a_sub_complete` no longer take
`forall n, main_forall n`.**  That hypothesis was the assembly's last one
(§10 RESIDUAL A), and its single unsupplied premise was the mech-invented
`sub_shield` for a `P0` carrying a ∀ below its head — the residual that
survived the whole `prop_sub_shield_supply.v` campaign.

**Why it fell, and it is not because a supply route was found.**  The chain is
entirely a consequence of the authors' repaired `SolE-FlexR`:

1. P6-Cv stopped consuming `flex_apart` (`FLEXMONO` + the position-wise
   payload scope).
2. So P6-Sv stopped needing `flex_apart_walk` — every use was a relay.
3. So `sub_shield` lost its guess-descending conjunct, leaving the
   Δρ-CONSTANT half.
4. And that half, at the **Δρ = ∅** which P6-L and P7b's two ForallL rows
   instantiate it at, is **unconditionally true** (`sub_shield_empty`): the
   walk's growth condition `Δρ' ∩ ftv ψa ⊆ Δρ` reads as cleanliness, so every
   reachable state is `fa_clean`.

⚠️ Step 4 was FALSE before step 3: `fa_walk`'s `fastep_all_r` GROWS Δρ, so
from Δρ = ∅ the guess-descending half reached a state where the opened binder
sits in Δρ and `fa_clean` is blocked.  That is exactly the double-occurrence
refutation — now reversed (`p7_sub_shield_double_occ_holds`).

Consequently: P6-L drops the premise and discharges it internally; P7b's
`a_sub_complete_forall_l_tagged` / `_untagged` drop TASK 0's gate; §9's two
ForallL branches of `sub_complete_assemble` apply those row lemmas DIRECTLY, on exactly
the join rule's own premises; `sub_complete_assemble`, `sub_complete_arrow_holds` and the bundle
drop the hypothesis.  `main_forall` is retired (kept as documentation, no
consumers).

⚠️ **The earlier refutation of `main_forall` is RETRACTED**, not worked
around: `probe_main_forall_false` ran through the double-occurrence
configuration, where the OLD `SolE-FlexR` discarded the accumulated pattern so
no `a_sub` run existed.  The repaired row returns `guess^TY(P)` and the run
exists (`cex/probe_flexr_repair.v`).

**What the flagship still carries beyond the paper**: the EXTERNAL wf side
conditions of `docs/WF-SIDE-CONDITIONS.md` — well-formedness of the
counterpart, and the subject's ghost-freeness at the TY sort.  §10 is
rewritten to record all of this, including the retraction.


## 2026-08-05 — ⭐⭐⭐ **`flex_apart` RETIRED FROM P6-Cv AND P6-Sv; `sub_shield` COLLAPSES TO A DERIVABLE PREMISE**

`make coq` clean, every `.v` fresh, P6-Cv / P6-Sv / P6-Ss / P6-L /
`a_sub_sound` / the new `flex_apart_deep_sub_shield` all
`Closed under the global context`.

| lemma | premise before | after |
|---|---|---|
| P6-Cv | `flex_apart` | **gone** |
| P6-Sv | `flex_apart_walk` (closure over `fa_walk`) | **gone** |
| P6-Cs | `flex_apart_deep` | unchanged — one genuine consumer |
| P6-Ss / P6-L | `sub_shield` = `flex_apart_deep` ∧ guarded `flex_apart_walk` | `flex_apart_deep` alone, and **derivable** |

`fa_step` / `fa_walk` / `flex_apart_walk` and their kit are DELETED
(retraction banner in `prop_look_complete.v`), as are the five walk lemmas in
`prop_sub_shield_supply.v`, `the_step` in `regr_p7_shield_arrow.v` and the
`INVw` walk block in `cex_p7_shield_realizable.v`.

**What did it, in two steps.**  (1) P6-Cv stopped consuming `flex_apart`: the
SE-FlexR row goes through `FLEXMONO` (`uskl_rho_mono_target` +
`a_guess_ty_witness_mono_gen`, whose payloads are Θw-scoped POSITION-WISE via
`ppre_hole_payload_wf`), and SE-GhostL gets its cleanliness from
`ad_ppre__hole`'s own side condition.  (2) Everything above was a relay into
that premise.

⭐⭐ **THE ASYMMETRY THAT DECIDED IT.**  An earlier note said the move "cannot
come out" because P6-Ss's Sub-Arrow row has nothing to descend on.  True — but
only of the GUARDED conjunct: `fa_step` has no guess-fixed arrow descent (two
such rows existed and made the walk UNSATISFIABLE composed with `fastep_all_r`,
`cex/cex_p7_shield_realizable.v`).  `flex_apart_deep` closes over `p0_step`,
which DOES have `p0step_arrow_l/_r`.  So the surviving half descends freely and
`flex_apart_deep_sub_shield` derives the whole closure from the root, via
`ss_walk_p0_walk` and `flex_apart_delta_grow`.  **Lesson: when a premise is a
closure, ask which walk it closes over before concluding it cannot be
derived — two conjuncts of one definition had opposite answers.**

⭐⭐⭐ **TWO OF OUR OWN COUNTEREXAMPLES DIED WITH THE CONJUNCT**:
`sub_shield_forall_flex_p0_fails` RETRACTED (its two stuck-shape lemmas
stand), and `p7_sub_shield_double_fails` RETRACTED **AND REVERSED** —
`p7_sub_shield_double_occ_holds` proves the shield HOLDS at the
double-occurrence configuration (Δρ = ∅ there), and the headline is now
`p7_double_occ_row_premises_all_hold`.  **The double-occurrence obstacle to
`main_forall`'s supply is retired.**

⛔ **WHAT SURVIVES.**  P6-Cs keeps `flex_apart_deep` for ONE site — the
COLLECTION-side `LE-FlexR` row (`prop_look_complete_cstr.v` ≈ 2185).  Not for
the mono-ness (that transfers), but for the κ-IMAGE Δρ-CLEANLINESS: LE-FlexR
invents a fresh flexible whose image is the whole guess, and P6-Cs's
conclusion carries `Forall (ftv (snd p) ∩ Δρ = ∅) κc`, which a partly-dirty
guess violates; that conjunct is load-bearing for the arrow row's shielded-ftv
premise.  The authors' repair touched `SolE-FlexR`, not `LE-FlexR` — and
nothing indicates `LE-FlexR` is wrong, only that this obligation is open.


## 2026-08-05 — ⭐⭐ **P6-Cv NO LONGER CONSUMES `flex_apart`**: the position-wise payload-scope route

Step 3 of `docs/HANDOFF-solve-flexr-repair.md`, and the prescribed move in it
was **wrong**.  Replacing P6-Ss's `sub_shield` by `flex_apart_walk` +
`flex_apart_deep` cannot come out: `sub_shield`'s `sss_arrow_r` moves `P0` and
the subject with the GUESS FIXED, and the matching `fastep_p0_arrow_r` was
deliberately deleted (it made the walk unsatisfiable at a reachable P7b node,
`cex/cex_p7_shield_realizable.v`).  Carrying both facts across an arrow is
exactly the work the closure does.

The real target is the ROOT — `flex_apart`, P6-Cv's premise — and it is now
**unconsumed**.  `make coq` clean.

- `uskl_rho_mono_target` (new): ρ is CONGRUENT at every constructor and
  non-trivial only at a bare VARIABLE (`urho__leaf`), and a bare variable is
  itself a monotype.  A mono-paint ρ-IMAGE therefore forces a mono-paint
  GUESS — the whole content of `FLEX`'s cleanliness step, at no premise cost.
- `ppre_hole_payload_wf` (new): the payload scope, POSITION-WISE.  `guess^TY`
  invents a flexible exactly at `Pi`'s HOLES, and `ad_ppre__hole`'s own side
  condition keeps the target facing a hole apart from Δ; the only other route
  to a hole subject's target is `ad_ppre__flex_r`, whose target variable is a
  defined flexible already living in Θw.
- `a_guess_ty_witness_mono_gen` (new): the witness with `a_wf_ptyp Θw τ`
  weakened to `a_wf_ptyp Θ τ` + `ftv τ ⊆ dom Θw ∪ Δ` — what a ρ-DIRTY guess
  can supply, since `Δρ ⊆ Δ`.  The old statement is the `ftv τ ⊆ dom Θw`
  instance, so `a_guess_ty_witness_mono` is unchanged for every other caller.
- P6-Cv's `FLEXMONO` (new block) serves SE-FlexR; `FLEX` now takes the
  cleanliness DIRECTLY and its one remaining caller, SE-GhostL, has `Pi = ◇`
  and gets it from `ad_ppre__hole` for free.

⭐ WHY THE REPAIR IS WHAT DID IT.  The old `SolE-FlexR` answered a flexible
counterpart with the FLEXIBLE, so the obligation compared the WHOLE guess
against a κ-image — no position-wise escape, hence `flex_apart` had to be
assumed.  The repaired row answers `guess^TY(Pi)`, whose obligation is
position-wise against `Pi`, whose holes the precision premise already keeps
Δ-apart.  Consistently, the witness that motivated `flex_apart`
(`cex_p6_flex_counterpart.v`) is one of the two the repair retired.

⛔ NOT YET DELETED.  The premise stays on P6-Cv's statement (annotated
`⭕ RETAINED BUT UNUSED`) and threaded internally, because removing it breaks
the whole downstream cluster at once — `flex_apart_deep` (P6-Cs),
`flex_apart_walk` (P6-Sv), `sub_shield` (P6-Ss, P6-L) all exist to supply it.
The strip of P6-Cv alone was machine-checked to go through; the recipe is in
the hand-off.  ⚠️ And the cascade is NOT pure threading: P6-Cs has a genuine
consumer at the COLLECTION-side `LE-FlexR` row (`prop_look_complete_cstr.v`
≈ 2185, `flex_apart_flex_var_clean`) — a rule the authors' repair did not
touch.  That one site decides whether the tower falls.


## 2026-08-05 — ⭐⭐⭐ **THE WHOLE P6 CLUSTER IS GREEN UNDER THE `SolE-FlexR` REPAIR**, the tree builds, and the repair RETIRES two of our own counterexamples

`make coq` is clean.  All five P6 lemmas are `Qed` and `Closed under the
global context` under the authors' repaired rule — P6-Cv, P6-Cs, P6-Sv,
P6-Ss and P6-L (`a_extract_complete`, the paper's `lemma:complete-look`) —
and so is P7b (`prop_sub_complete_thm.v`) and the whole soundness chain
including `a_sub_sound`, whose statement never moved.

### What the repair cost the cluster

ONE new premise, everywhere: **`ftvar_in_uskl ψa [<=] dom Θ`** (at the
fixed `Θw` in the generalized statements) — the ideal guess's own
well-formedness in the ambient context.  The repaired `SolE-FlexR` reads
the SOLVE block's payloads off that guess, so they are well-formed only if
it is, and it is NOT derivable: when α does not occur in `κR` the subject
`(κR)[ψa/α]` does not mention ψa at all.  Registered in
`docs/WF-SIDE-CONDITIONS.md`.

⚠️ It is NOT invariant in P6-Sv (whose ForallL row moves the guess to
`open ψsrc β` with β a fresh rigid absent from `Θw`) — and P6-Sv does not
need it, since the only lemma it feeds a guess to is P6-Cv's `_at`, which
carries no guess-scope premise.  Its ρ-side companion `Δρ ∩ dom Θw = ∅` IS
invariant everywhere and is what makes the SOLVE block's payloads Δρ-clean.

### ⭐⭐ The repair retires TWO of our own counterexamples

`cex_p6_flex_counterpart.v` and `cex_p6sv_forall_flex.v` both refuted a
`-var` lemma by the SAME step — the old row discarded the accumulated
pattern, forcing the answer to be the flexible.  The repaired row returns
`guess^TY(P)`, and at both configurations `P` is ghost-free, so the answer
IS the pattern: `c → ⟨⟩` instead of `β̂` (obligation becomes reflexivity),
and `∀β.β→β` instead of the vacuous `∀_.f̂`.  Machine-checked in
`cex/probe_flexr_neutralises_p6.v` (Qed, axiom-free, self-contained); both
files now carry retraction headers, their proof text at `d5f9169`.

⛔ This does NOT license dropping `sub_shield` — it was invented as the
repair of the second of these, and P6-Sv/P6-Ss/P6-L still carry it.  A dead
witness is not a proof; that is Step 3.

### ⚠️⚠️ THE PERFORMANCE TRAP OF THE CAMPAIGN — three occurrences

`L` is the LAST ∀-bound variable of every repaired statement, so a premise
slot filled by `ltac:(… fsetdec)`, or reached through a `solve [… fsetdec …]`
list, runs against a goal whose `?L` is still an EVAR — and **fsetdec on a
goal with a set metavariable does not terminate in any useful time**.
Measured: one such call took `prop_look_complete_sub_cstr.v` from 5 s to
>200 s; a second pair took it to >900 s; the same shape with `eapply
ad_ppre__arrow`'s tag evars hung a three-lemma probe file outright.  The
fixes are (i) name the avoid-set in an `assert` before the call so `exact`
instantiates `?L` structurally, (ii) put `exact HLav` FIRST in every
`solve` list, and (iii) PIN evar-valued tag sets with `apply … with (Ψ1 :=
…)`.  A related one: never use `simpl; clear - H; fsetdec` as a `solve`
alternative — a one-step lemma (`in_dom_app_r`) replaced eleven of those and
took another file from minutes back to 20 s.

## 2026-08-05 — ⭐⭐ **P6-Cs IS GREEN UNDER THE `SolE-FlexR` REPAIR**; P6-Sv started, its statement FINAL

`frost/algo/prop_look_complete_cstr.v` compiles: `a_lookeq_solve_complete_gen`
and the paper-facing corollary `a_lookeq_solve_complete` are both `Qed` and
`Closed under the global context`.  Every row now threads the SOLVE's own
block `Ξs` and its aligned extension `κs`, at `Ξs ++ Ξc ++ Θ0` — the order
`a_extract__solve` runs the final guess at, so P6-L consumes it verbatim.

**The arrow row** (the one the previous hand-off flagged as the last hard
one).  Its right IH runs at `Ξs1 ++ Ξc1 ++ Θ0` under `κs1 ++ κc1 ++ κ`, not at
`Ξc1 ++ Θ0`: `Pa1` is the LEFT SOLVE's output and mentions the flexibles solve
invented, so the precision the right branch consumes is stated under all three
blocks, and the only context at which that is an `a_inc` is `Hinc1` verbatim.
Everything it returns is permuted into the conclusion's `Ξs2 ++ Ξs1` /
`Ξc1 ++ Ξc2` order, and the permutation is FREE — `binds` over an append is
plain membership, so `analyze_binds` alone proves every reordering
(`binds_rot_app`, `binds_rot_app_rev`, `binds_app_perm5`).  The `a_inc` is
REBUILT from `Hκ` by four `a_inc_flex_prefix_build` steps rather than
permuted; the precision's κ-reordering is a lookup-level identity on
pairwise-disjoint blocks (new `msubst_lookup_app_congr`,
`msubst_lookup_ftv_app`).

⭐ **One new premise, forced by that row and by nothing else:**
`Δρ ∩ dom Θw [=] empty`.  The right IH has to re-establish the shielded-ftv
premise under the bigger metasubstitution, i.e. that a ρ-replaced variable
misses every image.  For `κc1` that is the `Forall … ∩ Δρ = ∅` conclusion; the
SOLVE block has no such conjunct **and cannot get one** (the LE-Var row reads
`κs` off P6-Cv, whose package carries no ftv bound at all), so the only handle
is its payloads' well-formedness at the FIXED `Θw`.  Δρ and Θw are both
constant inside P6-Cs, so it threads unchanged; vacuous at the ρ = identity
corollary, and P6-Ss's Sub-ForallL maintains it because the fresh rigid it
adds to Δρ is picked fresh for Θ ⊇ Θw.  A proof-construction fact about the
mech's own ρ-generalization — nothing for `docs/PAPER-GAPS.md`.

**The five ∀ rows** (including the two ε-tagged mirrors).  `Θw` does NOT move;
keeping it fixed is exactly what lets β be stripped out of the `a_inc`, since
the SOLVE payloads' only β-freeness argument is `a_wf_ptyp Θw` together with
`β ∉ dom Θw`.  Their IH runs at `add β L`, which is what makes `β ∉ dom Ξs`
available — needed both by `HβPa` (the solve's ftv bound now carries a
`dom Ξs` term) and by the strip.  `a_inc_strip_tvar_mid` peels BOTH blocks at
once.

**The corollary** gained the avoid-set parameter `L` and one further
paper-external wf side condition, `ftvar_in_uskl ψa [<=] dom Θ`: the repaired
`SolE-FlexR` reads the solve block's payloads off the ideal guess, and when α
does not occur in `κR` the subject does not mention ψa at all, so the
subject-wf premise says nothing about it.

### P6-Sv started — `prop_look_complete_sub_var.v`

New upstream kit in `prop_look_complete.v`: ⭐ **`solve_sub_ext`** and its glue
(`_nil`, `_step`, `_post`, `_post_solve`, `_of_eq`) — the SUBTYPING twin of
`solve_ext`.  Two differences: the judgment carries a MODE, and the package
includes the OUTPUT's well-formedness at `Ξ ++ Θ0`, because on the sub side
that is a genuine CONCLUSION of the completeness lemma rather than a derivable
fact (`cex/cex_solve_sub_wf_leak.v`).

Converted in P6-Sv: `a_solve_sub_hole_output`, `a_solve_sub_complete_rho_var`,
⭐ `arrow_grid` (its `KEY` hypothesis now hands back the whole MERGED package,
since SS-Arrow and SS-GhostLF THREAD), ⭐ `a_solve_sub_eq_unshielded`, the
Infer row, and **the main theorem's STATEMENT, which is FINAL** (the Θw pack,
`Δρ ∩ dom Θw = ∅`, the avoid-set `L`, and a `solve_sub_ext` conclusion).  A
`⛔⛔ RESUME HERE` block above `a_solve_sub_complete_var` carries the plan;
`coqc` stops in the CHECK row.

⚠️ **Four traps, all of which will recur in P6-Ss.**  (1) The five binder rows
avoid `ftvar_in_aenv Θ`, not `dom Θ`, so every ltac pattern
``?b `notin` (dom _ `union` _)`` stops matching — match ``?b `notin` ?S`` with
a `match S with context [ftvar_in_aenv _] => idtac end` guard.  (2) The binder
rows AND the threading rows run their premise at a GROWN context, so a
``β0 ∈ dom Θ`` premise must be weakened: use the one-step `in_dom_app_r` —
`solve [ … | simpl; clear - H; fsetdec | … ]` at eleven sites turned the file
into a **multi-minute** build.  (3) `a_solve_{eq,sub}_ftv`'s bounds grew a
`dom Ξ` term, and at every consumer it must be ELIMINATED, not absorbed
(`solve_eq_generated_not_dom`: a context variable is never a generated name).
(4) A new SE-FlexR case appears in every induction over the solve — its output
is `guess^TY`'s PAINT, which shields nothing
(`pskl_shielded_ftv_ptyp_to_pskl`).

## 2026-08-04 — ⭐⭐ **P6-Cv IS GREEN UNDER THE `SolE-FlexR` REPAIR**: the ∀-row payload-scope obligation is CLOSED, and the hand-off's prescribed derivation was wrong twice

Branch `solve-flexr-repair-wip`, commits `3e44c4d` + follow-up.
`frost/algo/prop_look_complete_var.v` compiles, `Qed`,
`Closed under the global context`; `a_solve_eq_complete_var` now carries the
κ-extension package (`Ξ`, `κ'`, `keys κ' = keys Ξ`, the avoid-set parameter
`L`, and the payload `Forall`).

**The obligation.**  `a_guess_ty_witness_mono` reports the extension's
payloads well-formed in `Θw` — the context that stays FIXED as the induction
goes under ∀ binders, because the solve's ∀ rows pass the generated block
through unchanged, so a payload naming a bound rigid would be ill-scoped.  A
row has the counterpart monotype's well-formedness only at `Θ`, which under a
∀ row is `Θw` plus the bound rigids.  The transport is three steps, and the
content is that **both ftv bounds are over the context's DEFINITIONS, never
over a domain** — a rigid binder carries no definition, so it can never enter
either bound:

```
  ftv (ψa1 → ψa2) ⊆ ftv (Q1 → Q2) ∪ dom Θw   consis_subject_ftv_defs_bound
  ftv (Q1 → Q2)   ⊆ dom Θw                   ad_refine_mono_paint_ftv_bound
  a_wf_ptyp Θ τ + ftv τ ⊆ dom Θw ⟹ a_wf_ptyp Θw τ
                                             a_wf_ptyp_mono_strengthen_dom
```

The middle lemma is the interesting one: `ad_refine_syn_ftv_rhs_bound`'s
`dom Θ` is over-generous by exactly the refinement's HOLE rule, whose fill is
only `Θ`-scoped — and a mono paint has no hole, so refining one introduces no
variable the source and the context's definitions do not already have.

⚠️ **Two corrections to the active hand-off, both recorded there.**  (i) Its
prescribed route through `dom Θr` does not work: "a ∀ row's binder joins Θtv,
never Θr" is false — the `forall_syn_tagged` row puts its binder on the Θr
side (`aenv_split_cons_r`), so `dom Θr ⊆ dom Θw` is not invariant.  (ii) Its
prescribed new premise `κ ∷ Θ0 ⊑ Θw` is not invariant either — a ∀ row's
binder is rigid in the extended `Θ0` but absent from `Θw`, and `a_inc__tvar`
cannot produce it.  What IS invariant, and is what the theorem now carries, is
the strictly weaker IMAGE bound
`forall α, a_flex_tvar Θ0 α -> ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θw`
(preserved by `a_flex_tvar_strip_tvar`; at the top-level call it is just
`a_inc_lookup_flex_ftv_dom` on `Hκ` with `Θ = Θw`, so the paper-facing
statement pays nothing).

**Also in this pass.**  The three ∀ blocks (`forall_inh_tagged`,
`forall_syn_tagged`, `topholeg`) converted to the package; their body-IH
avoid-set is `add α Lav`, not `Lav`, because the block is emitted outside the
∀ and the fold renames α — it costs nothing, since the IH's own avoid-set
premise needs `α ∈ L` anyway.  ⚙️ The three ∀ rows no longer call
`a_solve_eq_strengthen_tvar`: SE-Forall / SE-GhostForall / SE-ForallGhost run
their premise at `(β ~ tvar) ++ Θ` now (the repair's decision §2(1)), so the
IH output IS the premise; SE-UnivGhost, having no binder, still needs it.
Both `FOLD`s are generalised over the body's extension `κ0` and run under
`κ0 ++ κ`.  Nine lemmas were added to or moved into
`frost/algo/prop_look_complete.v` (the three above plus
`a_binds_tvar_strengthen`, `aenv_binds_dom_sub`,
`forall_wf_mono_images_dom`, `a_inc_lookup_flex_ftv_dom`, and
`msubst_lc_app_wf` moved up from `prop_look_complete_extract.v` §8).

**P6-Cs: STATEMENT FINAL, five rows through.**  `prop_look_complete_cstr.v`
compiles up to the ARROW row's RIGHT IH call.  The pre-theorem half is done
(the nine moved-up copies deleted; `a_solve_cstr_app`, `a_solve_cstr_ctx_change`
— with two new `a_flex_tvar_app_mono` / `a_flex_app_anti` lifts, since its eq
row's tail runs at `Ξ1 ++ Θ` — `a_solve_cstr_weaken_mid_flex` with the new
`dom Ξm ∩ dom Ξ = ∅` premise, and `a_solve_cstr_strip_tvar_mid` all threaded),
and the conclusion carries a second block `Ξs` at `Ξs ++ Ξc ++ Θ0`, the order
forced by `a_extract__solve`.

Three premises had to be added beyond the first design, each from a concrete
obstruction: (i) the **Θw pack**, because the ∀ rows strip β from the `a_inc`
with `a_inc_strip_tvar_mid`, whose `Forall (β ∉ ftv)` premise `κc` gets from
its `ftv ⊆ ftv ψa` conjunct and `κs` has no analogue for — which also forced
`a_solve_eq_complete_var_at`, since the paper-facing `a_solve_eq_complete_var`
pins `Θw := Θ` and is unusable under a binder; (ii)
`ftvar_in_uskl ψa [<=] dom Θw`, because in the flexible-P0 row `ψa` is the mono
paint `syn τψ` and `τψ` IS the κs payload; (iii) `all_flex_mono Ξs` and
`uniq Ξs`, which the arrow row needs to rebuild `a_wf_aenv (Ξs ++ Ξc ++ Θ0)`.

⭐ The flexible-P0 row — the only place `SE-FlexR` itself fires — is through,
and its `WIT`/`a_guess_ty_witness_mono` shape is the template downstream.
⚠️ Its `Pi` grid is SIX ways now, not two: `nonghost_pskl` sends `◇` to
SE-GhostL (returning the target — the sharing that side condition protects) and
`∀◇P` to SE-GhostGuarded, whose peel lands on a body wf forces GUARDED, hence
nonghost.  That peel needed a new `ad_ppre_def_chain_fold` to re-fold the
precision along the definition chain `ad_ppre_tophole_subject_chain_inv`
unfolds.  ⚠️ And the arrow row's right IH does NOT run at `Ξc1 ++ Θ0`: `Pa1`
mentions the flexibles the LEFT SOLVE invented, so it runs at
`Ξs1 ++ Ξc1 ++ Θ0` under `κs1 ++ κc1 ++ κ` (= `Hinc1` verbatim) and everything
it returns is permuted afterwards — cheaply, since `binds` over an append is
plain membership.

Nothing for `docs/PAPER-GAPS.md`: all of this is proof construction, not a
paper finding.

## 2026-08-04 — ⭕⭐⭐ TASK A (reachability of the refuting payload): the POSITIVE half is MACHINE-CHECKED — a refuting program must FREEZE a polymorphic argument

`frost/algo/cex/probe_payload_reachability.v` (all `Qed`, three
`Print Assumptions` closed; compiles in under a second).  The refuting
configuration of `probe_double_occ_run.v` needs BOTH (1) a raw `Θ0`-flexible
at the payload's codomain and (2) a **bare** ∀ at its domain — bare, because
the domain is the consistency-feeding position and a guess's tag is payable
only against a `bskl_all_inh`, which `pskl_to_bskl_inh` produces exactly at a
`pskl_all_syn` of `P0`.

**Conjunct (2) is settled.**  A payload's arrow-LEFT is the argument's
COLLECTION, an `a_pat` output at `(TC, ◇)` — the SK sort.  `a_sub_sk_no_spine_all`:
at the SK sort with a mode-compatible payload, an `a_sub` output's MODE-SPINE
never ends in a bare ∀ (`__infer` is the only verbatim row and it is TI-only;
`__ghost` returns the payload, whose `skmod[SK]` spine ends in ◇;
`__univ_ghost_r` wraps in `⫯`; `__arrow` hands the spine to its codomain;
`__flex_mono` / `__forall_l` / `__univ_ghost_l` and the whole flexible walk
relay — Flex-Assign's monotype substitution leaves the arrow spine alone).
Lifted through `a_pat` (`a_pat_spine_all_out_freeze`,
`app_payload_domain_all_needs_freeze`): **a bare-∀ payload domain forces a
freeze in the argument.**  ⭐ So the hand-off's warning becomes a theorem in
the positive direction — not "domains are never ∀-headed" (false: `{|e|}`
collects at TI where `a_sub__infer` is verbatim) but "only `{|e|}` makes them
so".

**The other half of the tension, at the rule level.**  `a_guess_mono_all_free`:
a monotype guess exists only for a ∀-free skeleton.  Since `a_assign__solve_m`
is the only rule that solves a flexible against an inherited skeleton and it
demands `mono_ptyp τ`, a flexible can NEVER absorb a ∀ — simultaneously the
mechanism of the cex's collapse (SolE-FlexR overwrites the eq-constraint's
polytype yield; SolveM cannot recover it) and the obstruction to checking a
frozen polymorphic argument at a raw-flexible payload.

⭕ **Still open — conjunct (1), now one crisp statement.**  A raw-flexible
ambient arises only where the enclosing COLLECTION is uninformative
(`a_consis__ghost_r`, payload ◇ / output = subject, is what leaves a ForallL
guess raw).  But that collection is computed by the SAME `a_sub` run, at the
same subject and the same payload domain, differing only in the SORT (SK
guesses ghosts, TY flexibles) — so the ∀ that (2) demands makes the marker's
instantiation informative and the codomain output `⫯`-wrapped, not ◇.  That
co-determination is why (1) and (2) pull in opposite directions.  Closing it
needs one EXTRACT-level fact — *the extract's output is ghost-ish only if the
look collected nothing at the marker* — which is P6 machinery and is not
proved.  DESIGN §14.10; HANDOFF-close-subtyping-completeness.md TASK A box.

## 2026-08-03 — ⚠️⚠️ RETRACTION (co-author caught it): the "incompleteness on programs" claim is WRONG — the declarative system rejects that program too; reachability is OPEN again

The entry below claimed a source-level separation.  **It is withdrawn.**
`pipe (λg. g arg)` is ill-typed DECLARATIVELY as well, so met.exe's
rejection is correct behaviour and nothing goes to the authors.

**The error.**  I read `d_sub__forall_l_untagged` for a `mono_ptyp`
restriction, found none, and concluded impredicative instantiation was
unconstrained.  The operative constraint is the TAG obligation — the
paper's *"never guess polymorphism out of thin air"*: the rule runs its
premise at `Ψ ∪ Ψ'` with `d_tags Ψ' ph`; the ONLY `d_consis` rule that puts
a tag into Ψ is `d_consis__forall_inh_tagged`, whose counterpart must be
`btyp_all_inh` (an INHERITED ∀); and `d_sub__infer` demands `Ψ [=] empty`.
So a polytype instantiation must be PAID FOR by an inherited ∀ in the
counterpart, which is what the SKELETON supplies — and the skeleton
`⫯(◇ → ◇)` of `λg. g arg` supplies none at `r`'s position.  `pipe`'s `r`
and `g`'s `b` are mutually dependent.

**The paper documents it twice (§2.9)**: *"Only flowing back and forth
once"* (third limitation) is this program structurally — its own example
`f : ∀c d.(c → c → List d) → Int` applied to `g : ∀b.(∀a.a→a) → b → List b`
needs the information to flow BACK to instantiate `b`; and *"ghosts are
nameless"* (second limitation) is the same defect in `⫯(◇ → ◇)`.  The
co-author's remark — the program becomes typeable if `pipe`'s skeleton
first flows INTO `λg. g arg` — is exactly that extension.

**Survives**: the rule-level results (`probe_no_run`,
`probe_motive_instance_false`, `probe_main_forall_false`).  That
configuration's declarative side DOES pay its tag (`consis_d` discharges ε
against a `bskl_all_inh` counterpart at the domain), so `main_forall` is
genuinely false and the two flagships stay vacuous-as-stated.

**Reopens**: reachability, now sharply stated — the cex needs BOTH a raw
`Θ0`-flexible at the payload's codomain (no inherited information) AND a
concrete counterpart there with the tag paid at the domain (information
present).  These pull in opposite directions; the withdrawn program is the
near-miss that gets the first and loses the second.  If the conjunction is
unreachable, the theorem is merely OVER-QUANTIFIED and HANDOFF TASKS 2–3
are back ON.

**Lesson** (same species as the MODE confusion): before any "decl accepts"
claim, enumerate ALL the declarative side conditions — the TAG obligation,
not just the monotype one — and consult §2.9's limitation list.

## 2026-08-03 — ~~⚠️⚠️⚠️ TASK 2's VERDICT: the failing payload class is TYPING-REACHABLE~~ — **RETRACTED, see the entry above**

Reading the payload invariant off the producers (HANDOFF TASK 2) refuted the
planned repair's premise instead of supplying it.  Call-site map: every
`a_sub` payload is the ambient `a_typing`/`a_pat` payload; FN payloads are
`arrow(P_arg, Q_amb)` with `P_arg` the spine collection's output at TC/◇.
Two producer facts compose into the cex shape:

1. **The collection ghosts only HEAD quantifiers.**  `a_pat` on an argument
   typed `(∀c.c→c) → unit` fires SK-ForallL only at a ∀ HEAD; the guarded
   arrow then goes through `a_sub__univ_ghost_r` VERBATIM — output
   `⫯((∀c.c→c) → unit)`, the raw ∀ surviving BELOW the head.  The
   implementation's SI-UnivGhostR (type.ml:1002) is the same rule.
2. **An undetermined result becomes a fresh flexible.**  When the body's
   collected skeleton has ◇ at the result (a lambda-bound function applied
   in the body — LE-Vacuous emits no constraint), the look's guess invents
   `r̂` and the re-check runs the body at `[tc; r̂]`.

So the typing builds `arrow(⫯((∀c.c→c)→unit), r̂)` — the probe's payload
shape modulo the ⫯ — and there the FlexR collapse fires for real:
**met.exe REJECTS**

    val pipe : forall r . []( ( (forall b . [](b -> b)) -> r ) -> r )
    let test = pipe (fun g -> g arg)        -- arg : []((∀c.[](c→c)) → unit)

with `this expression has type ˆx1 but expected 👻.(∀c.[](c→c)) → unit` —
the collapsed guess — while the DECLARATIVE side accepts
(`r := (∀c.[](c→c)) → unit`, impredicatively).  CONTROL: the same program
with `r` pre-instantiated concretely PASSES met.exe (by soundness that
certifies the body's declarative check; decl ForallL supplies the
instantiation).  ABLATION: `arg : [](unit→unit)` PASSES — the collapse
still happens but the collapsed guess is MONO and Assign-SolveM succeeds.
The ∀ below the argument type's head is the exact discriminator.  Repros:
`docs/repros/thm_complete_subtyping_reachable_reject_pipe{,_control_concrete_r,_ablation_no_forall}.mle`.

**Consequence.**  thm:complete-subtyping is false ON PROGRAMS, not merely
over-quantified; NO payload side condition can make the completeness bundle
cover all typing-reachable instances (the reachable set contains failing
ones).  HANDOFF TASK 3 (motive side condition + discharge) is therefore
INVALID AS SCOPED — what remains provable is completeness on the
completable class (the supply routes' shapes), which excludes real
programs.  Restrict the theorem or fix the solve's threading (e.g.
SolE-FlexR depositing the accumulated pattern as the flexible's definition
instead of discarding it): an AUTHOR-level decision.  P7c is BLOCKED on it.
Full entry: docs/PAPER-GAPS.md (2026-08-03); DESIGN §14.8.

## 2026-08-03 — ⚠️⚠️⭐⭐⭐ THE PROBE IS MACHINE-CHECKED: no `a_sub` run exists at the double-occ payload — `main_forall` is FALSE, thm:complete-subtyping OVER-QUANTIFIES `P0`

`cex/probe_double_occ_run.v` rewritten from scaffold to a full Qed
development (three `Print Assumptions` closed; the tree stays green,
admit-free, axiom-free).  The 2026-08-03 rule-level trace is now a lemma per
step, each one FORCED by inversion and uniform in every fresh name:

1. **Steps 1–3 constructed** (`probe_looksub` / `probe_solve` /
   `probe_guess`, assembled in `probe_extract`): LS-Arrow = LE-Var + LS-Var
   collects `[eq (∀γ.γ→γ); sub tc f̂]`; the solve runs the eq on the HOLE
   (SE-GhostL), then the sub-constraint solves ON the accumulated pattern —
   SS-ForallL / SS-Check / SE-FlexR, whose output IS the flexible — so the
   close re-binds a VACUOUS binder: `∀_.f̂`; the TY guess passes it through.
2. **Each step is DETERMINISTIC** (`probe_look_det` / `probe_solve_det` /
   `probe_guess_det` / `probe_extract_det`): the only shape-surviving
   inversion branches are refuted by their own side conditions (LS-Absent by
   the marker's occurrence, LS-Check by the subject BEING the looked-for
   variable, SS-Check by `guarded_pskl (pskl_all_syn _)` inversion).  ⭐ The
   vacuous binder swallows the fresh names, so the extract's output
   `(nil, ∀_.f̂)` is name-free — determinism needs NO renaming kit.
3. **The continuation is stuck** (`probe_continuation_stuck`): Arrow forces
   the domain consistency `∀_.f̂ ∼ ∀γ.γ→γ`, ForallInh forces the leaf
   `f̂ ∼ β1→β1` at the freshly pushed rigid `β1`, FlexL's assignment walk
   meets the context head `β1 ~ tvar` with `β1 ∈ ftv` — and the ONLY rule
   matching a rigid head, Assign-SkipRigid, refuses
   (`a_assign_rigid_head_occurs_stuck`, ONE inversion).  The two consis
   stuck shapes are fully general (`a_consis_var_vs_head_rigid_arrow_stuck`,
   `a_consis_forall_arrow_vs_vacuous_var_stuck`: any context, any variable,
   any names).

**The headline chain.**  `probe_no_run` (¬∃ run at the configuration) + the
motive premises already Qed in `p7_sub_shield_positional_over_strong` ⟹
`probe_motive_instance_false` (the P7b motive instance at
`n=3, NM=TY, M=FN(TC)` is FALSE) ⟹ `probe_main_forall_false :
~ main_forall 3` and `probe_main_forall_hyp_false :
~ (forall n, main_forall n)`.  **The bundle's one hypothesis is REFUTED, so
`a_sub_complete_bundle_holds` / `a_sub_complete` are VACUOUS as
stated.**  The "`main_forall` is KNOWN-TRUE (an instance of the theorem
being proved)" line was CIRCULAR exactly at the paper theorem's
over-quantification of `P0`; the language is retracted in dispatch.v §10,
AGENTS/CLAUDE.md, and DESIGN §14.6–§14.7.

**What it means, and what it does NOT.**  met.exe ACCEPTS the corresponding
source program (`docs/repros/thm_complete_subtyping_fn_tc_passes.mle`) — the
typing's spine collection builds payloads with GHOSTS, never a ∀ below the
head at a consis-feeding position.  So the algorithm is fine ON PROGRAMS;
it is thm:complete-subtyping's quantification over `P0` that is broader than
the typing-reachable payloads, and the shield saga's residual shape is
exactly the unreachable one (`prop_sub_shield_supply.v`'s covered shapes are
the reachable ones).  PAPER-GAPS entry is owed WITH the repair: a payload
side condition on the P7b motive, read off `a_typing`/`a_pat`'s `a_sub`
call sites + type.ml's spine collection
(docs/HANDOFF-completeness-repair.md TASKS 2–3).
⚠️⚠️ *(Superseded later the same day: TASK 2 showed the failing class IS
typing-reachable — see the top entry.  "Fine on programs" held only for
collection-determined instantiations.)*

## 2026-08-03 — ⭐⭐⭐ REVIEW FROM SCRATCH: `flex_shield` is DEAD — deleted from P6-Sv; the precision tag index Ψi identified as the REAL positional handle

User directive: review `flex_apart`/`flex_shield` from the very beginning
instead of patching a fourth time.  Outcome, all machine-checked:

1. **`flex_shield` was pure relay.**  Every `Hfsh` site in
   `a_solve_sub_complete_var`'s induction relays (descend_l/descend_r/
   arrow_inv/topholeg_inv/fsh_clean-rebuild); the cash-out lemma
   `flex_shield_flex_leaf` fed only the regression test.  The premise is
   DELETED and P6-Sv compiles; P6-Ss's LS-Var row now uses
   `sub_shield_here`'s first conjunct only.  What actually closes the
   leaves (post ρ-generalization): `ad_ppre_mono_subject_target_tags_empty`
   (precision at a mono κ-image), `a_solve_sub_complete_rho_var` (the
   ρ-leaf), and P6-Cv's FLEX chain, whose only walk-supplied need is
   Δρ-CLEANLINESS at a flexible (⟹ ρ = id there); tags/mono flow from the
   FILL (`ad_refine_mono_paint_rhs_monoish` +
   `ad_pat_consis_monoish_counterpart`).
2. **No contradiction with cex_p6sv_forall_flex**: the original witness is
   excluded by `flex_apart_walk` ALONE (`fastep_all_r` reaches the stuck
   (α̂, β→β) leaf).  The shield was belt-and-braces from the repair day that
   later refactors made unnecessary.
3. **The Ψi insight.**  cex_p6sv (conclusion genuinely false) vs the
   double-occ witness (premise over-strong) differ in exactly one thing at
   the same local shape: whether the guess's tag is solved AT that position —
   `ε ∈ Ψi` (precision P-Forall matches Pi's ∀) vs the position's index ∅
   (the copy is only instantiated).  The precision judgment already splits
   Ψi positionally, so the clean replacement for the mech-invented
   (P0, ψa)-walks is a condition read off `⊑ᵖ[Ψi]` — see
   memory `remech-flex-shield-dead` for the queued follow-ups (drop the
   vestigial conjunct + Ψ' index, then attempt the Ψi-form; if it lands,
   `sub_shield` dies entirely and `main_forall` discharges).

## 2026-08-03 — ⭐ ghost-freeness ON THE MOTIVE (residual component 2 CLOSED) + ⚠️⚠️ the shield's positional index REFUTED AGAIN: the DOUBLE-OCCURRENCE witness

`make coq` green, admit-free, axiom-free; every flagship
`Print Assumptions`-clean.  The P7c hand-off's Step A is DONE and its Step B
is SETTLED — in the negative.

**Step A — the TY ghost-freeness is ON THE MOTIVE.**  `sub_complete_concl`
gained the guarded last premise `NM = a_sub_mode_ty -> uskl_ghost_free R'` on
the JOIN-side subject; `a_sub_complete` carries it as the paper-facing
EXTERNAL side condition (WF-SIDE-CONDITIONS.md updated — at the reflexive
instance `R' := κ⌈P⌉ᵘ` it is ghost-freeness of the input).  The two ForallL
rows DROPPED their own `Hgfj` hypothesis (the motive supplies it; their
construction is the shared `Hgfswap` assert, consumed by both the
`ad_pat_sub_precise_upre_gv` swap and the IH).  Suppliers, all cheap and all
landing FIRST TRY: Sub-Arrow inverts the arrow's; Sub-ForallR passes the same
subject through; Flex-Assign derives it OUTRIGHT from the walk's own
≡ᵘ-to-a-monotype-painting slack (new helper `tyequiv_mono_paint_ghost_free`);
Flex-Solve from the deposited painting; the dispatcher's `__univ_ghost_l/lg`
by `discriminate` (SK-only rows) and `__flex_mono` by
`mono_ptyp_to_uskl_syn_ghost_free` + `a_wf_aenv_binds_def_mono`.  ⭐ The whole
reason this was tractable: every ghost-heading join rule is SK-only, so all
SK-side suppliers are vacuous.

**Step B — ⚠️⚠️ the general shield supply DOES NOT EXIST: the positional
index is still over-strong.**  `cex/cex_p7_shield_double_occ.v` (all Qed,
axiom-free, first compile) takes the §14.1 realizable witness and DUPLICATES
the marker: `R = ∀^t.(□₀ → □₀)`, `κ = α̂ ↦ unit→unit`,
`Q = (∀ᵢ.β→β) → (unit→unit)`, with `P0 = (∀γ.γ→γ) → α̂` and the tagged guess
`ψa = ∀^e β.β→β` unchanged.  Every hypothesis of
`a_sub_complete_forall_l_tagged` except the shield is machine-checked
inhabited (`p7_sub_shield_positional_over_strong`; the join can only end in
ForallL there, `join_at_Rd_is_forall_l`) — the tag is still discharged at the
arrow's DOMAIN while the CODOMAIN copy of the guess is ForallL-INSTANTIATED
(with `unit`) against the raw flexible's mono-ish counterpart at NO tag cost —
and the shield is FALSE at every marker (`p7_sub_shield_double_fails`): the
subject is now `α → α`, one `sss_arrow_r` step reaches `(α̂, α)`, the guard is
MET, and the leaf is the boundary cex's stuck shape.  ⭐ **What the guard
cannot see is WHAT THE DERIVATION DOES at a position** — with two marker
occurrences the two guess copies are treated DIFFERENTLY (domain: MATCHED,
tag solved against the ∀ᵢ; codomain: INSTANTIATED, no tag solved) while
`flex_shield` demands whole-guess protection at every guarded position.
DESIGN §14.6 records the witness and the repair direction: index positions by
match-vs-instantiate, which the FILL pins (a raw flexible's counterpart is
`bskl_inh_free`, and an inh-free counterpart solves no tags —
`ad_pat_sub_g_inh_free_tag_free`); the open question is what P6-Sv's LS-Var
leaf needs at an INSTANTIATED position, and the relaxation must replay
through P6-Sv → P6-Ss → P6-L → the P7b ForallL rows.  ⚠️ Nothing to
PAPER-GAPS.md — `sub_shield` is mech-invented, and the ALGORITHM plainly
succeeds at the witness.

**Consequence.**  `main_forall n` — now carrying ONLY the shield component —
STAYS as the bundle's hypothesis (it is KNOWN-TRUE, so the conditional
flagships remain honest), and the flagships stay out of README.v.  Closing
subtyping completeness now goes through the shield's FOURTH re-indexing, a
P6-tower campaign, not an assembly step.
⚠️⚠️ *(Superseded later the same day: `main_forall` is REFUTED —
`cex/probe_double_occ_run.v`, see the top entry.  The repair is a motive
payload condition, not a re-indexing.)*

## 2026-08-03 — ⭐⭐⭐ **SUBTYPING COMPLETENESS IS ASSEMBLED**: P7a's last two rows, the ForallL/ForallR join permutation, and `a_sub_complete_bundle_holds` — one hypothesis left

`make coq` green, admit-free, axiom-free.  Everything the P7c hand-off
(docs/HANDOFF-p7c-finish.md) scoped is done except its TASK 2b, which is TASK
0's shield and is a design question, not an assembly one.

**TASK 1 — P7a's two TERM-VARIABLE rows are `Qed`.**
`a_sub_flex_complete_skip_tm_var` / `_skip_tm_skl`
(`algo/prop_sub_complete_thm.v` §(N)/§(O), ~365 lines each, axiom-free).  They
came straight out of DESIGN §12.3's substitution table against
`a_sub_flex_complete_skip_rigid`, and the recipe held with no surprises:

* `a_inc__var` / `a_inc__var_skl` shrink the `a_inc` TARGET exactly as
  `a_inc__tvar` does, so the IH still runs at the truncation `Θ'`;
* neither row carries `α ≠ β` or `β ∉ ftv P0` — both are DERIVED in four lines
  (a term entry is never `a_binds_tvar`, so under `uniq` neither the flexible
  subject nor a free variable of a well-formed `P0` can be it).  That is why
  the RULES carry none either, matching the twin walk's `Assign-SkipTmVar`;
* the ONE genuinely new obligation is the SEMANTIC MIDDLE `Θ' ⊢ A' ≡ᵗ κQv` —
  a rigid entry has no payload, a term entry does.  The consistency twin's
  `Assign-SkipTmVar` (prop_consis_complete.v:5595-5690) proves exactly it;
* ⚙ ONE step beyond that twin: subtyping re-attaches through the JUNK SWAP, so
  the witness is `kswap_msubst β β1 ζ` and the middle is read back with
  `msubst_ptyp_kswap` — free, since `β`/`β1` are fresh for a payload scoped in
  `Θ0`.

⚠️ The transcription hazard worth recording: **watch the two sides of the
entry.**  Occurrences inside `Ξv ++ …` are the `a_inc` TARGET and become
`(β ~ abind_var_typ A')`; every other occurrence is the SOURCE and stays
`(β ~ abind_var_typ Qv)`.

Consequence: `a_sub_flex_walkable` and its two lemmas are **deleted**,
`sub_flex_complete_holds` takes no side condition on `Θ0`, and its two `exfalso` branches
are ordinary delegations.  Obstacle (B) of DESIGN §12.2 is closed.

**TASK 2a — the ForallL/ForallR overlap is closed, and the paper was right.**
subtyping-proofs.tex:3385 already covers it with a one-sentence WLOG; ⚠️ it is
NOT a defect and must not be reported as one.  Its mechanical content is
`algo/prop_sub_complete_dispatch.v` §11:

* `sub_gv_all_inh_forall_r_family` — from ANY TY/TC join onto a
  `bskl_all_inh` target, extract the cofinite ForallR family
  `a_sub_complete_forall_r` consumes.  Induction on the join; the ForallL
  chain must bottom out in `__forall_r` because `__check` is the only other
  TY/TC row that can carry that target and its `guarded_pskl` premise refutes
  a ∀-inh counterpart (§8's step, read backwards).  Each ForallL step is
  re-applied under the new binder, its `Θ ⊢ ⌊ψ⌋ˢ` premise weakened along the
  added rigid.
* `ad_pat_sub_gv_fuel_weaken` — the fuel arithmetic the hand-off warned about:
  the extraction returns the family at whatever height it finds, while
  `a_sub_complete_forall_r` wants it at exactly `n` for a conclusion at `S n`.
  A 20-line induction; only the four rules whose conclusion fuel is `S n` need
  `destruct m`.
* `sub_complete_all_inh_counterpart` composes them — **whenever the counterpart is
  ∀-inh the row goes through ForallR, whatever the join's last rule and
  whatever `P0`**, so the ForallL rows' `guarded_pskl P0 ∨ P0 = ◇` premise
  costs nothing (a ∀-headed `P0` forces a ∀-inh counterpart through the FILL).
* ⭐ **and A2 is DISCHARGED INSIDE the dispatch**: `p0_wlog_trichotomy` reads
  the WLOG off mode compatibility (at SK every compatible `P0` is a hole or an
  arrow; at TY the only non-guarded, non-hole shape is a `∀`, and only at
  `M = TC`), `sub_complete_assemble`'s two ForallL cases split on it, and the escaping
  shape goes to `sub_complete_all_inh_counterpart`.  So **`main_forall` now TAKES
  `guarded_pskl P0 ∨ P0 = ◇` as a hypothesis** — the bundle's residual is
  strictly narrower.

**TASK 3 — the assembly.**  `a_sub_complete_bundle_holds`
(`prop_sub_complete_dispatch.v` §12) is exactly DESIGN §12.1's three layers
glued by `lt_wf_ind` on the fuel and, inside it, `lt_wf_ind` on the CONTEXT
LENGTH: `sub_complete_arrow_holds` (fuel IH) → `sub_complete_ctx_lt n k` (length IH) →
`sub_flex_complete_holds` → `sub_complete_assemble` with `ESC := fun _ => True` (the two tophole
closures are `exact I`; the third hands back `sub_flex_complete n Θ0`, which is
`sub_flex_complete_holds` at `Ξ = nil`).  `a_sub_complete` (algorithmic.tex:1446) is the
`Ψ := ∅`, `R := ⌈P⌉ᵘ` instance.

⭕ **The residual is `main_forall n`, and it has exactly TWO components** — a
count worth stating, because DESIGN §12.2 listed only one and the P7c hand-off
listed only the other:

1. **TASK 0's `sub_shield`** for a `P0` carrying a ∀ below its head, whose
   boundary is machine-checked (`sub_shield_forall_flex_p0_fails`,
   cex/cex_p7_shield_forall_flex.v).
2. ⚠️ **NEW FINDING — `NM = TY -> uskl_ghost_free (uskl_all_tag ε Rj)`**, the
   ForallL rows' third premise.  It is the last premise of
   `ad_pat_sub_precise_upre_gv` (P5's precision-substitution transport, which
   threads the same predicate through every lemma of its pack), and it is **NOT
   derivable from the join**.  The near-miss is the trap: all four rules that
   put a ghost AT THE HEAD of the subject (`__ghost`, `__ghostg`,
   `__univ_ghost_l`, `__univ_ghost_lg`) are SK-only, so ghost-freeness *looks*
   like a TY invariant — but `__arrow`'s DOMAIN is an arbitrary consistency
   leaf with no sort constraint and `__infer` accepts an arbitrary subject, so
   a ghost can sit inside a TY join's subject.  It is an EXTERNAL side
   condition, now registered in docs/WF-SIDE-CONDITIONS.md.  Closing it means
   putting it ON THE MOTIVE at `NM = TY`, which every recursing row then owes
   for its recursive subject (Sub-Arrow at `R2`, Sub-ForallR, both Sub-ForallL
   rows, P7a's Flex-Assign / Flex-Solve).  **That is a motive change, not an
   assembly step.**

⚠️ **The hypothesis is deliberately `main_forall` and not a "shield supply".**
Stating
the residual as the thing actually missing would mean guessing the side
conditions under which the shield holds — and the unguarded form is FALSE, so
a wrong guess yields a vacuously true theorem.  `main_forall n` is
KNOWN-TRUE (it is an instance of the theorem being proved), so the conditional
bundle is honest.  Both flagship theorems are `Print Assumptions`-clean; they
are NOT yet in README.v, which indexes UNCONDITIONAL paper claims.
⚠️⚠️ *(Superseded 2026-08-03, later: the "KNOWN-TRUE" reasoning was circular
at the paper theorem's over-quantification of `P0`, and `main_forall` is now
REFUTED — `cex/probe_double_occ_run.v`, see the top entry.)*

## 2026-08-03 — ⭐⭐⭐ **Flex-SkipTmVar LANDS**: the paper's missing subtyping-walk rule is added tree-wide, and the tree is green

`make coq` green, admit-free, axiom-free.  The authors' call on the gap found
earlier today (see the entry below) was to add the rule, so it is added — in
the paper's own idiom, as verbatim mirrors of the twin walk's
`Assign-SkipTmVar` (full-algo-spec.tex:1791):

```
                    Θ₀ ∣ Ξ  ⊢[N][FN M][P₀] α̂ ⩽ Q ⊣ Θ₁
  ──────────────────────────────────────────────────────── Flex-SkipTmVar
   Θ₀, x:Q' ∣ Ξ  ⊢[N][FN M][P₀] α̂ ⩽ Q ⊣ Θ₁, x:Q'
```

**DEFINITIONS.**  `a_sub_flex__skip_tm_var` / `__skip_tm_skl`
(`algo/def_rules.v`) plus the decorated mirrors on `a_subtag_flex`
(`algo/def_decorated.v`).  The mech splits the paper's single `x : P` entry
into a type binding and a skeleton binding, hence two rules for the paper's
one.

**THE THREE MUTUAL INDUCTIONS OVER THE PAIR**, each +2 cases, each a mirror of
Flex-SkipRigid: the soundness bundle (`prop_sub_sound.v`, with
`a_isub_cons_var_typ` / `_var_skl` for the increase and `a_wf_ptyp_isub` /
`a_scope_pskl_isub` for the re-attached entry's wf), the decoration bundle
(`prop_soundness_sub.v`), and equivariance (`prop_swap.v`).

⭐ **THE ONE THING THE RULES DO NOT CARRY** — and the twin walk's does not
either — is a freshness premise for `P0`.  Both `a_wf_pskl_strip_mid`
consumers need `x ∉ ftv P0`, and it is DERIVED rather than premised: a term
entry is never `a_binds_tvar`, so under `uniq` no free variable of a
well-formed `P0` can be it.  Four lines at each consumer
(`a_wf_pskl_ftv_tvarish` + `binds_unique`).  Do not add it to the rules.

**THE COUNTEREXAMPLE, RESTATED SO IT SURVIVES THE REPAIR.**
`cex/cex_p7_flex_walk_tm_var.v` now proves the new rule is the ONLY one that
fires at a term head (`a_sub_flex_tm_var_head_is_skip_tm_var`), and its
witness is a solvable problem EVERY run of which goes through it
(`complete_subtyping_needs_flex_skip_tm_var`) — so with the five printed rules
it has no run at all.  That is the permanent record of why the rules are
needed.

⭕ **STILL OWED: P7a's two COMPLETENESS rows.**  They are why `sub_flex_complete_holds` still
carries `a_sub_flex_walkable Θ0`.  Their shape is fully determined
(DESIGN §12.3): `a_inc__var` / `a_inc__var_skl` shrink the `a_inc` TARGET
exactly as `a_inc__tvar` does, so each row is
`a_sub_flex_complete_skip_rigid`'s ⇓-truncation apparatus with the tvar pieces
swapped (`a_inc_var_inv`, `a_inc_var_mid_strip_id`,
`a_inc_equiv_mid_insert_var`, `a_wf_aenv__var_typ`) and both of SkipRigid's
premises DERIVED.  ⚠️ The one genuinely new obligation is the **SEMANTIC
MIDDLE** `Θ' ⊢ A' ≡ᵗ κ A`, which a rigid entry does not have; the consistency
twin's `Assign-SkipTmVar` case proves exactly it
(prop_consis_complete.v:5595-5690) and is the model.  ⚙ One extra step beyond
the twin: the subtyping row re-attaches through the JUNK SWAP, so the
increase's witness is `kswap_msubst β β1 ζ` — close the gap with
`msubst_ptyp_kswap`, whose hypotheses are free because the payload is scoped
in `Θ0`.

## 2026-08-03 — ⭐⭐⭐ P7c: **ALL THREE LAYERS LAND** (stuck-check, flex half, twelve-row join dispatch) — and a MACHINE-CHECKED PAPER GAP the implementation crashes on

`make coq` green, admit-free, axiom-free.  `frost/algo/prop_sub_complete_dispatch.v`
is now 1093 lines, §1–§10, everything `Qed` and *Closed under the global
context*; it still compiles in <1 s.  Five row-lemma HYPOTHESES in
`prop_sub_complete_thm.v` were weakened to match what the assembly can supply
(the lemmas are otherwise untouched, and the file still compiles in 65 s).

**⭐ §5 — THE STUCK-CHECK IS CLOSED** (`sub_flex_rigid_head_absurd`), the piece
DESIGN §12.1 marked "build this first".  A rigid head `β` with `β ∈ ftv P0`
matches no `a_sub_flex` rule, so the dispatcher must refute it from the
solution.  The chain is NOT consistency's — there the pattern IS the join's
subject, here `P0` sits on the FILL side and the join's subject is `κα̂` — and
its last step, "the SUBJECT confines the TARGET", is FALSE for the join in
general.  ⭐ **What makes it true is that the walk's subject is a MONOTYPE, and
P7a's `Flex-SkipRigid` row had already built exactly that confinement**:
`sub_gv_bskl_downarrow_mono_scoped` composed with the fill's
`refine_syn_f_downarrow_source_ftv`.  The ⇓-form is also what absorbs the
motive's ≡ᵘ slack — `≡ᵗ` does not preserve ftv-scoping but it *does* preserve
⇓ (`a_tyequiv_downarrow`).  So the refutation is steps 0–4 of
`a_sub_flex_complete_skip_rigid` re-read as a refutation, plus
`rigid_survives_solution` and `β ∉ dom Θ'`.  **No new induction was needed.**

**§3/§4 — the transfer, completed, and the OTHER half of the arrow escape.**
`msubst_uskl_syn_var_inv` (only a variable's image is a variable) and
`msubst_uskl_syn_all_syn_inv_mono` (the ∀-escape closes once the images are
known to be MONOTYPES, which `a_inc` supplies).  §4 refutes a RIGID variable
subject at the `__arrow` row: `κ` never touches a rigid variable, a rigid
variable is its own ⇓-normal form (`downarrow_rigid`, on the new
`aenv_msubst_dom_flex`), and ⇓ of an arrow is an arrow.

**§7 — THE FLEX HALF (`sub_flex_complete_holds`), DESIGN §12.1's layer (b).**  Structural
induction on `Θ0` with the suffix `Ξ` GENERALIZED and the total context length
bounded: Flex-Depend keeps the total and shrinks `Θ0` (the structural IH),
Skip/SkipRigid shrink both, Flex-Assign consumes the definition and re-enters
the main half ONE ENTRY SHORTER, Flex-Solve re-enters it at an ARROW subject
over a LARGER context.  That last edge is why the five hypotheses moved:
depend/skip/skip_rigid's walk IH gains `length Ξ' <= S (length Ξ)`, assign's
cross-half IH gains `length Θ0' <= length Ξ + length Θ0`, and **solve's
cross-half IH is restricted to an ARROW subject** — the only thing that breaks
§12.1's non-decreasing cycle.

**§9 — THE MAIN HALF's TWELVE-ROW JOIN DISPATCH (`sub_complete_assemble`), layer (c).**
Nine rows delegate to their `Qed` row lemma (fuel IH where the row consumes
fuel); the two UnivGhostL rows and `__flex_mono` preserve the fuel and are the
structural IH's work (`⌊∀◈R⌋ˢ` IS `∀◇⌊R⌋ˢ`, so both ghosts use the one
`a_sub__univ_ghost_l`; `__flex_mono` is a pure peel closed by
`flex_def_paint_tyequiv` + `a_uskl_tyequiv_trans`).  ⭐ **The P7a escape is
carried by an ABSTRACT predicate `PIH` on the motive's subject, with three
closure conditions** — that is what lets ONE dispatch serve both layers:
instantiate `PIH` with "is an arrow" and all three become vacuous (an arrow is
neither `∀◇` nor `∀◈` nor a variable), so the tophole-stripping rows can never
expose a variable subject and P7a is unreachable.  That is `sub_complete_arrow_holds`,
**layer (a), from the FUEL IH alone**, and it is exactly what
`a_sub_flex_complete_solve` now takes.

**§8 — the CHECK row's one obligation, `guarded_pskl P0`, discharged.**  Mode
compatibility gives `P0 = ptyp_to_pskl A`; a ∀-headed `A` is refuted against
the FILL by the new `ad_refine_syn_f_all_inh_l_shape` — a `bskl_all_inh`
SOURCE refines only to a `bskl_all_inh` TARGET (only `__all` and `__flex_r`
have such a source, and `__flex_r`'s chain cannot bottom out because a
monotype painting is never ∀-inh) — while the Check row's counterpart is
guarded.  This is the SOURCE-side mirror of `ad_refine_syn_f_all_inh_r_shape`.

### ⭕ WHAT REMAINS — two obstacles, and NEITHER is mechanical

**⛔ (B) A PAPER GAP — MACHINE-CHECKED, AND THE IMPLEMENTATION CRASHES ON AN
ORDINARY PROGRAM: the flexible SUBTYPING walk has NO rule for a TERM-VARIABLE
head** (docs/PAPER-GAPS.md; `cex/cex_p7_flex_walk_tm_var.v`,
`complete_subtyping_false_at_a_term_variable_head`, Qed + axiom-free — the
problem side holds, a solution exists, and no run does).  `met.exe` on
`let f = fun x -> x 1` traces `I-Abs / I-App / I-Var / SI-FlexMono` and then
dies with `Failure("broom_flex_poly: should not happen")`; `fun g -> fun y ->
g y` and `fun g y -> g (g y)` are identical.  The trigger is exactly "apply a lambda-bound variable whose
type is still an unsolved flexible".  `fig:alg-subtyping`'s
second box has five rules and none matches an `x : P` entry, while the paper's
TWIN walk has `Assign-SkipTmVar` (full-algo-spec.tex:1791).  Nothing in
`thm:complete-subtyping`'s problem definition excludes a term entry above the
subject, and the configuration is reachable (check a lambda against a guessed
`α̂`: the split pushes `x : α̂1` above earlier flexibles).  **The reference
implementation agrees with the paper and therefore shares the gap** — `assign`
has `U-Assign-SkipTmVar` (type.ml:386-390), `sub_flex` falls through to
`Errors.type_mismatch` (type.ml:1047-1050).  The repair is `Flex-SkipTmVar` in
the paper's own idiom, but it is a RULE change: `a_sub_flex` + `a_subtag_flex`
each gain two constructors, three mutual inductions reopen
(`prop_sub_sound.v`, `prop_soundness_sub.v`, `prop_swap.v`), and P7a gains two
rows carrying `Flex-SkipRigid`'s whole ⇓-truncation apparatus (the consistency
twin's two cases are ~670 lines).  So it is the authors' call, and `sub_flex_complete_holds`
carries the explicit premise `a_sub_flex_walkable Θ0` meanwhile.  ⚠️ It cannot
simply be carried to the bundle: the row lemmas' fuel IH is the UNRESTRICTED
motive, so the restriction would have to move INTO `sub_complete_concl` and
every row would owe walkability of the contexts it recurses at.

**⭕ (A) `main_forall n` — the two ForallL rows**, isolated as the single
residual hypothesis of `sub_complete_assemble`.  It bundles TWO independent problems:

  * **A1** — TASK 0's `sub_shield`.  Unchanged: `prop_sub_shield_supply.v`
    covers flex-free / atomic / mono-counterpart / inh-free-counterpart /
    ∀-free `P0`; a `P0` with a ∀ below its head has no general route.  (The
    premise is machine-checked SATISFIABLE at the node that used to refute it,
    so this is a missing SUPPLY, not a falsity.)
  * **A2** — the ForallL rows also demand `guarded_pskl P0 \/ P0 = ◇`, and at
    `NM = TY` with `M = TC` that is not derivable: `a_ty_mode_compat mode_tc
    P0` admits a ∀-headed `P0`, and §8's refutation does not transfer (it uses
    the Check row's GUARDED counterpart; ForallL's is arbitrary).  **The
    join's last rule does not determine the algorithm's rule** — ForallL fires
    on a ∀ SUBJECT, ForallR on a ∀ INPUT, and a ∀-headed `P0` blocks ForallL by
    its own premise.  ⭐ **The paper HANDLES this**, in one sentence
    (subtyping-proofs.tex:3385): *"Since declarative subtyping is congruent, we
    assume WLOG that guarded(P0) ∨ P0 = □; otherwise we apply ForallR first."*
    What that WLOG costs mechanically is a JOIN-PERMUTATION lemma — extract the
    ForallR family from a ForallL-rooted join with a `bskl_all_inh` target.
    Recorded as a proof-step note (not a defect) in docs/PAPER-GAPS.md.

With A and B discharged the bundle is a three-line assembly: strong induction
on the fuel, then on `length Θ0`; (a) from the fuel IH, (b) from (a) plus the
main half at shorter contexts, (c) from the fuel IH plus (b) at `Ξ = ·`.

## 2026-08-03 — 🚧 P7c SCOPED AGAINST THE TREE: the shape-transfer kit lands, and §12's INDUCTION IS REFUTED

`make coq` green, admit-free, axiom-free.  New file
`frost/algo/prop_sub_complete_dispatch.v`: §1 is proved (Qed, axiom-free), §2
is the scoping, and docs/DESIGN-completeness-subtyping.md §12.1 carries it in
prose.  **The dispatcher itself is NOT written** — see the two open obligations
at the end.

**§1, THE SHAPE TRANSFER (proved).**  What the join does not fix is the
motive's unresolved subject `R`; only the ≡ᵘ slack `Θ ⊢ R' ≡ᵘ κR` ties them.
`msubst_uskl_syn` is structural except at a free variable, where it installs a
MONOTYPE PAINTING — and a painting is `unit` / a variable / an arrow, never a
∀, never a ghost.  So a κ-image of any other shape PINS the pre-image, and the
transfer is total at every join row except `__arrow`, where `R` may instead be
a bare flexible whose IMAGE is the arrow.  ⭐ **That is the one and only entry
into P7a.**  The `unit` case of the arrow row is not syntactic: `arrow ≡ᵘ unit`
dies only through ⇓ (`a_tyequiv_downarrow` is a congruence and `⇓(A→B)` is an
arrow), which is what `a_uskl_tyequiv_arrow_l_inv` does.

**⚠️⚠️ §12's INDUCTION IS WRONG — lex(fuel, |Θ0|) does not work.**  The two
halves call each other at the SAME fuel: `a_sub__flex_mono` enters P7a at the
same context, and P7a's `Flex-Solve` re-enters P7b at the same fuel with a
context TWO ENTRIES LARGER (it deposits `α̂0 ≔ α̂→β̂` plus the two fresh
flexibles, prop_sub_complete_thm.v:4586).  Neither component decreases on that
cycle.  ⭐ **What breaks it is the SUBJECT**: Flex-Solve re-enters at `α̂ → β̂`,
an ARROW, and a main call at an arrow subject can never come back into P7a —
the escape needs a VARIABLE subject and no join row shrinks an arrow to a
variable.  The layering that works: (1) the main half at an ARROW subject from
the fuel IH alone; (2) the flex half at `|Ξ ++ Θ0| = k` by an inner induction
on `|Θ0|`, using (1) for Flex-Solve and the main half at `k-1` for Flex-Assign;
(3) the main half at `k`, using (2) for the escape; (4) strong induction on `k`,
then on the fuel.

**⭕ TWO OPEN OBLIGATIONS, neither mechanical.**

1. TASK 0's residual at the two ForallL rows.  The premise is now positionally
   indexed and machine-checked SATISFIABLE at the node that used to refute it,
   but `prop_sub_shield_supply.v` still discharges it only for a flex-free /
   atomic / mono-counterpart / inh-free-counterpart / ∀-free `P0`.  A `P0` with
   a ∀ below its head has no general route, so the dispatcher takes it as a
   hypothesis (§12 item 3).

2. **P7a's STUCK-CHECK, and it is NOT consistency's.**  A rigid head `β` with
   `β ∈ ftv P0` matches no `a_sub_flex` rule, so the dispatcher must refute it
   from the solution.  Consistency's twin works because THERE the pattern IS
   the join's subject; here `P0` sits on the FILL side and the join's subject
   is `κα̂`, so the chain is `β ∈ ftv P0 ⟹ β ∈ ftv (κP0) ⟹ β ∈ ftv Q ⟹
   β ∈ ftv (κα̂)`, whose last step is "the SUBJECT confines the TARGET" — FALSE
   for the join in general (`ad_pat_sub_gv__ghost` gives a ◇ subject an
   arbitrary target).  It must be re-derived for the MONOTYPE subject the walk
   actually has, where every row carries a refinement premise off the subject's
   HOLE-FREE erasure.  **This is the piece to build first.**

## 2026-08-03 — ⭐⭐⭐ `sub_shield` **RE-INDEXED POSITIONALLY** and `fa_walk` **SPLIT**: the over-strong premise is repaired, tree-wide

`make coq` green, admit-free, axiom-free.  This lands the repair the entry
below diagnosed, and machine-checks it AT THE VERY WITNESS that refuted the old
premise (`cex/cex_p7_shield_realizable.v`, `p7_sub_shield_repaired_holds`).

**PART B first, because it decides everything else** (DESIGN §14.3 had it only
hand-verified).  `fa_step` carried two rows, `fastep_p0_arrow_{l,r}`, that
descended `P0` with the GUESS FIXED — they existed solely so
`flex_apart_walk_p0` could hand P6-Cs its own P0-only closure out of P6-Ss's
walk.  Composed with `fastep_all_r` (Sub-ForallL, which OPENS the guess and
grows Δρ) they reach `(α̂, β→β)` at `β ∈ Δρ`, where nothing applies — that was
`apart_w_fails`.  ⭐ **Without them the root obligation is SATISFIABLE**, and
the proof is a general closure argument, not a witness-specific one: the
invariant is `tag_free ψa ∧ (ψa is Δρ-clean ∨ ψa is an arrow-spine of
Δρ-variables matching P0's)`, closed under every remaining step — `fastep_all_r`
is VACUOUS on it (an ε-tagged ∀ is not `tag_free`), and `fastep_flexdef_r`
re-enters the clean branch because a monotype PAINTING carries no tag.

**THE SPLIT.**  `fastep_p0_arrow_{l,r}` and `flex_apart_walk_p0` are DELETED.
`flex_apart_deep` — P6-Cs's Δρ-CONSTANT closure — is now an independent
`sub_shield` conjunct instead of a consequence of `flex_apart_walk`.  The two
are compatible *at a `sub_shield` position* precisely because that definition's
Δρ' quantifier keeps ψa clean for whatever Δρ' adds, which `fastep_all_r` does
not.

**THE POSITIONAL RE-INDEXING (Part A).**  `ss_step` / `ss_walk` now step `P0`
and the SUBJECT in lockstep and carry the looked-for `α`: `sss_arrow_r` moves
both, `sss_all` moves P0 (Sub-ForallR), `sss_forall_l_{syn,tag}` and
`sss_univ_ghost_l{,g}` move the subject.  The premise reads

    sub_shield Θ0 Ψ' Δρ α P0 R ψa :=
      forall P0' R' Δρ', ss_walk (dom Θ0) α P0 R P0' R' ->
        Δρ [<=] Δρ' -> Δρ' ∩ ftv ψa [<=] Δρ ->
        flex_apart_deep Θ0 Δρ' P0' ψa
        /\ (α ∈ ftv R' -> flex_apart_walk Θ0 Δρ' P0' ψa
                          /\ flex_shield Θ0 Ψ' Δρ' P0' ψa)

⚠️ **The guard applies to EXACTLY TWO of the three closures**, and this is the
one place §14.2's sketch was wrong.  `flex_apart_deep` never descends the guess,
so it is harmless anywhere — and it MUST stay unguarded, because P6-Ss's Check
and Arrow rows hand it to P6-Cs at positions where `α` does not occur at all
(P6-Ss's own premise is `α ∉ ftv P ∨ P = α`, so `α` occurs only at the LS-Var
leaf).  The two closures that DO descend the guess (`fastep_all_r` /
`fsh_all_r` open ψa and grow Δρ) are the ones the witness refutes, and the guard
is FREE exactly where they are consumed — the LS-Var row, where `R' = α`.

**ROW MAP** (P6-Ss, `prop_look_complete_sub_cstr.v`): LS-Var takes both guarded
conjuncts (guard free); Check and Arrow-left take `flex_apart_deep` via the new
`sub_shield_here_p0`; Sub-ForallR steps by `sss_all`; Sub-Arrow-right by
`sss_arrow_r` + `_weaken_flex_prefix`; the two Sub-ForallL rows now ALSO step
the SUBJECT (`sss_forall_l_tag` / `sss_forall_l_syn`, premise `β <> α`, already
on hand as `Hβα`) before `_add_fresh` + `_weaken_tvar`; the two UnivGhostL rows
gained a `sub_shield_step` each (the subject moves, P0 stands still).

**P7b's ForallL rows** now take the premise at the SUBJECT they hand P6-L:
`forall α, sub_shield Θ0 Ψa ∅ α P0 (open Rb α) ψa`.  ⚠️ The `forall R` form is
NOT available — it is over-strong at the same witness (take `R = unit → α`,
which walks the guess onto a raw flexible it never meets;
`sub_shield_forall_flex_p0_fails` is now stated in exactly that form, and is the
BOUNDARY the guard exists to respect).  Every supply route
(`prop_sub_shield_supply.v`) is uniform in `α` and `R`, so it discharges it:
tag-free / atomic / flex-free / inh-free / ∀-free all still apply, with
`flex_apart_deep` free from `flex_apart_deep_clean` at Δρ = ∅.

⭐⭐ **THE DECISIVE CHECK.**  `p7_sub_shield_repaired_holds` (Qed, axiom-free)
proves the repaired premise, in exactly the form P7b's rows take, AT the §14.1
witness — where `p7_sub_shield_is_over_strong` (restated: the configuration is
inhabited AND both guess-descending closures fail at the CODOMAIN) refutes the
old one.  Part A kills the codomain obligation (subject `unit`, guard unmet);
Part B makes the root one true.

⚠️ Nothing goes to docs/PAPER-GAPS.md — `sub_shield` is mech-invented — and
neither P6-Sv nor P6-Ss changed statement beyond the premise's index.  ⭕ P7c's
two ForallL cases are UNBLOCKED; the dispatcher (§12) is the remaining work.

## 2026-08-03 — ⚠️⭐⭐⭐ TASK 0's residual is **REALIZABLE**: `sub_shield` is OVER-STRONG, and P7c's dispatcher is blocked on it

`make coq` green, admit-free, axiom-free.  `frost/algo/cex/cex_p7_shield_realizable.v`
(both theorems `Qed`, *Closed under the global context*).

**The question.**  `cex_p7_shield_forall_flex.v` (2026-08-02) settled the
FALSITY half — at a raw Θ0-flexible facing a TAGGED ∀ with a COMPOUND body,
`flex_shield` and hence `sub_shield` are UNDERIVABLE — and left REALIZABILITY
open: can P7b's Sub-ForallL rows actually be REACHED with such a `(P0, ψa)`
pair and `ε ∈ Ψa`?  **They can.**

**The witness** (`Θ0 = α̂`, `κ = α̂ ↦ unit`, `Θ = Θ0`):

    P0 = (∀γ. γ→γ) → α̂        a ∀ BELOW the head AND a walk-reachable raw flexible
    R  = ∀^t. (□₀ → unit)      the subject: one tagged ∀
    ψa = ∀^e β. β→β            the guess — TAGGED, with a COMPOUND body
    Q  = (∀ᵢ. β→β) → unit      the counterpart

`p7_sub_shield_is_over_strong` machine-checks, at that configuration: the whole
completeness input (wf of `Θ0`/`P0`/`P`/`⌊Q⌋`, `skmod[TY]{P0}{FN TC}`,
`guarded P0`, `ghost-free R`, `⌊R⌋ˢ = P`, `κ ∷ Θ0 ⊑ Θ`, the `≡ᵘ` slack), the
JOIN (`ad_pat_sub_gv 2` ending at `__forall_l_tagged` with exactly this `ψa`,
plus its `a_tags_sort` / disjointness / wf side conditions and the sub-join),
the FILL — and `~ sub_shield Θ0 {e} ∅ P0 ψa`.

⭐ **Why it goes through, and why the obvious probe does not.**  The tag `e` has
exactly ONE way to be discharged — `ad_pat_consis__forall_inh_tagged`, a tagged
∀ in the subject facing an INHERITED ∀ in the counterpart — and the counterpart
is pinned by the FILL, so `Q`'s inherited ∀ can only come from a ∀ in `P0` (κ's
images are monotypes; `__hole` / `__tophole_fill` emit `bskl_all_syn`, not
`_inh`).  Its BODY is therefore whatever `P0`'s ∀-body refines to.  With
`P0 ⊇ ∀γ.γ` that body is a bare VARIABLE and a compound guess is stuck (which is
why `fsh_rho_var` exists and why the first probe looked unreachable); with
`P0 ⊇ ∀γ.γ→γ` it is an ARROW and the guess goes through.  The residual is
realized by the SAME shape that makes the shield false.

⭐ **And the dispatcher has no way around it.**  `join_at_Rw_is_forall_l` shows
the join at that node can only have ended with `__forall_l_tagged`: `__infer`
wants `mode_ti`; `__check` / `__univ_ghost_r` want a GUARDED subject and a ∀ is
not; `__forall_r` / `__univ_ghost_r` want a ∀-inh / tophole counterpart and this
one is an arrow; every other row wants another subject shape.  So P7c MUST
apply the ForallL row there, and its `sub_shield` premise is false.

**Consequences.**  ⚠️ Nothing is refuted in the paper and nothing goes to
docs/PAPER-GAPS.md: `sub_shield` is a MECH-INVENTED repair premise (P6-Sv's),
not a paper statement.  P6-Sv and P6-Ss stay `Qed` — their premise is merely
stronger than it needs to be.  What must change is the INDEXING: `sub_shield`
pairs EVERY walk-reachable `P0`-part with the WHOLE guess, while the derivation
aligns `ψa` with ONE position (here the arrow's DOMAIN, where the tag is
legitimately discharged) and the shield is demanded at the CODOMAIN, a raw
flexible that guess never meets.  **The repair is a POSITIONAL re-indexing**,
replayed through P6-Ss and P7b's two ForallL rows, which consume the current
shape.  ⚠️ Trimming the `ss_walk` closure is NOT an alternative: P6-Ss's
Sub-Arrow row consumes it directly (prop_look_complete_sub_cstr.v:1546-1548).

So P7c is blocked until the re-indexing lands, and building the dispatcher's two
ForallL cases before it would be wasted work.  The other ten cases are
independent of the shield.  See docs/DESIGN-completeness-subtyping.md §14.1.

⚙ Ltac hazard, paid for once: `eapply <lemma-with-implicit-args>; auto` HANGS
when the lemma's implicit arguments are still evars — `auto` searches with
unresolved metavariables.  Build the premises as named `assert`s and close with
an evar-free `exact`/`apply … with (x := …)`.  Also: `repeat split` CLOSES a
reflexive equality goal (`eq` is a single-constructor inductive), so a bullet
list after it silently shifts.

## 2026-08-03 — ⭐⭐⭐ **P7a IS COMPLETE**: `Flex-SkipRigid` CLOSED (`a_sub_flex_complete_skip_rigid`, `Qed` + axiom-free) — all FIVE rows done

`make coq` green, admit-free, axiom-free; `prop_sub_complete_thm.v` reports 27
`Print Assumptions` sites, all *Closed under the global context*.

**The row.**  `Flex-SkipRigid` is the one row `a_inc`'s POSITIONALITY makes
different: `a_inc__tvar` shrinks the TARGET, so
`κ ∷ (Ξ ++ (β ~ tvar) ++ Θ0) ⊑ Θ` forces `Θ = Ξv ++ (β ~ tvar) ++ Θ'` and the
IH must run at the TRUNCATION `Θ'` (`κb ∷ Θ0 ⊑ Θ` is FALSE, not merely
unproved).  Every solution-side premise therefore has to move to `Θ'`, and
§(L)'s three strengthenings all take `ftv · ⊆ dom Θ'` as a HYPOTHESIS.  The
route is ⇓-NORMALIZE (the junk block `Ξv` above β is exactly what ⇓ unfolds),
then STRENGTHEN — §(L0) for the join, §(L1) (new, below) for the fill, §(L) for
the move.  The rest is the consistency walk's `Assign-SkipRigid` transcribed
(prop_consis_complete.v:5091-5355): `a_inc_downarrow_prefix` over the
Ξ-images, the junk swap for the rule's Barendregt premise `β ∉ dom Θ1`, and
`a_inc__tvar` / `a_inc_equiv_mid_insert_tvar` / `a_inc_equiv_self_downarrow`
for the package.

**§(L1) — three new lemmas, the ones the consistency walk does NOT need.**

- `refine_syn_f_downarrow` — the FILL moves to `(⇓ᵇ source, ⇓ᵇ target)`.  Unlike
  §(L0)'s two leaf normalizations the source `κP0` is NOT a monotype, so the
  induction covers every row: `__hole` needs wf under ⇓ (`a_wf_pskl_downarrow`,
  also new — `a_wf_pskl_msubst_inc` re-cut with the two facts ⇓ supplies
  directly, `aenv_msubst_image_wf` and `aenv_msubst_image_mono`), the ∀ rows
  need the open-commutation, and the two `__flex_*` rows are the chases ⇓ has
  already performed.
- `refine_syn_f_downarrow_source_ftv` — the ⇓-normalized SOURCE is scoped by
  the ⇓-normalized TARGET.  This is what turns the join's confinement into
  §(L)'s hypothesis for BOTH sides of the fill.  It is FALSE without the ⇓:
  `__flex_l`'s source is a bare variable whose definition is the premise's
  source, and only under ⇓ are the two literally the same term.
- ⭐ `ad_precise_downarrow` : `Θ ⨟ Δ ⊢ₚᵣᵃᵈ ⇓ˢ[Θ]P ⊑ P`.  **The one obligation the
  consistency walk does not have**: P7a's motive carries a PRECISION conjunct,
  so the IH proves it against `⇓ᵇQ` and the conclusion wants it against `Q`.
  The handover's planned route (`skl_tyequiv_refine_syn_f_transport`) does NOT
  apply — that transport moves the refinement's SOURCE and the precision's `Q`
  is its TARGET.  What works instead is composition: weaken `Θ' → Θ`
  (`ad_refine_syn_f_empty_intro` → `_weaken_ctx` → `_forget`), then
  `ad_refine_syn_trans` against `⇓ˢ⌊Q⌋ ⊑ ⌊Q⌋`.  ⭐ The lemma's own crux — the
  variable row, where re-folding a definition recurses into the definition's
  own definitions and is therefore NOT structural — is delegated wholesale to
  `tyequiv_mono_refine_syn` + `a_tyequiv_to_downarrow_mono`, which already do
  that recursion at the TYPE level.  With that, the induction is structural in
  `P` and mirrors `ad_refine_syn_refl_inh` line for line.

**⚠️ ONE MOTIVE CHANGE, and it is a STRENGTHENING of a premise.**
`sub_flex_complete_concl`'s flexibility premise moved from
`a_flex_tvar (Ξ ++ Θ0) α` to `a_flex_tvar Θ0 α` — the subject lives in the
SHRINKING half, not in the walked suffix.  That is the walk's own invariant
(`a_sub__flex_mono` enters at `Ξ = ·`; `Flex-Depend` moves only a `β ≠ α` into
Ξ; `Flex-Skip`/`Flex-SkipRigid` drop only a `β ≠ α`), it is what the
consistency motive `assign_complete_at` already states, and the entry point
supplies it verbatim, so NO downstream statement changed.  It is load-bearing
at `Flex-SkipRigid` ONLY, where it gives `α ∉ dom Ξ` hence `α ∉ dom κa`, so the
subject's image is read off the TRUNCATED increase `κb ∷ Θ0 ⊑ Θ'`.  ⭐ Read off
the Ξ-block instead the argument is CIRCULAR: Ξ's images are confined only by
the join's ⇓-confinement, and that confinement's hypothesis IS the subject's
scope.  (Enlarging the confinement's `D` to `dom Θ' ∪ ftv(⇓ᵗκα̂)` does not break
the circle — it makes the Ξ-bound a tautology and `a_inc_downarrow_prefix` still
wants `dom Θ'`.)  Cost of the change: four one-line repairs (a head-strip in
`Flex-Depend`/`Flex-Skip`, an `a_flex_tvar_app_weaken` in `Flex-Assign`;
`Flex-Solve` never used the premise).

**WHAT REMAINS FOR P7.**  The DISPATCHER (§12) — the lex(n, |Θ0|) well-founded
induction proving `a_sub_complete_bundle` by peeling each rule and feeding the
matching row.  All seven P7b rows and all five P7a rows are `Qed`, so this is
assembly, not new machinery — with ONE genuinely new obligation, which no row
carries because no rule has it as a premise: the **STUCK-CHECK**.  A RIGID head
β with `β ∈ ftvar_in_pskl P0` matches no `a_sub_flex` rule at all
(`__depend` wants β flexible, `__skip_rigid` wants `β ∉ ftv P0`), so the
dispatcher must REFUTE that configuration from the solution — the
subtyping-level twin of `rigid_survives_solution` +
`ad_pat_consis_rigid_ftv_rev_scoped` (prop_consis_complete.v:5060-5090, where
the consistency walk pays exactly this).

## 2026-08-03 — 🚧 P7a `Flex-SkipRigid`: §(L0) is COMPLETE for the JOIN — confinement, both leaf normalizations, and `sub_gv_downarrow_mono`

`make coq` green, admit-free, axiom-free.  This is the first increment on the
last open row of P7a; the row itself is not closed.

**What was blocking.**  `Flex-SkipRigid` must run its IH at the truncation
`Θ'` that `a_inc_tvar_inv` hands back (`a_inc__tvar` shrinks the TARGET, so
`κ' ∷ Θ0 ⊑ Θ` is FALSE), and §(L)'s three strengthenings all take
`ftv Q [<=] dom Θ'` as a HYPOTHESIS.  That is not derivable of `Q` itself:
`ad_pat_consis__flex_r` and `ad_refine_syn_f__flex_r` let the counterpart be
an arbitrary DEFINED flexible of Θ, so `Q` may name one of the junk block
above `β`.  It IS derivable of `⇓ᵇ[Θ] Q`, which unfolds exactly those — which
is why the consistency walk normalizes before it truncates.

**What landed** (`prop_sub_complete_thm.v` §(L0), all `Qed`,
*Closed under the global context*).  The MIRROR of
`join_pskl_downarrow_mono_scoped`.  In the consistency walk the monotype is
the COUNTERPART (`syn{κα̂}`) and the lemma scopes the ⇓ of the SUBJECT; the
flexible SUBTYPING walk has it the other way round — its subject IS the
monotype — so the mirror scopes the ⇓ of the COUNTERPART:

- `consis_bskl_downarrow_mono_scoped` — over `ad_pat_consis`.  Each row either
  pins `Q` to the subject's variable (`__var`), recurses (`__arrow`), chases a
  definition (`__flex_l` / `__flex_r`, which is exactly what ⇓ unfolds), or is
  excluded because a monotype painting is never a ∀, a hole or a tophole.
- `sub_gv_bskl_downarrow_mono_scoped` — over `ad_pat_sub_gv`.  Every row a
  monotype-painting subject admits ties `Q` to the subject through a
  consistency leaf (Infer / Check / UnivGhostR / Arrow's domain), recurses
  (Arrow's codomain, ForallR, FlexMono), or is shape-excluded (both ForallL
  rows, Ghost / GhostG, UnivGhostL / LG).

Plus the plumbing: `⇓ᵇ[Θ]` (= `msubst_bskl (aenv_msubst Θ)`),
`msubst_bskl_ptyp_to_bskl_syn`, `ftvar_in_bskl_ptyp_to_bskl_syn`,
`aenv_msubst_tvar_cons`, `msubst_bskl_open_rec_ftv_lower` (ForallR opens the
target under a fresh rigid binder), `msubst_bskl_ftv_fresh` and
`aenv_msubst_image_dom`.

⚙ The `ad_pat_consis` half would sit just as well beside its mirror in
prop_consis_complete.v; it is here because P7a is its only consumer and
because editing that file forces a ~10-minute rebuild of the whole algo tree.

⚙ The confinement's hypothesis is stated on `⇓ᵗ[Θ] A`, not on `A`.  That is
what the consumer actually has — the walk knows its subject only up to `≡ᵗ`
(`a_uskl_tyequiv_mono_r_inv` hands back a monotype painting `syn{τ'}` with
`Θ ⊢ κα̂ ≡ᵗ τ'`, and `≡ᵗ` does NOT preserve ftv-scoping, only ⇓
(`a_tyequiv_downarrow`)).  It is also strictly more general (with a def-closed
`D`, `ftv A ⊆ D` gives it via `downarrow_ftv_closed`) and it makes the
def-closedness side condition unnecessary: the definition-chasing rows now
discharge it by `aenv_msubst_lookup_def` alone.

**The ⇓-NORMALIZATIONS** (same day).  The confinement scopes `⇓ᵇ Q`; to USE it
the leaf has to hold at the normalized pair.  Both are the same shape and both
are SMALL, because at a monotype subject only five rows are reachable — unit,
var, arrow and the two definition chases — and ⇓ is the identity on the first
three and exactly the chase on the last two:

- `consis_downarrow_mono` : `Ψ ⨟ Θ ⊢ᵃᵈ syn{A} ∼ Q` ⟹
  `Ψ ⨟ Θ ⊢ᵃᵈ syn{⇓ᵗA} ∼ ⇓ᵇQ`.  The `var` row is where both sides collapse to
  the same monotype, so it is `consis_mono_refl`.
- `refine_pskl_downarrow_mono` : the same for the refinement leaf
  (`ad_refine_pskl` at a monotype source), via
  `ad_refine_pskl_f_mono_refl` + `_forget`.
- plus `bskl_to_pskl_msubst_bskl` — the leaves state their refinement on
  `⌊·⌋ˢ` / `bskl_to_pskl`, so ⇓ has to pass through the erasure.

⭐ **`sub_gv_downarrow_mono`** (same day) closes §(L0) for the JOIN: the whole
`ad_pat_sub_gv` derivation moves to `(syn{⇓ᵗA}, ⇓ᵇQ)`.  At a monotype-painting
subject the reachable rows are Infer / Check / ForallR / UnivGhostR / Arrow /
FlexMono, and each delegates to a leaf normalization, recurses, or chases a
definition ⇓ has already resolved.  Its plumbing: `msubst_bskl_open_rec_lc` /
`_open_lc` (ForallR opens the target under a fresh rigid binder — the
commutation must be an EQUALITY here, not the ftv inclusion the confinement
used), `is_sskl_ptyp_to_bskl_syn` / `is_sskl_msubst_bskl`,
`msubst_bskl_pskl_to_bskl_inh` (the two paintings agree on MONOTYPE images —
`mono_inh_eq_syn`), `msubst_{pskl,bskl}_lc_of_msubst_lc` and
`guarded_{pskl,bskl}_msubst_mono`, and `ptyp_to_uskl_syn_arrow`.

⚙ Two Ltac hazards, both paid for twice.  (i) `simpl`/`cbn` UNFOLD
`ptyp_to_uskl_syn` as soon as its argument is a constructor application, after
which the erasure rewrites (`uskl_to_pskl_ptyp_to_uskl_syn`) stop matching —
the Arrow row reads its component equations off the FOLDED painting instead
(`ptyp_to_uskl_syn_arrow` + `injection`).  (ii) `inversion H; subst` renames
the RULE's own variable, so the definition-chasing rows pick their lookup fact
out of the goal with `match goal` rather than naming it.

**What remains for the row**, in order: (1) the same normalization for the
fill `Hrs`, whose source `κP0` is NOT a monotype — that induction has to cover
all the rows, including the `__hole` fill (wf under ⇓) and the ∀ rows;
(2) scoping `⇓ˢ(κP0)` from `⇓ᵇQ`'s (refinement's source ftv sits below its
target's, modulo the definition chases ⇓ has already performed);
(3) §(L)'s strengthenings on the normalized data (they exist already);
(4) the β-freeness of the Ξ-images, from the motive's `dom Ξ [<=] ftv P0` +
`msubst_pskl_ftv_lower` + the confinement, exactly as `Hgr` does in the
consistency walk (prop_consis_complete.v, Assign-SkipRigid); (5) the row
itself — junk swap (`a_sub_flex_skip_rigid_no_loss` exists), rebuild with
`a_inc__tvar` / `a_inc_equiv_mid_insert_tvar` / `a_inc_equiv_self_downarrow`,
and — the one thing the consistency walk does NOT have to do — transport the
PRECISION conjunct back from `(Θ', ⇓ᵇ Q)` to `(Θ, Q)`.

⚠️ Two REJECTED shortcuts, recorded so they are not retried.  (a) Running the
IH at `Ξv ++ Θ'` (the junk block kept, only `β` dropped) fails at the
PACKAGE, not at the premises: `a_inc__tvar` demands `ζ ∷ Θ1 ⊑ Θ'` at the
TRUNCATION, so the lift stops.  (b) Supplying `ftv Q [<=] dom Θ'` for the
ORIGINAL `Q` is impossible — `ad_refine_syn_f__hole` fills with any
Θ-scoped skeleton, junk block included.

## 2026-08-03 — ⭐⭐⭐ TASK 4 **CLOSED**: the `F` avoidance set is DELETED from the whole tree, and the avoid set now lives on the COMPLETENESS MOTIVE

`make coq` green, admit-free, all 25 `README.v` flagships *Closed under the
global context*.

**The judgments.**  `a_assign` / `a_unify` / `a_consis` lost the used-name
index `F`: signatures, 28 constructors, notations, `Assign-SolveM`'s side
condition (now just `α1 ∉ add α (dom (Ξ ++ Θ0))`), and the derived
`a_assign_unify_consis_compat` → `_delta_compat` (Δ-transport only) /
`_uniq_fprotect` → `_uniq` (a third of its length — the walk's own output
premise states directly what the `F`-protection conjunct used to supply).
In its place the eight re-attaching rules of the walk carry the paper's
Barendregt output premise `β ∉ dom Θ1`, exactly like `a_sub_flex`'s three —
and ⭐ `prop_swap.v` §13b proves that shape LOSES NOTHING (finite support gives
a fresh `γ`, equivariance moves the run to it fixing every INPUT,
`swap_junk_dom_out` discharges the premise), which is what makes the encoding
admissible rather than a strengthening.

**Soundness** (prop_consis_sound.v).  Conjunct 4 (`x ∈ dom Θ1 → x ∈ dom Θ0 ∨
x ∉ F`) deleted with its four projections; conjunct 5's coverage restated
OUTPUT-relative as `Δ ∩ dom Θ1 [<=] dom Θ0` (assign: `[<=] dom (Ξ ++ Θ0)`).
All 28 cases go through, and every `X ∉ dom Θ1` formerly read off conjunct 4
is now the rule's own premise.

**⭐ Completeness — the piece this entry closes** (prop_consis_complete.v §2).
The eight discharge sites can no longer read conjunct 4, so the three
completeness motives gain a parameter `N : atoms` and one conclusion conjunct,
placed between the derivation and the optimality half:

```coq
forall γ, γ `in` dom Θ1 -> γ `in` dom (Ξ ++ Θ0) \/ γ `notin` N
```

That is literally the old `F`, moved from the JUDGMENT to the COMPLETENESS
STATEMENT — where it is FREE, because completeness is the direction that
CHOOSES the guessed names.  The walk rows relay `N := add α1 N` exactly where
they used to relay `add α1 F`; `assign_solve_m_complete`'s `set (L := ...)`
just keeps `N` as its first component, and the guessed `β̄` dodge `L ⊇ N` by
construction.  `complete_mu` / `consis_complete` instantiate `N := ∅` and drop
the conjunct, so no downstream statement changed.

⭐ **The general lesson: an avoid set is a CONSTRAINT on a judgment and a
FREEDOM on a completeness proof.**  `F` was in the wrong place all along.

Everything the ~30 new conjunct obligations need is four atom-set facts, each
two lines: `avoid_relay` (pop the head, recurse at `add α1 N`, re-attach),
`avoid_head_miss` (the SAME hypothesis discharges the Barendregt premise —
the head is in the relayed set and fresh for the sub-run's input),
`avoid_compose` (Arrow's two runs in sequence), `avoid_truncate` (the ∀ rows
run under their own rigid binder and hand back the truncation, so the binder
must be shown absent from the tail — `auc_uniq_consis` supplies it).  Their
at-the-shape wrappers are `avoid_relay_cons` / `_cons_mid` /
`avoid_truncate_cons` / `avoid_same_dom` / `avoid_mono`.  No new theory, and
no junk swap: the rejected alternative (swap each IH's run and transport the
optimality package through §14/§15's `kswap` kit) is `a_sub_flex_complete_skip`
eight times over and additionally needs `a_inc_binds_provenance` moved
upstream.

**Stage 5** (`prop_swap.v` §13c).  The eight `_no_loss` twins, now provable
because `β ∉ F` is vacuous: `a_assign_{skip,skip_rigid,skip_tm_var,
skip_tm_skl,assign}_no_loss` and `a_unify_{flex_skip,skip_other,
flex_assign}_no_loss`, all `Qed`, all *Closed under the global context*, six
lines each over §13's junk-swap corollaries.  This is what makes the
assign/unify walk's encoding exactly as defensible as the subtyping walk's:
none of the eight rules can reject where a premise-free version would fire.
The two back-edge rows (whose premise is CONSISTENCY) need the walked
definition `τ` to be free of its own head — the same extra hypothesis §13b's
`a_sub_flex_assign_no_loss` carries.  One local helper,
`ftvar_ptyp_to_pskl`.

**Fallout, all mechanical.**  `a_consis_hole_p0_output` and three
`a_consis_complete` call sites in prop_sub_complete_thm.v lost their `F`
argument; `prop_decorate_sub.v`'s `match goal` pattern for `a_assign` lost an
underscore; `test_unify_regression.v`'s two explicit constructor applications
lost theirs.  Stale doc comments in `def_extra.v` / `prop_consis_rename.v` /
`prop_consis_sound.v` rewritten as history notes.

**Out of scope, deliberately** (unchanged from the 2026-08-02 entry): retiring
`a_assign_unify_consis_rename_tvar` is NOT a swap corollary — the rename is
TARGET-ONLY and a swap would also move payload occurrences of `α`, needing
`α ∉ ftvar_in_aenv Θ1`, which is false without a wf hypothesis.

## 2026-08-02 — ⭐⭐ TASK 4 (the `F`-deletion) — three stages landed, and the output-premise shape is PROVED LOSSLESS; the deletion itself is BLOCKED on soundness conjunct 5

Tree green, admit-free, axiom-free at `134ed1d`.  Partial stage 4 preserved on
branch `f-deletion-wip` (does not compile; see its commit message).

**Landed.**

1. `prop_swap.v` §13 gains `a_assign_swap_junk` / `a_unify_swap_junk` /
   `a_consis_swap_junk`, derived from §11's equivariance exactly as §13 already
   derived the `a_sub` pair, plus `eq_swap_atoms_fresh` for the set indexes.
2. ⭐ **Three rename consumers in `prop_consis_complete.v` were STALE.**  Cluster
   4 made `a_consis`'s ∀ rows exists-fresh but left the completeness proof
   assembling its ∀ nodes the old way — rebuild the whole cofinite family from
   the α-instance with `a_assign_unify_consis_rename_tvar`, then repair the set
   indexes with `a_assign_unify_consis_compat`.  None of it is needed: the run
   already produced its instance at α and the conclusion's
   `close_pskl_wrt_pskl α P1` matches the constructor verbatim, so each site is
   `apply a_consis__forall_inh with (α := α); [ clear - Fr; fsetdec | exact Hc ]`.
   −138 lines, the file's rebuild drops to 27s, and three of the six consumers of
   the bespoke rename plus two of the three `compat` uses evaporate.
3. The eight re-attaching rules of the assign/unify walk gain
   `β ∉ dom Θ1`, matching the three `a_sub_flex` already carried.  `F` is still
   present in this commit, and completeness discharges the new premise for free
   from soundness conjunct 4 (new `a_unify_notin` / `a_consis_notin` beside
   `a_assign_notin`).  Mechanical fallout: 48 `intros` slots across the four
   mutual inductions, the rename's two walk cases, the cex and the regression
   test — no statement changed.
4. ⭐⭐ **`prop_swap.v` §13b: the output-premise shape LOSES NOTHING.**
   `a_sub_flex_{skip,skip_rigid,assign}_no_loss`, `Qed`, axiom-free.  A rule
   constraining its own output can only REJECT, so the fair objection is that the
   encoding might get stuck where `type.ml` succeeds.  It cannot — a derivation
   is finitely supported, equivariance moves the run to a `γ` fresh for its whole
   output while fixing every INPUT pointwise, and `swap_junk_dom_out` discharges
   the premise.  The rule fires whenever a premise-free version would, with the
   run's GENERATED names transposed and nothing else touched.  Flex-Assign's case
   covers `α = β` (the subject reduces to `τ`, β-free by scope).

**⚠️ The blocker was soundness conjunct 5, not conjunct 4 — and it is now
SOLVED** (`f-deletion-wip` @ `53155fd`, prop_consis_sound.v green).  Conjunct 4
is genuinely dead (vacuous, no external consumers) and is deleted with its four
projections.  Conjunct 5's coverage `Δ [<=] (F ∪ dom Θ0)` was the load-bearing
one — at Assign-SolveM it is the only thing excluding the guessed `β̄` from the
protected `Δ`, which BOTH halves of the Δ-invariant need.  The repair is to make
it OUTPUT-relative, `Δ ∩ dom Θ1 [<=] dom Θ0`, mirroring the change to the rules;
all 28 cases go through, and every `X ∉ dom Θ1` formerly derived from conjunct 4
is now the rule's own premise (which also cut `a_assign_unify_consis_uniq` to a
third of its length).

**⚠️ What remains, and the lesson.**  prop_consis_complete.v's eight discharge
sites can no longer use conjunct 4.  The right fix is NOT the junk swap the
handover imagined (that is `a_sub_flex_complete_skip` ×8, each with an
optimality package): it is to put the avoid-set on the COMPLETENESS MOTIVE —
`forall γ, γ ∈ dom Θ1 -> γ ∈ dom (Ξ ++ Θ0) \/ γ ∉ N`.  That is the old `F`
moved from the judgment to the completeness statement, where it is FREE,
because completeness is the direction that CHOOSES the guessed names.  ⭐ An
avoid-set is a CONSTRAINT on a judgment and a FREEDOM on a completeness proof;
`F` was in the wrong place all along.  DESIGN §4.3.

**⚠️ Retiring the bespoke rename is NOT a swap corollary.**
`a_assign_unify_consis_rename_tvar`'s three surviving consumers are
`a_consis_decorate_size`'s ∀ rows, which genuinely need a family because
`a_consistag` is (rightly) cofinite.  Equivariance is not a drop-in replacement:
the rename is TARGET-ONLY — it moves the binder occurrence and leaves payload
occurrences of `α` in the output tail alone — whereas a swap moves those too, so
it needs `α ∉ ftvar_in_aenv Θ1`, a leak lemma that is FALSE without a wf
hypothesis (`a_consis_decorate_size` has only `uniq Θ0`) and unproved with one.

## 2026-08-02 — ⭐⭐ P7a STARTED: the swap kit's discharge pattern is MACHINE-CHECKED (Flex-Depend + Flex-Skip `Qed`), and `Flex-SkipRigid` is BLOCKED on something else entirely

**What landed** (`prop_sub_complete_thm.v`, new P7a section, all `Qed`, tree green
and axiom-free):

- **The pattern works end to end.**  `a_sub_flex_complete_skip` discharges the
  walk's Barendregt output premise (`β ∉ dom Θ1`, algo/def_rules.v:1116) exactly
  as the swap kit predicted: PEEL κ around the mid β entry
  (`a_inc_strip_flex_mid`) → IH at the stripped context → junk-swap the IH's run
  (`a_sub_flex_swap_junk`) → re-attach via `swap_junk_dom_out` → rebuild the
  package as `(β, κ's β-image) :: kswap_msubst β β1 ζ`, with `a_inc_kswap` for
  the increase, `msubst_compose_kswap_id` + `msubst_compose_head_id` for the
  equivalence, and `msubst_bskl_head_notin` + `msubst_bskl_kswap_paint` for the
  precision.  Every §14/§15 lemma the K4 commit built is consumed; none was
  wrong or missing.
- **`a_sub_flex_complete_depend`** — re-association only.
- **The two en-route facts, both cheap after all**: `a_sub_flex_sound`
  (`(Ξ ++ Θ0) ⊴ Θ1 ∧ a_wf_aenv Θ1`, by composing `a_sub_decorate_bundle`'s and
  `a_subtag_sound_bundle`'s SECOND halves — no new mutual), and RIGID
  PROVENANCE, which is `a_inc_binds_provenance` (a target entry is flexible or
  comes from the source by name) applied to that ⊴ witness.  Also new and
  reusable: `ad_pat_sub_target_wf` (the subtyping twin of
  `ad_pat_consis_target_wf`), `a_sub_flex_out_scope`, `a_wf_aenv_ftvar_dom`,
  `a_inc_equiv_insert_flex_mid`.

**⚠️ THE REAL P7a BLOCKER IS NOT THE SWAP KIT — it is `a_inc`'s POSITIONALITY.**
The pattern works for `Flex-Skip` / `Flex-Assign` because `a_inc__flex` /
`a_inc__flex_def` keep the TARGET fixed, so peeling a flexible source entry
leaves `κ' ∷ (Ξ ++ Θ0) ⊑ Θ` at the SAME Θ and the join / fill / wf premises
transport verbatim.  `a_inc__tvar` does not: `κ ∷ (Ξ ++ (β ~ tvar) ++ Θ0) ⊑ Θ`
forces `Θ = Ξv ++ (β ~ tvar) ++ Θ'` with `κ' ∷ Θ0 ⊑ Θ'` (`a_inc_tvar_inv`), so
the IH's target must be the TRUNCATION Θ'.  And `κ' ∷ Θ0 ⊑ Θ` is not merely
unproved but FALSE as soon as Θ0 carries a rigid or term entry, because
`a_inc__tvar` admits only an `a_suffix` above the matching target entry and Θ
has `β ~ tvar` there.  So `Flex-SkipRigid` needs the ⇓-TRUNCATION apparatus the
consistency walk already has (`a_inc_self_downarrow`,
`join_pskl_downarrow_mono_scoped`), lifted from `ad_pat_consis` to
`ad_pat_sub_gv`.  `prop_consis_complete.v:4930-5153` (`Assign-SkipRigid`) is the
model to crib, line for line.

**⚠️ AND THE P7a MOTIVE IS MISSING AN INVARIANT.**  The consistency walk's
`assign_complete_at` (prop_consis_complete.v:2249) carries
`dom Ξ [<=] ftvar_in_pskl P`; `sub_flex_complete_concl` does not.  Without it
nothing confines the images of Ξ's flexibles — and Ξ sits ABOVE β in the source,
so `κ γ̂` may legitimately mention the skipped rigid β, after which NO ζ over the
output `(β ~ tvar) ++ Θ1` can reproduce it (the rule re-attaches β at the TOP, so
Θ1's flexibles are scoped below it).  The invariant is supplied at
`a_sub__flex_mono` (Ξ = ·) and preserved by every walk row, exactly as in the
consistency motive; adding it is a motive change the dispatcher can pay for.
A third obligation falls out of the same place: with a RIGID head and
`β ∈ ftvar_in_pskl P0` there is no rule at all, so the row must REFUTE that
configuration from the solution — the subtyping twin of
`rigid_survives_solution` + `ad_pat_consis_rigid_ftv_rev_scoped`.

**Also corrected against the tree**: `Flex-Assign` and `Flex-Solve` do NOT stay
inside the walk — both re-enter the MAIN half (`Flex-Assign` at the substituted
subject `α̂[τ/β̂]`, which for `β̂ = α̂` is the bare monotype τ), so their row
lemmas take the P7b motive `sub_complete_concl` as their IH, not
`sub_flex_complete_concl`.  Only Depend / Skip / SkipRigid are walk-internal.

**SAME DAY, three more closures** (`b6b7b2d`, `5fcd4ca`, `b7f8bde`):

- the motive GAINED `dom Ξ [<=] ftvar_in_pskl P0`; **Flex-Depend re-establishes
  it from its own `β ∈ ftv P0` premise**, which is a nice confirmation that it is
  the right invariant;
- **`Flex-Assign` CLOSED** — the paper's second interesting case and the first
  CROSS-HALF row (its IH is the P7b motive).  New: `msubst_pskl_subst_mono` (a
  monotype substitution pushed through a metasubstitution is absorbed as a head
  entry — pure), `msubst_pskl_tyequiv_pointwise` /
  `msubst_ptyp_tyequiv_two_msubst` (the ≡ˢ/≡ᵗ congruence for TWO
  metasubstitutions agreeing pointwise — the dual of `a_pskl_tyequiv_msubst`),
  `a_inc_equiv_insert_flex_def_mid`, `a_sk_mode_compat_subst_mono`.  ⭐ The fill
  transports across the resulting ≡ˢ by the ALREADY-EXISTING
  `skl_tyequiv_refine_syn_f_transport`: `a_inc__flex_def`'s middle is SEMANTIC,
  so `msubst κih (P0[τ/β̂])` is only ≡ˢ-equal to `msubst κ P0`, and the motive's
  ≡ᵘ slack covers the SUBJECT only.  The subject's own slack goes through
  `a_uskl_tyequiv__mono`, which IS the ≡ᵗ → ≡ᵘ paint transport;
- **`Flex-Solve`'s CRUX closed** — `ad_pat_sub_gv_mono_fn_arrow_inv`, the paper's
  step ⓒ→ⓓ.  The mech must CHASE definitions the paper does not: a monotype
  subject may be a defined flexible, so the join fires `__flex_mono` rather than
  `__arrow` — and that row PRESERVES the fuel, so the chase is free and the
  regenerated join returns at the same `n`.  P7c's `__flex_mono` join case wants
  the same lemma.

- **`Flex-Solve` CLOSED** (`012e066`) — the paper's FIRST interesting case.  θs
  is built exactly as the paper's ⓕ; the package is its ⓖ+⑫ ⇒ ⑭ (peel the
  deposited block out of BOTH identity witnesses, identify by
  `is_id_inc_unique` + length, collapse with `a_inc_equiv_collapse_solve`).  Six
  more reusable enablers, of which the one worth remembering is
  **`a_wf_pskl_weaken_tvarish`**: `a_wf_pskl` reads Θ ONLY through
  `a_binds_tvar` and its context never grows (the binder rule extends Δ), so it
  weakens along a TVAR-ISH map — the `binds`-monotone `a_wf_pskl_weaken` is too
  strong the moment a DECLARATION becomes a DEFINITION, which is exactly what
  Flex-Solve does to `α̂0`.

⚙ **A performance datum worth the standing rule** (measured with `coqc -time`,
not by bisecting): ONE `fsetdec` against the row's three overlapping freshness
unions cost **152s of the file's 153s**.  Two fixes, both now standing practice
— keep each `atom_fresh` avoid set MINIMAL (audit what the binder is actually
used for; two of the five components were never needed), and SHATTER it into
atomic facts immediately, one single-hypothesis `fsetdec` each, then `clear` the
union.  152s → 0.09s.

**P7a's only remaining row is `Flex-SkipRigid`.**

**`Flex-SkipRigid`'s CONTEXT-MOVE half landed the same day** (`d486dcd`):
`ad_refine_pskl_strengthen` and `ad_pat_sub_gv_mono_strengthen` move the
solution-side premises from Θ to the truncation Θ'.  ⚠️ The join does NOT
strengthen in general — the two ForallL rows introduce a guess whose scope no
condition on the conclusion controls; at a MONOTYPE subject they cannot fire,
which is exactly SkipRigid's configuration.  Two shape lessons: the MODE must
stay general (`__arrow`'s recursive premise runs at `M`, not `mode_fn M`, so an
FN-only statement does not even induct), and the ftv bound must read
`Δ ∪ dom Θ'` with Δ apart from `dom Θ`.

`ad_refine_syn_f_strengthen` (the FILL's counterpart) followed, so all three
solution-side judgments — refinement, fill, join — now move to a sub-context.

⚠️ **CORRECTION, same day.**  I recorded that this REPLACES the consistency
walk's ⇓-normalization route.  It does not.  All three strengthenings take
`ftv Q [<=] dom Θ'` as a HYPOTHESIS, and that is **not derivable**: both
`ad_pat_consis__flex_r` (def_consis_refine.v:116) and `ad_refine_syn_f__flex_r`
(prop_consis_sound.v:384) let the COUNTERPART be an arbitrary DEFINED flexible
of Θ, independent of the subject — so `Q` may name a flexible of the junk block
`Ξv` that sits ABOVE β in the target.  `⇓[Θ]` unfolds exactly those, which is
why the consistency walk normalizes before it truncates.  And keeping `Ξv`
rather than dropping it does not rescue the argument: `a_inc__tvar` then demands
ζ at Θ', not at `Ξv ++ Θ'`, so the package stops lifting.  The strengthenings
are necessary, not sufficient.

**Next**: ⇓-normalization of the solution data (`a_inc_downarrow_prefix`'s
analogue), then §(L) on the normalized data; then the β-freeness argument for
the Ξ-images (the motive's `dom Ξ ⊆ ftv P0` + the fill + the confinement of the
NORMALIZED `Q`); then `Flex-SkipRigid` itself and its stuck-check — the package
lift is free (`a_inc__tvar` / `a_inc_equiv__tvar`).  Then the shield's
realizability question; then the dispatcher (§12).

**TASK 0's residual, falsity half SETTLED the same day**
(`cex/cex_p7_shield_forall_flex.v`, Qed, axiom-free).  For a Θ0-flexible `α̂` and
`ε ∈ Ψ'`, `flex_shield Θ0 Ψ' Δρ α̂ (∀^ε β.β→β)` is UNDERIVABLE — `fsh_clean` is
blocked by the tag, `fsh_flexfree` by the flexible, and `fsh_all_r` only descends
into `α → α` at `add α Δρ`, where `fsh_clean` is blocked by α itself and every
congruence by a shape mismatch.  Hence
`sub_shield Θ0 Ψ' ∅ ((∀γ.γ) → α̂) (∀^ε β.β→β)` is underivable too, since
`ss_walk` reaches the codomain in one step and `sub_shield` demands the shield at
EVERY walk-reachable `P0`-part against the WHOLE fixed `ψa`.  So the documented
residual (a `P0` with a ∀ below its head) is not merely unproved: where it also
carries a walk-reachable raw flexible the shield is FALSE, and the ∀-free supply
route cannot stretch to it (with a ∀ inside `P0`, `κP0` carries a ∀, the fill may
emit a `bskl_all_inh`, `Q` stops being `bskl_inh_free`, and
`ad_pat_sub_g_inh_free_tag_free` no longer collapses `Ψa`).  What remains open is
REALIZABILITY — whether P7b's Sub-ForallL can be reached with that `(P0, ψa)` and
`ε ∈ Ψa`.  If it can, the finding is that `sub_shield` (a MECH-INVENTED repair
premise, not a paper statement — nothing for PAPER-GAPS.md) is over-strong
because it is indexed NON-POSITIONALLY, and the repair is a positional
re-indexing replayed through P6-Ss and P7b's two ForallL rows.  See
DESIGN-completeness-subtyping.md §14.

## 2026-08-02 — ⭐⭐⭐ THE SWAP KIT (equivariance) LANDS: `prop_swap.v`, the UNIFORM renaming primitive — P7a's K1–K3 subsumed in one pass

**The user's uniformity directive** (2026-08-02): ONE treatment of freshness
repair across the whole proof — no mixture of the `F` avoidance set, exists-`L`
avoid-set hand-backs, size-induction renames, and ad-hoc devices.  That
directive DECIDES the P7a route: only equivariance under an atom transposition
serves every judgment with one statement shape — the exists-`L` shape is forced
where no measure decreases (the consis mutual, `a_sub`), and the size shape is
forced where it does (look), so no substitution-based discipline can be
uniform.  The 30-minute option-(C) check settled faithfulness first: the
reference implementation genuinely pops AND re-attaches the walked entry
(`pop_binding` type.ml:1009; `add_binding bind` :1028/:1040/:1046), the paper's
rules write the output `Θ1,β̂` (full-algo-spec.tex:883-909), and only the global
counter (`incr counter`, :563) makes `β ∉ dom Θ1` true in the implementation —
so the mech rules are faithful and the discharge obligation is real.

**What landed (`frost/algo/prop_swap.v`, ~1450 lines, all `Qed`, compiles in
under 3s, tree green)**:

- §1–§4 the syntax layer: `swap_atom` (`simpl never` — destructs match it
  syntactically) lifted through `ptyp`/`pskl`/`abind`/`aenv`; involutions,
  fresh-identity (`swap_*_fresh_id`), ftv/dom/binds/uniq transport, and
  commutation with open/close/subst and `ptyp_to_pskl`.  LN untouched: swap
  acts on free atoms only.
- §6 `swap_atoms` for the set indexes, with the MEMBERSHIP SPEC
  (`swap_atoms_iff`) as its interface — set-indexed judgments take their
  swapped indexes EXTENSIONALLY (`S' [=] swap_atoms a b S`), and the
  `add`-extending rules step through `eq_swap_atoms_add`.
- §5, §9–§12 equivariance for EVERY judgment `a_sub` reaches:
  `a_guess_mono`/`a_guess`, the small predicates (incl. both cofinite wf
  judgments — the binder case needs NO re-picking: `L' := swap_atoms a b L`),
  `a_looksub`/`a_lookeq`, `a_solve_sub`/`a_solve_eq`/`a_solve_cstr`,
  `a_extract`, the consis mutual (28 cases), and `a_sub`/`a_sub_flex`.
  Every binder case is re-apply-the-same-constructor: the ONE fixed name
  transports because a bijection cannot collapse it into anything.
- §13 the K3 consumption shape: `a_sub_swap_junk` / `a_sub_flex_swap_junk`
  (inputs β0-free and β1-fresh ⇒ same run with swapped OUTPUTS) and
  `swap_junk_dom_out` (β1 ∉ dom Θ1 ⇒ β0 ∉ dom of the swapped output) — exactly
  what the walk rows' Barendregt premises need.

**Corrections to the 2026-07-31 kit map, verified against the tree**: K0 as
imagined (`dom Θ1 ⊆ dom (Ξ ++ Θ0)`, "the consis layer invents no names") is
FALSE — `a_assign__solve_m` deposits `a_guess_mono`'s fresh flexibles; the
honest, F-relative form ALREADY EXISTS as soundness conjunct 4
(`forall x, x ∈ dom Θ1 → x ∈ dom Θ0 ∨ x ∉ F`, prop_consis_sound.v:2556-2610).
And because `a_sub` has no `F` slot (its consis leaves run at `F = ∅`), no
input-side discipline can see the walked-out β — the after-the-fact rename is
the only non-encoding-touching route, which is what the kit provides.

**Standing consequence for uniformity (queued, NOT yet executed)**: with the
kit landed, the sole recorded ground for withdrawing the F-deprecation
("output-freshness premises multiply the P7a blocker ×8") evaporates — after
P7a closes, `F` can be deleted and the consis walk re-encoded with the same
Barendregt output premises the subtyping walk carries, discharged the same
way; the exists-`L` rename (`a_assign_unify_consis_rename_tvar`) and the
rename siblings of cluster 3 become derivable corollaries of equivariance and
their bespoke proofs retirable.  Sequenced AFTER P7a proves the pattern
end-to-end.

⚙ Three tactic-level gotchas the kit's build recorded (in-file comments):
`simpl` unfolds `List.map` into its `fix` (rewrite through `swap_aenv_cons`
instead); `f_equal` is a no-op on 0-ary constructor equalities (`reflexivity`
in the solve list); prop_ln's `==` tests carry THEIR elaboration's instance
term, so destruct them by capturing `if ?t then _ else _` from the goal, never
by re-elaborating the test.

**Next**: K4 (the θ-algebra transport: `a_inc` source/target swaps, ζ
key-swap, `msubst` key-swap equalities) — then the P7a rows themselves.

## 2026-08-02 — ⭐⭐⭐ FRESHNESS CAMPAIGN cluster 5 **CLOSED**: `a_sub__forall_l` is EXISTS-FRESH, and the DECORATED layer stays COFINITE by design

**QUESTION ZERO, machine-checked before anything was converted** (probe `Qed`,
axiom-free, both directions).  `a_sub__forall_l` LOOKED defective — its shared
outputs `Ξ` / `P1` are produced under the cofinite α and are never re-bound,
which is exactly the shape that made the 2026-07-31 ForallR fix a real repair.
It is NOT defective: the look cluster's generated names already avoid the
looked-for variable, so ONE instance at an α meeting only the input-only
condition `α ∉ ftv P` generates the WHOLE family with the SAME `Ξ ↪ P1`
(`a_extract_family_of_instance`).  Proved both ways —

- exists-fresh premise ⟹ cofinite premise (the rule does not under-generate),
- cofinite premise ⟹ exists-fresh premise (nothing is lost),

for `a_sub__forall_l` and for both `a_subtag__forall_l_{tagged,untagged}`.  So
cluster 5, like cluster 4, is a conversion for ONE discipline per layer, not a
repair.

**THE RULE.**  One opener plus `α ∉ ftvar_in_aenv Θ0 ∪ ftv P ∪ ftv P0`, and the
`a_extract` premise stated once.  `a_extract_family_of_instance` MOVED
prop_look_complete_extract.v → prop_looksub.v §11, because prop_soundness_sub.v
needs it now and is a SIBLING of P6-L's file, not a consumer.

**CONSUMERS.**  Construction got EASIER — prop_sub_complete_thm.v's two P7b
sites used to build the family explicitly and now hand over P6-L's instance
verbatim.  Inversion got harder in exactly one place, prop_soundness_sub.v's
`a_sub_sound` ForallL row, which rebuilds the family from the run's ONE
opener (the decorated layer is still cofinite) and then picks its own α for the
decoration as before.

**⚙ TWO PERFORMANCE TRAPS in test_examples.v**, both because the opener's
freshness union now lives in the AMBIENT context rather than inside one bullet:
`repeat rewrite ftvar_in_aenv_app in H` unfolds `Θlib` and its σ-types and never
terminates (the same hazard the file already documents for a bare
`simpl in *`), so cbn's delta list must not reach `ftvar_in_aenv`; and leaving a
shattered copy of the 3-way union in context made two `crush_wf` calls take 34s
each — `clear`-scoped they are 2.7s and the file totals 22s.  Kit:
`pick_forall_l` / `forall_l_absent`.

**⭐ THE SCOPE DECISION: `algo/def_decorated.v` STAYS COFINITE.**  The campaign's
line was `decl/` vs `algo/`; that is wrong at one place.  `a_consistag` /
`a_subtag` / `a_solvetag` live under `algo/` but are **not the algorithm** — the
decorated system is a proof device, nothing runs it, no implementation
corresponds to it — so the reason exists-fresh is FORCED (an algorithm picks one
name from a counter and cannot deliver one output for every fresh binder) simply
does not apply.  The line is *is it the algorithm?*, not the directory.

The proviso is leakage, and the sharp form of the question is **what does each
cofinite family SHARE — the output context `Θ1` above all?**  Audited rule by
rule (table in DESIGN §4.3): `a_consistag`'s five ∀ rows share `Θ1` in the exact
shape cluster 4 machine-checked for `a_consis` in BOTH directions;
`a_subtag__forall_l_*`'s TYPE binder shares only `Ξ` / `P1` (machine-checked,
`Θ1` does not occur under that quantifier); `a_solvetag`'s four ∀ rows have no
context output at all.  Exactly ONE family shares `Θ1` unchecked — the TAG pack
`(Ψg, ψg)` — and two things make that safe: cofinite is the STRONGER premise, so
it makes the decorated relation **smaller**, never larger, and can only block a
PRODUCER; and the decorated judgments are **purely internal**, appearing in no
exported statement (`README.v` mentions neither), produced only from
`a_sub`/`a_consis` and consumed only toward the declarative system.  A smaller
intermediate cannot weaken an end-to-end theorem — it can only fail to be
constructible, and every construction is `Qed`.

⚠️ **Recorded for the authors / future cleanup.**  The paper's decorated ForallL
writes `Ψ_g fresh` (appendices/decorated-algosub.tex:92) — ONE pack.  So the
mech's cofinite tag pack is a deliberate STRENGTHENING, and it is load-bearing:
`a_subtag_decoration_var`'s ForallL crux inverts the node and rebuilds it at the
ENLARGED tag context `Ψ ∪ Ψa`, needing `Ψg # Ψa`, and those two come from
INDEPENDENT runs, so no input-only side condition on the rule can separate them
(the TWO-INDEPENDENT-GENERATORS gap, tag instance).  Going exists-fresh there
would require either an avoid-set hand-back threaded through both decoration
inductions or a genuine RETAGGING lemma — and retagging would have to be built
from scratch, since lngen generated only `subst_uskl_in_uskl` and there is no
tag substitution on `uskl`.  Worth revisiting only if retagging gets built
anyway.

**Files touched:** `algo/def_rules.v` (the rule), `prop_looksub.v` (§11, the
relocated family lemma), `prop_look_complete_extract.v` (pointer),
`prop_soundness_sub.v`, `prop_sub_complete_thm.v`, `test_examples.v`, DESIGN §4.3.

**Remaining:** cluster 6 (`a_pat`/`a_typing`, 8 cofinite rules at
algo/def_rules.v:1160–1264 — these bind TERM variables, so audit first whether
the same "is it the algorithm?" reasoning applies), the walk's three
`∉ dom Θ1` premises (P7a), THEN the P7b dispatcher.  Deferred: the
`a_tags_sort` → `a_tags_skl` rename (naming only, 244 occurrences).

## 2026-08-02 — ⭐⭐⭐ FRESHNESS CAMPAIGN cluster 4 (consis mutual) **CLOSED** — a UNIFORMITY conversion, machine-checked as such; and `F` STAYS

**QUESTION ZERO, settled with a machine check before anything was converted.**
`a_consis`'s three ∀ rows (`__forall_inh`, `__forall_syn`, `__univ_ghost1`)
were NOT defective.  They CLOSE — the skeleton output is re-bound, the context
output strips the opener — so cofinite was faithful, and one fresh instance
generates the whole cofinite family.  Proved in both directions for all three
rows (axiom-free) and kept as prop_consis_rename.v §9's `_cofinite`
admissibility lemmas, which are now also the tool for any consumer wanting a
family (`test_examples.v` and `prop_consis_complete.v`'s three sites go through
them).  The conversion was made anyway, per the standing directive of ONE
freshness discipline per layer — recorded as such in the commit and in
DESIGN §4.3, so it is not mistaken for a repair later.

The general criterion, now written into DESIGN: **cofinite is faithful exactly
where a rule re-binds its skeleton output AND strips the opener from its
context output.**  That decides clusters 5 and 6 too.

**Three costs, all of which generalize.**

- **`a_assign_unify_consis_compat` WIDENED.**  Its condition
  `α1 ∈ F' → α1 ∈ F ∨ α1 ∉ dom Θ1` transported into the premise only because
  cofinite let the proof pick the opener outside `F'`.  With the opener fixed,
  `α1 = α` satisfies neither disjunct.  Re-picking needs §8's rename, which is
  proved USING compat — so the repair had to go into the statement: a third
  disjunct `α1 ∈ dom (input context)`.  Sound at Solve-M for the same reason
  the original was.
- **⚙ The rename lemma now HANDS BACK its own avoid-set** —
  `deriv -> exists L, forall β0 ∉ L, …`, each ∀ case contributing its opener.
  This is the TWO-INDEPENDENT-GENERATORS gap, fourth instance, and it is
  forced: the opener occurs in NO component of the conclusion, so no set
  computable from the statement can name it, and `a_consis : Prop` rules out a
  function from derivations to sets.  Cluster 3's size-induction escape is NOT
  available — `a_consis` recurses on skeleton size, `a_assign`/`a_unify` on the
  context, and `a_assign__assign` crosses between them, so no measure decreases
  on every rule.  The three `_cofinite` lemmas need no rename (the
  `close`/`open` round-trip does it), which is why they stayed clean.
- **`a_consis_decorate_gen` MOVED** from prop_decorate.v to
  prop_consis_rename.v §10 and became a SIZE induction on
  `size_pskl P + size_pskl P0` (the subject alone fails: UnivGhost1 fixes it
  and shrinks only the input, ForallSyn does the opposite).  `a_consistag` is
  still cofinite, so each ∀ row rebuilds a family from the run's ONE opener;
  the rename lives downstream of prop_decorate.v via prop_flex.v, so the lemma
  moved rather than the asset.  It gained `uniq Θ0`, discharged at all three
  consumers from `a_wf_aenv_uniq`.

**Soundness needed one more move.**  `a_consis_sound_aux`'s three ∀ cases used
to `pick fresh α` and instantiate a cofinite family; now they get the rule's
opener, which the wf judgments' cofinite bounds have no reason to avoid.
`a_wf_pskl_ftv_dom` / `a_wf_pskl_rename_delta` / `a_wf_pskl_all_inv_at` moved
UP from prop_consis_complete.v to prop_consis_sound.v to instantiate the wf at
that opener.  The invariant conjunct used to need a SECOND fresh atom (one
missing the tag set `Δ`); the rule's opener cannot miss `Δ`, but it does not
have to — the `α0 = α` branch is refuted by `α ∉ dom Θ1`, which the premise's
own output well-formedness supplies and the freshly-picked atom never had.

**⚠️ `F` must NOT enter the ∀ rules' avoid-sets.**  Tried, and it REFUTES
`a_assign_unify_consis_compat` (that lemma swaps `F` for an `F'` that may
contain the rule's own opener, which is fresh and hence outside the output).
Reverted; the soundness case that motivated it is closed by `α ∉ dom Θ1`.

**`F`-DEPRECATION WITHDRAWN from the campaign.**  It was listed as something
that "should largely fall out"; it does not.  `F` is the only carrier of the
names the walk has already passed — `a_assign__skip` recurses at the TAIL and
re-attaches on the way out, and `Ξ` holds only Assign-Depend's dependency
block.  Three replacements were evaluated (DESIGN §4.3 records all three):
output-freshness premises (multiplies the P7a blocker by eight);
walked-prefix-as-context (a retype, not a deletion — the prefix cannot join the
working context without letting the consistency premise solve entries the walk
has passed); and re-freshening the output before re-attaching, which is
genuinely VIABLE and does delete `F`, but makes the output context
non-syntactic and so breaks L8, the lemma that shapes the ∀ rules'
`⊣ (α ~ tvar) ++ Θ1` premise.

**⚙ The principled asset, if renames keep recurring: EQUIVARIANCE.**  The
avoid-set exists only because substitution is not injective.  A *swap*
`α ↔ β0` moves every atom of the derivation at once, openers included, so it
needs no freshness condition at all — and the substitution-shaped rename falls
out as a corollary, WITHOUT `L`, and without `tvar_prefix Ξr` or `uniq`.  Cost:
`swap` over `ptyp` / `pskl` / `abind` / `aenv` plus equivariance for the small
side judgments.  Clusters 5, 6 and P7a's K1–K4 all need renames; build it there
if the avoid-set starts leaking into consumer statements.

**Files touched:** `def_extra.v` (the three rules), `prop_decorate.v` (lemma
moved out), `prop_consis_rename.v` (§8 restructured, §9 admissibility, §10 the
relocated decoration lemma), `prop_consis_sound.v`, `prop_consis_complete.v`,
`prop_inc_strengthen.v`, `prop_soundness_sub.v`, `test_examples.v`, `README.v`.

**Remaining:** cluster 5 (`a_sub__forall_l` + `a_subtag__forall_l_*`; the four
`a_consistag` ∀ rows are the same CLOSE shape as cluster 4 — ⚠️ still worth
confirming whether `a_sub__forall_l`'s `Ξ`/`P1` really escape, since the look
rules' generated names already avoid the looked-for α), cluster 6
(a_pat/a_typing), the walk's three `∉ dom Θ1` premises (P7a), THEN the P7b
dispatcher.

## 2026-08-02 — ⭐⭐⭐ FRESHNESS CAMPAIGN cluster 3 (look) **CLOSED** — the whole tree is GREEN, admit-free and axiom-free

Everything the stage-4 entry below specified is Qed, and the two files it left
red are converted.  The campaign's staging rule held throughout: the enabler
was proved before the rule change reached its consumers, and the tree is green
at the end of every commit but the deliberately-red WIP ones.

**The blocker's enabler — `a_looksub_lookeq_subst_gen_size` (prop_decorate_sub.v
§8, Qed, axiom-free).**  Source substitution with EXISTENTIAL outputs: the ∀
rows RE-PICK their binder away from `P0` and hand back RENAMED `Ξ ⨾ 𝒞`, so the
lemma needs NO context premise and the solvetag obligation rides across on
`a_solvetag_subst_cstrs`.  Every prediction in the spec held — the measure
`2·(size P + size P')` (+1 on the looksub side), the six re-picking rows, the
thirteen congruences.  Two shapes were NOT in the spec and are worth naming:

- LS-Check and LE-UnivGhostR guard the SOURCE, and `guarded_pskl` includes
  variables, so where the source IS the substituted variable the row switches
  to Absent — the source was α-free, so the run collected nothing.  §4 already
  had that move; it transfers verbatim.
- both arrow rows need `a_solvetag_split` **and a new `a_solvetag_join`**,
  which is conditional on the LEFT list being all-eq: `a_solvetag__sub` fires
  only on a SINGLETON, so a sub constraint may never be followed by anything.
  `a_lookeq_cstr_eq` moved down from prop_look_complete_cstr.v to
  prop_looksub.v to serve it (that file is downstream).

**The same two-generators gap surfaced twice more, and both times one rigid
rename settled it — no further induction.**  `a_looksub_avoid_atom` freshens a
run away from ONE atom: there is at most one offending name, so renaming that
name to a fresh `δ` moves the outputs and leaves the inputs alone.  It is what
`a_subtag_decoration`'s ForallR row needs (it opens the run's target at the
`a_subtag` rule's own binder, which must miss the run's outputs), after
shrinking the look context away with `a_looksub_ctx_ftv_mono` to make the
opener's `ftvar_in_aenv` condition vacuous.

**`prop_soundness_sub.v`.**  `a_subtag_decoration`'s look hypothesis now carries
its OWN context `Θl`, universally quantified INSIDE the induction — the ForallL
rows hand the recursive call a run living under the look rule's binder while
the subtag premise sits at `Ξ ++ Θ0`, and since the lemma only CONSUMES the run
there is no alignment constraint.  Both ForallL rows substitute the node's
guess for the ONE binder LS-ForallL gives them, via `a_looksub_subst_gen`.

**`prop_look_complete_sub_cstr.v` (P6-Ss)** mirrors P6-Cs: three ∀ rows
collapsed, the arrow row descends with `a_looksub_ctx_ftv_mono`, the ftv sites
go through the `_ftv_ctx` corollaries, and its generated-names conjunct gained
`ftvar_in_uskl ψa` for the same arrow-row reason.

**Two downstream encoding fixes**, both real:

- P6-L's guess runs at `Ξc ++ Θ0`, so the L-bound handed to
  `a_guess_ty_witness` must cover that context's PAYLOADS — cluster 3's
  avoid-input is `ftvar_in_aenv`, not `dom`.
- `a_extract_family_of_instance` now HANDS BACK its own avoid-set
  (`exists L, forall α' ∉ … ∪ L`).  Renaming the looked-for variable is an
  OUTPUT-freshness lemma now, and a leaked binder is by definition a name no
  input mentions, so no condition on `P`/`P0` can exclude it — only the
  instance knows its own `Ξl ⨾ 𝒞l`.  Its two P7 consumers are cofinite and
  just union `L` in.

**Audit follow-through.**  `a_looksub_lookeq_subst_stable` (§4) and
`a_looksub_lookeq_subst_stable_rev` (§4b) now have ZERO consumers, as do
`a_lookeq_rename_tvar_keep`, `a_looksub_rename_tvar_keep` and
`a_lookeq_rename_var`.  They are retirement candidates with a RESTART NOTE;
left in place for now because the P7 layer has not yet been re-checked against
the converted look cluster.  `cex/cex_look_subst_stable_leak.v` stays either
way — it is a registered paper gap.

**Remaining:** clusters 4 (consis mutual), 5 (`a_sub__forall_l` + the decorated
mirrors — ⚠️ confirm with the user first: `a_solvetag`'s only output is a TAG
SET, so type binders cannot enter it and it may legitimately STAY cofinite) and
6 (a_pat/a_typing); F-deprecation; the walk's three `∉ dom Θ1` premises (P7a);
THEN the P7b dispatcher.

## 2026-08-01 — 🚧 FRESHNESS CAMPAIGN cluster 3 stage 4: **P6-Cs CONVERTED** (`prop_look_complete_cstr.v` GREEN, axiom-free) — and the decoration layer's subtyping half is BLOCKED on one missing enabler, now fully specified

Third stage of cluster 3, on `freshness-campaign-cluster3-wip` @ `bf413fa`.

**`prop_look_complete_cstr.v` (P6-Cs) is GREEN in 26s and axiom-free.**  Both
theorems' `Print Assumptions` read "Closed under the global context".  What the
tail needed:

- LE-FlexR's own `fresh γ̂` at both generating sites (extend the site's
  `pick fresh α1` with `ftvar_in_aenv Θ0`, the flexible on the right and the
  subject's ftv; discharge with `cbn; clear - Fr; solve_notin`);
- the three ∀ rows COLLAPSED, exactly as predicted, from a
  pick-a-representative-and-rename-back dance to
  `apply a_lookeq__forall_inh with (β := β); [ clear - Fr; solve_notin |
  exact HLK ]`.  Each ∀ row's `pick fresh β` gained `ftvar_in_aenv Θ0` (the
  rule's own avoid-input); nothing else moved;
- the ARROW row's right half now descends with `a_lookeq_ctx_ftv_mono`: the
  right IH runs at the GROWN `Ξc1 ++ Θ0` (its flexibles avoid the left
  branch's block), while `a_lookeq__arrow` wants both halves at `Θ0`.
  Dropping declarations only SHRINKS `ftvar_in_aenv`, which is the direction
  the mono lemma goes.

**Three repairs the DISJUNCTIVE `a_looksub_lookeq_ftv` forced.**  Cluster 3
weakened that lemma to "…or the run INVENTED this name" (the ∀ rules leak), and
four P6-Cs sites had been relying on its exact bound.  All three repairs
RESTORE the exact bound where it is still true rather than weaken a consumer:

1. **`a_looksub_ftv_ctx` / `a_lookeq_ftv_ctx`** (prop_looksub.v, both Qed) —
   the escape arm is refuted outright for a variable of `dom Θ`, because every
   generating rule avoids `ftvar_in_aenv Θ ⊇ dom Θ`.  Three sites use it: the
   arrow row's Δρ-apartness for its new `Pi := Pa1`, and both ForallSyn rows'
   `β ∉ ftv 𝒞`.
2. **`a_inc_binds_tvar_rev`** (+ `a_suffix_no_tvar`) PROMOTED from
   `cex/cex_p6cs_rsubst_delta_vacuous.v` into `prop_inc.v`, beside its converse
   `a_inc_binds_tvar`.  An increase never INVENTS a rigid, so `Δρ ⊆ dom Θ0`
   — which is what makes (1) applicable to a ρ-replaced variable.  The cex
   now imports it instead of re-proving it.
3. **the theorem's generated-names conjunct gained `ftvar_in_uskl ψa`**:
   `∀ α0 ∈ dom κc, α0 ∉ add α (dom Θ0 ∪ dom Θ ∪ ftvar_in_uskl ψa)`.  This is
   load-bearing, not tidying: with the exact ftv-𝒞 bound gone, the ARROW row
   can no longer show that the RIGHT branch's fresh flexibles miss the LEFT
   branch's constraints — the only surviving bound on `𝒞` is the ψa-based
   conjunct, so the flexibles have to be known to miss `ψa`.  Both LE-FlexR
   rows pick their flexible for `ψa` too; every other row passes it through.
   The corollary `a_lookeq_solve_complete` exposes the strengthened form.

`cex/cex_p6cs_subject_wf.v` got the look judgment's context argument (Qed,
axiom-free).

### ⛔ THE BLOCKER — `prop_soundness_sub.v`'s two ForallL rows need a new enabler

`a_subtag_decoration` (prop_soundness_sub.v:98) has not been converted at all —
its look hypothesis is still written context-free, which is the file's
first syntax error (:102).  Converting it is NOT mechanical, and the reason is
worth writing down because it is the first place the campaign's avoid-input
discipline is genuinely NOT enough.

Both ForallL rows (:511 and :786, tagged and untagged) do the same thing: take
the look run's LS-ForallL premise and SUBSTITUTE the node's guessed skeleton
`P1` for the binder.  They call `a_looksub_subst_stable`, which since this
cluster carries the Barendregt premise the counterexample forces:

    ftvar_in_pskl P1 [<=] add α (ftvar_in_aenv Θ)

and **that premise cannot be supplied here.**  `P1` is the ForallL node's
guess, well-formed at `Ξ ++ Θ0`, so its variables include the extract's fresh
block `dom Ξ`.  The look run is at `(b ~ tvar) ++ Θl`, and its binders avoid
`ftvar_in_aenv Θl` only.  `Ξ` and the look run's binders are generated by two
INDEPENDENT runs at the same context, so nothing keeps them apart — the
reference implementation's global counter does, the relational rendering does
not.  `a_looksub_lookeq_ctx_ftv_mono` cannot help: it SHRINKS the context, and
here we would need to grow it.

**The designed repair** (specified, not yet written).  It is cluster 3's
standard shape, and `a_looksub_open_target_at_size` (prop_decorate_sub.v:2737)
is the working model for every step of it:

    Lemma a_looksub_lookeq_subst_gen_size : forall n,
      (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
         2 * (size_pskl P + size_pskl P') + 1 <= n ->
         forall β P0, β <> α -> α ∉ ftv P0 -> lc_pskl P0 ->
         forall ψa Ψa, 𝒞 ⊩ᵗ ψa ⤳ Ψa ->
         exists Ξ' 𝒞',
           Θ ⊢ (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ' ⨾ 𝒞' /\
           𝒞' ⊩ᵗ ψa ⤳ Ψa) /\
      (… the a_lookeq half, measure 2 * (size P + size P') …).

Points that are already settled:

- **No context premise.**  Instead of demanding that the derivation's binders
  already avoid `P0`, the ∀ rows RE-PICK their binder away from `P0` and hand
  back RENAMED outputs.  That is why `Ξ` and `𝒞` become existential, and it is
  why the solvetag obligation must ride along — `a_solvetag_subst_cstrs`
  carries it across the rigid renaming, exactly as in
  `a_looksub_open_target_at`.
- **The counterexample does NOT refute this form.**  On
  `cex/cex_look_subst_stable_leak.v`'s witness
  `Θ ⊢ ∀.(α → β) ∼[α] ∀.(0 → 0) ⤳ · ⨾ [β₀ ≐]`, substituting `β₀` for `β`
  IS re-derivable at any binder `δ ≠ β₀`, returning `𝒞' = [δ ≐]` — a rigid
  RENAMING of `𝒞`.  Only the fixed-output form (§4) is false.
- **The measure must be `2·(size P + size P')`, +1 on the `a_looksub` side.**
  A plain source measure fails at LS-Check (source and target both unchanged
  as the judgment switches to `a_lookeq`) and at LS-ForallR (source
  unchanged).  The stated one strictly decreases in all 19 rows.
- **Six rows need the re-pick + rename**: LS-ForallR, LS-ForallL, LE-FlexR
  (its generated flexible must also avoid `ftv P0` now), LE-ForallInh,
  LE-ForallSyn, LE-UnivGhost1.  The other thirteen are congruences.
- **`a_subtag_decoration`'s look hypothesis must also take a FREE context**
  `Θl`, universally quantified INSIDE the induction (each row may use a
  different one).  There is no alignment constraint with the `a_subtag`
  judgment's own `Θ0`: the lemma only ever CONSUMES the look run.  Without
  this the ForallL rows cannot even state their recursive call, which needs
  the derived run at `(b ~ tvar) ++ Θl` while the subtag premise sits at
  `Ξ ++ Θ0`.

Once that lemma is Qed, §4 (`a_looksub_lookeq_subst_stable`) loses BOTH of its
consumers and can be retired.

### Audit of what the exists-fresh encoding lets us drop

Run against the actual consumer sets (`grep -rn NAME frost | grep '\.v:'`):

- **★ the P6-Cs ftv-𝒞 conclusion is NOT a cofinite artifact — it stays.**  The
  hypothesis was that it existed only to let a single `𝒞` serve a whole
  cofinite family of openers.  It does not: every ∀ row needs
  `β ∉ ftvar_in_cstrs 𝒞` to restate its outputs at the conclusion's context,
  which has no `β` — `a_solve_cstr_strip_tvar_mid` and `a_wf_pskl_strip_tvar`
  demand it whatever the binder encoding.  The conjunct is also the ONLY
  surviving bound on `𝒞` now that `a_looksub_lookeq_ftv` is disjunctive, and
  the arrow row was found to need it (above).  `Θs`, `Δρ`, `flex_apart_deep` and
  the ρ apparatus therefore stay too.  The same argument applies to P6-Ss's
  mode-guarded ftv-𝒞 disjunction.
- **`a_looksub_lookeq_subst_stable` (§4)** — consumers are exactly
  prop_soundness_sub.v:511 and :786, and both are the rows the blocker above
  rewrites.  RETIRE once the generalized lemma lands (with a RESTART NOTE).
  `cex/cex_look_subst_stable_leak.v` stays either way: it is a registered
  paper gap, not scaffolding.
- **`a_looksub_lookeq_subst_stable_rev` (§4b)** — ZERO real consumers;
  prop_look_complete_sub_cstr.v mentions it only in comments, one of which
  (:1816) says outright that the route it was built for does not need it.
  Deletion candidate; deferred until P6-Ss is converted, in case that
  conversion resurrects it.
- **`a_lookeq_rename_tvar_keep` and `a_lookeq_rename_var`** — now have ZERO
  consumers (P6-Cs's two `_keep` uses were the last, and they died in this
  commit).  Their `a_looksub` siblings are still used —
  prop_look_complete_sub_cstr.v:1262/:2176/:2561 for `_keep`,
  prop_soundness_sub.v and prop_look_complete_extract.v:1304 for `_rename_var`
  — so the pairs are kept intact until P6-Ss and the decoration file are
  converted, at which point both `a_lookeq` halves should go.
- **`a_looksub_rename_var` STAYS.**  The re-freshening dance at
  prop_soundness_sub.v:228-263 does NOT evaporate: `a_looksub_open_target_at`
  requires `β <> α`, where `β` is the ForallR rule's Barendregt binder and `α`
  the looked-for variable — and the rule's binder is chosen by `induction
  Hsub`, i.e. BEFORE the looked-for variable is introduced, so no freshness
  relates them.  Moving the looked-for variable is forced.
- **`a_looksub_lookeq_generated_ftvar` vs `_generated_fresh`** — neither
  subsumes the other.  `_ftvar` (`ftv Ξ ⊆ dom Ξ`) is the workhorse INSIDE
  prop_looksub.v's own rename proofs (a dozen call sites); `_fresh`
  (generated names avoid the ambient context) is the one consumers use.  Keep
  both.
- **FOUR size inductions, soon five.**  No master lemma subsumes them: the
  two renames constrain a TARGET name, `open_target_at` moves a binder to a
  GIVEN opener, `consistag_decoration` is a consumer-side induction, and the
  new substitution lemma changes the SUBJECT.  They share the shape, not the
  statement.

## 2026-08-01 — 🚧 FRESHNESS CAMPAIGN cluster 3 (look): BOTH RENAME LEMMAS CLOSED, the whole rename kit, and the decoration layer's consistency half — `prop_looksub.v` and `prop_decorate_sub.v` GREEN

Second stage of cluster 3, on `freshness-campaign-cluster3-wip`.  The two
lemmas the campaign's staging rule demands before anything else are **Qed**,
`prop_looksub.v` compiles clean **in 11s**, and the first genuine consumer
(the one that has to MOVE a binder) is closed too.

**Closed (all Qed, in prop_looksub.v):**

1. **`a_looksub_lookeq_rename_tvar_size`** — the TARGET-only rigid rename, all
   five ∀ rows written.  Each binder row takes the FORCED three-case split
   (source = the rule's binder → re-fire at the target; target = the rule's
   binder → it did NOT leak, so move it to a fresh δ and rename twice; else
   the binder stays), plus the `α1 = β` identity dispatch up front
   (`rename_aenv_same` / `subst_cstrs_same` / `subst_pskl_var_same`).  Size-free
   wrappers `a_looksub_rename_tvar` / `a_lookeq_rename_tvar` and the derived
   `*_rename_tvar_keep` corollaries (which now also need `β ∉ ftvar_in_aenv Θ`,
   since the rename touches the CONTEXT) are on top.
2. **`a_looksub_lookeq_rename_var_size`** — renaming the LOOKED-FOR variable,
   restated with the same two campaign shapes: an OUTPUT-freshness premise
   (`α' ∉ dom Ξ ∪ ftv 𝒞`) and SIZE induction.  Both are forced: LE-FlexR's
   generated flexible and the ∀ rules' leaked binders avoid the looked-for
   variable by their own side conditions, so they would have to avoid it after
   the rename too; and a binder that IS the new name has to be moved, which
   §5's rename does to a derivation that is no sub-derivation.  §5 and §6 were
   SWAPPED in the file for this reason — the tvar rename is now the cluster's
   primitive asset.

**New enablers (all Qed):**

- **`a_looksub_lookeq_ctx_ftv_mono`** + `a_looksub_ctx_exchange` /
  `a_lookeq_ctx_exchange`: look reads its context only through the avoid-inputs,
  so it is stable under any context with no LARGER `ftvar_in_aenv` — in
  particular under EXCHANGE, which every consumer that opens two binders in the
  other order needs.
- **`a_looksub_lookeq_generated_fresh`** + `a_looksub_binder_not_generated` /
  `a_lookeq_binder_not_generated`: cluster 1's DERIVED junk-freeness, in the
  look cluster.  A generated flexible can never BE an enclosing ∀ binder, which
  is exactly what lets a consumer move that binder with `Ξ` left FIXED.
- **`a_solvetag_subst_cstrs`** (prop_decorate_sub.v): renaming a rigid in the
  collected constraints leaves a solvetag run alone — the constraints only ever
  appear as the run's TARGETS, and target renaming is unconditional
  (`a_solvetag_sub_eq_target_rename`).  This is what lets a consumer hand back
  the RENAMED constraint list.
- **`a_looksub_open_target_at`** (prop_decorate_sub.v) — the cluster's one
  genuine "move a binder" consumer, REWRITTEN as a size induction: LS-ForallR
  renames the run's own binder to the requested opener (Ξ survives by junk-
  freeness, 𝒞 genuinely changes — the binder leaks into it — which is why the
  conclusion's constraint list is existential), and LS-ForallL re-freshens its
  own binder when it collides.  The cofinite `a_looksub_open_target` it
  supersedes was DELETED (it had no consumers, and its "one shared 𝒞 for a
  whole family" shape is the encoding the campaign rejects).

**⚙ The performance finding, and the kit it produced.**  The binder rows'
side conditions are five-way unions; a single `fsetdec` against five
OVERLAPPING such hypotheses did not finish in 100s for ONE row.  `clear -`
scoping was NOT enough.  The fix is a small structural kit — `notin_union_both`,
`notin_add_atom`, `notin_ftvar_in_aenv_cons_tvar`, `notin_ftvar_in_aenv_rename`,
`notin_ftvar_open_var`, `notin_ftvar_subst_var`, `notin_ftvar_in_cstrs_subst`(`_away`)
— driven by the `look_fresh` tactic, whose leaves are `assumption` /
`congruence` / a SINGLE-hypothesis `fsetdec`; plus the discipline of shattering
a `pick fresh` into atomic facts and `clear Fr`.  Row time went >100s → ~2s.
`look_fresh` is the tactic every remaining consumer should use.

**`a_consistag_decoration` CONVERTED — `prop_decorate_sub.v` is GREEN (13s).**
The decl-side `a_consistag` rules are (rightly) still COFINITE, so every ∀ row
has to serve a whole FAMILY of openers from the look run's ONE binder.  That
means MOVING the binder, and the moved premise is no sub-derivation, so
`a_consistag_decoration` became a SIZE induction
(`a_consistag_decoration_size`; measure = the two look skeletons' sizes, which
strictly decrease in every row — including LE-UnivGhostR, where only the TARGET
shrinks).  A size-free wrapper keeps the name its two call sites use.  The
service the rows run on is three new lemmas in prop_looksub.v —
**`a_lookeq_forall_move` / `_move_l` / `_move_r`**, one per ∀ shape — stated
with the premise's skeletons ALREADY OPENED, because that is the shape a
consumer holds after `inversion …; subst` has eaten the un-opened body's name
(the same reason the rows read the opener's avoid-set off `match type of Hp`).
`Ξ` survives such a move untouched (junk-freeness); 𝒞 does NOT — the binder
legitimately leaks into it — so the lemmas hand back `subst_cstrs`, and
`a_solvetag_subst_cstrs` carries the solvetag run across.

**Still RED, and where.**  Two files.  `prop_soundness_sub.v`
(`a_subtag_decoration` at :102 — the same ∀ rows, larger, plus the
`HDf : forall b, b ∉ ?L1` cofinite-family reads at :489/:764).  And
`prop_look_complete_cstr.v` (P6-Cs), which is PARTLY converted: the ∀ rows of
`a_lookeq_cstr_eq` and `a_lookeq_all_flex_mono` SIMPLIFIED to plain
`assumption` — the promised payoff, no more picking a representative off `L` —
and the theorem's conclusion now reads `Θ0 ⊢ P ∼[α] P0 ⤳ Ξc ⨾ 𝒞` (the avoid-
input is `Θ0`, the same context the conclusion's solve already runs at as
`Ξc ++ Θ0`).  What remains there is a mechanical tail: every
`apply a_lookeq__flex_r` gains LE-FlexR's own `fresh γ̂` premise (extend the
site's `pick fresh α1 for …` with `ftvar_in_aenv Θ0`, the target variable and
the subject's ftv, then discharge with `cbn; clear - Fr; solve_notin`), and the
three ∀ rows (:3033 / :3533 / :4054) apply the rule at the binder they already
picked.  `cex/cex_p6_flex_freshened.v` was fixed (arity) along the way.

**Remaining, in order:** (i) `prop_look_complete_cstr.v`'s FlexR/∀ tail; (ii)
`prop_soundness_sub.v`; (iii) `prop_look_complete_sub_cstr.v` (P6-Ss, same
shape); (iv) `test_examples.v` and the remaining `cex/` look runs; (v) then
clusters 4–6, F-deprecation, the walk's `∉ dom Θ1` premises (P7a), and finally
the P7b dispatcher.

**Two performance rules re-confirmed the hard way.**  `clear - H; fsetdec`
against a TWELVE-way union takes ~200s to FAIL — use metalib's `solve_notin`,
which shatters the hypothesis instead of normalising it.  And an `ltac:(…)`
argument inside a partially-applied IH is elaborated while the goal still holds
EVARS ("Cannot find witness" from `lia`): `assert` the side condition first and
pass it by name.

## 2026-08-01 — 🚧 FRESHNESS CAMPAIGN cluster 3 (look) STARTED — canon question (ii) DECIDED (look gains a context), and the source-substitution lemma REFUTED in its unconditional form

`remech` is green: it carries the cluster's **first stage only** — the
TARGET-only restatement of `a_looksub_lookeq_rename_tvar`.  The encoding
conversion itself is parked on `freshness-campaign-cluster3-wip` (RED,
deliberately) with the work below already done.

**The implementation settled canon question (i) with no room for doubt**:
all five look ∀ rules LEAK.  `constr_collect_eq` and `constr_collect_sub`
never call `bind_var` — LE-ForallInh (type.ml:579-583), LE-ForallSyn
(:595-598), LE-UnivGhost1 (:610-613), LS-ForallR (:668-672), LS-ForallL
(:685-688) all `unbind` and discard the name.

**Canon question (ii) — DECIDED (user): look gains a `Θ` avoid-input**,
and `a_guess` gains one too (`a_extract` feeds it `Ξ ++ Θ0`; running the
inner guess at `nil` had left cluster 1's discipline inert there).  What
made it not a matter of taste: `a_looksub_lookeq_ftv` cannot be STATED
without a context once the ∀ rules leak — its exact bound is FALSE
(`Θ ⊢ ∀b.α ∼[α] ∀b.b ⤳ · ⨾ [b₀ ≐]`), its repair is cluster 2's disjunctive
shape, and that disjunct *is* "∉ ftvar_in_aenv Θ".  The chain it feeds is
the paper's own `lemma:look-output-fresh` (subtyping-proofs:522).  See
DESIGN.md §4.3, "The look cluster".

⚠️ **THE FINDING** — `cex/cex_look_subst_stable_leak.v` (Qed, axiom-free):
the mech's UNCONDITIONAL `a_looksub_lookeq_subst_stable` (forward direction
of the paper's `lemma:constraint-collection-stable-substitution`) is FALSE
against the faithful rules.

    Θ ⊢ ∀. (α → β)  ∼[α]  ∀. (0 → 0)  ⤳  ·  ⨾  [ β₀ ≐ ]

substituting `β₀` for `β` puts the derivation's own leaked binder into the
SOURCE, and every binder the rule may then pick avoids it — so the collected
constraint changes.  **The paper is not wrong**: it argues under Barendregt.
The mech now spells that out with the smallest premise the rule's own side
condition supplies, `ftv P0 [<=] add α (ftvar_in_aenv Θ)` — the CONTEXT, not
the input skeletons, because only the context is monotone under descent.

Closed in this stage (all Qed): the target-only
`a_looksub_lookeq_rename_tvar` + its derived KEEP corollaries and
`a_looksub_lookeq_generated_ftvar`; the `subst_cstrs` kit; the disjunctive
`a_looksub_lookeq_ftv` and the repaired `a_extract_output_fresh`; the
repaired `a_looksub_lookeq_subst_stable` and `_rev` (the reverse needed
`βg ∈ ftvar_in_aenv Θ`, for the same reason).

**Remaining (in order), on the WIP branch:**

1. `a_looksub_lookeq_rename_tvar_size` — stated in final form, rows not
   written.  The three cases are FORCED and worked out in the ⛔ WIP comment
   above it: `β = b` (source IS the binder ⇒ substitution is the identity,
   re-fire at α1), `α1 = b` (target IS the binder ⇒ it must MOVE, and the
   output-freshness premise is exactly what says it did not leak, so the
   move preserves Ξ and 𝒞), otherwise (binder stays).  Model line-by-line:
   `a_solve_sub_eq_rename_size`'s SS-ForallL row (prop_solve_sub.v).
2. `a_looksub_lookeq_rename_var` (renaming the LOOKED-FOR variable) needs
   the same treatment — machine-checked reason: renaming α to the run's own
   leaked binder is refutable by the same witness.
3. The ∀ rows of P6-Cs / P6-Ss (prop_look_complete_{cstr,sub_cstr}.v) —
   these should SIMPLIFY: they currently build a cofinite family by renaming
   a fresh representative, and exists-fresh lets them use the derivation's
   own binder.
4. `prop_soundness_sub.v` / `prop_decorate_sub.v` (`a_looksub_open_target_at`
   is the one genuine "move a binder" consumer), then `test_examples.v` and
   the `cex/` files that build look runs.
5. Then the rest of the campaign: cluster 4 (consis mutual), cluster 5
   (`a_sub__forall_l` + decorated mirrors), cluster 6 (`a_pat`/`a_typing`),
   F-deprecation, the walk's `∉ dom Θ1` premises (P7a).

## 2026-08-01 — ⭐⭐⭐ FRESHNESS CAMPAIGN cluster 2 (solve) CLOSED — and a mech-only lemma REFUTED, restoring the paper's own P6-Sv conclusion

`make coq` green from clean, admit- and axiom-free.  The five solve rules
are exists-fresh now: `SolS-ForallL` and the four eq-∀ rules CLOSE their
output (the implementation's `bind_var`, type.ml:499-505), `SolS-ForallR`
LEAKS its binder (type.ml:517-520 discards the name).

Three recurring shapes did the work:

1. **Size induction wherever a consumer must MOVE a binder.**  An
   exists-fresh rule hands over ITS OWN binder, and a re-freshened premise
   is no sub-derivation.  Converted: `a_solve_sub_eq_weaken_mid_flex`
   (an inserted block can CAPTURE a pinned witness) and, in
   prop_soundness_sub.v, `dec_ext_solve_eq_step` / `dec_ext_solve_sub_step`
   — there the decoration ψ is an INPUT that may itself mention the rule's
   binder (a ◇ under the ∀ decorates to an arbitrary tagged skeleton), so
   the cofinite `dec_ext` / `d_tags_skl` / `a_solvetag` families cannot be
   rebuilt from it; the SOLVE derivation moves instead.
2. **Target-only renaming** (`a_solvetag_sub_eq_rename_target`): the
   solvetag judgments never inspect a target VARIABLE, only its SHAPE, so
   `SSub-ForallR` — whose binder leaks and therefore cannot be moved — can
   still build its cofinite family.
3. **Output-freshness as an explicit premise** where a leaked binder
   cannot be re-freshened (`a_solve_sub_eq_weaken_mid_flex`,
   `a_solve_cstr_weaken_mid_flex`).  Both call sites discharge it from the
   EXACT `a_solve_cstr_ftv_eq` — their constraint lists are all-eq, and the
   eq half never leaks.  This is the paper's Barendregt convention spelled
   out, not a weakening.

⚠️ **THE FINDING.**  `a_solve_sub_wf` ("sub-solving preserves wf", a
MECH-ONLY lemma) is FALSE against the faithful rule —
`cex/cex_solve_sub_wf_leak.v`, Qed, axiom-free:

    ◇ ≼[TC] ∀a. a ⤳ ∀◇ b        (SolS-ForallR at b, then SolS-GhostL)

with `Δ = ∅` and `Ξ = ·`, the very configuration its single call site
used.  Both inputs are wf at `Θ ⨟ ∅`, but the output carries the escaped
`b`.  **The paper never had this lemma**: its P6-Sv states `Θ₀ ⊢ P_a`
among its own conclusions (subtyping-proofs.tex:1737), carries it as
`Θ₀,β ⊢ P_a` through the SolS-ForallR row, and discharges β from
`β ∉ ftv ψ_a` plus PRECISION (:1897-1900).  So the repair moved the mech
CLOSER to the paper: `a_solve_sub_complete_var` now returns
`Θ0 ⨟ empty ⊢ₚₛᵃ Pa`, P6-Ss reads it off, and `a_solve_sub_wf` is gone
(RESTART NOTE at prop_look_complete_sub_cstr.v:323).

Two mech-only steps the paper's single-context `Θ ⊢ P` does not need
(both new, prop_look_complete_sub_var.v): a ∀◇ body is typed at the EMPTY
Δ, so SolS-ForallL's row may move its binder from the context into Δ only
for an UNSHIELDED variable — `a_wf_pskl_tvar_to_delta` plus
`a_solve_sub_eq_unshielded` ("solving does not shield a context variable
the subject leaves unshielded"; `a_solve_sub_ftv`'s escape disjunct is
closed off by `β ∈ dom Θ`).

Other assets: `a_wf_pskl_all_of_one` / `a_wf_pskl_all_inv_at` (the
exists-fresh idioms on wf, prop_consis_complete.v, beside the
`a_wf_pskl_rename_delta` moved there); `pskl_no_hole_close`,
`pskl_no_top_close`, `pskl_top_guarded_close`,
`pskl_shielded_ftv_close_upper` (close-stability for the predicates whose
consumers used to see an opened body); `a_solve_sub_eq_ctx_change` is
SHRINK-only (growth can capture a witness) and `a_solve_cstr_ctx_change`
inherits that premise.

Remaining clusters unchanged: look, consis mutual, decorated mirrors,
a_pat/a_typing, F-deprecation, the walk's output premises (P7a).

## 2026-08-01 — ⭐⭐⭐ FRESHNESS CAMPAIGN cluster 1 (guess) CLOSED under the FINAL canon — avoid-input discipline, junk-freeness DERIVED, close-based ∀

`make coq` green from clean, admit- and axiom-free.  The uniform-encoding
campaign's first cluster ([a_guess_mono]) is converted, and — more
importantly — the CANON is now settled by three user corrections plus one
machine-found obstruction, each of which reshaped the design:

1. **Input-only side conditions** (user): a rule CHOOSES its binder, so
   its freshness condition may name only INPUTS — "pick β avoiding P'" is
   not an algorithm when P' is an output.
2. **Explicit close where the algorithm re-binds** (user): without an
   output condition the relation is ambiguous (the premise output can be
   read back closed or unclosed); the implementation arbitrates which
   rules close ([bind_var] — SolS-ForallL type.ml:499-505, guess_mono/TForA
   :88-91) and which leak (SolS-ForallR :517-520 discards the binder; the
   leak is BY DESIGN, wf side conditions reject harmful outputs downstream).
3. **Renaming lemmas constrain their TARGET, never their source** (user):
   the inherited `β ∉ dom Ξ` hypothesis was the unprovable one; the correct
   asymmetric statement renames the CONTEXT and the GENERATED block too
   (payloads included — [rename_aenv]/[ftvar_in_aenv], def_extra.v).
4. **The junk-derivation obstruction** (machine): with scope-insensitive
   generators, a hole below a ∀ can generate the ∀'s own recorded witness
   (Ξ ∋ b0), and the ∀-opening bridge is FALSE on such derivations — no
   freshness demanded of the lemma's α can fix a collision between two
   names INSIDE the derivation.  Resolution (user suggestion, mechanized):
   the ∀ rule's witness ENTERS the premise's context ([(β~tvar) ++ Θ]) and
   the hole rule avoids [ftvar_in_aenv Θ] — both INPUT-only — whence
   `generated names avoid enclosing witnesses` is DERIVED
   ([a_guess_mono_generated_fresh], prop_flex.v), not assumed.  This is
   also the honest explanation of the F avoidance set: F exists precisely
   to supply this discipline externally; with it internalized, F's
   deprecation stays on the campaign plan.

The kit (prop_flex.v): [ftvar_in_aenv]/[rename_aenv] algebra;
[a_guess_mono_generated_fresh]/[_binder]; [close_ptyp_subst_var];
[a_guess_mono_rename_tvar] (SIZE induction — when the target IS the
recorded witness the derivation is renamed TWICE, and the second rename
applies to the result of the first, no sub-derivation); the OPENED intro
form [a_guess_mono_all_of_one]; and the decl/algo boundary bridge
[a_guess_mono_open_at] (one instance → the family a cofinite declarative
target needs — NOT cofiniteness creeping back; decl stays cofinite by
design).

**Context-generic guess claims are RETIRED.**  `forall Θg, a_guess_mono
Θg P Ξ A` (an artifact of the previously-inert context slot) became:
- the TRANSPORT form `forall Θg, (dom Ξ avoids ftvar_in_aenv Θg) → …`
  where construction and consumption sites differ
  (prop_consis_complete.v's witness lemmas; provable there because the
  counterpart is a monotype — no ∀ case), and
- the L-BOUNDED form `forall Θg, ftvar_in_aenv Θg [<=] L → …` where a ∀
  case must pick its witness BEFORE the context is known
  ([a_guess_ty_witness], prop_look_complete_extract.v — the bound is fixed
  by the lemma's own avoid-parameter L, so the ∀ case instantiates the IH
  at [(β~tvar) ++ Θg] and no weakening lemma is needed).

Consumers reworked: [a_guess_mono_consis] and [dec_ext_guess_mono_anchor]
(∀ cases via the bridge, size-inducted); Solve-M completeness's guess
witness L widened to [ftvar_in_aenv]; test_examples discharges the new
hole freshness with a targeted-rewrite tactic (a bare `simpl in *`
unfolds Θlib's σ-types and diverges — keep the library opaque).

Remaining clusters unchanged (solve, look, consis mutual, decorated
mirrors, a_pat/a_typing, F-deprecation, the walk's output premises).  For
each: the SAME questions — which outputs close vs leak (implementation
arbitrates), and whether generated names can collide with enclosing
witnesses (if yes, the avoid-input discipline extends there too).

## 2026-07-31 — ⚠️ P7a BLOCKER FLAGGED: the walk's Barendregt output conditions (`β ∉ dom Θ1`) are undischargeable without new infrastructure — DECISION NEEDED

Scoping item 6 (P7a + bundle) against the Qed interfaces hit a real
gap.  The flex walk's three re-attaching rules —
`a_sub_flex__assign` / `__skip` / `__skip_rigid` — carry the
prose-completed Barendregt premise `β ∉ dom Θ1` (the audit's
registered completion; SOUNDNESS consumes it for output wf).  In the
COMPLETENESS direction this is an obligation about the sub-run's
OUTPUT junk: the run `Θ1` returned by the IH (main-half or flex-half)
may mention `β` as an incidentally-colliding fresh name, and nothing
bounds it — `sub_complete_concl`'s conclusion has no dom-bound on
`Θ1`, `a_consis_complete`'s neither, and no a_sub run-renaming
kit exists (`prop_consis_rename.v`'s
`a_assign_unify_consis_rename_tvar` renames RIGID tvars through the
consis layer only; the walk's junk is FLEX names in a_sub runs).
The walk's OTHER freshness conditions are unproblematic: Flex-Solve's
deposited `α̂,β̂` are input-fresh (completeness chooses them); Depend
has none.

Options, all needing a decision:
(A) Build the flex-junk RENAMING for `a_sub`/`a_sub_flex` runs
    (mutual over the full algorithmic layer — effectively a slice of
    the standing de-cofinite campaign's rename infrastructure, pulled
    forward).  Correct, large.
(B) Thread an AVOID-SET through the completeness conclusions
    (`dom Θ1`'s new names avoid a caller-supplied finite `V`) — but
    the Infer/Check/Arrow-domain rows get their `Θ1` from
    `a_consis_complete`, so the closed consistency-completeness
    bundle would re-open with the same parameterization.  Large.
(C) Re-encode the three walk rules' prose-completion (e.g. re-attach
    through a rename on the output, or thread `β` positionally so no
    re-attachment freshness is needed) — touches the ALGORITHM's
    encoding; soundness (prop_soundness_sub) re-checks; needs sign-off
    on paper-faithfulness.
(D) Parameterize the ALGORITHM's fresh choices by an avoid-set
    (algorithm-side) — also encoding-touching.

Recommendation: (A) is the doctrinally clean one and its kit is
wanted anyway by the de-cofinite campaign; (C) is the cheap one if a
faithful re-encoding exists (e.g. `__skip` keeping `β` in place
instead of walking it out — but that changes the walk's measure and
the paper's rule shape).

**USER DECISION SUPERSEDED (same day, second directive): DEFER P7a's
freshness to a UNIFORM ENCODING CAMPAIGN.**  The observation: the
codebase currently has FOUR freshness disciplines side by side —
(i) the `F` avoidance-set parameter threaded through the consis
mutual (`a_consis`/`a_unify`/`a_assign`'s first index; consumed in
exactly ONE rule, `a_assign__solve_m`, where the guessed `βs` avoid
`F ∪ {α} ∪ dom (Ξ ++ Θ0)`; pure pass-through everywhere else),
(ii) prose-completed Barendregt `∉ dom Θ1` premises on the walk's
re-attachments, (iii) exists-fresh with side conditions (ForallR
after the encoding fix, Flex-Solve's deposits), (iv) cofinite
quantification elsewhere.  That is non-canonical.  The directive:
ONE canonical treatment of rule encoding, executed as a single
deliberate pass together with the standing de-cofinite campaign —
and the `F` avoidance set is to be DEPRECATED in that pass (its one
real consumer, Solve-M's fresh `βs`, moves to the canonical
discipline).  P7a (and hence the bundle's flex half) WAITS for that
campaign; do not build the rename kit piecemeal now.

**Still actionable before the campaign**: the bundle's MAIN half —
the P7b dispatcher over the join's last rule (all row lemmas are
Qed) — can be built with the flex half as an explicit hypothesis,
plus K0 (the consis converse-dom lemma) as a standalone fact if
useful.  The kit map below is RETAINED as the campaign's
reference, not as current work:

- **K0** (small, first): the CONVERSE dom lemma for the consis mutual
  — `dom Θ1 [<=] dom (Ξ ++ Θ0)`-shaped (`a_assign_unify_consis`
  creates NO new names: assign attaches only the caller's Ξ, whose
  names are subject-derived; the existing `_dom_mono` at
  prop_consis_rename.v:91 is the growth direction, same 20-line
  mutind shape).  Consequence: the ONLY junk sources in a_sub runs
  are (i) ForallR's junk suffix Ξj, (ii) ForallL's extract-Ξ (the
  look's LE-FlexR picks + guess-mono's fresh flexibles), (iii)
  Flex-Solve's deposited α̂,β̂.  Each becomes CONTEXT for everything
  downstream of its introduction, so the rename must still traverse
  all judgments.
- **K1**: `a_assign_unify_consis_rename_flex` — rename a FLEX context
  entry β0→β1 (undefined at entry; may become DEFINED during the run —
  the rename carries through the definition payload) through the
  consis mutual.  Mirror the tvar version
  (`a_assign_unify_consis_rename_tvar`, prop_consis_rename.v:1070,
  ~570 lines); the positional discipline differs (flex entries move
  under the reorder kit, unlike the rigid `tvar_prefix` discipline).
- **K2**: the look/solve/extract layer — renaming β0 as a collected
  or context name through `a_looksub`/`a_lookeq`/`a_solve_*`/
  `a_guess(_mono)`/`a_extract` (the looked-var and rigid renames
  exist; the flex-name congruences are subst-stability-shaped).
- **K3**: the mutual `a_sub`/`a_sub_flex` junk rename built on K1+K2:
  `run → β0 ∉ dom Θ0-input → β1 fresh → run with β0→β1 renamed
  outputs` (output context, output skeleton P1/A both renamed).
- **K4**: package transport under the rename — `a_inc`/`a_inc_equiv`
  rename a source-flex KEY (positional: rename the metasubst key;
  images unchanged), precision transports since the composed lookups
  agree.
- Consumption: in the walk rows, if the IH's Θ1 collides with β,
  K3-rename the run at a fresh β1 and re-derive the package by K4;
  then the re-attachment premises hold.

Also settled while scoping the bundle (recorded for the assembly):
the joint measure is lex(fuel, |context|, |subject|): the third
component covers the NON-incrementing subject-peeling join rows
(`gv__univ_ghost_l`/`_lg`, same fuel, same context — the memory's
plain "lex(fuel, |Θ0|)" note was incomplete); Flex-Assign re-enters
the MAIN half at a context one entry smaller (second component);
Flex-Solve's re-entry join at the arrow painting can only end with
`__arrow` at mode `fn M` (every other row's mode or subject shape
mismatches), so it drops fuel through the Arrow row lemma; the flex
motive should carry `a_flex_tvar Θ0 α` (not `(Ξ++Θ0)`) so the
Θ0 = nil walk case refutes — the walk preserves it (Assign with
β̂ = α̂ exits to the main half before it could break).

## 2026-07-31 — ⭐⭐⭐ Sub-ForallL CLOSED: `a_sub_complete_forall_l_tagged` / `_untagged` Qed — ALL SEVEN P7b ROWS DONE; only P7a + the bundle remain

Both variants of P7b's last row landed (end of
prop_sub_complete_thm.v), Qed + axiom-free, `make coq` green.  The
assembly follows the paper :3374-3453 exactly as mapped, with these
session discoveries folded in:

- **The motive gained the external wf-Q premise**
  (`Θ ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q)`, in `sub_complete_concl` AND
  `sub_flex_complete_concl`): P5-gv's `Hwfq` cannot be derived from
  the fill (refinement does not transport wf — the standing doctrine),
  so it is the paper's external-wf side condition surfaced on the
  theorem.  Mechanical re-close of the 7 existing rows: Arrow inverts
  the arrow's wf for its codomain IH; ForallR moves the ∀-body's wf
  down with `a_wf_pskl_delta_to_tvar` (its freshness pick gains `Lw`).
- **P6-L now returns `a_decls Ξ`** (the pieces were already in its
  proof: `all_flex_mono_a_decls` on the look's and the guess's
  blocks) — needed by the package's Ξ-flex-block peels.
- **The package avoids upstream peel surgery**: the peel lemmas only
  return `dom`-facts, but the tails are identified by LENGTH —
  `a_inc_same_length` (two increases from the same source have
  equally long metasubstitutions; the walk is positional) +
  `app_inj_tail_length`, both local.  `wb = κf` by `is_id_inc_unique`
  after `a_inc_peel_suffix`; `κ1b = κ` and `κ2b = ζ'∘κf` by the
  length identification on `a_inc_equiv_inc_peel_suffix`'s splits.
- **The TY ghost-freeness obligation** (P5-gv's `Hgf` at the swapped
  subject): a new row hypothesis carries the SUBJECT's TY
  ghost-freeness (`NM = TY → ghost_free (all-form Rj)` — the bundle
  threads it; at the headline the TY subject is the decorated type,
  ghost-free by sort); the INSTANTIATION's side comes from the
  TY-guess being a TYPE (`a_guess__ty` outputs `ptyp_to_pskl A`) via
  the new `pskl_to_uskl_paint_ghost_free` (induction on the
  PAINTING's lc with the type generalized — the lc_ptyp-based twin
  can't recurse through the binder).
- New leaf plumbing: `msubst_uskl_syn_pskl_to_uskl`,
  `ftag_in_uskl_pskl_to_uskl`, `a_wf_pskl_all_open`
  (`subst_pskl_in_pskl_intro` + `a_wf_pskl_subst_tvar`).

Coq gotchas (new): `a_wf_pskl_ftv_dom`'s `[<=]` lands UNFOLDED
pointwise after `pose` — fsetdec cannot consume the ∀-form, use
`apply (a_wf_pskl_ftv_dom H)`; `cbn` on erasures/paintings unfolds
the fixpoints into raw `fix` terms that later `match goal`/`rewrite`
patterns miss — prefer `change` with the constant forms;
`map_app`/`map_length` need the `List.` qualifier here;
`a_extract_family_of_instance` and both peels need `@`-application
(the handover's Set-Implicit-Arguments gotcha).

**Remaining for P7**: item 6 only — P7a (`sub_flex_complete_concl`'s
rows) and the lex(fuel, |Θ0|) bundle, which dispatches the join's last
rule to the row lemmas (ForallR before ForallL when `P0` is a ∀ — the
H3 WLOG), supplies the shield from the closed TASK-0 cases, and
threads the two new row hypotheses (shield, TY-subject
ghost-freeness) plus the motive's new wf-Q premise to the headline.

## 2026-07-31 — ⭐ Sub-ForallL enabler (iii) CLOSED: `ad_pat_sub_g_tyequiv_subject` Qed — ALL row enablers done, only the row + bundle remain

The ≡ᵘ-slack eraser landed (end of prop_sub_msubst_equiv.v), in three
parts, all Qed + axiom-free, `make coq` green:

- **Part 1**: `a_tyequiv_mono_iff` / `a_tyequiv_mono` (under a wf
  context ≡ᵗ preserves monotype-hood — proven as a BICONDITIONAL, the
  only way the `sym` case closes), `flex_def_paint_tyequiv`, and
  `ad_pat_sub_g_unfold_flex` (the flex UNFOLD twin of `fold_flex`,
  same fuel; consistency premises ride enabler (ii); `FlexMono` IS the
  unfolding).
- **Part 2**: `ad_pat_consis_paint_skl_transport` (consistency at a
  painting subject moves along ≡ᵗ for ANY types, via `a_tyequiv_pskl`
  + `skl_tyequiv_consis_transport` — no monotype restriction) and
  `ad_pat_sub_g_paint_tyequiv_subject` — the join at a MONOTYPE
  painting subject moves both ways along ≡ᵗ.  Architecture as planned:
  outer induction on ≡ᵗ (sym/trans structural, `flex_def` =
  fold/unfold, `__all` VACUOUS by `a_tyequiv_mono`); the arrow case
  runs one inner induction on the join per direction (generic-subject
  rows `__infer`/`__check`/`__forall_r`/`__univ_ghost_r` survive the
  subject-equation discriminate and rebuild via the paint-skl
  transport; `__forall_r` recurses through the inner IH with the
  context-monotone parameters reverted into the motive).
- **Part 3**: `ad_pat_sub_g_tyequiv_subject` — the join transports to
  ANY ≡ᵘ-related subject, fuel-preserving.  Leaf rows need NO ≡ᵘ
  inversion (enabler (ii) takes any related subject; guardedness rides
  `a_uskl_tyequiv_guarded` on the sym'd slack); congruence rows invert
  structurally, `__mono` endings reconstitute the node and delegate to
  part 2; the ForallL rows instantiate the inverted body family at the
  row's own ψ (`a_uskl_tyequiv_open`) and carry the `Ψ'`-tag
  conditions across by `a_uskl_tyequiv_ftag` (enabler (i)).

Coq gotchas collected: base-Θ of the paint-skl transport is invisible
to the conclusion — pin `with (Θ := Θ)` or `assumption` dies on the
evar; the inner inductions' `try (cbn in HeqS; discriminate)` ALSO
kills `__flex_mono` (its subject is a var, an arrow-painting is not) —
count surviving branches, don't assume; the transported subject cannot
be named `T` (the `__check` rule binder).

**What remains for Sub-ForallL**: ONLY item 5's row assembly
(`a_sub_complete_forall_l`, per the row plan in the re-scoping entry
below — every interface it consumes is now Qed) and item 6 (P7a +
bundle).

**ROW IMPLEMENTATION MAP (scouted, for the next session).**  Statement:
TWO variants (subject `uskl_all_tag ε Rj` / `uskl_all_syn Rj`),
each taking the IH bundle + the join row's fields as explicit
hypotheses (M ≠ ti, `Ψa ∩ Ψ`, `Ψa ∩ ftag(subject)`, `a_tags_sort`,
wf ⌊ψa⌋, the `_gv` premise at `(Ψ ∪ Ψa, open Rj ψa)`), plus
`sub_shield Θ0 Ψa ∅ P0 ψa` and the WLOG `guarded P0 ∨ P0 = ◇`;
conclusion `sub_complete_concl (S n) …` (the motive's own Hsub is
ignored — the future bundle dispatches, as ForallR did).  Steps with
the located kit:
(1) Pin `R = uskl_all_tag ε Rb` from Hrel by destructing R —
    var-R refutes since paintings never have `all_tag` heads (untagged
    variant: var-R refutes via image mono-ness, `a_inc_lookup_mono`);
    body family by inversion (∀-heads shape-rigid).
(2) Fresh α; feed P6-L (Ψsub := Ψ ∪ Ψa) at
    `R' := open Rb (var α)`: subject premise = forget(HD) slack-erased
    by `ad_pat_sub_g_tyequiv_subject` along `a_uskl_tyequiv_open`
    (sym'd body family, lc ψa via `is_tskl_lc`), then rewritten to the
    subst-form by `subst_uskl_in_uskl_intro` + κ-open commute
    (`msubst_uskl_syn_open`, α ∉ dom κ); ftag conditions via the
    body-instance of `a_uskl_tyequiv_ftag` + `ftag_in_uskl_open_var` +
    `ftag_in_uskl_msubst_uskl_syn` (prop_look_complete_cstr:171);
    Ψsub-range via `ad_pat_sub_g_ftag_sub` on forget(HD) +
    `ftag_in_uskl_open_upper` + `d_tags_skl_ftag`; subject wf via
    `uskl_to_pskl_open_gen` + `a_wf_pskl_msubst_inc`
    (prop_consis_complete:2695) + wf-of-opened-∀ =
    `subst_pskl_in_pskl_intro` + `a_wf_pskl_subst_tvar`
    (prop_sub_sound:132); fill = `ad_refine_syn_f_forget Hrs`.
(3) `uskl_precise_of_precise` on P6-L's precision (a_tags_sort
    inversion supplies is_tskl + d_tags) → item 2's
    `uskl_precise_open_into` (body-lc from `lc_uskl_of_pskl` +
    `a_uskl_tyequiv_lc`) → item 3 `ad_pat_sub_precise_upre_gv` on the
    ORIGINAL gv HD with (Ψsup := Ψa, Ψn := Ψ, Ψna := Ψa); its Hwfq
    (wf ⌊Q⌋) — find the P6-Sv/P6-Ss recipe for it (grep
    `ad_pat_sub_precise_upre` call sites) or derive from the row data.
(4) IH at `(Ξ++Θ0, κa++κ)` with subject `open Rb (pskl_to_uskl Pa)`;
    slack regenerated by `a_uskl_tyequiv_open` on the sym'd body
    family at ψPa := `pskl_to_uskl (msubst_pskl (κa++κ) Pa)` —
    `(κa++κ)Rb = κRb` by `msubst_uskl_syn_agree` (κa keys = Ξ keys,
    fresh from Θ0) and the embedding/msubst commute (grep
    `pskl_to_uskl`+msubst; provable by induction if missing); fill at
    `(κa++κ)P0 = κP0` by `msubst_pskl_agree`.
(5) Run: `a_sub__forall_l` with item 4's family on P6-L's look,
    `uniq (Ξ++Θ0)`, `HwfPa`.
(6) Package: mirror ForallR :2136-2278 with the α-tvar peel replaced
    by the Ξ-flex-block peel — `a_inc_suffix_prefix_inv`,
    `a_inc_equiv_tvar_inv`-style flex inversions (prop_metasubst:762
    area; a flex-block app-inversion may need writing),
    `msubst_compose_id_app_agree`, `is_id_inc_dom_mono`; the precision
    conclusion passes through unchanged (the output P1' is the opened
    run's own).

## 2026-07-31 — Sub-ForallL item 5 RE-SCOPED: "erase the ≡ᵘ slack" needs a WHOLE-JOIN transport (new work-list) + first ≡ᵘ enablers landed

Reading the row against the Qed interfaces exposed TWO gaps the
scoping entry's assembly sketch glossed over:

1. **"Erase the ≡ᵘ slack" is a real lemma, and it does not exist.**
   P6-L (`a_extract_complete_gen`) demands the join at the EXACT
   subject `(κR')[ψa/α]` with `R'` κ-free — P6-Ss inducts on that
   join, so no slack can ride along — while the motive supplies the
   join only at some `T` with `Θ ⊢ T ≡ᵘ κR`.  The slack design's
   "only the leaves transport" trick works for rows that consume
   consistency LEAVES (Infer/Check/Arrow-domain); ForallL hands the
   WHOLE join to P6.  Required new enablers, in dependency order:
   (i) ftag-preservation of ≡ᵘ (`ftag S' [=] ftag S`; the `__mono`
   row's paintings are tag-free on both sides); (ii) a decorated
   `ad_pat_consis` ≡ᵘ-subject transport (flex rows may relate
   DIFFERENT defined variables through `__mono`'s ≡ᵗ; a
   monotype-painting subject reduces to the pskl-level
   `skl_tyequiv_consis_transport` via `pskl_to_uskl_ptyp` after
   `ftag_sub` forces Ψ [=] ∅); (iii) the fuel-preserving
   `ad_pat_sub_gv` ≡ᵘ-subject transport (12 rows; consistency leaves
   by (ii), the `_gv` refinement leaves along
   `a_uskl_tyequiv_erase` + the pskl `skl_tyequiv_refine_*`
   transports, ForallL rows by `a_uskl_tyequiv_open` below).
2. **P6-L's join premise is pinned at tag context `Ψa`** while the
   row's premise runs at `Ψ ∪ Ψa`.  NOT a real repair job: P6-Ss
   (`a_looksub_solve_complete`) already carries the general range
   parameter `Ψsub` (`Ψa ⊆ Ψsub ⊆ ftag R' ∪ Ψa` — the ambient Ψ fits
   via `ftag_sub`); P6-L just instantiated `Ψsub := Ψa`.  Surface the
   parameter on `a_extract_complete_gen` (pass-through diff; the
   Δ = ∅ paper-facing corollary keeps `Ψa`).

**Landed now** (prop_sub_msubst_equiv.v, end): the ≡ᵘ row-enabler kit —
`a_uskl_tyequiv_all_syn_inv` / `a_uskl_tyequiv_all_tag_inv` (∀-heads
are shape-rigid: `__mono` cannot produce one), `a_wf_ptyp_paint_notin`,
`a_uskl_tyequiv_subst` (common substitution at a Θ-fresh variable; the
`__mono` leaves are Θ-scoped hence untouched — exactly the consumer the
rule's design note anticipated), `a_uskl_tyequiv_open` (instantiate
two ≡ᵘ ∀-bodies at a common lc argument), and — enabler (i) —
`a_uskl_tyequiv_ftag` (≡ᵘ preserves the syntactic tag reading; every
row is tag-homomorphic and `__mono`'s paintings are tag-free both
sides).  ALSO landed: the P6-L Ψsub surfacing (gap 2 above) — with a
fresh sighting of the evar-fsetdec wedge: the Δ = ∅ corollary's bare
`eapply` left `?Ψsub` undetermined (the conclusion never mentions it)
and the range obligations' `clear; fsetdec` WEDGED; pin `with
(Ψsub := Ψa)`.

**Enablers (i) and (ii) LANDED same session** (commits 7d4ecc4,
f4463ea): `a_uskl_tyequiv_ftag` and `ad_pat_consis_tyequiv_subject`
(+ its `__mono` catch `ad_pat_consis_mono_row_subject`), both in
prop_sub_msubst_equiv.v.  Gotcha recorded in the (ii) commit:
inversion does NOT discriminate the `__mono` branch by itself even at
∀/∀◇-headed subjects — the painting equation only refutes after
destructing `mono_ptyp` — so a uniform destruct-discriminate branch
precedes every congruence case.

**Enabler (iii) REFINED (scope cut found while starting it)**: the row
does NOT need the `_gv` join transport.  P6-L's premise is the PLAIN
`ad_pat_sub_g` (forget of the row's `_gv` join), and item 3's subject
swap runs on the ORIGINAL `_gv` join at `open Rj ψa` — untouched by the
slack; only P6-L sees the exact-κ-image subject.  So (iii) =
`ad_pat_sub_g_tyequiv_subject` (12 rows, fuel-preserving, no
refinement leaves — the consistency premises transport by (ii)).  Its
one hard branch is `__mono` at a painting-shaped subject (reachable at
`__arrow`/`__flex_mono`/`__infer`-with-painting nodes): delegate to a
helper `ad_pat_sub_g_paint_tyequiv_subject`
(`Θ ⊢ τ1 ≡ᵗ τ2 → _g at syn τ2 ∼ Q → _g at syn τ1 ∼ Q`) proven by
OUTER induction on the ≡ᵗ derivation — the same architecture as
`skl_tyequiv_consis_transport` (refl/sym/trans structural; arrow-cong
inverts the join at an arrow painting, where `__flex_mono` cannot fire
and the consis leaves use (ii)'s catch; the ≡ᵗ flex-unfold rows
rebuild via `ad_pat_sub_g__flex_mono`, whose `mode_fn` guard matches
the Arrow row's mode).  NB the top-level slack instance is ∀-headed,
where `__mono` cannot conclude — the branch only matters inside the
induction.

Row plan after the enablers (per the paper :3374-3453): erase the
slack with (iii) at the ∀-subject; invert the join's ForallL row;
P6-L (Ψsub-general) at the ψa-form; `uskl_precise_of_precise` + item
2's `open_into` build the ⊑ᵤ pair; item 3 swaps the subject to the
`(κa++κ)Pa`-form dropping Ψa; regenerate the IH slack from
`a_uskl_tyequiv_open` on the body family + κ→κa++κ agreement (Rb is
Θ0-scoped, κa's keys are Ξ's — fresh); IH at `(Ξ++Θ0, κa++κ)`;
`a_sub__forall_l` via item 4's family; package glue mirrors
Arrow's/ForallR's (`a_inc_equiv_glue`, junk-row peels).

## 2026-07-31 — ⭐ Sub-ForallL items 1–4 CLOSED — `uskl_precise_erase_refine`, `uskl_precise_subst_into`, `ad_pat_sub_precise_upre_gv`, `a_extract_family_of_instance` all Qed

**Item 4 (same session, fourth commit)** —
`a_extract_family_of_instance` (end of prop_look_complete_extract.v):
`a_sub__forall_l`'s cofinite extract family from the ONE instance
P6-L produces.  Exactly as scoped: the look's outputs (Ξ ⨾ 𝒞) never
mention the looked variable and solve/guess don't see it, so the
family = `a_looksub_rename_var` on the look + the SAME solve + the
SAME guess, with `subst_pskl_in_pskl_intro` folding the rename back
into the opening.  25 lines.  (Still a de-cofinite-campaign deletion
candidate once `a_sub__forall_l` goes exists-fresh.)

**Item 3 (same session, third commit)** — the LEAF-VALID transport of
P5, `ad_pat_sub_precise_upre_gv` (end of prop_sub_complete.v): the
precision-substitution over `ad_pat_sub_gv`, so the join's leaf
refinements survive the subject swap.  Built as a systematic mirror of
step (3):

- The 12-row main + the nine per-rule transports (`_gv` twins of the
  step-(3) `ad_pat_sub_g_*_transport` family) + the four uniform
  helpers (`psi_cong` / `refl_transport` / `wrap_tophole` /
  `fold_flex` / `hole_intro`).  The `_gv` analysis helpers reuse the
  `_g` ones through `ad_pat_sub_gv_forget` (`ftag_sub`,
  `concrete_target`) — only REBUILDING lemmas need real `_gv` twins.
- The NEW leaf obligations sit exactly where scoped: `__infer`,
  `__check`, `__univ_ghost_r`, and `__arrow`'s domain.  Each is
  discharged by **item 1** (`uskl_precise_erase_refine`) at Δ = ∅,
  whose assumed-target-wf premise is exactly the row's `Hwfq` (Check
  first rewrites the `bskl_to_pskl ∘ pskl_to_bskl_inh` roundtrip).
- Across the peels: `__tophole_remove`-on-the-ghostier-side wraps with
  `__tophole_remove` on the leaf (TI re-route inside `wrap_tophole`);
  `flex_l` re-folds the leaf with `ad_refine_pskl__flex_l`
  (`fold_flex`); the `upre__flex_r` peel (subject IS a defined
  flexible) unfolds the leaf with the NEW
  `ad_refine_pskl_unfold_def_subject` (the ⊳-mirror of
  `consis_unfold_def_subject`; ~25 lines, remember + explicit
  `revert HeqS` before the induction per the fixed-hypothesis gotcha).

Remaining: items 4–6 — the extract cofinite family, the row, P7a +
bundle.

## 2026-07-31 — ⭐ Sub-ForallL items 1 AND 2 CLOSED: `uskl_precise_erase_refine` + `uskl_precise_subst_into` Qed — item 1 in the PLAIN judgment, no `_f` mirror needed

**Item 2 (same session, second commit)** — the subst-INTO congruence
landed in the ⊑ᵤ-kit section of prop_consis_precise.v (right after
`uskl_precise_lc_l`, which it uses for the left side's lc), three
forms:

- `uskl_precise_subst_into_in` — the occurring form (`α0 ∈ ftv R`):
  induction over `lc_uskl R`; every occurrence replaces the SAME
  `Ψrep` and sets absorb (the arrow case pins `upre__arrow`'s
  `Ψ1`/`Ψ2` by explicit `with`-bindings — `Ψrep`/`Ψrep`, or
  `Ψrep`/`∅` via `subst_uskl_in_uskl_fresh_eq` + `upre__refl` when a
  component misses the variable; NB `apply IH; assumption` cannot
  instantiate the Ψ-evars — `assumption` never instantiates evars, and
  pinning also dodges the evar-fsetdec wedge on the union equality).
- `uskl_precise_subst_into` — the packaged disjunction
  `∃ Ψrep', (Ψrep' [=] Ψrep ∨ Ψrep' [=] ∅) ∧ …` (top-level
  `In_dec`; absent case = `fresh_eq` both sides + `upre__refl`).  The
  ∃ is fine here and NOT inside the binder rows — a per-β existential
  under `upre__all_syn`'s cofinite family could not be assembled into
  one `Ψrep`, which is why the occurring form is the primitive.
- `uskl_precise_open_into` — the OPENING form the ForallL join rows
  actually consume (their premise runs at subject
  `open_uskl_wrt_uskl R ψ`): `subst_uskl_in_uskl_intro` at a fresh α +
  the packaged form; body-lc premise stated as
  `∀ α, lc_uskl (R ^ α)` so it inverts from either `lc_uskl
  (uskl_all_syn R)` or `lc_uskl (uskl_all_tag ε R)`.

Note `subst_uskl_in_uskl` IS the uskl-into-uskl substitution (ott
sort-naming quirk — its payload argument is a `uskl`); there is no
`subst_uskl_in_uskl`.

## 2026-07-31 — ⭐ Sub-ForallL item 1 CLOSED: `uskl_precise_erase_refine` Qed — in the PLAIN judgment, no `_f` mirror needed

`make coq` green from clean; axiom-free (`Print Assumptions` closed).
Item 1 of the Sub-ForallL plan (the entry below) landed at the end of
`frost/algo/prop_consis_precise.v`:

    Lemma uskl_precise_erase_refine :
      Θ ⨟ Δ ⊢ᵣₚᵃᵈ Qm ⊳ Qr → a_wf_aenv Θ → (∀ α ∈ Δ, α ∉ dom Θ) →
      Θ ⨟ Δ ⊢ₚₛᵃ Qr →
      ∀ Θb Ψr R' R, uskl_precise Θb Ψr R' R →
      (∀ x b, binds x b Θb → binds x b Θ) → ⌊R⌋ˢ = Qm →
      Θ ⨟ Δ ⊢ᵣₚᵃᵈ ⌊R'⌋ˢ ⊳ Qr

**DESIGN DEVIATION — the scoping entry's "candidate resolution" (state
item 1 over the F-indexed mirror `ad_refine_pskl_f` + prove
`ad_refine_pskl_f_wf0` in an F-clean form) was NOT taken.**  The wf∅
crux dissolves the way `ad_refine_syn_trans` (prop_precise.v) already
dissolved the same crux: the TARGET's wf is ASSUMED — the paper's
external-wf side condition (declarative.tex:1427), which the use site
already carries (P5's `Hwfq : Θ' ⨟ ∅ ⊢ₚₛᵃ ⌊Q⌋`) — and the □-node's
empty-Δ form is recovered from the Δ-discipline.  Why this beats the
F-form: (a) the `_gv` joins' leaf refinements are PLAIN `⊢ᵣₚᵃᵈ` at
Δ = ∅, so the plain statement slots into item 3 with zero conversion;
(b) the conclusion derivation is rebuilt node-by-node at the SAME
(possibly `__tophole_fill`-extended) context as the input — wf over
the UNEXTENDED context, the thing `__tophole_fill` cannot transport
(`cex_p7_sskl_precise.v`), never arises; (c) the F-clean `wf0` would
need "the path's opened binders ∈ F", which a fixed F cannot express
for cofinitely-quantified binders without a rename kit.

**New kit** (all in prop_consis_precise.v, end of file):

- `ad_refine_pskl_ftv_policed` — the Δ-discipline transport: a set S
  fresh for Θ and absent from the source is absent from the target
  (fills are wf∅ hence Θ-scoped; flex definitions Θ-scoped; fresh
  binders re-bound by the target ∀).  Unlike the bskl-level
  `ad_refine_syn_syn_delta_free` it needs NO syn-painting/shape
  restriction: the policed set is decoupled from the judgment's Δ, so
  `__all` / `__tophole_fill` just pick their binder outside S.
- `ad_refine_pskl_hole_l` — the □-helper (mirror of
  `ad_refine_syn_hole_l`): a ghost refines to anything a wf∅ source
  refines to, given target wf at Δ; = policed transport +
  `a_wf_pskl_delta_shrink`.
- `uskl_precise_mono_refine` — ⊑ᵤ against a MONOTYPE syn painting
  yields the erasure-refinement into the painting.  Discharges the
  rows where the refinement side is exhausted (var ⊳ var on a defined
  flexible) while the precision keeps unfolding definitions
  (`upre__flex_r` under `__var`).

**Main proof shape**: outer induction on the ⊳-derivation; per case,
reconstitute the node (`Hrr`), then inner `revert Heq; induction Hp;
intros Heq; simpl in Heq; try discriminate Heq` — the erasure equation
kills all shape-mismatched ⊑ᵤ rows; three administrative rows are
shared `Local Ltac`s (`erase_refine_hole` / `_remove` / `_flexl`);
congruence rows re-enter the outer IHs; `__flex_l`'s inner
`upre__flex_r` aligns definitions by `binds_unique` and re-enters the
outer IH at `⌊ptyp_to_uskl_syn τ⌋ = ptyp_to_pskl τ`
(`uskl_to_pskl_ptyp`).

**Gotchas** (new, beyond the thm file's list): (i) `induction Hr`
names each case's recursive premise `Hr` (the inducted hypothesis's
own name), NOT `H` — non-recursive premises still go `H`, `H0`;
(ii) the `change (pskl_tophole ⌊R⌋) with ⌊uskl_tophole R⌋`
re-expression needed before consuming an IH must happen AFTER
`intros`-ing the `__tophole_fill` cofinite premise — doing it before
the constructor is useless, `apply`'s unification re-reduces it (and
leaves a raw `fix`, unmatchable by `match goal`); (iii) an inner IH's
Δ is not inferable from its arguments — instantiate positionally.

**Remaining** (per the scoping entry below): items 2–6 — subst-into
congruence, the `_gv` transport of P5 (item 3 consumes item 1 exactly
at its `Hwfq`), the extract cofinite family, the row, P7a + bundle.

## 2026-07-31 — Sub-ForallL SCOPED end-to-end: six work items, one open gate (the shield residual)

Scoping session after ForallR's close; no code yet.  The row =
paper :3374-3453: P6-L extracts the guess, P5's precision-substitution
swaps the join's subject instantiation to the guess's semantic image
(fuel-preserved), the IH runs at `(Ξ ++ Θ0, κa ++ κ)`, algorithmic
`a_sub__forall_l` reassembles.  **Interfaces verified against the Qed
statements**:

- **P6-L** (`a_extract_complete_gen`, prop_look_complete_extract.v:1145)
  consumes: the `_g` join at subject `(κR')[ψa/α]` (forget from `_gv`), the
  fill, wf/mode/freshness data, `a_tags_sort NM Ψa ψa`, tag-disjointness,
  `Θ ⨟ Δ ⊢ₚₛᵃ ⌊ψa⌋ˢ`, `delta_def_fresh`, and **`sub_shield Θ0 Ψa ∅ P0 ψa`**.
  Returns Ξ, Pa, κa with the extract run, wf(Pa), wf(Ξ++Θ0),
  `keys κa = keys Ξ`, `(κa++κ) ∷ Ξ++Θ0 ⊑ Θ`, `a_inc_equiv Θ0 κ κ Θ`, and
  `Θ ⨟ Δ ⊢ₚᵣᵃᵈ msubst (κa++κ) Pa ⊑ ⌊ψa⌋ˢ`.
- **The shield gate**: supplies exist for `pskl_flex_free Θ0 P0`
  (`sub_shield_flex_free`), ∀-free P0 (`sub_shield_supply_all_free_p0`),
  inh-free counterpart, mono-ish counterpart, atomic P0
  (prop_sub_shield_supply.v §4-§8).  ⚠️ THE RESIDUAL — P0 an arrow with a
  `pskl_all_syn` strictly BELOW its head, Θ0-flexibles inside, non-inh-free
  counterpart — is OPEN and "a new lemma of P6 size"
  (DESIGN-completeness-subtyping §9.0.2).  DECISION: the ForallL ROW takes
  `sub_shield` as a ROW HYPOTHESIS (like Check's external wf); the bundle
  supplies it from the closed cases and the residual stays the documented
  gate on the headline theorem.
- **P5** landed as `ad_pat_sub_precise_upre` (prop_sub_complete.v:1637,
  ⊑ᵤ-form over `_g`, 12 rows, ~125 lines) with the kit in
  prop_consis_precise.v: `uskl_precise` (:1231, LEFT = the substituted/
  ghostier side), `uskl_precise_of_precise` (:1446 — builds the leaf ⊑ᵤ
  from the P6-L precision), `uskl_precise_subst` (:1359 — subst-OF cong),
  `ad_pat_consis_precise_subst` (:852 — the consis-level subject-subst
  form).  ⚠️ NO subst-INTO congruence exists yet (item 2 below), and NO
  `_gv` version exists (item 1).

**The six work items** (in dependency order):

1. **`uskl_precise_erase_refine`** — THE key new lemma, replacing both "1a
   erasure-refinement" and "1b pskl-trans" of the first sketch with ONE
   FUSED induction (general `ad_refine_pskl_trans` is NOT needed and its
   all-vs-tophole_fill case is nasty — avoid):

       Θ ⨟ Δ ⊢ᵣₚᵃᵈ Qm ⊳ Qr → a_wf_aenv Θ → (Δ ∩ dom Θ = ∅-style disj) →
       (wf sides as needed) →
       ∀ Θb Ψr R' R, uskl_precise Θb Ψr R' R → (binds-mono Θb → Θ) →
       ⌊R⌋ˢ = Qm → Θ ⨟ Δ ⊢ᵣₚᵃᵈ ⌊R'⌋ˢ ⊳ Qr

   Induct on the ⊳-derivation; invert `uskl_precise` at each erasure
   shape.  The upre rows that are Qm-shape-INDEPENDENT (refl / hole /
   tophole_remove / flex_l) are handled uniformly (`__hole` uses wf Qr;
   upre__hole itself CARRIES `Θb ⨟ ∅ ⊢ₚₛᵃ ⌊R⌋`).  Congruence rows pair up
   (arrow/all_syn/all_tag/all_inst ↦ __arrow/__all with
   `strip_uskl_open` for the erasure-open commute; tophole-family ↦
   __tophole_keep with the guard from wf, or __tophole_fill REBUILT from
   Hr's own Θ-extended premise family — binds-mono composes into the
   extension).  flex rows use `binds_unique` to align definitions.
   Mirror ad_refine_syn_trans's remember/inner-induction skeleton
   (prop_precise.v:423-572).
   ⚠️ **THE CRUX FOUND WHILE DESIGNING IT** (stopped here, nothing
   written): the upre__hole inner case must conclude `□ ⊳ Qr`, whose rule
   demands `Θ ⨟ ∅ ⊢ₚₛᵃ Qr` — and refinement does NOT transport wf∅ from
   source to target through `__tophole_fill` (the target's ∀-syn body may
   mention the Θ-side binder via a FILL — the `cex_p7_sskl_precise.v`
   phenomenon; `a_wf_pskl__tophole` checks ∀◇-bodies at Δ = ∅, so the
   tvar→Δ wf move is false there).  This is the memory's "new holes' fills
   must stay Δ-clean" caveat materializing.  Candidate resolution: state
   item 1 (and hence item 3's leaf obligations) over the F-INDEXED mirror
   `ad_refine_pskl_f` with the path's opened binders in F — `_f`'s __hole
   row carries `F ∩ ftv(fill) = ∅`, which is exactly the Δ-cleanliness
   that makes the □-node's target wf∅-able; the `_gv` leaves are consumed
   through `ad_refine_pskl_f_empty_intro` + the `_f` transports anyway, so
   the F-form is the natural home.  Verify against how
   `a_consis_complete` threads its own precision (`ad_precise_f` with
   F = Δ1∪Δ2) — that is the shape to mirror.  Also note: wf∅-of-target at
   a □-source node IS derivable from the node's own subderivation when the
   source is wf∅ AND the derivation is F-clean along the path — prove
   `ad_refine_pskl_f_wf0` in that form, not the plain one.
2. **`uskl_precise_subst_into`**: `lc_uskl R → uskl_precise Θ Ψr ψ' ψ →
   uskl_precise Θ Ψr' (R[ψ'/α]) (R[ψ/α])` with Ψr' = Ψr-or-∅ depending on
   α's occurrence (upre's congruence rows take exact set equalities; state
   the disjunction or demand α ∈ ftv).  ~60 lines over lc_uskl.
3. **`ad_pat_sub_precise_upre` → `_gv`**: copy the 12-row proof; the NEW
   obligations are the leaf refinements at `__infer` / `__check` /
   `__univ_ghost_r` / `__arrow`'s domain: compose the row's own leaf
   `⌊Rg⌋ ⊳ ⌊Q⌋` with item 1 to get `⌊Rg'⌋ ⊳ ⌊Q⌋` (wf(⌊Q⌋) is P5's
   existing Hwfq premise; wf-plumbing per row).
4. **Extract cofinite family from ONE instance**: `a_sub__forall_l`'s
   premise is cofinite in the LOOKED var α'.  Cheap: `a_looksub_rename_var`
   (prop_looksub.v, exists) renames the looked var KEEPING Ξ ⨾ 𝒞, and the
   solve/guess components don't mention it (look-output-freshness), so the
   family is the renamed look + same solve + same guess.  ~40 lines.
   (This is also a de-cofinite-campaign candidate — converting
   `a_sub__forall_l` to exists-fresh would delete this step; defer.)
5. **The row** `a_sub_complete_forall_l` (shape: subject `uskl_all_tag ε
   R` / `uskl_all_syn R` — TWO variants or one lemma over both rows'
   common data; row hypotheses: the join row's fields incl. the tag
   conditions + `sub_shield`).  Assembly: erase the ≡ᵘ slack; P6-L; move
   the join's premise subject κ→(κa++κ) along the slack (the motive's ≡ᵘ
   + `a_inc_equiv Θ0 κ κ Θ` reflexivity makes this the SAME slack — check
   whether a new ≡ᵘ-generation step is even needed); build the ⊑ᵤ premise
   by `uskl_precise_of_precise` on P6-L's precision + item 2; item 3
   swaps the subject; IH at `(Ξ++Θ0, κa++κ)` (fuel PRESERVED — `_gv`'s
   ForallL rows are the S n rows, the substituted derivation is at n);
   algorithmic `a_sub__forall_l` with item 4's family + `uniq (Ξ++Θ0)`
   (from P6-L's wf) + `(Ξ++Θ0) ⨟ ∅ ⊢ₚₛᵃ P1` (P6-L's wf(Pa) — note P1 :=
   Pa's EMBEDDING?  check `a_sub__forall_l`'s P1 sort against Pa); package
   glue mirrors Arrow's (`a_inc_equiv_glue` across Θ0 → Ξ++Θ0 → Θ1).
   ⚠️ H3 hazard (DESIGN §9.1): the WLOG "guarded P0 ∨ P0 = ◇" — the row
   receives it as a hypothesis; the BUNDLE dispatches ForallR first when
   P0 is a ∀ (the join inversion order must reflect it).
6. **Bundle + P7a** after the row: lex(fuel, |Θ0|) induction; P7a's flex
   walk (measure |Θ0| at fixed fuel); the ForallL case is where the
   shield-hypothesis surfaces as the headline's documented premise until
   the residual closes.

## 2026-07-31 — ⭐ Sub-ForallR CLOSED: `a_sub_complete_forall_r` Qed + axiom-free — P7b has ONE row left (Sub-ForallL)

`make coq` green from clean.  The row landed the same day as the encoding
fix below, and NEEDED it: with the exists-fresh `a_sub__forall_r`, the IH's
ONE run at one fresh binder IS the rule's premise — no renaming machinery,
no cofinite family construction.

**The row** (`prop_sub_complete_thm.v`, `a_sub_complete_forall_r`): takes
the fuel-n IH + the join's `__forall_r` cofinite family as a row hypothesis
(the bundle owes the inversion, as for Arrow).  Structure:

- FILL pins the input: `ad_refine_syn_f_all_inh_r_shape` (only `__all` and
  a ∀◇-headed `__tophole_remove` reach a ∀-inh counterpart; `__hole` fills
  are SYN paintings, `__flex_l` chains bottom out in monotype paintings) +
  the painting/msubst inversions give `P0 = ∀.(ptyp_to_pskl A0)` — the ∀◇
  branch dies on `skmod[TY]` (an embedded TYPE has no ∀◇ head).
- IH premises at (Θ0,α ⊑ Θ,α): wf-body via `a_wf_pskl_all_syn_open_tvar`,
  κ extends by `a_inc__tvar (Ξ:=nil)`, the ≡ᵘ slack weakens by the new
  `a_uskl_tyequiv_weaken_cons`, and the fill's opened body moves Δ→Θ by the
  new SYN mirror `ad_refine_syn_f_reassoc(_mid)`.
- OUTPUT: `a_sub_ty_tc_output` ((TY,TC) returns its input — Check/ForallR
  by shape, ForallL passes through; the paper's :3243 equivalence detour is
  unnecessary at this mode) and the context decomposition
  `Θo = Ξ ++ (α~tvar) ++ Θ1` comes FREE from `a_inc_tvar_inv` on the run's
  own identity increase — no rigid-spine surgery.  Barendregt payloads:
  `is_id_inc_dom_mono` (an id-increase loses no names) gives
  `dom Θ0 ⊆ dom Θ1`, whence `uniq (Ξ ++ Θ0)` and the rule's freshness.
- PACKAGE: extend the caller's id along `a_inc__tvar (Ξ:=Ξjunk)`; peel ζ's
  junk rows with the new `a_inc_suffix_prefix_inv` (a declaration-only
  source prefix is consumed one κ-row each), strip the binder with
  `a_inc_tvar_inv` / `a_inc_equiv_tvar_inv` (nil-suffix by uniq), and
  collapse the composite with `msubst_compose_id_app_agree` (the junk rows'
  domain is disjoint from Θ0's flexes).
- PRECISION rebinds the quantifier from the α-instance via the GHOST-FREE
  route: `ad_refine_syn_f_ghost_free_strip_rename` (the subject is an
  embedded type — TY-mode has no ghosts to fill), with `msubst_pskl_agree`
  moving the subject off the junk rows and `msubst_pskl_subst_var` +
  `subst_pskl_in_pskl_intro` collapsing the rename; the ⚠️ evar-fsetdec
  wedge (this file's own warning) bit twice — pin every freshness in a
  NAMED assert before rewriting.

**New reusable pieces**: `a_sub_ty_tc_output`, `is_id_inc_dom_mono`,
`a_inc_suffix_prefix_inv`, `msubst_lookup_app_notin`,
`msubst_compose_id_app_agree`, the fill-inversion kit
(`ad_refine_syn_f_all_inh_r_shape`, `pskl_to_bskl_inh_{all_inh,tophole}_inv`,
`msubst_pskl_{all_syn,tophole}_inv`, `ptyp_to_pskl_{not_tophole,all_syn_inv}`),
`ad_refine_syn_f_reassoc(_mid)`, `ad_refine_syn_f_fgrow`,
`a_uskl_tyequiv_weaken_cons` (prop_sub_msubst_equiv.v).

**Remaining in P7b**: Sub-ForallL (P6-L + Task 0's shield + the P5
precision-substitution's `_gv` transport), then P7a and the bundle.
**Then the user-directed CAMPAIGN: drop cofinite encoding from the WHOLE
algo layer** (exists-fresh + rename lemmas; decl stays cofinite; no mixed
encodings within a layer) — a_consis's three ∀-rows, `a_sub__forall_l`'s
extract family, the solve/look/guess clusters, and the decorated mirrors.

## 2026-07-31 — ⚠️ ENCODING FIX opening Sub-ForallR: `a_sub__forall_r` / `a_subtag__forall_r` are now EXISTS-FRESH (one Barendregt binder, junk suffix per run)

`make coq` green from clean, axiom-free.  Found while scoping P7b's
Sub-ForallR: both ForallR rules quantified the discarded junk suffix `Ξ`
OUTSIDE their cofinite family — demanding ONE list shared by every fresh
binder α.  That is not the paper's rule and it BREAKS COMPLETENESS: the
paper (full-algo-spec.tex:806) runs ONE fresh α and discards Ξ ("anything
in Ξ is not mentioned in the result"), and the junk may lawfully MENTION
α — an extraction guess created by `a_lookeq__flex_r` (RHS a flexible) can
be eq-constrained against the binder and solved above it — so no shared Ξ
exists.  Soundness never noticed (it only CONSUMES the rule).

**The fix (user-directed)**: EXISTS-FRESH — the rule takes ONE binder α
with the Barendregt freshness side condition
`α ∉ dom (Ξ ++ Θ0) ∪ dom Θ1 ∪ ftv A ∪ ftv B` (prose-completion; the same
style as `a_sub_flex__solve`'s deposited names) and a single premise run at
`Ξ ++ (α~tvar) ++ Θ1`.  Completeness then needs NO renaming machinery: the
IH's one run IS the premise.  (Two richer encodings were built and
discarded on the way: a function-valued `Ξf : atom -> aenv` inside the
cofinite family — rejected as exotic-name-dangerous — and a
binder-opened template suffix; both survive only in this log entry.)

**Consumers of the cofinite family, reworked** (the cost of exists-fresh is
that consumers no longer choose the binder):

- `prop_sub_sound`'s ForallR already worked from ONE fresh instance — its
  `atom_fresh` is gone, the rule's α serves, and `α ∉ dom Ξ/dom Θ1` now
  come from the output's `uniq`.
- `a_subtag_psi_cong`, `a_subtag_decoration_var`, the decoration bundle's
  ForallR: single-instance maps at the rule's own α; the ∀-body wf that was
  read off the cofinite wf inversion now comes from the new helper
  `a_wf_pskl_all_syn_open_tvar` (prop_consis_sound.v: cofinite instance +
  reassoc + `a_wf_pskl_rename_tvar`).
- **`a_subtag_decoration`'s ForallR is the instructive one**: it pushes a
  substitution `[ψa/αv]` through the derivation and needs every binder ≠ αv
  — binder freedom exists-fresh does NOT give.  Resolution: the case
  RE-FRESHENS ITS OWN αv away from the now-in-scope α — the look run moves
  by `a_looksub_rename_var` (already existed), its ∀-target opens AT α by
  the NEW `a_looksub_open_target_at` (given-opener form of
  `a_looksub_open_target`; its LS-ForallR case renames ONE representative
  with `a_looksub_lookeq_rename_tvar`, which keeps the shared 𝒞 because
  the representative avoids `ftv 𝒞`), and the detour collapses by the NEW
  `subst_uskl_in_uskl_rename_compose`.  This per-case re-freshening is the
  exists-fresh discipline's standing recipe for substitution transports.
- `a_looksub_lookeq_rename_tvar` (+ `ftv_subst_var_keep`,
  `subst_var_pskl_neq_var`) MOVED from prop_look_complete_cstr.v to
  prop_looksub.v — the decoration layer now needs it below itself.
- test_examples' three ForallR constructions pick a concrete `atom_fresh`.

**Standing decision**: the user wants cofinite encodings dropped from the
ALGORITHMIC layer wholesale (exists-fresh + rename lemmas everywhere);
that big-bang is a SEPARATE campaign — this fix converts only the two
ForallR rules, which is what P7b needs.

**Remaining for Sub-ForallR** (scoped, in order): (i) output decomposition
`Θo = Ξ ++ (α~tvar) ++ Θ1` via rigid-spine preservation + first-nonflex
split; (ii) `(TY,TC) ⇒ output = P0` (syntactic — Check/ForallR return P0,
ForallL passes through, Arrow/FlexMono are FN-mode); (iii) fill inversion
at `bskl_all_inh` pinning `P0 = ∀α.P0'` (mirror
`ad_refine_pskl_f_tophole_r_shape`'s flex_l-kill); (iv) IH transports (wf
reassoc ✓ kit, κ cons-tvar via `a_inc__tvar (Ξ:=nil)`, NEW ≡ᵘ cons-tvar
weakening, fill Δ→Θ move — syn mirror of `ad_refine_pskl_f_reassoc`);
(v) the rule's freshness conditions (α picked fresh; dom-parts from the
run's uniq, `α ∉ ftv Θ1-images` NOT needed — no family to share);
(vi) package: peel ζ's Ξ-flex rows (new `a_inc` source-flex-prefix
inversion), then `a_inc_tvar_inv` / `a_inc_equiv_tvar_inv` exactly as
consistency's ForallInh (prop_consis_complete.v:7095-7118), and the
precision re-binds the quantifier via the `ad_refine_syn_f_rename` route
(same file :7140-7179).

## 2026-07-31 — ⭐ Sub-Arrow CLOSED: `a_sub_complete_arrow` Qed + axiom-free — SIX of P7b's seven rows done

`make coq` green from clean, zero admits.  The row landed on essentially the
first assembly pass because the blueprint — the consistency Arrow case at
prop_consis_complete.v:6631-6790 — mapped over almost 1:1 once the ≡ᵘ slack
and its kit were in place (the entry below).

**The row** (`prop_sub_complete_thm.v`): takes the fuel-n IH (the full
motive) + `R = uskl_arrow Ra Rb` via the conclusion's shape (the bundle owes
the flex-dispatch-first disambiguation).  Structure: invert the join (only
`__arrow` matches the arrow subject at `mode_fn M`); split the ≡ᵘ slack with
`a_uskl_tyequiv_arrow_arrow_inv`; `skmod` inversion splits `P0 = P0a → P0b`
keeping the codomain's mode-compat implications; fill inverts componentwise.
DOMAIN: erase the slack component and transport the `__arrow` leaf data
(consis via `skl_tyequiv_consis_transport`, refinement via the pskl
transport) to `κ⌊Ra⌋`, then `a_consis_complete`; its run's
`a_consis_sound_aux` gives the id-witness w1 + wf Θ1 + the Θ1-join for the
output's SCOPE.  CODOMAIN at (Θ1, ζ1): wf's weaken by `a_wf_pskl_isub`; the
IH's slack = `a_uskl_tyequiv_trans` of the motive component with
`a_inc_equiv_msubst_uskl` (at Hie1), collapsed by
`msubst_uskl_syn_compose_id` (every Rb-variable is Θ0-bound —
`a_wf_pskl_ftv_binds_tvar` + `ftvar_in_pskl_uskl_to_pskl`; rigids are
outside both domains by `binds_unique` discrimination); the fill moves κ→ζ1
by `msubst_compose_id_pskl` + `a_inc_equiv_msubst_pskl` + the syn transport.
ASSEMBLE `a_sub__arrow`; package: `a_sub_sound` gives w2; `is_id_inc_unique`
identifies κf = w1; `a_inc_equiv_glue` (dom-mono via
`a_assign_unify_consis_flex_preserve` over the domain run); precision is
`ad_refine_syn__arrow` with the domain source moved ζ1→ζ2 along ≡ˢ
(scope from `ad_pat_consis_target_wf` — NO wf-of-⌊Q1⌋ side condition, the
lighter route the consistency case already used; my earlier
`ad_refine_syn_trans` sketch was needlessly heavy).

**New helpers**: `ad_refine_syn_f_empty_intro` (syn mirror of the pskl
intro), `a_wf_pskl_ftv_binds_tvar` (Δ-closed wf ⟹ every variable Θ-bound),
`msubst_compose_id_lookup` + `msubst_uskl_syn_compose_id` (obligation 7b).

⚠️ Import gotcha: `prop_decorate_sub` SHADOWS the ptyp-level `msubst_lc`
(its ρ machinery has a uskl-valued one) — Require it BEFORE `prop_normal`.

**Remaining in P7b**: Sub-ForallR (Ξ-suffix strip; `_fgrow` transport kit
waiting), Sub-ForallL (P6-L + P5c + Task 0's shield — and the P5
precision-substitution still needs its `_gv` transport, whose one new fact
is that it preserves the leaves' subject refinement).  Then P7a and the
bundle assembly.

## 2026-07-31 — Sub-Arrow's enablers: the ≡ᵘ SLACK is in the motive, the Arrow leaf premise landed, all five rows re-closed

Continuation of the motive repair below, opening the Sub-Arrow campaign.
All Qed + axiom-free; `make coq` green.

**⚠️ `ad_pat_sub_gv__arrow` gained the DOMAIN leaf premise** — the Arrow
row's domain-consistency premise is ITSELF a consistency leaf (the paper's
Sub-Arrow invokes thm:complete-consistency on it, :3334), so it now carries
`Θ ⨟ ∅ ⊢ᵣₚᵃᵈ ⌊R1⌋ˢ ⊳ ⌊Q1⌋` like `__infer` does.  Caught while planning the
Arrow row; the leaf-valid design's rule of thumb is now explicit: EVERY
rule field of sort "consistency judgment" is a leaf and carries the
subject refinement.

**⚠️ The κ→ζ1 REBASE ROUTE IS DEAD — remember why.**  The plan to build
`κ2 ∷ Θ1 ⊑ Θ` agreeing with κ syntactically (so the codomain IH needs no
transport) founders on `a_inc`'s POSITIONALITY: a run can move a flexible
BELOW a binder (the optimality-cex fact), so ζ's row for that flexible
needs image-wf at a SMALLER Θ-suffix than κ's derivation ever supplies.
This is also why consistency's own Arrow case transports its second
component's premises SEMANTICALLY at the fixed Θ (prop_consis_complete.v
:6686-6727) rather than rebasing.  Follow that precedent.

**The ≡ᵘ kit** (`frost/algo/prop_sub_msubst_equiv.v`, new file):
`a_uskl_tyequiv` (`Θ ⊢ R ≡ᵘ R'`) — same tagged skeleton, ≡ᵗ-monotype
paintings at the leaves; STRUCTURAL rows only (inversion at a known shape
stays trivial; refl/sym are lemmas), the `__mono` row carries wf at the
relation's own Θ, binder rows keep the same Θ.  Lemmas: refl (lc), sym,
`a_uskl_tyequiv_erase` (≡ᵘ → ≡ˢ on erasures), the generation workhorse
`a_inc_equiv_msubst_uskl` (pointwise-equivalent increases give ≡ᵘ images;
each leaf fact reads off `a_inc_lookup_{wf,mono}` / `a_inc_equiv_lookup`),
ghost inversions (`hole_l_inv` / `holeg_l_inv`: ghosts are ≡ᵘ-inert), lc,
and `a_uskl_tyequiv_guarded` (guardedness transports — a mono painting is
always guarded).

**The motive carries the slack**: `sub_complete_concl` (and the flex half)
now take the join at an arbitrary subject `R'` with
`Θ ⊢ R' ≡ᵘ (msubst_uskl_syn κ R)` — so Sub-Arrow's codomain IH will take
the ORIGINAL join derivation unchanged (relation premise built by
`a_inc_equiv_msubst_uskl`), and only the consistency LEAVES transport, via
`a_uskl_tyequiv_erase` + the EXISTING pskl-level transports
(`skl_tyequiv_{consis,refine_syn_f,refine_pskl_f}_transport`,
prop_consis_complete.v).  This mirrors how the paper does it "informally by
type equivalence" (the author's own margin note at completeSubtyping).
All five closed rows re-closed under the slack: Ghost/GhostG use the ghost
inversions, Infer/Check/UnivGhostR erase the slack and transport their
leaf facts from `R'` to `κP` before the `a_consis_complete` call;
Check/UnivGhostR get `guarded_pskl P` through `a_uskl_tyequiv_guarded`.

**Naming**: the slack subject is `R'` (uskl ⇒ R-family; the first cut's `T`
violated the metavariable convention).  The Check rows' pskl `B` is the
PAPER's `B` (the inherited btyp of `syn A ⩽ inh B`, embedded) — a
pre-existing rule binder of `ad_pat_sub_g__check` kept to avoid the
inversion-auto-name hazard.

**Sub-Arrow's remaining assembly** (next session).  The row mirrors
prop_consis_complete.v's arrow case :6631-6790 — domain via
`a_consis_complete` (its three premises from the `__arrow` leaf data +
fill inversion), run soundness for the id-witness w1 + wf Θ1 + isub,
package at w1 → (ζ1, Hie1, Hprec1); codomain IH at increase ζ1 with the
slack; assemble `a_sub__arrow`; glue with `a_inc_equiv_glue` +
`is_id_inc_unique`; move the domain precision ζ1 → ζ2 via
`a_inc_equiv_precise_msubst(_flip)` + `msubst_compose_id_pskl` +
`ad_refine_syn_trans` (⚠️ external wf of `⌊Q1⌋` — WF-SIDE-CONDITIONS
pattern).  The row takes `R = uskl_arrow Ra Rb` as a premise (bundle owes
the disambiguation; flex-dispatch first).

**The EXACT remaining ≡ᵘ obligations, scoped 2026-07-31** (the IH's slack is
`R2' ≡ᵘ msubst ζ1 Rb`, built from the motive's component `R2' ≡ᵘ κRb` and
generation's `κRb ≡ᵘ σRb` — which needs TRANSITIVITY, deliberately not a
row; and the motive's arrow relation must split into components).
✅ **(1)–(7a) LANDED same day, all Qed + axiom-free** in
prop_sub_msubst_equiv.v: `a_tyequiv_downarrow_refl` (with
`msubst_ptyp_tyequiv_pointwise` + `a_tyequiv_weaken_cons1`),
`a_tyequiv_arrow_inv`, `ptyp_to_uskl_syn_inj`, `a_uskl_tyequiv_mono_r_inv`,
`a_uskl_tyequiv_trans`, `a_uskl_tyequiv_arrow_arrow_inv`,
`msubst_uskl_syn_agree`.  Still open: (7b) the compose-id pointwise fact at
the row's call site, and (8) the row assembly itself.  Coq gotchas hit:
`congruence` closes a goal that IS a hypothesis; `injection ... as` with
variable LHSs substitutes instead of naming; the `usklvar`-vs-`atom` alias
makes hand-typed `(β == α)` scrutinees miss the goal's `if` (destruct via
`lazymatch goal with |- context [if ?c then _ else _]`); the `__var_typ`
rule binder `A` shadows a lemma-level `intros A`:

1. `a_tyequiv_downarrow_refl : a_wf_aenv Θ → Θ ⊢ A ≡ᵗ ⇓ᵗ[Θ]A` — the ⇓
   REFLECTION, the one genuinely new fact (prop_normal.v has only the
   forward `a_tyequiv_downarrow`).  Θ-structure induction + inner
   τ-induction; flex-def leaf via `aenv_msubst_lookup_def` + the
   `__flex_def` row; needs ≡ᵗ cons-weakening.
2. `a_tyequiv_arrow_inv` : `τa→τb ≡ᵗ τa'→τb'` → component ≡ᵗs — via (1) +
   `a_tyequiv_downarrow` + cbn (⇓ is an msubst, homomorphic on arrows) +
   injection.
3. `ptyp_to_uskl_syn` injectivity (tiny).
4. `a_uskl_tyequiv_mono_r_inv` : anything ≡ᵘ a MONO PAINTING is itself one
   (with ≡ᵗ to it) — induction over the relation against τ's mono shape.
5. `a_uskl_tyequiv_trans` — induction on the first derivation, inversion
   on the second; the mixed mono/structural middles collapse via (4); the
   mono∘mono case is ≡ᵗ-trans; binder rows take L-unions.
6. `a_uskl_tyequiv_arrow_arrow_inv` — `__arrow` direct; `__mono` via (2)
   after painting-arrow inversion (destruct τ).
7. uskl compose-id collapse: `msubst_uskl_syn_agree` (lookup-agreement ⇒
   equal images, mirroring `msubst_ptyp_agree`) + the pointwise fact from
   `msubst_compose_id_pskl`'s underlying lemma — so
   `msubst (ζ1∘w1) Rb = msubst ζ1 Rb` on Θ0-scoped `Rb`.
8. The row assembly itself, per the recipe above.

⚠️ Dead end to remember while proving (5)/(6): the relation CANNOT express
`arrow ≡ᵘ defined-var` — that is fine, because (4) shows any side ≡ᵘ-related
to a mono painting IS a mono painting syntactically (paintings are
structural, so `arrow (painting τa) (painting τb) = painting (τa→τb)`
definitionally); the apparent counterexamples dissolve into the `__mono`
row.

## 2026-07-30 — ✅ THE MOTIVE REPAIR LANDED: leaf-valid join `ad_pat_sub_gv`, root third premise GONE, Sub-UnivGhostR proved FOR REAL

`make coq` green from clean (exit 0, 45 `Print Assumptions` all closed, zero
admits).  Executes the repair the review below called for, same day.

**The new relation** — `ad_pat_sub_gv` (def_decl_algo_sub_hyg.v): a verbatim
copy of the tag-hygienic fuel mirror `ad_pat_sub_g` whose three
CONSISTENCY-LEAF rows additionally carry the subject's refinement into the
leaf's counterpart: `__infer` and `__univ_ghost_r` at `bskl_to_pskl Q` (for
UnivGhostR that IS the stripped counterpart — the rule's conclusion is
`∀◇.Q`), `__check` at `B` directly.  The ghost leaves carry nothing (their
refinement is derivable from their own wf premises).  `ad_pat_sub_gv_forget`
recovers `_g` for every P5/P6 invocation.

**The motives** (prop_sub_complete_thm.v): `sub_complete_concl` /
`sub_flex_complete_concl` now take the `_gv` join and NO root-level subject
refinement.  New plumbing: `ad_refine_pskl_f_empty_intro` (plain `⊳` → `_f`
at `F = ∅`; converse of `_forget`), `ad_pat_sub_gv_ti_refine` (every TI row
yields the subject refinement — note `congruence` closes the `__infer` case
itself, the goal IS the rule's premise).

**Row adaptations**: Ghost / GhostG — one `ad_pat_sub_gv_forget` line each
(they never used the old premise).  Infer — takes the refinement from
`ad_pat_sub_gv_ti_refine` instead of the motive.  Check — takes it as a row
premise (the `__check` leaf's own field, which the bundle will supply by
inversion).

**Sub-UnivGhostR is now a REAL proof** (`a_sub_complete_univ_ghost_r`, Qed +
axiom-free) instead of vacuous-by-contradiction, and it is exactly the
paper's route (:3282): `skmod[SK]` pins `P0 = □`; the subject erasure is
guarded (`guarded_uskl_msubst_erase`, moved up from the Check section), so
the run is algorithmic `UnivGhostR` outputting `∀◇.P` at `Θ0`; the precision
runs the shared `□`-P0 core (`a_sub_complete_hole_p0_precision`) at the
STRIPPED counterpart — `ad_refine_syn_f_hole_tophole_inv` strips the motive's
fill from `∀◇.Q` to `Q` (only `__hole` has a `◇` source; its painting target
must be a `pskl_tophole`, whose body inherits wf and hygiene) — and wraps
both sides with `ad_refine_syn__tophole_keep`, whose guard is
`guarded_bskl_inh_repaint` (guardedness survives erase-and-repaint;
`guarded_bskl__arrow` carries `lc`, so transport `lc_pskl_to_bskl_inh ∘
lc_bskl_to_pskl`).

**Coverage check**: the three cex configurations (`unit ⩽ ∀◇.unit`,
`∀a.a ⩽ unit`, `unit ⩽ ∀a.unit`) are now inside the theorem's coverage —
their leaf refinements are `unit ⊳ unit`.  The capture configuration stays
correctly excluded (its Infer leaf demands `∀X.◇ ⊳ ∀X.X`).  Both cex files
kept as historical witnesses, headers updated.

**⚠️ REMAINING OBLIGATION (registered in DESIGN §1 + PAPER-GAPS)**: the P5
precision-substitution (`ad_pat_sub_precise_upre`) and the `_n→_g`
freshening/renaming kits must be transported to `_gv` when the ForallL /
ForallR rows are written.  The one genuinely NEW fact: precision-substitution
must preserve the leaves' subject refinement (ghostier subject ⟹ erasure
refines further, but new holes' fills must stay Δ-clean).  Also still open:
the paper-facing corollary must either take leaf-validity as a premise (SK
mode) or derive it from the join for hole-free subjects (TY mode — the
restricted derivation lemma DESIGN-subtyping §3.1 sketched).

## 2026-07-30 — ⚠️ REVIEW of the UnivGhostR vacuity: the third premise truncates FAR more than one row — P7b's motive must be repaired before further rows close

Requested review of the vacuity finding below.  Verdict: the finding was
correct but UNDERSTATED.  Everything here is machine-checked; `make coq`
untouched (the new file compiles standalone, axiom-free).

**The diagnosis.**  The motive's third solution premise
`⊢ᵣₚᵃᵈ κ⌊R⌋ˢ ⊳ ⌊Q⌋` is a **LOCKSTEP** condition — `ad_refine_pskl` descends
subject and counterpart together, so it can only hold where the two sides
agree in shape (modulo ghosts on the LEFT and flexible definitions).  It was
imported verbatim from `a_consis_complete`, where it is the PAPER'S OWN
augmentation (consistency-proofs.tex:2230-2242) and harmless — because
`ad_pat_consis` is itself lockstep (its ∀-inh-counterpart rows
`__forall_inh_tagged` / `__forall_inh_untagged` / `__tophole_inh` all demand
a ∀-or-ghost subject), so on consistency the condition adds only the
no-capture discipline on hole fills it was designed for.  Subtyping's
`ForallL` / `ForallR` / `UnivGhostR` exist precisely to BREAK lockstep, so
the verbatim import cuts exactly the solutions those rules create.

**New counterexample file** `frost/algo/cex/cex_p7_third_premise_forall.v`
(Qed + axiom-free): two configurations satisfying the paper's two solution
conditions, well formed and mode-compatible, that FAIL the third premise —

- `∀a.a ⩽ unit` (Sub-ForallL): third premise `∀a.a ⊳ unit`, no rule;
- `unit ⩽ ∀a.unit` (Sub-ForallR): third premise `unit ⊳ ∀a.unit`, no rule.

So the mechanized theorem currently says nothing about ForallL
instantiation or ForallR generalisation — i.e. about most of TY-mode
subtyping — not just about the ∀◇ corner.

**The repair (registered as option (c), RECOMMENDED, in PAPER-GAPS.md).**
Move the condition from the ROOT to the CONSISTENCY LEAVES of the
declarative derivation: subject-refinement data exactly at `__infer` /
`__check` / `__univ_ghost_r` (the latter at the STRIPPED counterpart `Q0`),
either as a leaf-augmented `ad_pat_sub_g` variant or as a mirror predicate
over the derivation.  Why this is right: (i) it is precisely what the
`a_consis_complete` invocations consume — Infer/Check use the current
premise ONLY for that (checked: Ghost/GhostG never touch it); (ii) it holds
in all three cex configurations (each leaf is `unit ⊳ unit`); (iii) it still
excludes the capture configuration `(P0=◇, P=∀X.◇, Q=∀X.X)` whose Infer leaf
demands `∀X.◇ ⊳ ∀X.X`.  Cost: transporting leaf-validity through the P5
precision-substitution and the freshening kits; the five closed rows'
substantive content (`a_inc_equiv_precise_msubst`,
`a_sub_complete_hole_p0_precision`) survives unchanged.

**Paper-side fallout (also registered).**  The paper's TOP-LEVEL 2-condition
`thm:complete-consistency` (full-algo-spec.tex:1473-1546) is FALSE as
literally stated — only the augmented 3-condition proof statement is true,
and the 2-condition form is not derivable from it (same capture
configuration).  `thm:complete-subtyping`'s Infer / Check / UnivGhostR /
Arrow cases invoke the false top-level form; under the true one they need
the leaf refinement, which the paper's 2-condition subtyping-solution notion
does not supply.  A restricted derivation lemma (join ⇒ leaf refinement for
HOLE-FREE subjects) is plausibly true and would rescue the paper's statement
for TY-mode; SK-mode needs the leaf-validity notion.

**Docs updated**: PAPER-GAPS.md (MECH-PREMISE entry extended + paper-side
consequence), DESIGN-completeness-subtyping.md §1 (third-premise bullet now
carries the refutation + repair), cex_p7_univ_ghost_r_vacuous.v header
(follow-up note), CLAUDE.md TL;DR.

## 2026-07-30 — P7b: metasubstitution-stability CLOSED, and with it Sub-Infer / Sub-Check; ⚠️ Sub-UnivGhostR is VACUOUS under the motive's third premise

`make coq` green from clean, all `Print Assumptions` closed, zero admits.
Everything below is in `frost/algo/prop_sub_complete_thm.v` unless said
otherwise.

**PRECISION IS STABLE UNDER EQUIVALENT METASUBSTITUTIONS** —
`a_inc_equiv_precise_msubst` (+ `_gen`, `_flip`), Qed + axiom-free.  This was
the one piece DESIGN §9.1.1 left open, and the induction is on the **wf of
`P`**, not on `≡ˢ`: the equivalence in play is congruence over `P`'s own
structure with `≡ᵗ`-MONOTYPES at the leaves, because a metasubstitution's
images are monotypes.  `unit` / `hole` are constructors, `arrow` / `all` /
`tophole` congruences (the last by `__tophole_keep`, whose guard wf supplies and
`msubst` preserves), and the flexible leaf is `tyequiv_mono_refine_syn`
verbatim.  Two corrections to the plan: the guessed Δ-freshness side condition
is NOT needed (only `Δ0 ⊆ Δ` is — the variable row splits on `α ∈ dom κ` /
`α ∈ dom σ`, and BOTH answers are usable: a hit gives `a_binds_tvar α Θ0` via
`a_inc_dom_flex`, a double miss makes both sides the same variable); and the
hypothesis is stated POINTWISE (`∀α, a_binds_tvar α Θ0 → Θ ⊢ κα ≡ᵗ σα`), which
is what makes the FLIPPED direction free — Sub-Check needs it, and `a_inc_equiv`
itself is not obviously symmetric.

**Sub-Infer and Sub-Check CLOSED** (`a_sub_complete_infer`,
`a_sub_complete_check`, Qed + axiom-free), both by the paper's own route
(:3134): `skmod` forces `P0 = □` at Infer; `a_consis_complete` on the
consistency subproblem `(Θ0; □; P)`; `a_consis_hole_p0_output` says the run
returns the SUBJECT; the stability lemma + `ad_refine_syn_trans` move the
precision from the theorem's ζ to κ.  Shared core:
`a_sub_complete_hole_p0_precision`.  Supporting, all Qed:
`uskl_to_pskl_msubst_uskl_syn` (the one-line commutation),
`ad_pat_sub_g_ti_consis` (at `M = TI` only `__infer` / `__ghost` / `__ghostg`
fire, and all three carry a TAG-FREE consistency), and
`ad_refine_syn_hole_l_target_wf`.

⚠️ **Sub-Check does NOT need `a_consis_concrete_output_equiv`.**  The plan
routed its precision through the consistency OUTPUT, but `a_sub__check` hides
that output existentially inside `a_consis_chk` and returns `P0` — so the goal
is `ζP0 ⊑ ⌊Q⌋`, and at `Q = inh{B}` the motive's P0-FILL premise IS `κP0 ⊑ B`
by definition of `ad_precise`.  What `a_consis_complete` supplies there is
the RUN and the two increase conjuncts.  Sub-Check does take two hypotheses
beyond the motive, both for the bundle to supply and both registered in
docs/WF-SIDE-CONDITIONS.md: `guarded_pskl P0` (the algorithm's
Check-vs-ForallR dispatch — the paper's own case split) and `Θ ⨟ ∅ ⊢ₚₛᵃ ⌊Q⌋`
(external wf of the counterpart, which `ad_refine_syn_trans` needs; the
`P0 = □` rows get it free from `ad_refine_syn_hole_l_target_wf`).

⚠️ **Sub-UnivGhostR is VACUOUS under the motive's THIRD solution premise** —
machine-checked, `frost/algo/cex/cex_p7_univ_ghost_r_vacuous.v` (Qed +
axiom-free) plus `ad_refine_pskl_f_tophole_r_shape`.  The row's subject is
`guarded_uskl` and its counterpart is `∀◇.Q0`, so the premise reads
`κ⌊R⌋ˢ ⊳ ∀◇.⌊Q0⌋` with a guarded left — and refinement has no rule putting a
`∀◇` on the RIGHT of a non-ghost left.  The case is therefore proved BY
CONTRADICTION (`a_sub_complete_univ_ghost_r`, Qed) and the theorem says nothing
about the solutions it describes.  The premise is the MECH's, not the paper's
(`subtyping-proofs.tex:3054-3074` gives TWO conditions), and DESIGN §1's
justification for it — "it is what `a_consis_sound` / `a_sub_sound`
produce" — is HALF WRONG: `a_sub_sound` produces no subject-refinement
conjunct, and could not, since algorithmic `UnivGhostR` outputs `∀◇.P` from the
input `P`.  §2 of the cex file exhibits the smallest configuration where the
paper's two conditions hold and the third fails, so this is a real loss of
coverage.  The authors must decide; see docs/PAPER-GAPS.md and DESIGN §9.1.3.

## 2026-07-30 — P7 TASK 0: the flex-free and ∀-FREE branches CLOSED; the paper's own TODO property REFUTED

`make coq` green, all `Print Assumptions` closed, zero admits.

**TASK 0 (a) — the FLEX-FREE branch** (`prop_sub_shield_supply.v` §6, Qed,
axiom-free).  §10.6 gave `flex_apart` the base row `flex_shield` already had
(`fa_flexfree`), so `sub_shield` follows for ANY flex-free `P0`, uniformly in
ψa **and in Δρ** — subsuming §5's `sub_shield_atomic`.  The only content is
that flex-freedom survives both walks (`ss_walk_flex_free`,
`fa_walk_flex_free`): every `P0`-moving step takes a subterm or opens a ∀ at a
binder the AVOID SET keeps out of `dom Θ0`, and a variable outside the context
is bound nowhere, hence flexible nowhere.  Second payoff of the avoid set.

**TASK 0 (b) — the residual is far smaller than the plan assumed**
(`prop_sub_shield_supply.v` §7/§8, Qed, axiom-free).  ⚠️ The planned positional
route (`fsh_arrow`/`fsh_all_l`/`fsh_all_r` + the mono lemma at each flexible
leaf) is not what the case needs: **`bskl_monoish` was never the load-bearing
hypothesis.**  A tag LEAVES the index at exactly ONE rule in the whole system,
`ad_pat_consis__forall_inh_tagged`, whose counterpart is a `bskl_all_inh`;
every other row of consistency AND of subtyping forces `Ψ = ∅` on the rule or
passes Ψ down.  So the real hypothesis is `bskl_inh_free` — no INHERITED
quantifier in the counterpart — which admits ghosts and synthesised ∀s (all of
which refinement really produces) and needs neither `is_tskl` nor
`a_wf_aenv`.  New: `ad_pat_consis_inh_free_tag_free`,
`ad_pat_sub_g_inh_free_tag_free`, `ad_refine_syn_inh_free`,
`sub_shield_supply_inh_free_counterpart`, `sub_shield_supply_all_free_p0`.
The chain is `P0` has no ∀ ⟹ `κP0` has none (κ's images are monotypes) ⟹ the
refinement's output is inh-free ⟹ `Ψa = ∅` ⟹ the shield.  **Residual: a `P0`
carrying a ∀ BELOW its head** (the head is `unit | var | arrow | □` by the
WLOG) — see DESIGN §9.0.2 for exactly where the remaining work sits.

**⚠️ FALSE — the property the paper marks with its own TODO**
(`subtyping-proofs.tex:3243`, "when input `P_0` is a concrete type, RHS of algo
subtyping is always `P_0`").  Machine-checked:
`frost/algo/cex/cex_p7_concrete_rhs.v` (`p7_concrete_rhs_is_false`, Qed,
axiom-free).  Consistency's `FlexL` returns the SUBJECT, and algorithmic
`Arrow` copies it: at `P_0 = unit → unit` (concrete, and flexible-FREE) with
subject `α̂ → unit`, the RHS is `α̂ → unit`.  The witness carries wf and
`skmod[TY]`, so no side condition explains it away.  **This does not break
Sub-Check or Sub-ForallR** — the paper's own text for both already argues via
the EQUIVALENCE, which the output context (`α̂ ≔ unit`) supplies.  Only the
proposed simplification is refuted; the mech keeps the equivalence route.

**…and the CONSISTENCY half of that equivalence is PROVED**
(`frost/algo/prop_sub_concrete_rhs.v`, Qed + axiom-free).  The relation was
already in the development — `a_pskl_tyequiv` (`≡ˢ`), built for `a_inc`'s
GMM-style semantic middles, is exactly "definitions of flexible variables
unfold" — and the proof is on the REFINEMENT, not on consistency:
`a_consis_sound` already exports `Θ1 ⨟ ∅ ⊢ᵣᵃᵈ inh{P0} ⊳ Qt` with `⌊Qt⌋ = P'`, so
what is left is `ad_refine_syn_ghost_free_equiv` (refinement out of a ghost-free
source only unfolds definitions — one induction, no context threading, since
every ghost row is excluded and the two flexible lookups ARE
`a_pskl_tyequiv__flex_def`).  Hence `a_consis_concrete_output_equiv`:
`Θ1 ⊢ P0 ≡ˢ P'`, the paper's `:3181` step.  §4 adds the three transports the
`a_sub`-level half needs to MOVE an equivalence (`a_pskl_tyequiv_isub_mono` for
Sub-Arrow's `Θ0 → Θ1 → Θ2`, `_weaken`, `_subst_flex_def`).

**And the `a_sub` half is closed too** — `a_sub_concrete_output_equiv`.  It was
planned as a mutual induction with `a_sub_flex`; that is NOT needed:
`a_sub_sound` already exports the output's refinement FROM the input
skeleton, in the same shape `a_consis_sound` does, so the same lemma applies and
the half collapses to one `destruct`.  **Both cases the `:3243` TODO was meant to
simplify therefore get their step from the SOUNDNESS theorems.**  DESIGN §9.1,
PAPER-GAPS.md.

**P7's MOTIVE is LOCKED** — `frost/algo/prop_sub_complete_thm.v`
(`sub_complete_concl` / `sub_flex_complete_concl` / `a_sub_complete_bundle`,
typechecked; the unresolved subject is spelled `R`, the `uskl` metavariable,
not the paper's `S`).
Writing it out corrected DESIGN §1 in two places: the fuel judgment is
`ad_pat_sub_g`, not `ad_pat_sub_n` (precision-substitution is FALSE over `_n`,
and P5 + all five P6 lemmas are stated over `_g`); and ⚠️ the factored
`forall κ1 … exists ζ` conclusion is FORCED, not stylistic — `a_inc_equiv` is
POSITIONAL, so the paper's flat `inc[θ≡θ1]{Θ0}{Θ}` as `a_inc_equiv Θ0 κ ζ Θ`
with `ζ ∷ Θ1 ⊑ Θ` is not even the right SHAPE (ζ is keyed by Θ1, which has
entries Θ0 does not, and at Flex-Solve in the MIDDLE).  Also fixed: P7a's
context split — the FULL context is `Ξ ++ Θ0`, so its premises and `a_inc_equiv`
are stated there and the measure is lex(n, |Θ0|).

**The first two cases of P7b are closed** (same file, Qed + axiom-free):
`a_sub_complete_ghost` and `a_sub_complete_ghostg` — the ◇- and ◈-subject rows.
Each is wider than one declarative rule (at `N = SK` a ◇ subject admits
`__infer` as well as `__ghost`), but both algorithmic rules return the INPUT
SKELETON at the INPUT CONTEXT, so one witness serves both and the derivation is
inverted only to learn the counterpart's COLOUR, which the precision conclusion
needs.  They establish the leaf plumbing every axiom-node case reuses:
`opt_axiom_factor` (prop_metasubst.v) discharges the two increase conjuncts at
`ζ := κ`, and the precision conclusion IS the P0-fill premise once both sides
are repainted (`msubst_bskl_pskl_to_bskl_syn` +
`bskl_to_pskl_pskl_to_bskl_{syn,inh}` + `ad_refine_syn_f_forget`).

⚠️ **Sub-Infer / Sub-UnivGhostR: FOLLOW THE PAPER — an elaborate detour here was
my own misreading, and is retracted.**  The paper (:3134) says "the consistency
premise, together with `⌊S⌋ = P` and **thm:complete-consistency**, gives
`Θ ⊢ precise{θP}{Q}`" — i.e. it invokes a THEOREM already mechanized as
`a_consis_complete`, on the consistency problem `(Θ0; □; P)` (`skmod` forces
`P0 = □` in both rows).  I read it as "read a precision off the consistency
premise", refuted THAT, and then built a threaded induction and a Θ↔Δ transport
kit to repair something that was never broken.  ✅ All the paper's route needs
beyond the black box is `a_consis_hole_p0_output` (Qed): at `P0 = □` the
algorithmic consistency OUTPUT is the SUBJECT — only three of the fifteen rows
admit `P0 = □` and each returns its own subject — so the theorem's precision,
stated about the run's output, IS a precision about `P`.

What the detour produced and is worth keeping: `cex/cex_p7_sskl_precise.v` (the
SHORTCUT — precision from the consistency premise without completeness — is
FALSE, and structurally so: consistency opens a ∀ into Θ while refinement opens
it into Δ, so a consistency derivation may fill a ghost with a binder precision
cannot see; witness `∀◇.` vs `∀α. α`); the Θ↔Δ transport kit
(`a_wf_pskl_reassoc_mid`, `ad_refine_pskl_f_reassoc_mid` / `_reassoc`,
`ad_refine_pskl_f_fgrow`, the two `_weaken_tvar`s), all general facts about
refinement's hygiene index with Sub-ForallR's Ξ-strip the next likely consumer;
and the context-free `ad_pat_consis_ghost_subject_no_forall` /
`is_sskl_inh_no_forall`.  **Lesson: when the paper cites one of its own
theorems, follow the citation before inventing a lemma.**  Sub-Check is the same
shape one level up (`a_consis_complete` + `a_consis_concrete_output_equiv`).

**The two rows are now assembled down to ONE missing lemma.**  `skmod` gives
`P0 = □`; `a_sub__infer` gives the run (output `P` at `Θ0`, so the increase
conjuncts are `ζ := κ` + `opt_axiom_factor`); the DECORATED consistency premise
undecorates by `ad_pat_consis_strip_tags` plus a one-line
`⌊κR⌋ˢ = κ⌊R⌋ˢ` commutation; `a_consis_complete` applies at `(Θ0; □; P)`
because its other two premises ARE the motive's refinement premises at `P0 = □`;
and `a_consis_hole_p0_output` makes its precision a precision about `P`.  ⚠️ That
precision arrives under the theorem's own `ζ`, not under `κ`.  The missing lemma
is **precision is stable under equivalent metasubstitutions** —
`Θ ⨟ Δ ⊢ₚᵣᵃᵈ msubst_pskl κ P ⊑ msubst_pskl σ P` given `a_inc_equiv Θ0 κ σ Θ` and
wf of `P` — after which `ad_refine_syn_trans` composes.  ⚠️ Not the general `≡ˢ`
transport, which an earlier note here asked for and which is awkward (`≡ˢ` is an
equivalence CLOSURE, so the induction carries both directions and its `trans` row
wants wf of a middle skeleton nobody supplies).  Inducting on the WF OF `P`
sidesteps that: the equivalence in play is congruence over `P`'s structure with
`≡ᵗ`-MONOTYPES at the leaves, and that leaf case is already Qed —
`tyequiv_mono_refine_syn` (prop_precise_recover.v:90), with
`a_inc_equiv_lookup` + `a_inc_lookup_mono` supplying its premises.

**P7's MOTIVE is LOCKED** — `frost/algo/prop_sub_complete_thm.v`
(`sub_complete_concl` / `sub_flex_complete_concl` / `a_sub_complete_bundle`,
typechecked; the unresolved subject is spelled `R`, the `uskl` metavariable,
not the paper's `S`).
Writing it out corrected DESIGN §1 in two places: the fuel judgment is
`ad_pat_sub_g`, not `ad_pat_sub_n` (precision-substitution is FALSE over `_n`,
and P5 + all five P6 lemmas are stated over `_g`); and ⚠️ the factored
`forall κ1 … exists ζ` conclusion is FORCED, not stylistic — `a_inc_equiv` is
POSITIONAL, so the paper's flat `inc[θ≡θ1]{Θ0}{Θ}` as `a_inc_equiv Θ0 κ ζ Θ`
with `ζ ∷ Θ1 ⊑ Θ` is not even the right SHAPE (ζ is keyed by Θ1, which has
entries Θ0 does not, and at Flex-Solve in the MIDDLE).  Also fixed: P7a's
context split — the FULL context is `Ξ ++ Θ0`, so its premises and `a_inc_equiv`
are stated there and the measure is lex(n, |Θ0|).

**The first two cases of P7b are closed** (same file, Qed + axiom-free):
`a_sub_complete_ghost` and `a_sub_complete_ghostg` — the ◇- and ◈-subject rows.
Each is wider than one declarative rule (at `N = SK` a ◇ subject admits
`__infer` as well as `__ghost`), but both algorithmic rules return the INPUT
SKELETON at the INPUT CONTEXT, so one witness serves both and the derivation is
inverted only to learn the counterpart's COLOUR, which the precision conclusion
needs.  They establish the leaf plumbing every axiom-node case reuses:
`opt_axiom_factor` (prop_metasubst.v) discharges the two increase conjuncts at
`ζ := κ`, and the precision conclusion IS the P0-fill premise once both sides
are repainted (`msubst_bskl_pskl_to_bskl_syn` +
`bskl_to_pskl_pskl_to_bskl_{syn,inh}` + `ad_refine_syn_f_forget`).

**Sub-Infer / Sub-UnivGhostR: the lemma they share is FALSE, and the mech's own
third premise is what rescues them.**  Both carry `is_sskl Q` on the rule and
both algorithmic counterparts return the input skeleton at the input context, so
all that is left of either row is "consistency against an `is_sskl` counterpart
gives precision of the erasures" — the paper's `:3181` / `:3288` step.
Machine-checked FALSE: `frost/algo/cex/cex_p7_sskl_precise.v`
(`p7_sskl_precise_is_false`, Qed, axiom-free).  Witness `R = ∀◇.` against
`Q = ∀α. α` over the EMPTY context: consistency's ∀ rule puts the fresh binder
into **Θ**, so `__hole` may fill the ghost with it; refinement's ∀ rule puts it
into **Δ** and checks a fill at `Θ ⨟ ∅`, where it is out of scope.  Same Θ-vs-Δ
asymmetry that forces `ad_refine_syn_f`'s `F` to exist.  ✅ The second theorem in
that file shows the mechanization's THIRD solution premise (the SUBJECT's own
refinement, DESIGN §1's "lesson 1", not in the paper) is UNSATISFIABLE on the
witness — so the configuration never reaches either row, and the lemma should be
RESTATED with that premise, becoming a COLOUR BRIDGE
`ad_refine_pskl_f → ad_precise_f` whose only non-identity rows are `__hole` and
`__tophole_fill`.  ⚠️ Two earlier records in this session's DESIGN §9.1.1 (first
"false on a colour mismatch at ∀◇", then "holds") were both reasoned ahead of the
checker and are retracted there; the real break is the ∀-over-a-hole row.
Sub-Check is in neither group — its counterpart is `is_sskl` only when `B` is
∀-free, so it takes the paper's own route (`a_consis_complete` +
`a_consis_concrete_output_equiv`).

**Next unit on the corrected path, measured.**  Threading the subject-refinement
premise through the consistency induction collides with the binder disciplines:
consistency opens a ∀ into Θ, refinement into Δ.  The Θ→Δ direction exists
(`ad_refine_syn_f_strip`, under `F`-hygiene); the Δ→Θ direction does not and is
what the threading needs — the refinement analogue of `a_wf_pskl_reassoc`, with
NO hygiene condition since adding a Θ-binder only adds scope.  ✅ **Both transports LANDED** (Qed + axiom-free):
`a_wf_pskl_reassoc_mid`, `ad_refine_pskl_f_reassoc_mid`, and the head corollary
`ad_refine_pskl_f_reassoc`.  MID-INSERTION form is forced, not generality for
its own sake: `ad_refine_pskl_f__tophole_fill` extends Θ at the HEAD with its
own binder, so a head-only statement would need the IH at `(α1,α0),Θ` where the
goal wants `(α0,α1),Θ` — same `binds` graph, no congruence for it in either
judgment; the mid form absorbs the head into the left block.  (The existing
`a_wf_pskl_reassoc` is head-only and suffices there only because wf's ∀ rule
puts its binder in Δ, never in Θ.)  ✅ Plus the CONTEXT-FREE ghost-row fact
`ad_pat_consis_ghost_subject_no_forall` (`⌊R⌋ˢ = □` + `is_sskl Q` ⟹ `⌊Q⌋`
∀-free), which is what the threading needs where the two paintings can disagree.

✅ **The threading's transport kit is COMPLETE** — `ad_refine_pskl_f_fgrow`
plus `ad_refine_pskl_f_weaken_tvar` / `a_wf_pskl_weaken_tvar` (Qed).  F-GROWTH
is the piece that was missing: `_fmono` only SHRINKS `F`, but every ∀ row opens a
fresh binder and then wants to strip it, so it must first put that binder INTO
`F` — sound for a binder the context does not know, since a ghost fill is wf at
`Θ ⨟ ∅` and its free variables therefore live in `dom Θ`.  The route is settled
(induct on CONSISTENCY, carry the subject-refinement premise, and at each ∀ row:
invert `__all` → `fgrow` → `weaken_tvar` → IH → `ad_refine_syn_f_strip` →
`fmono`), and the ghost rows take their fill's wf from the REFINEMENT premise,
which is the premise doing the work.

⚠️ **One row is still open**, now small and exactly stated: at consistency's
`__tophole` / `__topholeg` the refinement premise need not decompose the same
way — inverting it gives `__tophole_keep` (the premise the IH wants) OR
`__tophole_remove` (`⌊R0⌋ ⊳ ∀◇.⌊Q'⌋`), and in the second case neither judgment
can re-wrap.  Needs a normalisation of the refinement premise at `∀◇`, or an IH
tolerating the extra `∀◇`.

## 2026-07-30 — P7 opened: the Δ = ∅ corollary, the P7 plan, and TASK 0's SUPPLY CLOSED on the branch that was blocking

`make coq` green from clean, all `Print Assumptions` closed, zero admits.

**`a_extract_complete`** answers "can P6-L's extra premises be absorbed?".
The two Δ-hygiene premises can, and now are: `delta_def_fresh Δ Θ` and
`Δ ∩ ftv ψa = ∅` are vacuous at Δ = ∅, which is where every consumer enters (Δ
tracks the counterpart's ∀-binders and grows only inside the precision
derivation).  ⚠️ `sub_shield` cannot be — it is P6-Sv's repair, and the paper's
statement without it is machine-checked FALSE (`cex/cex_p6sv_forall_flex.v`); it
can only be DISCHARGED where derivable.  The rest are the paper's own EXTERNAL wf
side conditions (docs/WF-SIDE-CONDITIONS.md) plus Barendregt freshness for α,
both supplied by the caller.

**DESIGN §9 is the P7 plan.**  P7 is a mutual bundle — P7a
(`lemma:complete-flex-subtyping`, :2836) ⇄ P7b (generalised
`thm:complete-subtyping`, :3050), then P7c — with a case map for P7b (§9.1) and
P7a's two interesting rows (§9.2).  Four of P7b's seven cases are applications of
the Qed `a_consis_complete`.

⚠️ **TASK 0 — supplying `sub_shield` at P7b's Sub-ForallL — is where P7 stands,
and its planned route is now REFUTED.**  `cex/cex_p7_sub_monoish.v`
(`p7_sub_monoish_counterpart_is_false`, Qed, axiom-free) shows the subtyping-side
analogue of `ad_pat_consis_monoish_counterpart` is FALSE: consistency's ∀ rules
require the counterpart to be a quantifier too — which is exactly why a mono-ish
counterpart forces the subject mono there — whereas subtyping's ForallL
INSTANTIATES.  So `∀^ε α. α` (`is_tskl`, ghost-free, legal at TY) instantiated
with a rigid β lands on the target β, which is `bskl_monoish` by `bmi_var`, while
the subject is no mono paint at all.  It is `ad_pat_sub_g__forall_l_tagged`
again — the same row, and literally the same witness derivation, as
`cex/cex_p6ss_sub_target_ftv.v`.

✅ **BUT ONLY THE SHAPE HALF IS FALSE, AND THE HALF THE SHIELD NEEDS IS TRUE —
`ad_pat_sub_g_monoish_tag_free` (`frost/algo/prop_sub_shield_supply.v`, Qed,
axiom-free) closes TASK 0's leaf.**

    ad_pat_sub_g n NM M Ψ Θ ψ Q → a_wf_aenv Θ → is_tskl ψ → bskl_monoish Q → Ψ = ∅

Unfolding `sub_shield` at Δρ = ∅, the flexible-P0 leaf admits only `fsh_clean`,
whose `ftag ψa ∩ Ψa = ∅` plus `d_tags_skl`'s `Ψa ⊆ ftag ψa` IS "Ψa = ∅" — so TAG
ACCOUNTING, not a shape bound, is what the wall needs, and that is exactly the
surviving conjunct.  One induction, through unchanged: a tag reaches the
conclusion's Ψ only by being SOLVED, i.e. by a rule MATCHING a tagged quantifier
of the subject against a quantifier of the counterpart; every other row carries
`Ψ = ∅` on the rule, delegates to `ad_pat_consis_monoish_counterpart`, or is
`is_tskl`-impossible.  ⚠️ `__forall_l_tagged` — the row that killed the shape
half — is harmless here: it DROPS its own ε and hands the IH `Ψ ∪ Ψ'`, so a
collapse below collapses Ψ too.  A `bskl_monoish` counterpart has no quantifier,
so nothing can be solved; and the counterpart IS mono-ish exactly where P0 is
flexible (metasubstitution images are monotypes +
`ad_refine_mono_paint_rhs_monoish`).

**So the flex-mono wall is NOT a blocker, and the earlier "P7 is blocked"
reading was wrong.**

✅ **AND THE SUPPLY IS CLOSED on that branch** — `sub_shield_supply_mono_counterpart`
/ `sub_shield_supply_mono_p0` (same file, Qed, axiom-free): a mono-ish
counterpart gives `sub_shield Θ0 Ψa ∅ P0 ψa` UNIFORMLY in P0, with the corollary
taking the refinement premise directly for `κP0` a mono PAINT — which is what a
raw Θ0-flexible P0 gives, since metasubstitution images are monotypes.  That is
exactly `cex_p6sv_forall_flex.v`'s configuration, so the premise P6-L had to
carry is discharged where P7b's Sub-ForallL needs it.  No positional
decomposition was needed here: once Ψa = ∅, `fsh_clean` ignores the payload and
shields every `ss_walk` residue at once.  The work was in the OTHER conjunct,
`flex_apart_walk` — where the invariant is that a TAG-FREE guess can never take
`fastep_all_r` (the only Δρ-growing step) while every other step preserves
tag-freeness, so Δρ stays put and `fa_clean` closes every walked point
(`fa_walk_tag_free` / `flex_apart_walk_tag_free` / `sub_shield_tag_free`).

⚠️ **ONE RULE NARROWED.**  `fastep_flexdef_r` installed `ptyp_to_uskl_syn τ` for
an UNCONSTRAINED τ, which makes `flex_apart_walk` underivable from cleanliness of
ψa (the walk admitted garbage no context justifies).  It now carries
`ftv (paint τ) ∩ Δρ = ∅` — exactly the fact its own comment said a call site
would discharge.  Cost zero: its single builder (P6-Sv's FlexMono row) already
had it in scope as `Hclean`, and the full rebuild was green first time.  ⚠️ The
fix recorded in the previous entry — "the Δρ' generality is slack, make
`sub_shield` Δρ'-monomorphic" — was WRONG: `sub_shield_add_fresh` genuinely uses
that quantifier.

✅ **The non-composite shapes of P0 are done too** — `sub_shield_atomic`: at
`unit` / `◇` / a RIGID variable NEITHER walk moves P0 (`ss_step`'s two rows need
an arrow or a ∀; of `fa_step`'s nine only the three ψ-side ones fire, and they
leave P0 alone), so the shield is one `flex_apart` constructor plus
`fsh_flexfree`, with no tag reasoning at all.

⚠️ **AND THAT RESIDUAL IS UNSATISFIABLE, NOT MERELY UNPROVED** — machine-checked,
`cex/cex_p7_shield_arrow.v` (two witnesses, Qed, axiom-free).  `sub_shield`'s
`flex_apart_walk` conjunct quantifies over the ρ-walk, and Sub-ForallL's step
`fastep_all_r` (built by P6-Sv's own ForallL row) opens a tagged quantifier of
the guess at a fresh β, adds β to Δρ, and LEAVES P0 alone — so the walk reaches
`flex_apart Θ0 {β} P0 (var β)`, and at an ARROW P0 no rule applies.  **The
repair is a MISSING MIRROR:** `flex_shield` carries `fsh_rho_var` (added because
"WITHOUT this rule the premise is TOO STRONG"), `flex_apart` never got it, and
`fa_rho_var` kills both witnesses.  ⚠️ **HELD PENDING THE AUTHORS' DECISION** —
`flex_apart` is P6-Cv's repair premise, so reshaping it changes a side condition
the paper must adopt; cost measured in docs/PAPER-GAPS.md (the ~8 inversion
lemmas are clerical, but `flex_apart_flex_var_clean` genuinely breaks and P6-Cs's
Arrow row needs rework).

**TASK 0's RESIDUAL IS EXACTLY ONE SHAPE.**  P7b's Sub-ForallL comes with the
paper's WLOG `guarded(P0) ∨ P0 = □`, and `guarded_pskl` is `unit | var | arrow`,
so a ∀ / ∀◇ P0 never reaches the call.  `□` / `unit` / rigid var → §5; FLEXIBLE
var → §4 (κP0 IS that variable's monotype image, so Q is mono-ish); any P0 with a
mono-ish Q → §4.  ⚠️ **What is left: P0 an ARROW with a non-mono-ish Q** — there
Ψa need not collapse and P0 need not be flex-free, so neither `fsh_clean` nor
`fsh_flexfree` fires and the shield must come from `fsh_arrow`, i.e. it needs ψa
to be an ARROW there — genuine structural ALIGNMENT between P0 and the guess.
That is the pipeline invariant, and it is the last thing task 0 owes.  DESIGN
§9.0.

## 2026-07-30 — ⭐⭐⭐ P6-L CLOSED — **P6 IS COMPLETE** (all five lemmas); P7 opens

`make coq` green from clean, 35 `Print Assumptions` all closed under the global
context, zero `admit` / `Admitted` in `frost/`.  `a_extract_complete_gen`
(subtyping-proofs.tex:2730, `frost/algo/prop_look_complete_extract.v`) is `Qed`
and axiom-free, and with it **P6's five lemmas are all closed**:
`P6-Cv → P6-Cs → P6-Sv → P6-Ss → P6-L`.

**The encoding fix that had to come first.**  `a_extract` now carries a context
and runs its solve at `Ξ ++ Θ0`:

    a_extract__solve : P ≼[α,m] P' ⤳ Ξ ⨾ 𝒞 -> (Ξ ++ Θ0) ⊩ 𝒞 ⨾ □ ⤳ Q
                       -> a_guess NM Q Ξ' Q' -> Θ0 ⊢ P ⊳[NM,α,m] P' ⤳ (Ξ++Ξ') ↪ Q'

The old `Ξ`-only reading made P6-L UNPROVABLE.  `a_solve_eq__flex_r` is the only
context-sensitive rule in the whole solve cluster, `Ξ` alone hides Θ0's
flexibles, and P6-Ss delivers its solve at `(Ξc ++ Θ0)`.  The paper's solve and
guess judgments are CONTEXT-FREE (`full-algo-spec.tex:1216-1375` — there `α̂` is
a syntactically distinct metavariable class), so this is a faithfulness FIX, not
a design change; it is the same unfaithful narrowing already corrected once at
that very rule.  Soundness was unaffected — `a_extract_decls` reads Ξ, not the
solve, and `a_extract_decorate`'s solve lemmas quantify Θ universally.

**The proof, and where the paper's one-liner hides work.**  The paper's
`(a)`–`(g)` are a direct assembly: P6-Ss at `Pi := □` / `Ψi := ∅` (whose
precision premise IS the precision hole rule), then P5b-i
(`ad_partial_precise_complete`) upgrading `⊑ᵖ[Ψa]` to plain `⊑ ⌊ψa⌋ˢ`.  The work
is the third premise — the paper's *"by induction on the definition of
guess^N(P_s)"*:

- **We CHOOSE the guess.**  P6-L's conclusion is existential in Ξ and the
  extract output, so `a_guess_ty_witness` BUILDS `a_guess_mono` and the
  metasubstitution extension κ′ SIMULTANEOUSLY, descending `P_s` on
  `size_pskl`, and reads the counterpart's matching piece off the precision
  premise at each step.
- ⚠️ **`guess_join_witness` does NOT serve P6-L**, contrary to what DESIGN §7's
  table said: it is CONSISTENCY-driven and needs a MONOTYPE counterpart, while
  guess^TY passes ∀ through and P6-L's counterpart `⌊ψa⌋ˢ` is a general
  ghost-free skeleton.
- **The `__flex_r` CHASE is the real hidden case.**  Three rules can conclude
  precision at a composite source, and `ad_refine_syn__flex_r` fires whenever
  the counterpart is a DEFINED flexible — replacing the target by that
  definition's monotype painting and leaving the source alone.  At the ∀ that
  chain REFUTES (`ad_refine_syn_all_l_not_mono`: a ∀-headed source never refines
  to a monotype painting — its `__all` case dies on the target equation for
  EVERY monotype shape, `ptyp_all` included, because that painting is
  `bskl_all_SYN`).  At the ARROW and the ∀◇ it does NOT refute — κs can turn a
  flexible into an arrow — so `ad_precise_arrow_l_inv` /
  `ad_precise_tophole_l_inv` chase it and return a REPLAY function that
  re-applies the chased steps.  (One-step re-application, NOT transitivity of
  refinement, which is false: `cex/cex_refine_not_transitive.v`.)  The chase
  terminates on the DERIVATION, so those are inductions on it, not on a size.
- **Why the θ-extension is well-defined at all:** `ad_refine_syn__hole`'s fill
  premise is `Θ ⨟ empty ⊢ₚₛᵃ P` — CLOSED — so a hole under a binder is never
  filled with the bound variable, and κ′'s images stay Θ-well-formed however
  deep the ∀-nesting goes.  That is what makes them legal metasubstitution
  images, and it removes the obvious ∀-case worry.
- **BOTH Δ's move.**  `Δ0` carries `P_s`'s binders (wf) and `Δ` the
  counterpart's (precision); `a_wf_pskl__all` and `ad_refine_syn__all` each grow
  their own, and the ∀◇ case RESETS `Δ0` to ∅ (`a_wf_pskl__tophole`'s body is wf
  CLOSED).  They are independent parameters of the induction.
- **One-instance→cofinite-family, three times.**  The ∀ case runs the IH at one
  fresh β and must hand back cofinite families: for the guess (§2's
  `a_guess_mono_all_of_one`, with the payload CLOSED over β), for wf
  (`a_wf_pskl_all_of_one` + a new `a_wf_pskl_rename_delta`) and for precision
  (`ad_precise_all_of_one` + `ad_precise_rename_delta`).  The refinement rename
  routes through the fill-hygiene `_f` kit: `ad_refine_syn_f_rename` wants the
  renamed name in `F`, and `ad_refine_syn_f_fextend_dom` puts it there for free
  because it is outside `dom Θ`.  ⚠️ The ftv-keyed `ad_refine_syn_f_fextend_ftv`
  would NOT do — β occurs in the target `X0^β`, which is the whole point.
- **Assembly used the existing HOMOGENEOUS-FLEX REORDER KIT**
  (`prop_look_complete_cstr.v`): `a_extract` emits `Ξc,Ξ'` where the natural
  build order is `Ξ',Ξc`.  Both blocks are undefined flexibles, so the order is
  immaterial — but not syntactically so, and
  `a_inc_flex_prefix_build/_split` + `msubst_pskl_app_swap` +
  `a_wf_pskl_swap_app` are exactly the four moves needed.  No new reorder
  machinery, and `a_extract`'s emission order was left alone.

**Statement deltas vs the paper** (both are the paper's own prose, restored):
`Θ ⨟ Δ ⊢ₚₛᵃ ⌊ψa⌋ˢ` (the "ψa is a valid instantiation" premise, which P5b-i
needs) and `Δ ∩ ftv ψa = ∅` (the precision hole rule's side condition).  As in
P6-Ss, the paper's `inc[θ≡θa]{Θ0}{Θ}` is the reflexive `a_inc_equiv Θ0 κ κ Θ`,
with the real content in the a_inc conclusion exhibiting θa as `κa ++ κ`.

**Housekeeping.**  §1's locally-defined `pskl_ghost_free` Inductive was a
DUPLICATE of `prop_pat_sub.v`'s Fixpoint and is gone; the file now uses the
existing one (which also brings `ptyp_to_pskl_ghost_free` and
`pskl_ghost_free_open_rec`).  `README.v` gained Check + `Print Assumptions` rows
for P6-Sv, P6-Ss and P6-L.

## 2026-07-30 — ⭐⭐⭐ P6-Ss CLOSED: Sub-ForallR done, the mechanization is admit-free again

`make coq` green from clean.  `a_looksub_solve_complete_gen` and the paper's
premise-free `a_looksub_solve_complete` are both `Qed` and
`Closed under the global context`.  **There is no `admit` or `Admitted`
anywhere in `frost/`.**

⚠️ **P6 is NOT finished.**  It has FIVE lemmas (§7's table), and this closes
the fourth: `P6-Cv → P6-Cs → P6-Sv → P6-Ss → `**`P6-L`**.  `a_extract_complete_gen`
(subtyping-proofs.tex:2730) is not written yet — it is a WRAPPER, not a new
induction: P6-Ss at `Pi = □` / `Ψi = ∅`, then `a_guess` (identity at SK,
`guess_join_witness` at TY), then `ad_partial_precise_complete` to upgrade
⊑ᵖ to ⊑ exactly as complete-look does at tex:2764.  P7 opens only after it.

The route is NOT the one Phase B planned — that prerequisite is false (see the
2026-07-29 entry below and `cex/cex_p6ss_sub_target_ftv.v`).  What the
statement carries is a MODE-GUARDED DISJUNCTION,

    M = mode_tc ->
      ftv 𝒞 ⊆ ftv ψa ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ
      \/ (alpha_stack α P /\ Ξc = nil /\ κc = nil /\ 𝒞 = a_cstr_sub M P0 :: nil)

and **Sub-ForallR lets the IH's own disjunct pick the branch** — no
decidability of `alpha_stack` is needed:

- **LEFT** — `β ∉ ftv 𝒞` (β is fresh for ψa, Ξc and κ, and is a RIGID so
  `def_ftv` never sees it); strip β from every output with P6-Cs's ∀-binder
  kit and rebuild with `a_looksub__forall_r` +
  `a_looksub_lookeq_rename_tvar`.  This is the Sub-ForallL rows with the
  renamed side swapped — there the SUBJECT moves and the target is fixed,
  here the reverse — and Δ does not grow, so there is no `delta_shrink` step.
- **RIGHT** — P is an α-STACK, and such a run never descends the target:
  `alpha_stack_looksub` collects `a_cstr_sub tc P0` at the UNDESCENDED P0, so
  the binder is never introduced.  The IH still supplies the solve, at the
  descended target; lifting it over the ∀ is P6-Sv's recipe
  (`a_solve_sub_strengthen_tvar`, then `a_solve_sub__forall_r` with
  `a_solve_sub_eq_rename`).

**Why the case split is exhaustive** is `ad_pat_sub_g_ty_tc_subject`:
`__forall_r` forces `a_sub_mode_ty` + `mode_tc`, and NM is invariant along a
derivation, so there only `__check`, `__forall_r` and `__forall_l_*` fire.
The α-leaf is therefore reachable under a Sub-ForallR only for an α-stack;
every other α-leaf sits under LS-Check, i.e. inside P6-Cs, whose bound is
already ψa-relative.  The `mode_tc` guard is what makes Sub-Arrow VACUOUS —
that row's left branch always yields the left disjunct while its right branch
may yield the right one, and no single bound could concatenate the two.

**Supporting changes that landed with it:** `uskl_rho_ftv_apart`; P6-Cs's
ftv-𝒞 conclusion now names NO CONTEXT (new premise `ftv ψa ∩ Δρ = ∅` replaces
the `dom Θs` slack — a Sub-ForallL nested under a Sub-ForallR drags β into the
ρ-images' scope); `alpha_stack` with `alpha_stack_subst_var` /
`alpha_stack_all_of_one` / `alpha_stack_looksub`; and
`ad_pat_sub_g_ty_tc_subject`.

**Two traps paid for.**  (1) `β ∉ ftv Pa` in the RIGHT branch does NOT come
from `a_solve_sub_ftv` — the target there legitimately mentions β — it comes
from PRECISION via `ad_partial_precise_src_ftv_avoid` (source bounded by
`ftv ψa ∪ Δ ∪ def_ftv Θ`) plus `msubst_pskl_ftv_dom_lower`.  (2) `repeat
split` CLOSES `keys nil = keys nil` by itself, because `split` on a
convertible equality is `eq_refl`; a stray bullet then shifts the whole list
and the error surfaces far away.

## 2026-07-29 — ⚠️ P6-Ss Phase B: the PLANNED ROUTE IS REFUTED; the route that works is identified and step 1 is landed

`make coq` green; the mechanization's ONLY admit is still P6-Ss's **Sub-ForallR**.

**The prerequisite Phase B was waiting on is FALSE.**  Machine-checked,
`frost/algo/cex/cex_p6ss_sub_target_ftv.v` (`p6ss_sub_target_ftv_is_false`,
axiom-free, with a non-vacuity witness).  The sub-side analogue of
`ad_pat_consis_target_ftv` —

    ad_pat_sub_g n NM M Ψ Θ R Q -> a_wf_aenv Θ -> is_tskl R ->
      ftv Q ⊆ ftv R ∪ def_ftv Θ

— fails at **`ad_pat_sub_g__forall_l_tagged`**, not only at the `__ghost` row
that was anticipated.  `is_tskl` does exclude `__ghost` (it admits the dotted
◈ `uskl_holeg`, not the plain ◇ `uskl_hole`), `__ghostg`, `__univ_ghost_l/lg`
and `__forall_l_untagged` — but `uskl_all_tag` IS `is_tskl`, and ForallL's
guess is bounded only by `dom Θ`, the DERIVATION's context, which
`__forall_r` grows by the very β Sub-ForallR must strip.  Witness: Θ = β,
subject `∀^ε α. α`, guess β, leaf `β ∼ β` ⇒ target `β`.  So `dom Θ` is the
strongest sound bound and it is exactly the wrong one; no shape premise
repairs it, because ForallL is the essential subtyping rule and consistency
escapes only by HAVING no ForallL.

**The theorem is not refuted — only the route.**  In every failing
configuration the algorithm still collects a β-free 𝒞, by taking LS-ForallL /
LS-UnivGhostL *before* LS-ForallR so that LS-Var fires at the UNDESCENDED
`∀β.P0`.  What makes this decidable by cases is a MODE RESTRICTION:
`__forall_r` forces `a_sub_mode_ty` + `mode_tc`, and at `(ty, tc)` the only
applicable rows are `__check` (whose subtree is pure consistency — no
guesses), `__forall_r` and `__forall_l_*`.  Hence under a Sub-ForallR the
P6-Ss leaf (`P = α`) is reachable ONLY when P is a ∀/⊤◇-stack over α — every
other α-leaf sits under LS-Check, i.e. inside P6-Cs, already ψa-bounded — and
in that case every ∀-body is constant, so the guesses are discarded and ∀L
permutes above ∀R (it does not in general; that is why the naive route dies).

**The Phase B statement that works** is a MODE-GUARDED DISJUNCTION,

    M = mode_tc -> ftv 𝒞 ⊆ ftv ψa ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ  \/  α_stack α P

whose mode guard makes Sub-Arrow vacuous (its conclusion is `mode_fn M`) —
the row that otherwise cannot concatenate a left disjunct with a right one.
P6-Cs must DROP the `dom Θs` term from its own ftv-𝒞 conclusion in favour of
an apartness premise `Δρ ∩ ftv ψa = ∅`; no third context parameter is needed
after all.  Full row-by-row plan and build order: DESIGN §8 (h).

**Landed this session (step 1 of that build order):** `uskl_rho_ftv_apart`
(`prop_look_complete.v`, `Qed`) — `uskl_rho … R' R` with `ftv R ∩ Δρ = ∅`
gives `ftv R' ⊆ ftv R`, i.e. the ρ transport with NO context slack.
`urho__leaf` is vacuous under the premise; the binder rows pick their opener
fresh for Δρ.

**On "𝒞 may mention β, but the later wf check makes it transparent"** (author
intuition, this session): not a licence to skip the obligation —
`a_looksub__forall_r` is COFINITE in β with one `Ξ ⨾ 𝒞`, so the RULE blocks,
not the extract-site `Θ0,Ξ ⊢ P1` check, and that check is not a filter either
(`a_solve_sub__var` discards its target).  But it IS a real simplification
inside the α-stack branch, where a flexible Pi makes the descended and
undescended solves agree; `a_solve_sub__forall_r` already made the same
encoding choice (cofinite, β-free output).

## 2026-07-29 — ⭐⭐⭐ P6-Ss Phase A: ρ-GENERALIZED, BOTH ForallL rows CLOSED (11/12); and P6-Cs's ρ premise was VACUOUS

`make coq` green.  The mechanization's ONLY admit is now P6-Ss's **Sub-ForallR**
(Phase B); everything else in the file, including both ForallL rows and the
ρ = identity corollary, is closed.

⚠️ **P6-Cs's ρ-generalization was VACUOUS as landed** — machine-checked in
`frost/algo/cex/cex_p6cs_rsubst_delta_vacuous.v`.  Its premise
`forall α0 ∈ Δρ, α0 ∉ dom Θ0`, beside `κ ∷ Θ0 ⊑ Θ` and `rho_fresh Δρ Θ κ`,
forces `Δρ = ∅`: an INCREASE NEVER INVENTS A RIGID (`a_inc_binds_tvar_rev`, the
converse of the existing `a_inc_binds_tvar` — `a_suffix` admits only flexible
entries), so every ρ-replaced variable is already a rigid OF Θ0.  Remember this
for any future ρ-style generalization over `a_inc`: a fresh ρ-binder introduced
by a Sub-ForallL MUST enter Θ0 and Θ together (`a_inc_cons_tvar`).
**Repair**: P6-Cs now takes the ftv-level premise
`forall α0 ∈ Δρ, α0 ∉ ftv P0 ∪ ftv Pi`, which is all the old one was ever used
for (via `a_wf_pskl_ftv_dom`) and is preserved by every descent
(`rho_ftv_apart_mono`; the Arrow row's RIGHT recursion EARNS it for its new
`Pi := Pa1` through `a_solve_cstr_ftv` + `a_looksub_lookeq_ftv`).  P6-Cs re-`Qed`,
axiom-free, corollary unchanged.

**P6-Ss is `a_looksub_solve_complete_gen`** (`frost/algo/prop_look_complete_sub_cstr.v`):
`+ Δρ Ψρ Rsub` and the ρ pack, `sub_shield` at Δρ, subtyping/wf premises on
`Rsub`, `Ψsub ⊆ ftag R' ∪ Ψρ ∪ Ψa`, and the output conjunct
`Forall (images ⊥ Δρ) κc`; plus `Θs`, the **derivation's** context (P6-Sv's
device, NOT P6-Cs's same-named one), because the ∀ rows must run the recursion
at `Θ,β` while the derivation's context is an INDEX — rule premises are weakened
on the spot right after `induction`.  The `remember`/`HeqSub` shape device is
GONE: every row inverts `Hrho` with the `uskl_rho_*_r_inv` family instead, and
`a_looksub_solve_complete_leaf_id` died with it.  The Check row and Sub-Arrow's
LEFT branch call P6-Cs's GENERALIZED form at the real ρ.

**Sub-ForallL** opens with a fresh RIGID β, absorbs the guess as `ρ ∘ [ψ/β]`
(`uskl_rho_subst`), recurses at `Θ0,β / Θ,β / add β Δ / add β Δρ`, and strips β
from every output with P6-Cs's ∀-binder kit; LS-ForallL's cofinite family comes
from the single β-instance by `a_looksub_lookeq_rename_tvar` — legal because the
TARGET P0 does not move, so the structural `a_looksub_ftv` already keeps β out
of 𝒞 (this is exactly what ForallR does NOT get).  The paper's broken step
(`κψ_b = ψ_b`) never arises.

**Tag bookkeeping — the one observation it needed.**  `ad_pat_sub_g` records the
paper's GLOBAL freshness of an instantiation's tags as only two conjuncts (fresh
from the tag index and from the SUBJECT's syntactic tags,
`def_decl_algo_sub_hyg.v`); Sub-ForallL also needs them fresh from ψa's tags Ψ'
to keep `Ψρ ∩ Ψ' = ∅`.  That is NOT a new side condition: the induction runs
under `α ∈ ftv R'`, so ψa sits INSIDE the ideal `(κR')[ψa/α]`, and `uskl_rho`
only ADDS tags going to the image (`uskl_rho_ftag_target_sub`) — hence
`Ψ' ⊆ ftag Rsub`, where the rule's own subject-freshness excludes them.  New,
both `Qed`: `ftag_in_uskl_subst_lower`, `msubst_uskl_syn_ftv_keep`.

**NEXT — Phase B (Sub-ForallR).**  Re-acquire the ψa-relative bound
`ftv 𝒞 ⊆ ftv ψa ∪ dom Θs ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ` that P6-Cs carries and
this statement drops; that needs P6-Cs's OTHER `Θs` (the ρ premise at a FIXED
context, since the ∀ rows strip β from 𝒞).  The ρ-generalization landed here is
what unblocks it: under ρ the lookup side never sees a guess.

## 2026-07-29 — ⭐ P6-Cs is ρ-GENERALIZED and re-`Qed`ed: the P6-Ss ForallL blocker is gone

`make coq` green; `a_lookeq_solve_complete` `Qed` and axiom-free; admits
unchanged (P6-Ss's four `admit`s + its one honest `Admitted`).  This was the
expensive half of the ForallL repair decided in the previous entry — with it
landed, P6-Ss's ForallL **and** ForallR are unblocked (they share this fix),
and everything downstream of P6-Cs is already prepared.

**What changed.**  The consistency subject of P6-Cs may now be the ρ-IMAGE
`Rsub` of the paper's ideal `(κR)[ψa/α]` rather than the ideal itself.  ρ =
identity gives the paper's statement back verbatim — and that is
machine-checked, not asserted: the non-vacuity witness
`p6cs_fires_when_the_subject_is_wf` (`cex/cex_p6cs_subject_wf.v`) still fires
at `Θs := ·`, `Δρ = Ψρ = ∅` and returns a real answer.

Statement delta (every new premise is vacuous at ρ = identity):

- `+` params `Θs Δρ Ψρ Rsub`, and `uskl_rho NM Θs Δρ Ψρ Rsub ((κR')[ψa/α])`;
- `+` binds-monotone `Θs → Θ`; `Ψρ ∩ Ψ' = ∅`; `rho_fresh Δρ Θ κ`; `Δρ ⊆ Δ`;
  `Δρ ∩ dom Θ0 = ∅`; the Pi-shielded-ftv condition; `flex_apart_walk Θ0 Δρ P0 ψa`;
- `~` consistency and subject-wf now speak of `Rsub`; the `Ψsub` bound gains `Ψρ`;
- `+` a new output conjunct `Forall (images ⊥ Δρ) κc`;
- `~` the ftv-𝒞 bound gains `dom Θs`.

⚠️ **`Θs` is load-bearing and is NOT `Θ`.**  ρ's images are fixed when ρ is
built — by a Sub-ForallL OUTSIDE P6-Cs — and P6-Cs never extends ρ, so the ρ
premise is stated at a FIXED context.  At `Θ` the ftv-𝒞 bound would read
`dom Θ`, and the ∀ rows (which run the IH at `Θ,β` and then strip β from 𝒞)
would be handed a bound that readmits the very binder being stripped.

**Two premises the recipe did not anticipate**, both forced by the Arrow row's
RIGHT recursion, whose `Pi` becomes the LEFT branch's `Pa1` under an extended
κ: `Δρ ∩ dom Θ0 = ∅` and the new `Forall` output.  Together they re-derive the
shielded-ftv condition for `Pa1`: `Ξc1` is fresh for Θ ⊇ Δρ so `Pa1` avoids
Δρ, and both κ's images (`rho_fresh`) and κc1's (the new `Forall`) do too.

**⚠️ The planned COMMUTATION route is FALSE.**  §8 (e) proposed
`ρ((κR)[ψa/α]) = (ρψa)[ρ(κR)/α]`.  `uskl_rho` is a RELATION, not a
substitution: `urho__leaf` may send two occurrences of the SAME Δρ-variable to
DIFFERENT images (take `R = α→α`, `ψa = β ∈ Δρ`).  The working route uses the
flexible-P0 row's own structure instead — at a FLEXIBLE P0 only `fa_clean` can
hold, so the guess is Δρ-CLEAN there and ρ IS the identity on it.  Landed as
five standalone lemmas in the preceding commit:
`flex_apart_flex_var_clean`, `psia_rho_leaf_step`, `psia_rho_leaf_impossible`,
`ad_pat_consis_rho_subst_psia_mono` (induction on the CONSISTENCY, so
`bskl_monoish Q` kills every binder case and no cofinite bookkeeping arises),
and `rho_fresh_weaken_tvar`.

**Definition changes.**  `fa_step` gains `fastep_p0_arrow_l/_r` — P6-Cs
descends P0 with the guess FIXED (ψa is the single guess for α and never
splits), which the positional arrow steps do not cover;
`flex_apart_walk_weaken` generalizes the tvar-only weakening that the Arrow
row's `Ξc1 ++ Θ0` growth needs.

**Row by row it is threading, not rewriting.**  Every row dispatches on the
ρ-free `R'`, so the `uskl_rho_*_r_inv` family reads `Rsub`'s shape off the
ideal's, and for a non-variable ideal returns a SINGLE congruence with no
disjunct.  The ∀ and ∀◇ rows actually got SIMPLER: consistency and wf now open
directly on the image, so `p6cs_subject_open` survives only in the ρ premise.

**The paper's statement is back as a corollary.**  The generalized theorem is
`a_lookeq_solve_complete_gen`; `a_lookeq_solve_complete` is its ρ = identity
instance (`Θs := ·`, `Δρ = Ψρ = ∅`, subject = the ideal) and is LITERALLY the
pre-generalization statement — same premises, same conclusion, no residue.
Use it unless you are threading a ρ down from a Sub-ForallL; P6-Ss's Check row
and the counterexample file both do.

Making the corollary premise-free needed one more definition: P6-Cs takes the
**P0-ONLY walk** `flex_apart_deep` (`p0_step` / `p0_walk`, prop_look_complete.v)
rather than `flex_apart_walk`.  P6-Cs descends P0 alone at a CONSTANT Δρ, so
at Δρ = ∅ every reachable state is `fa_clean` — whereas `flex_apart_walk`'s
`fastep_all_r` can grow Δρ and would have left a real premise behind.  P6-Ss
still threads the full walk and converts with `flex_apart_walk_p0`, which is
what the new `fastep_p0_arrow_l/_r` steps are for.

**Two statement cleanups on the corollary** (user review): the induction
FUEL `n` is absorbed — it is an artefact of the strong induction, not part of
the claim, so the corollary instantiates it at `size_uskl R' + size_pskl P0`
and drops the measure premise.  And the `α ∉ dom Θ0` premise beside the
paper's `α ∉ Θ` is now explained at the statement itself: it is NOT redundant
(`a_inc__flex` solves a source flexible away, so `dom Θ0 ⊆ dom Θ` is false),
it is consumed only to get `α ∉ dom κ` via `dom κ ⊆ dom Θ0` — "κ leaves α
alone", without which `(κR)[ψa/α]` means nothing — and it is forced anyway by
how `a_sub__forall_l` opens the binder (cofinitely, never into a context).
Not a wf side condition, so NOT registered in docs/WF-SIDE-CONDITIONS.md.

**Notation (comments only).**  The ghost family is now `◇` = `hole`,
`◈` = `holeg`, `∀◇` = `tophole`, `∀◈` = `topholeg`, matching the paper's
ghost-with-a-∀ glyphs.  Retired: `⊤◇` / `⊤̇◇` / `⊤◇̇` / `◇̇` / `⟨⟩̇` / `⊙̇`
— `⊤` read as an unrelated top type, and the dot was U+0307, a COMBINING
diacritic that renders as a floating smudge in monospace.  ~580 sites; the
convention is recorded in CLAUDE.md.  (`docs/PROPOSAL-notation-pass.md` keeps
its combining dots as specimens, and DESIGN.md keeps the one quoting the
paper's `□̇.P`.)

## 2026-07-29 — P6-Ss: ρ-repair infrastructure landed; ForallR gap RESOLVED by the authors; the repair's real scope measured

`make coq` green; admits unchanged (P6-Ss's four).  The P6-Ss statement has
NOT moved yet — everything below is additive.

**Landed (both `Qed`, in `prop_look_complete_sub_cstr.v`).**
- `sub_shield` now carries Δρ, with `sub_shield_add_fresh` and
  `sub_shield_weaken_tvar`; the current statement instantiates it at
  `empty`, so nothing else changed.  The Δρ quantifier is built INTO the
  definition (as the `ss_walk` one already was) because Sub-ForallL grows
  Δρ by a fresh β while ψa does NOT move — P6-Ss's ∀ comes from the
  SUBJECT — so neither `fastep_all_r` nor `fsh_all_r` applies and proving
  the growth as a lemma would mean simulating the `fa_walk`.
- `ad_partial_precise_delta_shrink_fresh`, the mirror of
  `ad_partial_precise_delta_weaken_fresh`: Sub-ForallL hands the IH the
  precision premise at `add β Δ` (β joins Δρ, and `Δρ ⊆ Δ`) and has to
  return the conclusion at plain Δ.

**ForallR: gap RESOLVED by the authors — reclassified, and the mech side
DECIDED (keep the cofinite rule; ForallL and ForallR are fixed by the SAME
change).**  WT: constraint collection is deliberately scoping-AGNOSTIC;
the scope check is the SEPARATE `Θ0,Ξ ⊢ P1` premise at the extract use
site.  So \lslab{ForallR} carries no `β ∉ ftv 𝒞` side condition and the
paper's proof owes nothing.  What remains is ours: the locally nameless
`a_looksub__forall_r` is COFINITE with one `Ξ ⨾ 𝒞`, which IS the side
condition, so the mech rule is strictly narrower — KEEP IT, since
completeness of a narrower algorithm is a stronger theorem.  ⚠️ It must NOT
be justified by "the wf check catches a β-mentioning 𝒞 anyway": checked,
and false — `a_solve_sub__var` is `α̂ ≼[m] Q ⤳ α̂`, it DISCARDS the target,
so a β-mentioning 𝒞 can solve to a β-free `P1` that `Θ0,Ξ ⊢ P1` accepts.
What the row actually needs is to re-acquire the ψa-relative bound
`ftv 𝒞 ⊆ ftv ψa ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ` that P6-Cs carries and this
statement dropped.  That route was thought closed ("Sub-ForallL
instantiates with a GUESS"); the ρ-generalization dissolves the objection,
because under ρ the lookup side never sees a guess.  **So ForallL and
ForallR are fixed by the SAME change.**

**ForallL: the ρ-repair's scope measured.**  The Check row hands its WHOLE
subject to P6-Cs and a ForallL can sit above a Check, so **P6-Cs must be
ρ-generalized too**.  That is threading, not new theory: P6-Cv
(`a_solve_eq_complete_var_gen`) ALREADY takes `uskl_rho NM Θ Δρ Ψρ ψsub
ψa`, the `uskl_rho_*_l_inv` inversion kit exists, P6-Cs's measure
(`size R' + size P0`, on the ρ-FREE ideal subject) is unaffected, its ∀
rows open with fresh VARIABLES so ρ never grows inside it, and its leaf
passes the real ρ down instead of `urho__refl`.  P6-Sv's ForallL row
(prop_look_complete_sub_var.v:2308) is the line-by-line template for
P6-Ss's, simplified: P6-Ss's ∀ comes from the SUBJECT, so ψa/P0/Pi/Ψi/Ψa
do not move and only Θ0/Θ/Δ/Δρ grow by β.

## 2026-07-29 (latest) — P6-Ss: the ForallL PREREQUISITE is closed; the ForallL ROW is blocked on a statement change

`make coq` green.  The mechanization is still admit-free except the four
`admit`s of `a_looksub_solve_complete` (P6-Ss), which remain honestly marked.

**Closed (Qed, axiom-free) — `prop_looksub.v` §4b.**
`a_looksub_lookeq_subst_stable_rev` and its two one-sided corollaries, plus
the helpers `a_looksub_subst_var` / `a_lookeq_subst_var`.  This is the
REVERSE direction of `lemma:constraint-collection-stable-substitution`
(subtyping-proofs.tex:2632), i.e. task 1 of the P6-Ss plan: a run collected
on a subject in which an α-free guess has already replaced a rigid β ≠ α
can be UNDONE, recovering the very same `Ξ ⨾ 𝒞`.  Mutual induction on the
derivation with the substituted subject `remember`ed, then `destruct` on the
un-substituted subject per row; the `= var β` branch is uniform (the run
happened entirely inside the α-free guess, so `a_looksub_lookeq_absent_nil`
empties it and LS/LE-Absent rebuilds).  The duplicate `a_looksub_lookeq_absent`
in `prop_look_complete_sub_cstr.v` is deleted in favour of it.

**Statement relaxation, both P6-Cs and P6-Ss.**  The scope premise
`ftv R' ⊆ add α (dom Θ0)` becomes `add α (dom Θ0 ∪ dom Θ)`, and the dual
conclusion `α0 ∈ dom κc ⇒ α0 ∉ add α (dom Θ0)` is strengthened the same way.
`a_lookeq_solve_complete` re-`Qed`s with no other change (its
flexible-generating row already picks its fresh name outside `dom Θ`).  The
relaxation is forced by P6-Ss's ForallL row, whose IH subject `open R0 ψ_b`
is Θ-scoped and never Θ0-scoped.

**P6-Ss ForallL — reclassified to a PROOF-STEP gap; repair decided, no
premise (two review rounds, all machine-checked in
`frost/algo/cex/cex_p6ss_inc_compat.v`).**
subtyping-proofs.tex:2600–2643 applies the IH with `S := S'[ψ_b/β]`, using
`θ(S'[ψ_b/β]) = (θS')[ψ_b/β]`, i.e. `θψ_b = ψ_b` — and NO side condition
on θ rescues that step: Barendregt disjointness `dom θ ∩ dom Θ = ∅` is
unsatisfiable at identity metasubstitutions (`id_inc_dom_overlap`;
algorithmic.tex:135–140 — ι's entries are all preserved in the target);
syntactic survivor-compat `θα̂ = α̂` excludes the legitimate
definition-substituting θ at `Θ = [α̂:=⟨⟩]`, which is inc-EQUIVALENT to ι
(`def_subst_theta_is_legit`); and the strongest defensible invariant — the
semantic `α̂ ∈ dom Θ ⟹ Θ ⊢ θα̂ ≡ᵗ α̂`, which kills the junk θ moving an
UNDEFINED survivor (`inc_moves_survivor`) — still leaves `θψ_b ≠ ψ_b` on
the legitimate θ.  The written step holds essentially only at ι-like θ.
REPAIR (decided, not yet built): the ρ-GENERALIZED induction, statement
UNCHANGED — guesses ride outside κ as `ρ ∘ [ψ_b/β]` on fresh rigids, and
the `P = α` leaf calls P6-Sv at the accumulated ρ (its general-ρ
interface, unused until now).  A separate definitional observation for
the authors (the ⊑ figure admits the junk θ; the semantic invariant is
the side condition that would exclude it) is registered in PAPER-GAPS.md.
Full analysis: docs/PAPER-GAPS.md (last entry, rewritten) and
DESIGN-completeness-subtyping.md §8 (e).
Arrow and ForallR are unaffected and remain next.

## 2026-07-29 (later) — NOTATION: the metasubstitution is `κ`; `ρ` is reserved for the paper's ρ

Corpus-wide rename, `make coq` green, all `Print Assumptions` still closed.
Two symbols were doing badly-chosen work:

- The paper's `θ` (information increase, `κ ∷ Θ0 ⊑ Θ`) is one stroke away
  from the CONTEXT `Θ` it appears next to in every statement.
- `ρ` was already the metasubstitution binder in `def_meta.v` (every
  `msubst_*`, and the `∷` notation) — but `ρ` is ALSO the paper's
  rigid-variable substitution, and subtyping completeness needs both at
  once: P6-Sv states `κ ∷ Θ0 ⊑ Θ` beside
  `uskl_rho NM Θ Δρ Ψρ ψsub ψa`.

So the metasubstitution alphabet is now **`κ`** (the increase), `σ` (the
second one, `a_inc_equiv`), `ζ` (the composing one, `ζ ∘ κ`), and **anything
spelled `ρ` denotes the paper's ρ** (`uskl_rho`, `rho_fresh`, `Δρ`/`Ψρ`,
and `msubst_uskl` in prop_decorate_sub.v).  Recorded in CLAUDE.md's
metavariable convention.

Mechanics worth remembering for the next such pass.  `θ → κ` is
unconditional (θ never meant anything else).  `ρ → κ` is NOT: it was applied
only in the metasubstitution-algebra files, and in `prop_look_complete*.v`
only to CODE, since their comments legitimately discuss the paper's ρ.
Two hazards actually fired: (1) replacing the CODEPOINT rather than the
token silently rewrote `Δρ`/`Ψρ` to `Δκ`/`Ψκ` — caught by the build, since
downstream files pass them as named arguments; (2) exactly two statements
bind two metasubstitutions at once (`msubst_{uskl_syn,pskl}_prepend_fresh`,
`msubst (ρ ++ θ) = msubst θ`), which would have COLLAPSED into one name —
they were pre-renamed to `κ' ++ κ`.  Everything else that looked like a
clash was a named argument (`(θ1 := ρ1)`), which renames consistently on
both sides.  `docs/PAPER-GAPS.md` deliberately stays in the paper's
notation and now carries a note mapping θ ↦ κ.

## 2026-07-29 — ⭐ P6-Sv CLOSED: `a_solve_sub_complete_var` Qed, axiom-free (repaired statement)

The last two cases — **Arrow** and **Sub-ForallL (tagged)** — are closed, so
the whole 12-case induction is done and `make coq` passes with the
mechanization still admit-free.

- **Arrow** delegates its LEFT premise to P6-Cv and its RIGHT one to the IH,
  exactly as the Check case does; the new part is `arrow_grid`, the case
  analysis on the input skeleton `Pi` (arrow / □ = SolS-GhostLF / ∀◇ /
  variable, with unit and ∀ refuted by the precision against an arrow
  guess).  The ∀◇ row recurses STRUCTURALLY on `Pi` — no measure needed,
  because well-formedness makes the ghost's body guarded.
- **Sub-ForallL** absorbs the rule's instantiation into ρ, as the paper's
  `ρ_b = ρ ∘ [ψ_b/β]` (`uskl_rho_subst`), so the recursive call runs at
  `Δρ,β`: β is the one variable `ρ_b` replaces and ρ did not, and it is the
  SAME β the precision premise pairs `Pi`'s binder with.  Its `Pi` grid has
  ONE live row (`Pi = ∀β.P1`, the paper's): every other shape would have to
  solve the top-level tag ε, and ε is already in `Ψi`.  That is proved, not
  assumed — `ε ∉ ftag R` (ρ only ADDS tags, `uskl_rho_ftag_target_sub`) and
  `ε ∉ ftag ψ` (the rule's own freshness) bound the premise's solved tags,
  giving `ε ∉ Ψsub ⊇ Ψa`, hence `ε ∈ Ψi` by `Ψi,Ψa = Ψ'`.

STATEMENT CHANGE beyond the `flex_shield` repair — **the context is
generalized**.  Sub-ForallL must run the IH at `Θ,β`, but the derivation's
own context is an INDEX of `ad_pat_sub_g` and cannot move.  So the
derivation now lives in a smaller `Θs` and every other premise in a `Θ`
related to it only by `binds`-monotonicity; at the top level `Θs = Θ` and
the premise is the identity.  This is the mech's reading of the paper's "by
weakening \refn[9] to Θ,β" (subtyping-proofs.tex:2153).  Each rule premise
stated in the small context is weakened on the spot, so all ten previously
closed cases read unchanged.

New reusable kit (all Qed, axiom-free):
`arrow_grid`; `uskl_rho_ftag_target_sub` / `uskl_rho_ftv_subject_bound` (the
two missing directions of ρ's tag/ftv transports);
`a_wf_pskl_shielded_dom` — a well-formed skeleton's ∀◇-SHIELDED variables
all live in `dom Θ`, never in Δ, which is exactly what lets Sub-ForallL add
its fresh binder to Δρ (the discipline DESIGN §7 names in prose);
`ad_ppre_guarded_all_tag_absurd`; and
`ad_partial_precise_tvar_to_delta_mid` — the converse of
`a_wf_pskl_delta_to_tvar_mid`: a rigid binder ALREADY in Δ may be dropped
from the aenv.  The `strip` version in prop_look_complete_cstr.v cannot be
used here, since it wants β free in NEITHER side and here β is free in both.

Coq gotchas paid for in this pass: `a_wf_aenv__tvar` takes the FRESHNESS
first (a wrong bullet order surfaces as "No matching clauses for match",
because `match goal` backtracks when its BODY fails, not its pattern);
`Ψ0` must be PINNED with `with (Ψ0 := …)` on `ad_ppre__forall`, or the tag
side condition's `fsetdec` runs forever on an evar; and Ltac cannot resolve
a `rename`-introduced name inside a `match goal` PATTERN — match on the
weakening hypothesis and bind the context as `?S` instead.

Cleanup: `flex_shield_admits_var_body` is deleted (it was an intermediate
check, unused by the proof; the shape it recorded is documented in
`fsh_rho_var`'s comment).  `flex_shield_excludes_cex` is KEPT and relabelled
— like the `cex/` files, it is what ties the mech-only premise to the
machine-checked counterexample.

## 2026-07-28 (later) — P6-Sv repair BUILT: `flex_shield` + descent kit, Qed and axiom-free; statement restated

New file `frost/algo/prop_look_complete_sub_var.v` (0 admits except the main
induction, which is `Admitted` with a case map).  It defines the repair
premise `flex_shield Θ0 Ψ' Δρ P0 ψa` — *positionally*, every raw-Θ0-flexible
position of the payload `P0` faces a part of the guess `ψa` that is both
Δρ-clean and Ψ'-tag-free — and proves the whole kit the induction needs:
`_delta_anti/_cong`, `_weaken_tvar`, `_rename_l`, `_rename_r(_gen)`,
`_arrow_inv`, `_topholeg_r_inv`, `_tophole_l_inv`, `_descend_l`
(Sub-ForallR), `_descend_r` (Sub-ForallL), `_flex_leaf`, and
**`flex_shield_excludes_cex`**, the regression test that the premise rules
the machine-checked counterexample out.  `Print Assumptions` on all three
flagships: "Closed under the global context".

Building it corrected the premise shape twice.  A SECOND failure shape
(hand-verified) puts the flexible at an ARROW-LEFT — a consistency position
— under the same ForallL: `Pi = ∀β.((β→β)→⟨⟩)`, `P0 = α̂→⟨⟩`,
`ψa = ∀^ε β.((β→β)→⟨⟩)`, `M = FN TC`; SolS-Arrow then SolE-FlexR gives
`Pa = ∀β.(α̂→⟨⟩)` and again `⟨⟩ ⊑ᵖ β` (Pi's left component is an arrow, so
SolE-Var does not shield it).  So a premise guarding only P0's result spine
is too weak, and a global "P0 flex-free ∨ ψa tag-free" is too strong (it
rejects the legitimate `α̂→⟨⟩` against `⟨⟩→∀^ε β.…`).  The structural point
that makes the relation work: its two one-sided ∀ rules do not commute
rule-by-rule, but each descent lemma's opposite-sided case closes because
the induction hypothesis re-derives the other rule.

Details and the case map for the remaining induction:
docs/DESIGN-completeness-subtyping.md §6 (z2).

## 2026-07-28 — ⛔ P6-Sv (subtyping constraint solving for variables) is FALSE as stated — machine-checked counterexample; work STOPPED

Starting P6-Sv (`lemma:complete-constraint-collection-solving-var`,
subtyping-proofs.tex:1696 — the subtyping twin of the closed P6-Cv) turned up
a genuine falsity rather than a proof-step gap, so per CLAUDE.md the work is
stopped and flagged instead of repaired.

**New file `frost/algo/cex/cex_p6sv_forall_flex.v`**
(`p6sv_with_p6cv_premises_is_false`, `Qed`, "Closed under the global
context").  It states P6-Sv with EXACTLY the premise set that closes P6-Cv
(`a_solve_eq_complete_var`) — including the mech-only `flex_apart`
invariant, the subject-wf premise that made P6-Cs true, and the
subtyping-side tag EQUATION `Ψi , Ψa = Ψ'` — and derives `False`.  The
conclusion refuted is the PAPER's (`∃ Pa κa`, with `κa : Θ0 ⊑ Θ`), not the
mech's `κa := κ` strengthening.

Witness — note **ρ is the IDENTITY** (`Δρ = ∅`), so this is not an artefact
of the ρ-relation encoding:

```text
Θ0 = α̂          Θ = α̂ := ⟨⟩→⟨⟩       κ = [α̂ ↦ ⟨⟩→⟨⟩]
N = TY  M = TC  Pi = ∀β. β→β         P0 = α̂
ψa = ψsub = ∀^ε β. β→β               Q  = inh{⟨⟩→⟨⟩}
Ψ' = Ψi = {ε}   Ψa = Ψsub = Ψρ = ∅   Δ = ∅
```

The subtyping premise is Sub-ForallL (`β := ⟨⟩`) then Sub-Check; the
algorithm is forced to `Pa = ∀β.α̂` (a `∀` is not `guarded`, so only
SolS-ForallL applies; its body goes SolS-Check + SolE-FlexR), and the
precision obligation reduces to `⟨⟩ ⊑ᵖ β`.  The file also proves the general
fact behind the refutation, `mono_paint_ppre_target_ftv`: a mono-paint
subject is never precise to a target mentioning a variable outside `Θ`.

Why the standing "unreachable" resolution (`cex_p6_flex_freshened.v`,
2026-07-25) does not cover this: (i) ρ here is created by the completeness
proof's OWN ForallL case (`ρb = ρ ∘ [ψb/β]`), so the induction manufactures
the bad premise set from innocent inputs, and any `flex_apart`-style
invariant stated at the current `ψa` is destroyed by that descent (`Δρ` gains
`β` while `P0` is not decomposed); (ii) the raw flexible payload arrives from
**LS-Var**, and `a_looksub` has no FlexR rule, so nothing freshens it on the
subtyping route; (iii) the paper's positional side condition on ρ is
satisfied all the way down.

Registered in `docs/PAPER-GAPS.md` (final entry, with three repair
directions for the authors) and `docs/DESIGN-completeness-subtyping.md`
§6 (2026-07-28 x).  Nothing already closed is retracted: P5, P6-Cv and P6-Cs
have no ForallL, so ρ never grows there.  P6-Ss / P6-L are blocked behind
this decision (P6-Ss's crux delegates to P6-Sv).

**Same-day UPDATE (impl experiments; see DESIGN §6 (y) + the PAPER-GAPS
"Correction" and "IMPLEMENTATION BUG" entries).**  Built and ran the
artifact.  (a) My two end-to-end reachability claims were WRONG — the
pipeline pre-shapes applied-λ binders from argument skeletons and
ghost-erases top-level ∀s of eq-payloads, and TC-checks against guarded
types collapse to consistency (shallow subtyping) — so the cex premise set
appears UNREACHABLE from real runs and the earlier SolE-FlexR-flip
proposal is WITHDRAWN.  (b) The fix is STATEMENT-SIDE: P6-Sv restated
with a NEW positional premise `flex_tags_apart Θ0 Ψi P0 ψa` (flexible
payload positions face tag-unsolved regions of ψa; full draft in DESIGN
§6 (y)); the mech cex becomes the regression test that the premise
excludes the configuration, and its ForallL flex-P0 case becomes vacuous
(`ad_ppre__tophole_fill` adds no tag — only rigid `ad_ppre__forall` does).
(c) NEW artifact bug found while probing reachability: a 5-line program
(`k : ∀a. list a → a`, `args : list (∀b.b→b)`, `let g = fun f -> f (k
args)`) CRASHES the implementation with `Failure("broom_flex_poly: should
not happen")` (type.ml:1048); the annotated twin passes.  Report to WT.

## 2026-07-28 — Naming/notation pass: atom-set notations, and the ott metavariable convention across all hand-written lemmas

Two style passes, both `make coq` green and axiom-free (all 26
`Print Assumptions` sites still report "Closed under the global context").

**1. Atom sets no longer name a module** (commit `8e0d6ee`).
`Metalib.Metatheory` abbreviates only part of the interface — `add` /
`empty` / `remove` / `singleton` / `union`, plus a re-export of
`AtomSetFacts` — and deliberately does not `Module Export AtomSetImpl`
(that would shadow `In`, `eq`, `filter`, `fold`, … on top of `List`'s).
`frost/notations.v` now finishes the job selectively, in metalib's own
style: abbreviations for `inter` / `diff` / `mem` and the ten
`AtomSetImpl` lemma names actually used, plus the infix forms the paper
writes — `S1 ∪ S2` (level 65, mirroring metalib's `union`), `S1 ∩ S2`
(63), `S1 ∖ S2` (61), all below `[=]` / `[<=]` so the dominant
disjointness side condition reads `Δ ∩ ftvar_in_pskl P [=] empty`.
All 348 qualified occurrences across 28 files are gone.

**2. Metavariable convention.**  Hand-written lemma binders now follow
`language.ott`'s own grammar symbols: `A` ptyp, `B` btyp, `C` utyp,
`P` pskl, `Q` bskl, `R` uskl, `𝒞` constraint lists (the paper's `\mC`),
and greek `α`/`β`/`γ`/`δ` for type/skeleton VARIABLES (Axis-4 part 2,
deferred since 2026-07-27).  ~655 lemma blocks across 41 files.

The rename is driven by Coq, not by guesswork: `About` is run on every
declared object, and each binder is rewritten by the SORT Coq reports
for it, per lemma block, simultaneously.  Two rules make it safe:

  - **Disambiguate with ONE prime, then digits 0/3/4/… — never `L1`/`L2`.**
    ott names the arrow-constructor arguments `A1 A2 / … / R1 R2` and the
    var argument `α`, so those are exactly the names `induction` /
    `inversion` manufacture; an explicit `intros Q1` after one then fails
    with "Q1 is already used".  Coq never auto-generates a primed name.
  - **A named argument spells the CALLEE's binder** (`foo with (A := e)`,
    and `eapply H0 with (S := e)` for an instance of the enclosing lemma),
    so its label follows the callee's map, not the caller's.

**The convention stops at the first case analysis.**  `intros … A A' H;
induction H` clears `A`/`A'` and re-binds each case from the RULE's own
argument names (`def_extra.v`, untouched here), so every later `A` in
that proof denotes a rule binder.  Those bodies keep the original names
— that is correct, not an oversight, and the sites carry a comment
saying so.  The same holds past `apply foo_mutind`.  Two smaller
consequences: `induction S` names its hypotheses `IHS`/`IHS1`/`IHS2`,
which had to be carried along with the binder; and `try rewrite IHS1`
fails SILENTLY when stale, surfacing only as a later `fsetdec` failure.

**3. The residual slice is now done too** — the type/skeleton VARIABLES.
`X`/`Y`/`Z`/`W` and `S` are gone from the hand-written corpus, definitions
included, so the names `induction`/`inversion` auto-bind are greek as well:

  | was | `X` | `Y` | `γ` | `δ` | `Z` | `W` | `S` |
  |---|---|---|---|---|---|---|---|
  | now | `α` | `β` | `α1` | `β1` | `α2` | `β2` | `R` |

with `HX`→`Hα` and friends: ~10,900 tokens over 54 files.  Only `α`/`β` are
bases (subscripts and at most ONE prime); `γ`/`δ` are retired, which also
removes their old informal "flex variable" reading.  What legitimately keeps a
latin name: generic Coq `Type` parameters (`forall (X Y : Type)`), notation
placeholders (`X ∪ Y`), and the 51 nat successors `S n` / `S (size_ptyp A)`.

An atom SET is never `R`: three lemmas quantified a set that is unioned into
the tag context (`Θ ⨟ (Δ ∪ S) ⊢ …`, `delta_def_fresh S Θ`), so it is a Δ and
takes `Δ'` — `inter_empty_pointwise`, `ad_partial_precise_delta_weaken_fresh`,
`a_solve_eq_complete_var_gen`.  In the last of these, HEAD's `S` (142
occurrences, the set) and HEAD's `R` (100, genuine skeletons) had BOTH
collapsed onto `R`; separating them again was a real repair, not cosmetics.

**Captures the sweep had to repair.**  A blanket rename can make an inner
binder capture an outer variable of the same new name, silently changing a
statement.  Scanning HEAD for statements binding two distinct tvars that
collapse found them; each was redirected (`X→α0`):
`consis_precise_core` and `rho_fresh` are the load-bearing ones — their inner
`forall X` genuinely referenced the outer `α`.  The same hazard bit a
`Local Ltac` whose formal parameter `Y` became `β` and captured a `β` bound in
its own body (`ftv_rev_extend`, prop_consis_complete.v).

**Method, for the next such pass.**  Re-derive the offending lemma from the
previous commit under an adjusted map rather than patching in place, and keep
the redirect *region-scoped*: in a long proof most `X`s are fine as `α`, and
only the ones a `pick fresh α` or a rule binder shadows need to move.  Two
traps: `induction S` names its hypotheses `IHS*`, which must move with the
binder, and a stale `try rewrite IHS1` fails SILENTLY, surfacing only as a
later `fsetdec` "goal beyond the scope of this tactic".


## 2026-07-28 — P6-Cs CLOSED: `a_lookeq_solve_complete` axiom-free, 0 admits (+ a load-bearing wf side condition, machine-checked)

`a_lookeq_solve_complete` (consistency-proofs.tex:920, "Completeness of
consistency constraint collection and solving") is `Qed` and "Closed under the
global context", in the new `frost/algo/prop_look_complete_cstr.v` (3537
lines, ~12 s).  It is the general lemma whose α-leaf delegates to P6-Cv.
Every paper case is covered: C-ForallInh / C-ForallSyn (tagged and untagged),
C-Arrow, C-UnivGhost, C-UnivGhost1, C-UnivGhost2, C-UnivGhostG.

**A wf side condition had to be restored, and it is not cosmetic.**  The
statement carries one premise beyond the paper's list — well-formedness of the
CONSISTENCY SUBJECT, `Θ ⨟ ∅ ⊢ₚₛᵃ ⌊(κS)[ψa/α]⌋ˢ` (stated on the erasure so the
existing `a_wf_pskl` expresses it; the only content used is the GUARDED ghost
body of `a_wf_pskl__tophole`, matching the declarative `d_wf_uskl__tophole`).
Without it the lemma is FALSE, and that is machine-checked in
`frost/algo/cex/cex_p6cs_subject_wf.v`:

  - `p6cs_without_subject_wf_is_false` — the lemma with EVERY premise except
    this one (conclusion weakened to its three essential conjuncts, which only
    strengthens the refutation) implies False.  Witness: `Θ = Θ0 = ·`, `κ = ·`,
    `S = ∀◇α`, `ψa = ∀◈⟨⟩`, `P0 = Pi = ∀◇⟨⟩`, `Q = ∀◇⟨⟩`; the subject is
    `∀◇(∀◈⟨⟩)`, a ghost over a ghost.  The algorithm is forced into
    `𝒞 = [α ≐ ⟨⟩]` (LE-UnivGhost, LE-Var) and `Pa = ⟨⟩` (SE-GhostGuarded,
    SE-Unit), and the precision goal `⟨⟩ ⊑ᵖ ∀◈⟨⟩` has no rule.
  - `p6cs_fires_when_the_subject_is_wf` — instantiates the CLOSED theorem on
    the same shape with `ψa := ⟨⟩`, showing the premise set is satisfiable
    (the theorem is not vacuous).

Both are `Qed` and axiom-free; registered in `docs/WF-SIDE-CONDITIONS.md`.
(An earlier closure also carried a wf premise on the SOURCE skeleton `P`, with
the looked-up rigid α as a context entry — a Δ-reading is unsatisfiable, since
`a_wf_pskl__tophole` resets Δ to ∅.  Once the subject wf is in, that premise is
dead weight and was removed.)

**Reusable machinery landed with it** (same file, §§1–3):
  - the **∀-BINDER KIT** — run the IH under a fresh rigid β added to both Θ and
    Θ0, then strip β from every output: `a_inc_strip_tvar_mid`,
    `a_solve_cstr_strip_tvar_mid` (free — solving only inspects Θ for
    flexibility), `ad_partial_precise_strip_tvar_mid` (ftv-based; the existing
    `_strengthen_tvar` wants `Z ∈ Δ`, which never holds here),
    `a_wf_ptyp_mono_strip_tvar`, plus `ad_refine_syn_delta_to_tvar_mid`, the
    Δ→Θ transport that reconciles the consistency's Θ-binder with the
    refinement's Δ-binder;
  - `a_looksub_lookeq_rename_tvar` — simultaneous rigid renaming on BOTH sides
    keeping Ξ and 𝒞, which turns one fresh-β instance into LE-ForallInh's /
    LE-UnivGhost1's cofinite family;
  - two extra conclusion conjuncts, both strengthenings: ρc's images are
    ψa-scoped, and `ftv 𝒞 ⊆ ftv ψa ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ` — the
    mechanized form of the paper's "Pi and 𝒞 cannot contain β", which is
    semantic, proved from `ad_pat_consis_target_ftv` (an `is_tskl` subject's
    counterpart mentions only its own variables plus the context's
    definitions — the target-inventing `__hole` rule needs a PLAIN hole, which
    `is_tskl` excludes) and `ad_refine_syn_src_ftv`;
  - `ad_pat_consis_*_refine_unify` — walk the target's defined-flex chain
    INSIDE the induction, unfolding both the consistency and the refinement
    (`ad_refine_flexdef_target_unfold`), so `__flex_r` never becomes a separate
    case;
  - `msubst_uskl` (+ erasure/tag/open/prepend-fresh lemmas), which makes the
    subject `subst_uskl_in_uskl ψa α (msubst_uskl κ S)` the paper's
    `(κS)[ψa/α]` exactly.  TODO: promote the definition to `algo/def_meta.v`
    when P6-Ss needs it (it forces a full algo rebuild, so it is deferred).


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
`P0 = □ ∨ no_hole` disjunct.  The Task A accumulated-skeleton invariant
(`prop_accum_no_hole.v`) was thereby made obsolete and its file **deleted
2026-07-27** — nothing consumed it once the premise was gone.


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
- the three rows: ∀◇ (UnivGhost, `tophole_both` + tophole_fill/rename),
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
already context-free).  Full `make coq` green; `a_sub_sound` still
Closed under the global context.

## 2026-07-24 (d) — P6 BLOCKED: the -var completeness lemmas REFUTED (machine-checked)

While drafting P6-Cv's statement, the Pi × P0 case grid exposed a subcase
every paper case analysis skips: the solve counterpart `P0` can be a
FLEXIBLE VARIABLE whose κ-image supplies the constructor that the
refinement-premise inversion "exposes".  Concrete configuration
(`Θ0 = X,α̂`; `κ = [α̂ ↦ unit→unit]`; `ψa = X→unit`; `ρ = [X ↦ unit]`;
`Pi = X→unit`; `P0 = α̂`; `Q = unit→unit`) satisfies every premise of
`lemma:complete-consistency-constraint-collection-solving-var`
(consistency-proofs.tex:1181; same for the subtyping twin at
subtyping-proofs.tex:1696) — including the positional side condition —
while the conclusion is unsatisfiable: FlexR forces `Pa = α̂` and the
precision `κa(α̂) ⊑ᵖ X→unit` fails for every `κa ≡ κ`.  Machine-checked
Qed axiom-free: `frost/algo/cex/cex_p6_flex_counterpart.v` (refutes for
arbitrary `Pa`, `κa`, Δ, tag set).  PAPER-GAPS entry added; DESIGN
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
show Δ-membership + precision alone admit ∀◇-wrapped/def-chained leaf
positions that break the conclusion — and is RECOVERED as the lemma
`ad_ppre_delta_var_inv` from freshness of the replaced variables
(Δ-membership, rigid binding, κ-image-/Θ-definition-/∀◇-shielded-ftv
avoidance via the new `pskl_shielded_ftv`).  Kit: solve-cluster
ctx-change/strengthen/weaken/rename + shielded-output bound, msubst
avoidance lemmas, `is_sskl` painting/refine-hole/consis-tags-empty
helpers, and the packaged -var leaf case `p6_leaf_var`.  Statement
decision: the -var lemmas conclude with κ itself (no κa existential).
NEXT: `uskl_rho` per-constructor inversions, then P6-Cv's main
induction (DESIGN §6 2026-07-24 (c) has the full map).

## 2026-07-24 (b) — P5b-ii step (3) QED: precision-substitution closed

**`ad_pat_sub_precise_upre` (paper `lemma:precision-substitution`) is Qed,
axiom-free** (commit f5b3e72; `Print Assumptions` closed; `make coq`
green) — fuel-PRESERVING precision-substitution over the tag-hygienic
mirror, in ⊑ᵤ-form.  Completed this pass: the remaining six per-rule
⊑ᵤ-transports (Arrow; ForallL tagged/untagged — the crux, via cofinite
body-⊑ᵤ + `uskl_precise_subst` + `subst_uskl_in_uskl_intro` + recursion
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
  precision-substitution fuel-preserving under ∀◇-wrapping/flex-folding).
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
to land the plain `⊢ᵣᵃᵈ`/`⊢ᵣₚᵃᵈ` refinements).  The 3 ∀-cases used the
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
algorithmic derivations `Θlib ⊢ᵃ[TI;□] e ⦂ B ⊣ Θ'` with concrete result
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
  `algo/def_consis_refine.v` (decl judgments over Θ with flex lookups:
  `⊢ₚₛᵃ`/`⊨ₛᵃ`/`⊢ᵣᵃᵈ`/`⊢ᵣₚᵃᵈ`, Δ as `atoms` to align with `a_consis`).
- **First lemma Qed**: `a_consis_decorate` = paper "Decorating algorithmic
  consistency" (`algo/prop_decorate.v`), with the `pskl→uskl` embedding kit.
- `algo/prop_inc.v`: ⊴-algebra — `msubst_*_id`, `a_suffix_app`,
  `a_inc_refl_gen` ⇒ `a_isub_refl`, `a_isub_weaken_suffix` (all Qed).
- Notation retrofit of `def_decorated.v`/`def_consis_refine.v` (ground rule 1);
  ground rules 1–3 added to CLAUDE.md.
- `a_wf_ptyp`/`a_wf_pskl` made REAL scoping judgments (`a_binds_tvar` moved
  to `algo/def_rules.v`); `a_inc__flex_def` gained the paper-PROSE side
  condition (κ maps to well-formed monotypes in the target,
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
(2) `frost/algo/def_rules.v` REWRITTEN from `full-algo-spec.tex`: new
`Δ₁∣Δ₂` tracking in `a_consis`, no `refresh`, `□`-RHS Vacuous rules,
GhostLF/GhostL solve rules with `∀◇` outputs, `∀ᾱ.A₀`-input
AbsCheck/AbsAnnoCheck (step/base), Freeze with type input, `a_guess` =
paper's `guess[N]`, `a_sub_flex` (ex-`a_broom`), `Assign-UnivGhost-Id`.
(3) proofs to be redone bottom-up following the paper's appendices; the
pre-sync proof files were moved to `*.v.legacy` (git-tracked, out of the
build) for incremental rebasing.
**Build 🟢 GREEN** (`make coq`).

<!-- BEGIN paper-refs (auto-generated by scripts/sync_paper_refs.py) -->
[thm:sound-type-inference]: ../paper/sections/algorithmic.tex#L410 "Theorem 4.2: Soundness of type inference"
[thm:complete-type-inference]: ../paper/sections/algorithmic.tex#L417 "Theorem 4.3: Completeness and optimality of type inference"
[thm:sound-skeleton-inference]: ../paper/sections/algorithmic.tex#L575 "thm:sound-skeleton-inference"
[thm:complete-skeleton-inference]: ../paper/sections/algorithmic.tex#L582 "thm:complete-skeleton-inference"
[thm:sound-consistency]: ../paper/sections/algorithmic.tex#L675 "thm:sound-consistency"
[thm:complete-consistency]: ../paper/sections/algorithmic.tex#L682 "thm:complete-consistency"
[thm:sound-subtyping]: ../paper/sections/algorithmic.tex#L1440 "Theorem 4.5: Soundness of subtyping"
[thm:complete-subtyping]: ../paper/sections/algorithmic.tex#L1447 "Theorem 4.6: Completeness and optimality of subtyping"
[lemma:no-guess-poly]: ../paper/sections/declarative.tex#L1241 "lemma:no-guess-poly"
<!-- END paper-refs -->
