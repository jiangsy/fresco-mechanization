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
| Decl judgments in algo contexts (app:decl-in-algo-context) | `algo/def_decl_algo.v` (`ad_pat_consis`, `ad_refine_syn`, `ad_refine_pskl`, `ad_wf_pskl` + flex-lookup rules); `algo/def_decl_algo_sub.v` (`ad_pat_sub`, its fuel-indexed `ad_pat_sub_n`, `ad_partial_precise`); `algo/def_decl_algo_sub_hyg.v` (`ad_pat_sub_g`, the hygienic mirror) | 🟡 consistency / refinement / skeleton-subtyping / partial-precision layers all DONE and used by closed proofs (audited 2026-07-28); only the TYPING layer (`ad_typing`-style, needed by section D) is still absent |

## Theorems / lemmas (bottom-up order; ⬜ = to prove, per paper appendix)

**B. consistency-proofs.tex** (§Consistency) — ALL PROVED (status audited 2026-07-28; every `algo/` file is admit-free)
- ✅ Soundness of decorated consistency (`a_consistag_sound_aux`, `algo/prop_consis_sound.v`)
- ✅ Decorating algorithmic consistency (`a_consis_decorate`, `algo/prop_decorate.v`); ✅ Consistency decoration (`algo/prop_decorate_sub.v`, consistency-proofs:88)
- ✅ Soundness of Consistency, all three parts: part 1 `a_consis_sound` / `a_consis_sound_aux` (`algo/prop_consis_sound.v`, the aconsis main induction), parts 2–3 `a_unify_sound` / `a_assign_sound` (mutual bundle `a_assign_unify_consis_sound`)
- ✅ Consistency constraint decoration for variables (`algo/prop_decorate_sub.v`, consistency-proofs:606)
- ✅ Completeness of consistency constraint collection & solving: `a_lookeq_solve_complete` (P6-Cs, `algo/prop_look_complete_cstr.v`) and `a_solve_eq_complete_var` (P6-Cv, `algo/prop_look_complete_var.v`) — both axiom-free; P6-Cs carries one paper-external wf side condition whose necessity is machine-checked (`algo/cex/cex_p6cs_subject_wf.v`, docs/WF-SIDE-CONDITIONS.md)
- ✅ Completeness and optimality of Consistency, all three parts (`a_consis_complete_thm` / `complete_mu` / `assign_complete_step`, `algo/prop_consis_complete.v`)

**C. subtyping-proofs.tex** (§Subtyping)
- ✅ Decorating algorithmic subtyping (`a_sub_decorate` / `a_sub_decorate_bundle`, `algo/prop_decorate_sub.v` + `algo/prop_decorate_key.v`); Soundness of decorated subtyping (`a_subtag_sound_bundle`, `algo/prop_sub_sound.v`)
- ✅ Look decoration (`algo/prop_pat_sub.v` §7); Decorating constraint solving (`algo/prop_decorate_key.v`); Constraint solving concatenation (`algo/prop_decorate_sub.v` §3, lemma:solvetag-concat)
- ✅ Subtyping decoration (variables → general) (`algo/prop_decorate_sub.v`, subtyping-proofs:175/541); Vacuous subtyping decoration (same file, :483)
- ✅ Stability of constraint collection (`a_looksub_lookeq_subst_stable`); Look freshness (`a_extract_output_fresh`) — both `algo/prop_looksub.v`
- ✅ Decorating instantiation (`a_extract_decorate`, `algo/prop_decorate_key.v`); Soundness of decorated algorithmic subtyping of flexible variables (the flex half of `a_subtag_sound_bundle`)
- ✅ **Theorem: Soundness of subtyping** (`a_sub_sound_thm`, `algo/prop_decorate_key.v`, axiom-free)
- ✅ Complete partial precision (`algo/prop_sub_complete.v` P5b, lemma:partial-precision-complete); Stability of subtyping under more precise substitution (`ad_pat_sub_precise_upre`, same file — P5)
- ✅ Completeness of constraint collection & solving **for variables** (subtyping-proofs:1696, P6-Sv) — `a_solve_sub_complete_var` in `frost/algo/prop_look_complete_sub_var.v`, **Qed and axiom-free** (`Print Assumptions`: closed under the global context).  The paper's statement is **FALSE as given**, machine-checked counterexample `frost/algo/cex/cex_p6sv_forall_flex.v` (`p6sv_with_p6cv_premises_is_false`): its own ForallL case builds, from a ρ = IDENTITY instance, the raw-flexible-payload configuration that `cex_p6_flex_freshened.v` rules unreachable on the constraint-collection route.  What is proved is the REPAIRED statement, which adds the positional premise `flex_shield Θ0 Ψ' Δρ P0 ψa` (plus `flex_apart_walk`, and a `binds`-monotone context generalization so Sub-ForallL can run the IH at `Θ,β`).  `flex_shield_excludes_cex` is kept as the regression test tying the premise to the counterexample.  See docs/PAPER-GAPS.md and DESIGN-completeness-subtyping.md §6 (x)–(a3)
- 🟢 Completeness of constraint collection & solving (subtyping-proofs:2202, P6-Ss) — **CLOSED 2026-07-30**, `Qed` + axiom-free — `a_looksub_solve_complete_gen` (ρ-generalized) + the paper's premise-free ρ = identity corollary `a_looksub_solve_complete` in `frost/algo/prop_look_complete_sub_cstr.v`; **11 of 12 rows closed**, ALL TWELVE ROWS closed.  ⚠️ Phase B's planned prerequisite — a sub-side `ad_pat_consis_target_ftv` — is FALSE at `ad_pat_sub_g__forall_l_tagged` even under `is_tskl` (`cex/cex_p6ss_sub_target_ftv.v`); what Sub-ForallR carries instead is a MODE-GUARDED DISJUNCTION (DESIGN §8 (h)), whose right disjunct (`alpha_stack`) is the shape that never descends the target.  Like P6-Sv it is a REPAIRED statement (`sub_shield`).  ⚠️ P6-Cs's `Δρ ∩ dom Θ0 = ∅` premise was VACUOUS — `cex/cex_p6cs_rho_delta_vacuous.v` — and is now the ftv-level one.
- ✅ **Look completeness** (subtyping-proofs:2730, P6-L) — **CLOSED 2026-07-30**, `Qed` + axiom-free — `a_extract_complete_gen` in `frost/algo/prop_look_complete_extract.v`.  **P6 IS COMPLETE**: all five of its lemmas (P6-Cv, P6-Cs, P6-Sv, P6-Ss, P6-L) are closed.  The statement is the paper's, with the paper's own PROSE well-formedness of ψa restored on the statement (`Θ ⨟ Δ ⊢ₚₛᵃ ⌊ψa⌋ˢ`, which `ad_partial_precise_complete` needs, plus the precision hole rule's `Δ ∩ ftv ψa = ∅`); the paper's `inc[θ≡θa]{Θ0}{Θ}` appears as the reflexive `a_inc_equiv Θ0 κ κ Θ` beside an a_inc conclusion exhibiting θa as the EXTENSION `κa ++ κ` — the mech's `a_inc_equiv` is positional, so that is where the content lives (same reading as P6-Ss).  One ENCODING FIX was required first: `a_extract` now carries a context and solves at `Ξ ++ Θ0`, not `Ξ` alone — the paper's solve/guess judgments are context-FREE, and handing the solve `Ξ` alone hid Θ0's flexibles from the one context-sensitive rule of the cluster (`a_solve_eq__flex_r`), which made P6-L unprovable.  See DESIGN-completeness-subtyping.md §7.4 / §7.5
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

## 2026-07-30 (latest) — P7 opened: the Δ = ∅ corollary, the P7 plan, and TASK 0's SUPPLY CLOSED on the branch that was blocking

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
the Qed `a_consis_complete_thm`.

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
and `__forall_l_untagged` — but `uskl_all_etag` IS `is_tskl`, and ForallL's
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
`frost/algo/cex/cex_p6cs_rho_delta_vacuous.v`.  Its premise
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
**P0-ONLY walk** `flex_apart_p0` (`p0_step` / `p0_walk`, prop_look_complete.v)
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
`ad_ppre_guarded_all_etag_absurd`; and
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
    subject `subst_bskl_in_uskl ψa α (msubst_uskl κ S)` the paper's
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
already context-free).  Full `make coq` green; `a_sub_sound_thm` still
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
(2) `frost/algo/def_extra.v` REWRITTEN from `full-algo-spec.tex`: new
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
