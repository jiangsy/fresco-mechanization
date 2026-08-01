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
- 🟡 Completeness of flexible-variable subtyping (subtyping-proofs:2836, P7a) — **IN PROGRESS**.  TASK 0 (supplying P6-L's `sub_shield` premise at P7b's Sub-ForallL) lives in `frost/algo/prop_sub_shield_supply.v`, all Qed + axiom-free: a mono-ish counterpart (§4, covers a raw FLEXIBLE `P0`), the non-composite shapes (§5), any **flex-free** `P0` (§6, uniformly in ψa and Δρ), and — the generalization that does the real work — any **inh-free counterpart** / any `P0` **with no ∀** (§7/§8: `ad_pat_consis_inh_free_tag_free`, `ad_pat_sub_g_inh_free_tag_free`, `ad_refine_syn_inh_free`, `sub_shield_supply_all_free_p0`).  Residual: a `P0` carrying a ∀ BELOW its head — DESIGN-completeness-subtyping.md §9.0.2
- 🟡 Theorem: Completeness and optimality of subtyping (subtyping-proofs:3050, P7b/P7c) — **IN PROGRESS**.  Motive locked AND REPAIRED 2026-07-30 (`sub_complete_concl` / `sub_flex_complete_concl` / `a_sub_complete_bundle`, `frost/algo/prop_sub_complete_thm.v`): the join is the LEAF-VALID mirror `ad_pat_sub_gv` (def_decl_algo_sub_hyg.v) carrying the subject refinement at the consistency leaves, with NO root-level third premise — the first-cut root premise was REFUTED as a lockstep condition (machine-checked `cex/cex_p7_univ_ghost_r_vacuous.v` + `cex/cex_p7_third_premise_forall.v`: it lost Sub-UnivGhostR entirely and the head-disagreeing ForallL/ForallR solutions `∀a.a ⩽ unit`, `unit ⩽ ∀a.unit`).  FIVE of P7b's rows closed, Qed + axiom-free — Sub-Ghost, Sub-GhostG, **Sub-Infer**, **Sub-Check** and **Sub-UnivGhostR** (a REAL proof: algorithmic UnivGhostR + the `□`-P0 precision core at the stripped counterpart + a `∀◇`-wrap).  The enabling lemma is `a_inc_equiv_precise_msubst` (precision is stable under equivalent metasubstitutions), with the shared core `a_sub_complete_hole_p0_precision`.  ⚠️ Remaining obligation: transport P5's precision-substitution + the freshening kits to `_gv` for ForallL/ForallR.  See docs/PAPER-GAPS.md and DESIGN §9.1.3 / §1.  ⚠️ The property the paper marks with its own TODO at `:3243` ("input `P_0` concrete ⟹ RHS is `P_0`") is **FALSE** — machine-checked `frost/algo/cex/cex_p7_concrete_rhs.v` (`p7_concrete_rhs_is_false`).  Sub-Check / Sub-ForallR are unaffected: both already argue via the EQUIVALENCE, and BOTH halves of it are proved in `frost/algo/prop_sub_concrete_rhs.v` — `a_consis_concrete_output_equiv` and `a_sub_concrete_output_equiv`, each `Θ1 ⊢ P0 ≡ˢ P'`, both falling out of the SOUNDNESS theorems' refinement conjunct plus `ad_refine_syn_ghost_free_equiv`.  See docs/PAPER-GAPS.md and DESIGN §9.1

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

## 2026-08-01 (latest) — 🚧 FRESHNESS CAMPAIGN cluster 3 stage 4: **P6-Cs CONVERTED** (`prop_look_complete_cstr.v` GREEN, axiom-free) — and the decoration layer's subtyping half is BLOCKED on one missing enabler, now fully specified

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
   `cex/cex_p6cs_rho_delta_vacuous.v` into `prop_inc.v`, beside its converse
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

### ⛔ THE BLOCKER — `prop_decorate_key.v`'s two ForallL rows need a new enabler

`a_subtag_decoration` (prop_decorate_key.v:98) has not been converted at all —
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
  the arrow row was found to need it (above).  `Θs`, `Δρ`, `flex_apart_p0` and
  the ρ apparatus therefore stay too.  The same argument applies to P6-Ss's
  mode-guarded ftv-𝒞 disjunction.
- **`a_looksub_lookeq_subst_stable` (§4)** — consumers are exactly
  prop_decorate_key.v:511 and :786, and both are the rows the blocker above
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
  prop_decorate_key.v and prop_look_complete_extract.v:1304 for `_rename_var`
  — so the pairs are kept intact until P6-Ss and the decoration file are
  converted, at which point both `a_lookeq` halves should go.
- **`a_looksub_rename_var` STAYS.**  The re-freshening dance at
  prop_decorate_key.v:228-263 does NOT evaporate: `a_looksub_open_target_at`
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

**Still RED, and where.**  Two files.  `prop_decorate_key.v`
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
`prop_decorate_key.v`; (iii) `prop_look_complete_sub_cstr.v` (P6-Ss, same
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
4. `prop_decorate_key.v` / `prop_decorate_sub.v` (`a_looksub_open_target_at`
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
   prop_decorate_key.v, `dec_ext_solve_eq_step` / `dec_ext_solve_sub_step`
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
`Θ1`, `a_consis_complete_thm`'s neither, and no a_sub run-renaming
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
    `a_consis_complete_thm`, so the closed consistency-completeness
    bundle would re-open with the same parameterization.  Large.
(C) Re-encode the three walk rules' prose-completion (e.g. re-attach
    through a rename on the output, or thread `β` positionally so no
    re-attachment freshness is needed) — touches the ALGORITHM's
    encoding; soundness (prop_decorate_key) re-checks; needs sign-off
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
TWO variants (subject `uskl_all_etag ε Rj` / `uskl_all_syn Rj`),
each taking the IH bundle + the join row's fields as explicit
hypotheses (M ≠ ti, `Ψa ∩ Ψ`, `Ψa ∩ ftag(subject)`, `a_tags_sort`,
wf ⌊ψa⌋, the `_gv` premise at `(Ψ ∪ Ψa, open Rj ψa)`), plus
`sub_shield Θ0 Ψa ∅ P0 ψa` and the WLOG `guarded P0 ∨ P0 = ◇`;
conclusion `sub_complete_concl (S n) …` (the motive's own Hsub is
ignored — the future bundle dispatches, as ForallR did).  Steps with
the located kit:
(1) Pin `R = uskl_all_etag ε Rb` from Hrel by destructing R —
    var-R refutes since paintings never have `all_etag` heads (untagged
    variant: var-R refutes via image mono-ness, `a_inc_lookup_mono`);
    body family by inversion (∀-heads shape-rigid).
(2) Fresh α; feed P6-L (Ψsub := Ψ ∪ Ψa) at
    `R' := open Rb (var α)`: subject premise = forget(HD) slack-erased
    by `ad_pat_sub_g_tyequiv_subject` along `a_uskl_tyequiv_open`
    (sym'd body family, lc ψa via `is_tskl_lc`), then rewritten to the
    subst-form by `subst_bskl_in_uskl_intro` + κ-open commute
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
`a_uskl_tyequiv_all_syn_inv` / `a_uskl_tyequiv_all_etag_inv` (∀-heads
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
  `Ψrep`/`∅` via `subst_bskl_in_uskl_fresh_eq` + `upre__refl` when a
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
  `open_uskl_wrt_uskl R ψ`): `subst_bskl_in_uskl_intro` at a fresh α +
  the packaged form; body-lc premise stated as
  `∀ α, lc_uskl (R ^ α)` so it inverts from either `lc_uskl
  (uskl_all_syn R)` or `lc_uskl (uskl_all_etag ε R)`.

Note `subst_bskl_in_uskl` IS the uskl-into-uskl substitution (ott
sort-naming quirk — its payload argument is a `uskl`); there is no
`subst_uskl_in_uskl`.

## 2026-07-31 — ⭐ Sub-ForallL item 1 CLOSED: `uskl_precise_erase_refine` Qed — in the PLAIN judgment, no `_f` mirror needed

`make coq` green from clean; axiom-free (`Print Assumptions` closed).
Item 1 of the Sub-ForallL plan (the entry below) landed at the end of
`frost/algo/prop_consis_precise.v`:

    Lemma uskl_precise_erase_refine :
      Θ ⨟ Δ ⊢ᵣₚᵃ Qm ⊳ Qr → a_wf_aenv Θ → (∀ α ∈ Δ, α ∉ dom Θ) →
      Θ ⨟ Δ ⊢ₚₛᵃ Qr →
      ∀ Θb Ψr R' R, uskl_precise Θb Ψr R' R →
      (∀ x b, binds x b Θb → binds x b Θ) → ⌊R⌋ˢ = Qm →
      Θ ⨟ Δ ⊢ᵣₚᵃ ⌊R'⌋ˢ ⊳ Qr

**DESIGN DEVIATION — the scoping entry's "candidate resolution" (state
item 1 over the F-indexed mirror `ad_refine_pskl_f` + prove
`ad_refine_pskl_f_wf0` in an F-clean form) was NOT taken.**  The wf∅
crux dissolves the way `ad_refine_syn_trans` (prop_precise.v) already
dissolved the same crux: the TARGET's wf is ASSUMED — the paper's
external-wf side condition (declarative.tex:1427), which the use site
already carries (P5's `Hwfq : Θ' ⨟ ∅ ⊢ₚₛᵃ ⌊Q⌋`) — and the □-node's
empty-Δ form is recovered from the Δ-discipline.  Why this beats the
F-form: (a) the `_gv` joins' leaf refinements are PLAIN `⊢ᵣₚᵃ` at
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
  `Θ ⨟ Δ ⊢ₚᵣᵃ msubst (κa++κ) Pa ⊑ ⌊ψa⌋ˢ`.
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

       Θ ⨟ Δ ⊢ᵣₚᵃ Qm ⊳ Qr → a_wf_aenv Θ → (Δ ∩ dom Θ = ∅-style disj) →
       (wf sides as needed) →
       ∀ Θb Ψr R' R, uskl_precise Θb Ψr R' R → (binds-mono Θb → Θ) →
       ⌊R⌋ˢ = Qm → Θ ⨟ Δ ⊢ᵣₚᵃ ⌊R'⌋ˢ ⊳ Qr

   Induct on the ⊳-derivation; invert `uskl_precise` at each erasure
   shape.  The upre rows that are Qm-shape-INDEPENDENT (refl / hole /
   tophole_remove / flex_l) are handled uniformly (`__hole` uses wf Qr;
   upre__hole itself CARRIES `Θb ⨟ ∅ ⊢ₚₛᵃ ⌊R⌋`).  Congruence rows pair up
   (arrow/all_syn/all_etag/all_inst ↦ __arrow/__all with
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
   `a_consis_complete_thm` threads its own precision (`ad_precise_f` with
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
5. **The row** `a_sub_complete_forall_l` (shape: subject `uskl_all_etag ε
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
  `subst_bskl_in_uskl_rename_compose`.  This per-case re-freshening is the
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
transport) to `κ⌊Ra⌋`, then `a_consis_complete_thm`; its run's
`a_consis_sound_aux` gives the id-witness w1 + wf Θ1 + the Θ1-join for the
output's SCOPE.  CODOMAIN at (Θ1, ζ1): wf's weaken by `a_wf_pskl_isub`; the
IH's slack = `a_uskl_tyequiv_trans` of the motive component with
`a_inc_equiv_msubst_uskl` (at Hie1), collapsed by
`msubst_uskl_syn_compose_id` (every Rb-variable is Θ0-bound —
`a_wf_pskl_ftv_binds_tvar` + `ftvar_in_pskl_uskl_to_pskl`; rigids are
outside both domains by `binds_unique` discrimination); the fill moves κ→ζ1
by `msubst_compose_id_pskl` + `a_inc_equiv_msubst_pskl` + the syn transport.
ASSEMBLE `a_sub__arrow`; package: `a_sub_sound_thm` gives w2; `is_id_inc_unique`
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
`Θ ⨟ ∅ ⊢ᵣₚᵃ ⌊R1⌋ˢ ⊳ ⌊Q1⌋` like `__infer` does.  Caught while planning the
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
leaf facts from `R'` to `κP` before the `a_consis_complete_thm` call;
Check/UnivGhostR get `guarded_pskl P` through `a_uskl_tyequiv_guarded`.

**Naming**: the slack subject is `R'` (uskl ⇒ R-family; the first cut's `T`
violated the metavariable convention).  The Check rows' pskl `B` is the
PAPER's `B` (the inherited btyp of `syn A ⩽ inh B`, embedded) — a
pre-existing rule binder of `ad_pat_sub_g__check` kept to avoid the
inversion-auto-name hazard.

**Sub-Arrow's remaining assembly** (next session).  The row mirrors
prop_consis_complete.v's arrow case :6631-6790 — domain via
`a_consis_complete_thm` (its three premises from the `__arrow` leaf data +
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
`⊢ᵣₚᵃ κ⌊R⌋ˢ ⊳ ⌊Q⌋` is a **LOCKSTEP** condition — `ad_refine_pskl` descends
subject and counterpart together, so it can only hold where the two sides
agree in shape (modulo ghosts on the LEFT and flexible definitions).  It was
imported verbatim from `a_consis_complete_thm`, where it is the PAPER'S OWN
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
`a_consis_complete_thm` invocations consume — Infer/Check use the current
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
(:3134): `skmod` forces `P0 = □` at Infer; `a_consis_complete_thm` on the
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
by definition of `ad_precise`.  What `a_consis_complete_thm` supplies there is
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
justification for it — "it is what `a_consis_sound` / `a_sub_sound_thm`
produce" — is HALF WRONG: `a_sub_sound_thm` produces no subject-refinement
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
`a_consis_sound` already exports `Θ1 ⨟ ∅ ⊢ᵣᵃ inh{P0} ⊳ Qt` with `⌊Qt⌋ = P'`, so
what is left is `ad_refine_syn_ghost_free_equiv` (refinement out of a ghost-free
source only unfolds definitions — one induction, no context threading, since
every ghost row is excluded and the two flexible lookups ARE
`a_pskl_tyequiv__flex_def`).  Hence `a_consis_concrete_output_equiv`:
`Θ1 ⊢ P0 ≡ˢ P'`, the paper's `:3181` step.  §4 adds the three transports the
`a_sub`-level half needs to MOVE an equivalence (`a_pskl_tyequiv_isub_mono` for
Sub-Arrow's `Θ0 → Θ1 → Θ2`, `_weaken`, `_subst_flex_def`).

**And the `a_sub` half is closed too** — `a_sub_concrete_output_equiv`.  It was
planned as a mutual induction with `a_sub_flex`; that is NOT needed:
`a_sub_sound_thm` already exports the output's refinement FROM the input
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
`a_consis_complete_thm`, on the consistency problem `(Θ0; □; P)` (`skmod` forces
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
shape one level up (`a_consis_complete_thm` + `a_consis_concrete_output_equiv`).

**The two rows are now assembled down to ONE missing lemma.**  `skmod` gives
`P0 = □`; `a_sub__infer` gives the run (output `P` at `Θ0`, so the increase
conjuncts are `ζ := κ` + `opt_axiom_factor`); the DECORATED consistency premise
undecorates by `ad_pat_consis_strip_tags` plus a one-line
`⌊κR⌋ˢ = κ⌊R⌋ˢ` commutation; `a_consis_complete_thm` applies at `(Θ0; □; P)`
because its other two premises ARE the motive's refinement premises at `P0 = □`;
and `a_consis_hole_p0_output` makes its precision a precision about `P`.  ⚠️ That
precision arrives under the theorem's own `ζ`, not under `κ`.  The missing lemma
is **precision is stable under equivalent metasubstitutions** —
`Θ ⨟ Δ ⊢ₚᵣᵃ msubst_pskl κ P ⊑ msubst_pskl σ P` given `a_inc_equiv Θ0 κ σ Θ` and
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
∀-free, so it takes the paper's own route (`a_consis_complete_thm` +
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
