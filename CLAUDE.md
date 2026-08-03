# AGENTS.md

Onboarding + ground rules for agents (and humans) touching this Coq
mechanization. **CLAUDE.md is a symlink to this file** — both names
point to the same content.

## TL;DR

- Rocq mechanization of the **Frost** calculus from the paper
  *Haunting Bidirectional Typing* (`paper/frost.tex`, rendered as
  `paper/frost.pdf`).
- Coq namespace: `src` (`-R . src` in `_CoqProject`).
- Build: `make coq` (full kernel check) — the bar for committing.
- **Status** (audited 2026-07-30): Phases 1–2 done; Phase 3 (the
  algorithmic system) is well past scaffolding — **the whole
  mechanization is admit-free and axiom-free**.  Consistency is closed
  in both directions (soundness `a_consis_sound` + `a_unify_sound` /
  `a_assign_sound`; completeness/optimality `a_consis_complete_thm` /
  `complete_mu`), subtyping SOUNDNESS is closed (`a_sub_sound_thm`),
  and subtyping COMPLETENESS has P5 done and **ALL FIVE of P6's lemmas**
  closed — P6-Cv, P6-Cs, P6-Sv, P6-Ss (`a_looksub_solve_complete`) and
  **P6-L (`a_extract_complete_gen`, subtyping-proofs.tex:2730, closed
  2026-07-30)**.  P6-Sv and P6-Ss are REPAIRED statements: the paper's
  P6-Sv is FALSE (`cex/cex_p6sv_forall_flex.v`), and P6-Ss's
  Sub-ForallR needed a mode-guarded ftv-𝒞 disjunction because the
  sub-side analogue of `ad_pat_consis_target_ftv` is FALSE
  (`cex/cex_p6ss_sub_target_ftv.v`) — see docs/PAPER-GAPS.md and
  docs/DESIGN-completeness-subtyping.md §8 (h).  P6-L needed one
  ENCODING FIX: `a_extract` now carries a context and solves at
  `Ξ ++ Θ0`, matching the paper's context-FREE solve/guess judgments
  (DESIGN-completeness-subtyping.md §7.4 / §7.5).  **P7 is the current
  front.**  Its TASK 0 (supplying P6-L's `sub_shield` premise) is
  closed for a flex-free `P0`, for a `P0` with no ∀, and for an
  inh-free counterpart (`prop_sub_shield_supply.v`), leaving only a
  `P0` carrying a ∀ below its head.  P7b's motive is locked (and
  REPAIRED — see below) and SIX of its seven rows are closed
  (`prop_sub_complete_thm.v`): Sub-Ghost, Sub-GhostG, Sub-Infer,
  Sub-Check, Sub-UnivGhostR and **Sub-Arrow** (`a_sub_complete_arrow`,
  2026-07-31; only Sub-ForallR / Sub-ForallL remain, then P7a and the
  bundle).  The enabler is `a_inc_equiv_precise_msubst` (precision
  is stable under equivalent metasubstitutions).  ⚠️ Two things the
  authors must see: the property `subtyping-proofs.tex:3243` marks
  with its own TODO ("concrete `P_0` ⟹ RHS is `P_0`") is FALSE
  (`cex/cex_p7_concrete_rhs.v`) though the paper's own cases are
  unaffected (they argue via the equivalence); and the first-cut
  ROOT-level third solution premise was REFUTED — it was a lockstep
  condition that made `Sub-UnivGhostR` vacuous AND excluded the
  head-disagreeing solutions of `Sub-ForallL` / `Sub-ForallR`
  (`∀a.a ⩽ unit`, `unit ⩽ ∀a.unit`; machine-checked in
  `cex/cex_p7_univ_ghost_r_vacuous.v` +
  `cex/cex_p7_third_premise_forall.v`).  **REPAIRED same day**: the
  motive's join is now the LEAF-VALID mirror `ad_pat_sub_gv`
  (def_decl_algo_sub_hyg.v) carrying the subject refinement exactly
  at the consistency leaves; the root premise is gone, all five rows
  re-closed, and `Sub-UnivGhostR` is a REAL proof.  Remaining
  obligation: transport the P5 precision-substitution + freshening
  kits to `_gv` when ForallL/ForallR are written.  The paper's own
  top-level 2-condition `thm:complete-consistency` is FALSE as
  literally stated (only the augmented 3-condition form of
  consistency-proofs.tex:2230 is true), so `thm:complete-subtyping`'s
  Infer/Check invocations of it are a paper gap (PAPER-GAPS.md).
  **TASK 0 SETTLED + REPAIRED (2026-08-03).**  The residual is
  REALIZABLE (`cex/cex_p7_shield_realizable.v`), which showed the
  mech-invented `sub_shield` premise was indexed NON-POSITIONALLY and
  therefore over-strong.  It has been re-indexed: `ss_walk` now steps
  `P0` and the SUBJECT in lockstep and carries the looked-for `α`, and
  the two GUESS-DESCENDING closures (`flex_apart_walk`, `flex_shield`)
  are demanded only where `α ∈ ftv R'`; the guess-FIXED
  `flex_apart_p0` is an independent, UNGUARDED conjunct.  `fa_step`
  lost its two guess-fixed P0 arrow descents (and with them
  `flex_apart_walk_p0`), which is what made the walk satisfiable at
  all.  `p7_sub_shield_repaired_holds` machine-checks the repaired
  premise at the very witness that refutes the old one.  Nothing goes
  to PAPER-GAPS.md — `sub_shield` is not a paper statement.
  **P7c: ALL THREE LAYERS LANDED (2026-08-03).**
  `frost/algo/prop_sub_complete_dispatch.v` (§1–§10, all `Qed` +
  axiom-free) now holds the stuck-check
  (`sub_flex_rigid_head_absurd`), the flex half (`flex_step`), the
  main half's TWELVE-ROW join dispatch (`main_join`) and the
  arrow-subject layer (`main_arrow_holds`).  ⚠️ **Two obstacles remain,
  and BOTH are for the authors** (docs/PAPER-GAPS.md): (i) the
  flexible SUBTYPING walk had **no rule for a term-variable head**
  while the twin assignment walk has `Assign-SkipTmVar` — MACHINE-
  CHECKED (`cex/cex_p7_flex_walk_tm_var.v`) and the reference
  implementation **crashes** on `fun x -> x 1`.  ⭐ **The rules are now
  ADDED** (`a_sub_flex__skip_tm_var` / `__skip_tm_skl`, with decorated
  mirrors and all three mutual inductions updated); what remains is
  P7a's two completeness rows, scoped in DESIGN §12.3.  And (ii) at ForallL
  the join's last rule does not determine the algorithm's rule
  (ForallL/ForallR commute), which the paper covers by a one-sentence
  WLOG whose mechanical content is a join-permutation lemma.  The residual is isolated as the single
  hypothesis `main_forall n`.
  See [`PROGRESS.md`](PROGRESS.md) Part 1 for the per-lemma map.
- **Read these three docs before touching code**: `AGENTS.md` (this
  file, ground rules), `DESIGN.md` (calculus + encoding design),
  `PROGRESS.md` (per-lemma status + daily progress log).

## Doc index

| File | Purpose |
|---|---|
| [`AGENTS.md`](AGENTS.md) | (this file) ground rules, dirs, tooling, conventions |
| [`DESIGN.md`](DESIGN.md) | **Two parts**: Part 1 — Frost calculus design (modes, colours, tags, skeletons, freezing); Part 2 — mechanization design (encoding choices, ctyp / `syn_color` / `inh_color`, proof-debugging methodology, gap rationales) |
| [`PROGRESS.md`](PROGRESS.md) | **Two parts**: Part 1 — paper → Coq mapping (every paper Lemma / Theorem with status, statement, location); Part 2 — daily progress log |
| [`README.v`](README.v) | Compilable paper-to-Coq theorem index. Has `Check` statements for every paper-claim theorem + `Print Assumptions` for D1 / D12. Run via `make coq`. |
| [`Makefile`](Makefile) | ott + lngen + coq pipeline; `coq` / `quick` / `clean` / `sync-paper-refs` targets |
| [`scripts/sync_paper_refs.py`](scripts/sync_paper_refs.py) | Sync paper Lemma / Theorem numbers from `paper/frost.aux` into .v comments and the auto-managed reference-link block in `PROGRESS.md`. Run via `make sync-paper-refs` or `make sync-paper-refs-md`. |
| [`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md) | Canonical registry of everything the paper's authors should see (gaps, prose-completions, refuted statements) |
| [`docs/WF-SIDE-CONDITIONS.md`](docs/WF-SIDE-CONDITIONS.md) | **Read before mechanizing any refinement / consistency / subtyping / skeleton-inference lemma.** The paper states well-formedness (and sometimes a further judgment) as an EXTERNAL requirement in prose, and its rules then omit the side conditions it would supply. Several judgments look FALSE until that condition is restored. |
| [`docs/HANDOFF-p7c-finish.md`](docs/HANDOFF-p7c-finish.md) | **ACTIVE hand-off**: the three tasks that finish subtyping completeness (`a_sub_complete_bundle`) — the two term-variable P7a rows, `main_forall`, the assembly |
| [`docs/HANDOFF-typ-all-plain-refactor.md`](docs/HANDOFF-typ-all-plain-refactor.md) | Historical hand-off doc from the 2026-05-15 typ_all_plain removal pass |
| [`../paper/sections/`](../paper/sections/) | Authoritative paper source (mechanize against `declarative.tex`, `syntax-directed.tex`, `algorithmic.tex`, `proofs.tex` only — `*-old.tex` and `*-quantifier-rows.tex` are abandoned drafts) |

## Phase status (current)

| Phase | Scope | Status |
|---|---|---|
| 1 | Syntactic / judgment **definitions** for the declarative system; algorithmic placeholder. | 🟢 **done** |
| 2 | Declarative metatheory (subsumption, subtyping soundness, refinement preserves wf, skeleton validity/safety, stability lemmas). | 🟢 **admit-free** — D1 / D12 and the restored chain are all Qed; `frost/decl/` has no `admit`/`Admitted` left. See [PROGRESS.md Part 1](PROGRESS.md#part-1-paper--mechanization-mapping). |
| 3 | Algorithmic system definitions and soundness/completeness vs. declarative. | 🟡 in progress, **admit-free** — consistency soundness AND completeness/optimality closed; subtyping soundness (`a_sub_sound_thm`) closed; subtyping completeness has P5 done and **P6 COMPLETE** — all five lemmas closed (P6-Cv, P6-Cs, P6-Sv, P6-Ss, P6-L), P6-Sv/P6-Ss as REPAIRED statements (`cex/cex_p6sv_forall_flex.v`, `cex/cex_p6ss_sub_target_ftv.v`).  **P7 is the current front** — TASK 0's shield supply closed for a flex-free `P0`, a ∀-free `P0`, and an inh-free counterpart; P7b's motive locked and FIVE rows closed (`prop_sub_complete_thm.v`), enabled by `a_inc_equiv_precise_msubst`.  ⚠️ For the authors: the paper's `:3243` TODO property is FALSE (`cex/cex_p7_concrete_rhs.v`); the first-cut ROOT-level third solution premise was REFUTED (lockstep — `cex/cex_p7_univ_ghost_r_vacuous.v` + `cex/cex_p7_third_premise_forall.v`) and REPAIRED via the leaf-valid join `ad_pat_sub_gv`; the paper's own 2-condition `thm:complete-consistency` is FALSE as literally stated (PAPER-GAPS.md). |

## Directory map

```text
mechanization/
├── CLAUDE.md             (this file — ground rules; also serves as AGENTS.md)
├── DESIGN.md
├── PROGRESS.md
├── README.v              (paper index + Print Assumptions, compilable)
├── Makefile              (ott + lngen + coq pipeline)
├── _CoqProject           (-R . src)
├── scripts/
│   └── sync_paper_refs.py  (paper.aux → .v / .md sync)
├── docs/
│   └── HANDOFF-typ-all-plain-refactor.md
└── frost/
    ├── language.ott      (PURE SYNTAX — types, terms, modes, skeletons,
    │                      tagged types/skeletons, contexts, formulas)
    ├── def_ott.v         (generated by ott — DO NOT EDIT)
    ├── prop_ln.v         (generated by lngen — DO NOT EDIT)
    ├── def_extra.v       (cross-system meta-fns + predicates)
    ├── predicates.v      (shape predicates: is_syn / is_styp / is_ityp /
    │                      is_ttyp / guarded_*, over the type hierarchy)
    ├── coercions.v       (paint/erase conversions: ptyp_to_btyp_syn,
    │                      ptyp_to_utyp_syn, btyp_to_utyp_syn, btyp_to_ptyp, …
    │                      + their open/commute lemmas)
    ├── prop_basic.v      (lemmas about top-level extras)
    ├── notations.v       (paper-faithful scoped notations)
    ├── ltac_utils.v      (tactics; coqhammer-backed)
    ├── decl/             (declarative system — FLAT, no subdirs)
    │   ├── def_extra.v   (Inductive rules: typing, subtyping, consistency,
    │   │                  skeleton inference, skeleton subtyping/consistency,
    │   │                  skeleton refinement, well-formedness)
    │   ├── notations.v   (paper-faithful notations for declarative judgments)
    │   ├── prop_basic.v
    │   ├── prop_wellformed.v          (d_wf_denv + well-formedness lemmas)
    │   ├── prop_weakening.v           (weakening / narrowing, split-syntax)
    │   ├── prop_renaming.v            (tvar-renaming closure for all judgments)
    │   ├── prop_skeleton.v            (skeleton refinement preserves wf, D4)
    │   ├── prop_general_subsumption.v (D1 + D12; CST; FN^n spine machinery —
    │   │                              is_fn_n / btyp_spine / d_consis_sub_trans /
    │   │                              d_sub_trans_spine)
    │   └── prop_stability.v           (order irrelevance d_typing_order_irrel +
    │                                  structural/stability lemmas;
    │                                  formerly prop_structural.v)
    └── algo/             (algorithmic system — all admit-free)
        ├── def_extra.v          (Phase 3 definitions — ~140 ctors)
        ├── def_meta.v           (metasubstitutions κ, a_inc / a_inc_equiv /
        │                         ⊴, msubst_{ptyp,btyp,pskl,uskl_syn})
        ├── def_decl_algo*.v     (declarative judgments over algo contexts:
        │                         consistency, refinement, subtyping, precision)
        ├── def_decorated.v      (decorated (tagged) skeletons + judgments)
        ├── notations.v
        ├── prop_inc*.v / prop_metasubst.v / prop_compose.v   (θ-algebra)
        ├── prop_flex.v / prop_normal.v / prop_mono_bridge.v  (flex + monotypes)
        ├── prop_consis_sound.v      (thm:sound-consistency, all 3 parts)
        ├── prop_consis_complete.v   (thm:complete-consistency, all 3 parts)
        ├── prop_decorate*.v         (decoration of consistency/subtyping;
        │                             prop_decorate_key.v holds a_sub_sound_thm)
        ├── prop_sub_sound.v         (soundness of DECORATED subtyping)
        ├── prop_sub_complete.v      (subtyping completeness: P5)
        ├── prop_look*.v / prop_solve_sub.v  (constraint collection + solving;
        │                             prop_look_complete_var.v = P6-Cv,
        │                             prop_look_complete_cstr.v = P6-Cs,
        │                             prop_look_complete_sub_var.v = P6-Sv,
        │                             prop_look_complete_sub_cstr.v = P6-Ss,
        │                             prop_look_complete_extract.v = P6-L)
        ├── test_*.v                 (benchmark / regression checks)
        └── cex/                     (machine-checked counterexamples, incl.
                                      cex_p6cs_subject_wf.v)
```

(History: the old `decl/{subtyping,typing}/` subdirs and the
`prop_subtyping.v` / `prop_typing.v` umbrellas were flattened; their contents
now live directly under `decl/` in the files above.)

## Encoding conventions

These are load-bearing decisions — read [`DESIGN.md`](DESIGN.md)
before changing any of them.

- **Pure syntax in `language.ott`, rules in `def_extra.v`.** The ott
  file declares only grammars, substitutions, freevars, and formulas.
  All `Inductive` rules go in the matching `def_extra.v` (top-level
  for cross-system, `decl/` for declarative, `algo/` for algorithmic).
- **Single `typ` AST with multiple colour / tag flavours of ∀.** Three
  `forall` constructors: `typ_all_col c A` (colour-tagged ∀, with
  `c ∈ {colour_syn, colour_inh}` from the paper), `typ_all_etag ε A`
  (ε-tagged ∀ for instantiation tracking). Paper's "synthesised type"
  / "inherited type" / "bidirectional type" are **predicates** over
  `typ` (`is_syn_typ` / `is_inh_typ` / structural), not separate
  inductives.
- **Colourless base `ctyp` + `syn_color` / `inh_color` paintings.**
  Where the paper writes `syn{A}` / `inh{A}` over a single
  meta-symbol `A`, the mechanization quantifies **one base `C : ctyp`**
  and writes `syn_color C` / `inh_color C` for the two paintings.
  Round-trips: `erase (syn_color C) = C = erase (inh_color C)`. See
  [`DESIGN.md` Part 2 — colour-encoding principle](DESIGN.md).
- **Tag context `Δ`** is `list atom`. Disjoint append: `list_disjoint
  Δ Δ'` premise + plain `++`. Multiset would simplify the `mod
  Permutation` arrow case of `d_consis_compose` — deferred.
- **Skeleton-scope context `Ψ`** is `list atom`, distinct from the
  term-context `Γ`. Used in skeleton well-formedness and refinement.
- **Locally-nameless via lngen**, including for ε tag variables.
  Cofinite quantification on binder rules. Imports go through
  `Metalib.Metatheory`.

## Build and workflow

- **Full kernel check**: `make coq` from `mechanization/`. Parallelism
  on by default (`-j 4`); override with `make NJOBS=8 coq` on bigger
  machines. **This is the bar for committing / pushing.**
- **Fast dev iteration**: `make quick` runs in `vos` mode (skips
  opaque-proof checking — ~3–4× faster). Useful when iterating on
  large files; the axiom/admit count is NOT verified in `vos` mode,
  re-run `make coq` before committing.
- **Sync paper refs**: `make sync-paper-refs` rewrites `[paper-ref:
  ...]`-marked comments in .v files and the auto-managed reference-
  link block at the bottom of [`PROGRESS.md`](PROGRESS.md). The Markdown-only
  variant is `make sync-paper-refs-md`. Run after editing
  `paper/sections/*.tex` or `paper/frost.aux`.
- Regenerate ott/lngen: `make ott && make lngen` (runs automatically
  as part of `make coq`).
- Clean: `make clean`. Removes `*/def_ott.v`, `*/prop_ln.v`,
  `CoqMakefile`, `.FILE_LIST`.
- `_CoqProject` lists module roots; `coq_makefile` is regenerated
  from `tree -if` output, so just adding `.v` files in the right
  place is enough.

## Tooling

- **ott** for syntax declaration. Use `repr-locally-nameless`
  metavars and define substitutions/freevars per ott convention.
- **lngen** for locally-nameless infrastructure. Generates
  `prop_ln.v` with free-variable lemmas, opening, substitution
  lemmas, etc.
- **coqhammer** for proof automation in `ltac_utils.v`. Prefer
  `hammer` / `sauto` / `qauto` for goals after manual case splits;
  never leave hammer calls in committed proofs (resolve the term
  they suggest, or use a tactic combination that doesn't depend on
  the hammer being installed).
- The paper uses Unicode in math notation. ott files may use Unicode
  in rule formulae; the Makefile sed-rewrites a few atoms. Keep
  encodings UTF-8 throughout.

## Style and conventions

- Naming follows the reference repo
  [jiangsy/proof_worklist_remechnization](https://github.com/jiangsy/proof_worklist_remechnization):
  `d_typing`, `d_sub`, `d_wf_typ`, `d_chk_inf` for declarative
  inductives; `a_` prefix for algorithmic counterparts.
- Constructor names mirror paper rule labels: paper rule `\dtylab{Sub}`
  becomes `d_typing__sub`.
- One `Inductive` per logical judgment; do not collapse multiple
  judgments into a single relation just to share constructors.
- File naming: `def_*.v` for definitions, `prop_*.v` for properties /
  metatheorems. `decl/` is flat (one `prop_*.v` per topic); pick the
  matching file by topic.
- **Never change the paper's definitions or lemma statements, and follow the
  paper's proof steps.**  Mechanize the statement exactly as the paper gives
  it.  If a paper PROOF STEP has a problem but the original statement is
  still provable (with your own repair), continue the proof with the repair
  and DOCUMENT the problem: a `[paper-gap]` comment at the lemma AND an
  entry in [`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md) (the canonical
  registry of everything the paper's authors should see).  If
  the STATEMENT itself is genuinely false — you have a concrete
  counter-example — STOP and flag it to the user; do not weaken or "fix" the
  statement.
- **Before concluding a statement is false, check the paper's EXTERNAL
  well-formedness conditions** — see
  [`docs/WF-SIDE-CONDITIONS.md`](docs/WF-SIDE-CONDITIONS.md).  The paper
  repeatedly requires well-formedness (and sometimes a further judgment) in
  *prose*, outside the rules — "we require well-formedness of both …", "we
  already required well-formedness separately", "as usual, all inputs are
  well-formed" — and its rules then legitimately omit side conditions that
  well-formedness supplies.  A Coq `Inductive` has no such notion, so each is a
  proof obligation: put it EITHER on the rule as a premise (try this first; it
  is less bookkeeping) OR, if it fails to transport through the structural
  lemmas — especially a `strip`, which removes a context entry — as a hypothesis
  on every lemma over the judgment.  Refinement looked refuted until this was
  restored.
- **Compilation must always end in reasonable time.**  If a proof compiles
  slowly, IDENTIFY the culprit first (time individual tactics /
  `Set Ltac Profiling`) instead of waiting out long builds.  The usual (not
  only) causes are `fsetdec` on a large context — scope it with
  `clear - <needed hyps>; fsetdec` — and unbounded `eauto`; prefer bounded
  depth (`eauto 4`) and explicit lemma application on hot paths.
- **Use notations as much as possible — in BOTH rule definitions and lemma
  statements — and keep them consistent with the paper's judgment forms.**
  Every judgment `Inductive` should be bound to a paper-shaped notation via
  a `where`-clause and its rules written in that notation; lemma statements
  use the notations too. See [`decl/notations.v`](frost/decl/notations.v)
  for the legend (`Γ ⊢[ M ] e ⇒ A` for `d_typing`, `Δ ⨟ Γ ⊨ T ≈ A`
  for `d_consis`, etc.). Only relations with no paper counterpart may use
  application form.
- **Atom sets never name a module.** `frost/notations.v` completes what
  `Metalib.Metatheory` abbreviates only partly: it adds `inter` / `diff` /
  `mem` and the `AtomSetImpl` lemma names we use (`union_1`, `inter_3`,
  `singleton_1`, …), plus the infix `S1 ∪ S2` (65) / `S1 ∩ S2` (63) /
  `S1 ∖ S2` (61) — all below `[=]`/`[<=]`, so the dominant disjointness side
  condition reads `Δ ∩ ftvar_in_pskl P [=] empty`. `AtomSetFacts` is already
  re-exported by metalib. Write **no** `AtomSetImpl.` / `AtomSetFacts.`
  qualifier; if something is missing, add the abbreviation there.
- **Metavariable convention — the `language.ott` grammar's own symbols.**

  `A` for `ptyp`, `B` for `btyp`, `C` for `utyp`, `P` for `pskl`, `Q` for
  `bskl`, `R` for `uskl`, and `𝒞` for constraint lists (`a_cstrs`, the paper's
  `\mC`) — with numeric suffixes for extras (`A1`, `Q2`) and mnemonic lowercase
  suffixes where they carry meaning (`Qb`, `Rg`, `Pi`, `Qsrc`). Type and
  skeleton VARIABLES (i.e. `atom`s) are greek — `α`, `β`, `γ`, `δ`; the
  generated `def_ott.v` / `prop_ln.v` already use `α` (Makefile sed on the
  ott metavar stems). Paper greek keeps its meaning everywhere: `τ` monotype,
  `ψ` ghost skeleton, `κ`/`σ`/`ζ` metasubstitutions, `Γ`/`Δ`/`Ψ`/`Θ`/`Ξ`
  contexts. Term variables stay `x`/`y`/`z`, ε tags stay `ε`.
  - ⚠️ **The metasubstitution is `κ`, NOT the paper's `θ` — and `ρ` is
    RESERVED for the paper's rigid-variable substitution.** Two renames are
    baked in here. `θ` is unreadable next to the context `Θ` (they differ by
    one stroke), and `ρ` cannot be reused for metasubstitutions because
    subtyping completeness needs BOTH at once: P6-Sv states `κ ∷ Θ0 ⊑ Θ`
    beside `uskl_rho NM Θ Δρ Ψρ ψsub ψa`, where `Δρ`/`Ψρ` are the
    ρ-replaced variables and the tags ρ introduces. So: `κ` is the
    information-increase metasubstitution (`msubst_*`, `a_inc`), `σ` the
    second one (`a_inc_equiv`), `ζ` the composing one (`ζ ∘ κ`); a second
    `κ` in one statement takes ONE prime (`κ'`), never `κ1`/`κ2` as fresh
    bases. Anything spelled `ρ` denotes the paper's ρ (`uskl_rho`,
    `rho_fresh`, `msubst_uskl` in prop_decorate_sub.v).
  - **Disambiguate with ONE prime, then digits 0/3/4/… — never `Q1`/`Q2`.**
    ott names the arrow-constructor arguments `A1 A2 / … / R1 R2` and the var
    argument `α`, so those are exactly the names `induction` / `inversion`
    manufacture; a later explicit `intros Q1` then fails with "Q1 is already
    used". Coq never auto-generates a primed name. At most one prime.
  - **Only `α` and `β` are bases** (plus `α1`/`β1`, `α2`/`β2`, and at most ONE
    prime). `γ`/`δ` are NOT used: keeping the alphabet small is deliberate, and
    it leaves the other greek letters for their paper roles. An atom SET is
    never `R` — a set unioned into the tag context (`Θ ⨟ (Δ ∪ S) ⊢ …`,
    `delta_def_fresh S Θ`) is a Δ, so it takes `Δ'`.
  - **Ghost glyphs in COMMENTS — `◇` `◈` `∀◇` `∀◈`, and NEVER a combining
    diacritic.** The paper draws these as a ghost outline (`\mathghost`),
    optionally containing a small `∀` (`\forallghost`), with the *dotted*
    variants as a dashed outline (`\DottedHole` / `\dottedforallghost`). The
    comment stand-ins are: `◇` = `hole`, `◈` = `holeg`, `∀◇` = `tophole`,
    `∀◈` = `topholeg` (`□` for `hole` also survives and is fine). ⚠️ The
    older spellings `⊤◇` / `⊤̇◇` / `⊤◇̇` / `◇̇` / `⟨⟩̇` / `⊙̇` are RETIRED:
    `⊤` reads as a top type it has nothing to do with, and the dot was
    U+0307, a COMBINING diacritic that renders as a floating smudge in
    monospace (the hazard `docs/PROPOSAL-notation-pass.md` already warned
    about — that file keeps its combining dots deliberately, as specimens,
    and `DESIGN.md` keeps one quoting the paper's own `□̇.P`).
  - ⚠️ **After `induction H` / `inversion H` the names in scope are the RULE's
    binders, not the lemma's.** The rules' *type variables* are greek now (the
    `def_*.v` inductives were renamed too), but their *skeleton/type* binders
    still read `P`/`Q`/`R`/`A`, so a proof body legitimately says `P` where the
    statement said `Q'`. When a rename breaks with "variable … not found" or
    "… is already used", that is almost always this: the name belongs to the
    rule. Say so in a comment rather than forcing the rename — and when the
    lemma's own variable really must move, prefer `α0` (that is how Coq itself
    freshens a shadowed binder) and keep the redirect scoped to the region
    that needs it, not the whole proof.
- Tactic style follows the reference repo — `eauto`-driven, with
  hammer-derived scripts simplified before commit.
- Comments document **why** an encoding is the way it is, not what
  the rule says (the paper says that). Cite paper rule names when a
  Coq constructor is non-obvious.
- **Never commit a KNOWN-FALSE proof; that is the real rule.**  The
  default remains ZERO `Admitted` / `Axiom`: a standalone lemma that
  cannot be finished is ABORTED — delete it, leave a short `RESTART
  NOTE` comment (what it claimed, why dropped, what a re-proof needs),
  plus a [`PROGRESS.md`](PROGRESS.md) entry.  **Exception (2026-07-15):**
  for a large INCREMENTAL mutual bundle (e.g. the completeness
  optimality / existence bundles), `Admitted` MAY be committed on
  individual cases that are TRUE and merely unfinished, so the bundle's
  structure + glue + closed cases stay durable instead of all-or-nothing.
  Each such admit must be marked honestly — `Admitted. (* TODO[..]:
  <case>; true; blocked on <reason> *)` — and the file must still
  `coqc`-compile.  What stays FORBIDDEN: admitting a case you suspect is
  FALSE, or a MOTIVE you think mis-stated → STOP and report a
  counterexample (a hard falsehood; abort/restart applies).  Standalone
  helper lemmas are still fully `Qed`'d; the relaxation is for the
  monolithic bundle's cases only.

## Common practices

- Read `paper/sections/declarative.tex`, `syntax-directed.tex`,
  `algorithmic.tex`, `proofs.tex` directly when in doubt — they are
  the authoritative specs. PDF is fine for human reading; LaTeX is
  fine for grep.
- Keep `mechanization/frost/language.ott` minimal. Resist the
  temptation to put rules into ott just because ott has `defns`
  syntax; we want the rules in Coq where they can be edited /
  debugged interactively.
- After editing `language.ott`, run `make` so `def_ott.v` and
  `prop_ln.v` regenerate. `_CoqProject` and `Makefile.coq` pick up
  new `.v` files automatically via the `tree`-based file list.
- Run `git status --short --branch` before and after significant
  edits.
- Do not edit `def_ott.v` or `prop_ln.v` by hand. If a generated
  file is missing a lemma, add the corresponding declaration in
  `language.ott` (or hand-write the lemma in `prop_basic.v`).
- When closing an admit, **always check `Print Assumptions` on the
  flagship theorems** (`d_sd_typing_general_subsumption` /
  `d_sd_typing_general_subsumption_spine` — general subsumption lives on the
  SYNTAX-DIRECTED system since the "Removed base terms" rework; the
  `d_typing`-side versions are corollaries) to ensure you didn't accidentally
  introduce a new transitive axiom. The `make coq` tail prints them all.

## Where things live (cheat sheet)

| Need to … | Edit … |
|---|---|
| Add a new syntactic constructor / sort | `frost/language.ott` |
| Add a meta-function shared by decl + algo | `frost/def_extra.v` |
| Add a predicate / well-formedness used by both | `frost/def_extra.v` |
| Add a declarative typing/subtyping rule | `frost/decl/def_extra.v` |
| Prove a declarative metatheorem | `frost/decl/prop_*.v` (flat; pick the matching file by topic) |
| Add an algorithmic rule | `frost/algo/def_extra.v` |
| Add a global notation | `frost/notations.v` or `frost/decl/notations.v` |
| Add a tactic | `frost/ltac_utils.v` |
| Update the paper → Coq map | `PROGRESS.md` Part 1 (then `make sync-paper-refs-md` if labels moved) |
| Log a closure / refactor / discovery | `PROGRESS.md` Part 2 (dated entry) |
| Explain an encoding choice or methodology | `DESIGN.md` Part 2 |

## References

- Paper: [`../paper/frost.tex`](../paper/frost.tex) (rendered as
  [`../paper/frost.pdf`](../paper/frost.pdf) and the paper-root
  [`../impredicative.pdf`](../impredicative.pdf)).
- Reference repo for file-organization patterns:
  <https://github.com/jiangsy/proof_worklist_remechnization>
  (different calculus — copy the structure, not the rules).
- Phase 2 + 3 design spec:
  [`../docs/superpowers/specs/2026-05-10-frost-phase23-design.md`](../docs/superpowers/specs/2026-05-10-frost-phase23-design.md).
- Phase 1 design spec:
  [`../docs/superpowers/specs/2026-05-09-frost-mechanization-design.md`](../docs/superpowers/specs/2026-05-09-frost-mechanization-design.md).
