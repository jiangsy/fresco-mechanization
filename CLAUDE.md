# CLAUDE.md

Onboarding + ground rules for agents (and humans) touching this Coq
mechanization.

⚙ This file used to claim it was `AGENTS.md` with `CLAUDE.md` a symlink to it.
That has not been true for some time — there is no `mechanization/AGENTS.md`;
this file is the only copy.  (The repo ROOT has its own separate
[`../AGENTS.md`](../AGENTS.md), which is about the paper, not the
mechanization.)  Corrected 2026-08-09.

## TL;DR

- Rocq mechanization of the **Frost** calculus from the paper
  *Haunting Bidirectional Typing* (`paper/frost.tex`, rendered as
  `paper/frost.pdf`).
- Coq namespace: `src` (`-R . src` in `_CoqProject`).
- Build: `make coq` (full kernel check) — the bar for committing.
- **Status** (audited 2026-08-05): Phases 1–2 done; **Phase 3 is
  admit-free and axiom-free, and both directions of subtyping are
  CLOSED AND UNCONDITIONAL.**
  - Consistency: both directions (`a_consis_sound` / `a_unify_sound` /
    `a_assign_sound`; `a_consis_complete` / `complete_mu`).
  - Subtyping SOUNDNESS: `a_sub_sound`.
  - ⭐⭐⭐ Skeleton-inference SOUNDNESS (section D, thm:sound-skeleton-
    inference): `a_pat_sound` — Qed, axiom-free, `Check`ed in `README.v`.
    Its last piece supplies a lemma the paper asserts inline and never
    states ("preservation of refinement under type equivalence",
    `a_consis_chk_annot_refine`); see `docs/HANDOFF-section-d.md` §7.
  - ⭐⭐⭐ Type-inference SOUNDNESS (section D, thm:sound-type-inference):
    `a_typing_sound` — Qed, axiom-free, `Check`ed in `README.v`.  Its
    prerequisites are `lemma:suffix-erasure` for all six judgements
    (`algo/prop_suffix_erase.v`) and `lemma:split-refine` COLOURED
    (`a_split_refines_gen`).  ⚠️ It required FOUR side conditions the paper
    leaves to prose to be stated ON the rules — the two Barendregt
    conditions the suffix-DISCARDING check rows need, the `uniq` filter
    `AT-Abs` needs on `guess^TY`'s block, and the correction of
    `AT-AbsAnnoCheck`'s result domain.  All in `docs/PAPER-GAPS.md`.
  - ⭐⭐⭐ Skeleton-inference COMPLETENESS (section D,
    thm:complete-skeleton-inference): `a_pat_complete` — Qed, axiom-free,
    `Check`ed in `README.v`.
  - ⭐⭐⭐ Type-inference COMPLETENESS (section D,
    thm:complete-type-inference): `a_typing_complete` — Qed, axiom-free,
    `Check`ed in `README.v`.  ⭐⭐ **At a CLOSED program it is now stated over
    the paper's own declarative judgements** (`· ⊢ˢ[M] e ⦂ B` and
    `· ⊢[M] e ⦂ B`), matching the soundness corollaries:
    `a_typing_complete_sd_infer` / `_sd_check` / `_decl_infer` / `_decl_check`.
    What closed them (2026-08-11) was carrying two presuppositions the paper
    states in PROSE and the mech had deferred — skeleton consistency implies
    refinement (`declarative.tex:2074`) and the counterpart is well-formed
    (`:1595`).  ⚠️ The first is NOT derivable from the consistency rules; read
    without it, declarative skeleton inference types programs no run can
    produce.  Author-facing note: [`docs/ghost-capture.tex`](docs/ghost-capture.tex).  Its one unrecorded prerequisite was
    `a_split_complete_tc`, completeness of SPLITTING at check mode (the
    paper's AbsCheck subcase 2); the suffix-discarding rows' scoping
    premise comes from `algo/typing/prop_scope.v`.
  - ⭐⭐⭐ Subtyping COMPLETENESS: `a_sub_complete` (thm:complete-subtyping),
    with **no residual hypothesis** — `Check`ed and audited in `README.v`.  Its
    generalized bundle `a_sub_complete_bundle_holds`
    (`algo/sub/prop_completeness_sub.v`) is deliberately NOT in `README.v`: the
    index carries the paper's statements, not the mech's inductive
    generalizations.  P5, all five P6 lemmas (Cv/Cs/Sv/Ss/L) and P7a/b/c are
    green.
  - What the completeness statement carries BEYOND the paper's own
    premises is only the EXTERNAL wf side conditions registered in
    [`docs/WF-SIDE-CONDITIONS.md`](docs/WF-SIDE-CONDITIONS.md):
    well-formedness of the counterpart, and the subject's ghost-freeness
    at the TY sort.  ⚠️ The latter is genuinely external — it is not
    derivable from the join (`__arrow`'s domain and `__infer` take
    arbitrary subjects), though it is automatic whenever the subject is a
    painting of a TYPE.  (Since 2026-08-06 `a_sub__check` DOES demand it of
    its own subject — see the sort-discipline bullet below — but that is a
    premise the algorithm must SATISFY, not one a caller may assume, so the
    motive still carries the condition.)
  - ⚠️ **For the authors**, the live findings are in
    [`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md) and, in the paper's own
    notation, [`docs/refutations.tex`](docs/refutations.tex).  The
    headline one: `SolE-FlexR` DISCARDED the accumulated pattern, which
    broke look-completeness; the authors' repair (thread the fresh
    suffix `Ξ`, return `guess^TY(P)`) is what the tree now mechanizes,
    and it is what retired the mech's own `sub_shield` / `flex_apart`
    repair tower along with four of our counterexamples.  Also still
    live: the paper's `:3243` TODO property is FALSE
    (`cex/cex_p7_concrete_rhs.v`); the paper's 2-condition
    `thm:complete-consistency` is FALSE as literally stated; refinement
    is NOT transitive (`cex/cex_refine_not_transitive.v`).
  - ⛔ **NOT yet done**: the paper itself.  `paper/` has not been touched
    — see [`docs/HANDOFF-solve-flexr-repair.md`](docs/HANDOFF-solve-flexr-repair.md)
    §0 (standing user directive) and §6 Step 4 for what the repair owes
    `full-algo-spec.tex`.
  - The per-lemma map and the dated history — including every retraction —
    are in [`PROGRESS.md`](PROGRESS.md); this bullet is deliberately short.

- **Sort discipline (2026-08-06)**: the algorithmic judgements range over one
  category (`pskl`), but the paper's rules are sorted BY METAVARIABLE — `A`/`B`
  mark TYPE positions, `P`/`Q` skeleton ones.  The rules now carry that as a
  `pskl_ghost_free` premise (frost/def_shapes.v; kit in `frost/prop_basic.v`).
  ⚠️ Three positions where the paper sorts a slot but the mech deliberately
  does NOT — each argued in [`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md): the two
  figures disagree on `SI-ForallR`'s subject, `SolS-ForallR`'s LHS `A` is a
  slip (sorting it strands `◇ ≼TC ∀β.B`), and `LS-Check`/`LS-ForallR`'s subject
  is true-but-not-free (the collection's structural lemmas are mode-agnostic).

- ⚙ **Before any performance work, read the `.aux` files** — they record
  `proof_build_time` per proof, so the hot spots are known WITHOUT rebuilding.
  Then narrow a single call with `time "F1" fsetdec`.  The 2026-08-06 pass cut
  the tree 970 s → 608 s serial; `prop_flex.v` alone went 133 s → 4.4 s, and
  BOTH culprits were `fsetdec` calls that `grep` would have called innocent
  (one already had a `clear -`, just too wide).

- **Read these three docs before touching code**: `CLAUDE.md` (this
  file, ground rules), `DESIGN.md` (calculus + encoding design),
  `PROGRESS.md` (per-lemma status + daily progress log).

## Doc index

| File | Purpose |
|---|---|
| [`CLAUDE.md`](CLAUDE.md) | (this file) ground rules, dirs, tooling, conventions |
| [`DESIGN.md`](DESIGN.md) | **Two parts**: Part 1 — Frost calculus design (modes, colours, tags, skeletons, freezing); Part 2 — mechanization design (encoding choices, ctyp / `syn_color` / `inh_color`, proof-debugging methodology, gap rationales) |
| [`PROGRESS.md`](PROGRESS.md) | **Two parts**: Part 1 — paper → Coq mapping (every paper Lemma / Theorem with status, statement, location); Part 2 — daily progress log |
| [`README.v`](README.v) | **The compilable paper→Coq HEADLINE index — 31 entries.** Deliberately NOT a catalogue: a paper label is not a reason to appear (the exhaustive map is PROGRESS.md Part 1). Each entry is: the paper's Lemma/Theorem name + label, the statement in the PAPER'S OWN NOTATION (unicode), then `Check` and `Print Assumptions` **together**. So the build tail prints one assumption report per claim and every one must read "Closed under the global context". Adding a claim means adding all three parts. Run via `make coq`. |
| [`Makefile`](Makefile) | ott + lngen + coq pipeline; `coq` / `quick` / `clean` / `sync-paper-refs` targets |
| [`scripts/sync_paper_refs.py`](scripts/sync_paper_refs.py) | Sync paper Lemma / Theorem numbers from `paper/frost.aux` into .v comments and the auto-managed reference-link block in `PROGRESS.md`. Run via `make sync-paper-refs` or `make sync-paper-refs-md`. |
| [`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md) | Canonical registry of everything the paper's authors should see (gaps, prose-completions, refuted statements) |
| [`docs/ghost-capture.tex`](docs/ghost-capture.tex) | **Author-facing note, in the paper's own notation**: the ghost-capture configuration — the consistency rules derive a pair that refinement rejects, so the paper's prose presupposition on skeleton consistency (`declarative.tex:2074`) is load-bearing and not derivable. Two refutations it forced (both since retracted BY the repair, and kept as its justification), and what the repair costs. Build: `make -f Makefile.ghost-capture` from `docs/` |
| [`docs/refutations.tex`](docs/refutations.tex) | **Author-facing note, in the paper's own notation**: the two machine-checked refutations (Lemma E.17 Look completeness; Theorem 4.6 Completeness of subtyping), the shared configuration, the diagnosis (`SolE-FlexR` discards the accumulated pattern) and the suggested repair. Build: `make -f Makefile.refutations` from `docs/`, or `TEXINPUTS=../../paper: pdflatex refutations.tex` |
| [`docs/WF-SIDE-CONDITIONS.md`](docs/WF-SIDE-CONDITIONS.md) | **Read before mechanizing any refinement / consistency / subtyping / skeleton-inference lemma.** The paper states well-formedness (and sometimes a further judgment) as an EXTERNAL requirement in prose, and its rules then omit the side conditions it would supply. Several judgments look FALSE until that condition is restored. |
| [`docs/HANDOFF-closed-corollaries-declarative.md`](docs/HANDOFF-closed-corollaries-declarative.md) | **ACTIVE hand-off**: state the closed-program corollaries against `d_sd_typing` / `d_typing` instead of `ad_sd_typing`. ⭐ SOUNDNESS LANDED 2026-08-10 via the conservativity bridge `algo_decl/prop_conserv.v`. ⭐ 2026-08-11 the TAG-HYGIENE blocker is CLOSED — all four subtyping judgements now read the paper's `fresh Ψ'` the same, GLOBAL way. ⛔ COMPLETENESS still open, blocked by ONE thing: the leaf-valid datum at a ghosty subject (`cex/cex_ad_pat_join_not_leaf_valid.v`) |
| [`docs/HANDOFF-close-subtyping-completeness.md`](docs/HANDOFF-close-subtyping-completeness.md) | **ACTIVE hand-off**: close subtyping completeness — decide reachability (TASK A), state+prove the payload invariant (B), make the shield supply total or kill it (C), land it on the motive and discharge `main_forall` (D) |
| [`docs/HANDOFF-p7c-finish.md`](docs/HANDOFF-p7c-finish.md) | **ACTIVE hand-off**: TASKS 1, 2a and 3 are DONE (2026-08-03); what is left is TASK 2b — TASK 0's `sub_shield` for a `P0` with a ∀ below its head, the bundle's one hypothesis |
| [`docs/HANDOFF-section-d.md`](docs/HANDOFF-section-d.md) | **CLOSED 2026-08-08 — HISTORY**: section D (`proofs.tex`) — soundness/completeness of skeleton and type inference.  All four theorems are Qed and axiom-free; the file keeps the exact Coq statement, the design decision and the obstacle found for each of the six lemmas and four theorems, pass by pass.  ⚠️ Three lemmas the paper calls "straightforward induction" are not |
| [`docs/HANDOFF-typ-all-plain-refactor.md`](docs/HANDOFF-typ-all-plain-refactor.md) | Historical hand-off doc from the 2026-05-15 typ_all_plain removal pass |
| [`../paper/sections/`](../paper/sections/) | Authoritative paper source (mechanize against `declarative.tex`, `syntax-directed.tex`, `algorithmic.tex`, `proofs.tex` only — `*-old.tex` and `*-quantifier-rows.tex` are abandoned drafts) |

## Phase status (current)

| Phase | Scope | Status |
|---|---|---|
| 1 | Syntactic / judgment **definitions** for the declarative system; algorithmic placeholder. | 🟢 **done** |
| 2 | Declarative metatheory (subsumption, subtyping soundness, refinement preserves wf, skeleton validity/safety, stability lemmas). | 🟢 **admit-free** — D1 / D12 and the restored chain are all Qed; `frost/decl/` has no `admit`/`Admitted` left. See [PROGRESS.md Part 1](PROGRESS.md#part-1-paper--mechanization-mapping). |
| 3 | Algorithmic system definitions and soundness/completeness vs. declarative. | 🟢 **admit-free and axiom-free; both directions of subtyping CLOSED**.  Consistency soundness AND completeness/optimality closed; subtyping soundness (`a_sub_sound`) closed; ⭐⭐⭐ subtyping COMPLETENESS closed and UNCONDITIONAL (`a_sub_complete` in `README.v`, off the generalized bundle `a_sub_complete_bundle_holds`) — P5, all five P6 lemmas and P7a/b/c green.  The remaining work is the PAPER, not the mechanization (hand-off §6 Step 4). |

## Directory map

```text
mechanization/
├── CLAUDE.md             (this file — ground rules)
├── DESIGN.md
├── PROGRESS.md
├── README.v              (paper index + Print Assumptions, compilable)
├── Makefile              (ott + lngen + coq pipeline)
├── _CoqProject           (-R . src)
├── scripts/
│   └── sync_paper_refs.py  (paper.aux → .v / .md sync)
├── docs/
│   └── HANDOFF-typ-all-plain-refactor.md
├── frost/
│   ├── language.ott      (PURE SYNTAX — types, terms, modes, skeletons,
│   │                      tagged types/skeletons, contexts, formulas)
│   ├── def_ott.v         (generated by ott — DO NOT EDIT)
│   ├── prop_ln.v         (generated by lngen — DO NOT EDIT)
│   ├── def_shapes.v      (cross-system meta-functions + ALL shape predicates:
│   │                      ftag_in_uskl, mono_ptyp, is_ttyp / is_tskl,
│   │                      is_styp / is_ityp / is_sskl / is_iskl, guarded_*,
│   │                      nonghost_pskl, is_value, mod_comp_{ty,sk},
│   │                      pskl_ghost_free / bskl_ghost_free.  The former
│   │                      def_tags.v and predicates.v folded in here
│   │                      2026-08-06)
│   ├── coercions.v       (paint/erase conversions — DEFINITIONS ONLY:
│   │                      ptyp_to_btyp_syn, ptyp_to_utyp_syn,
│   │                      btyp_to_utyp_syn, btyp_to_ptyp, … + the 4 Coercions)
│   ├── prop_tag.v        (ε-TAG EQUIVARIANCE, syntactic layer: §0 tags are
│   │                      blind to tvar substitution, §1 the transposition on
│   │                      atoms and atom SETS, §2 its action on `utyp`.
│   │                      The paper's ForallL `fresh Ψ'` is a statement about
│   │                      NAMES, and a swap is an automorphism with no side
│   │                      condition where a one-way rename would need the
│   │                      whole derivation's tags.  ⭐ §1 is SORT-AGNOSTIC and
│   │                      shared: `algo/prop_swap.v` imports it rather than
│   │                      redefining `swap_atom` / `swap_atoms`, which is what
│   │                      it used to do — six colliding names, and
│   │                      `algo/prop_pat_sub.v` imports both files)
│   ├── prop_coercions.v  (everything ABOUT those conversions, and the only
│   │                      place any of it goes: §1 retractions, §2 open /
│   │                      open_rec commutation, §3 lc + shape-predicate
│   │                      transport, §4 ftvar transport.  Created 2026-08-09
│   │                      from eleven scattered files — see the ⚠️ below)
│   ├── prop_basic.v      (the PREDICATE layer: the ghost-freeness kit and
│   │                      ghost_free_auto.  Re-exports prop_coercions.v, so
│   │                      its ~99 consumers see both)
│   ├── notations.v       (paper-faithful scoped notations)
│   ├── ltac_utils.v      (tactics; coqhammer-backed)
│   ├── decl/             (declarative system — FLAT, no subdirs)
│   │   ├── def_rules.v   (Inductive rules: typing, subtyping, consistency,
│   │   │                  skeleton inference, skeleton subtyping/consistency,
│   │   │                  skeleton refinement, well-formedness)
│   │   ├── prop_basic.v
│   │   ├── prop_wellformed.v          (d_wf_denv + well-formedness lemmas)
│   │   ├── prop_weakening.v           (weakening / narrowing, split-syntax)
│   │   ├── prop_renaming.v            (tvar-renaming closure for all judgments)
│   │   ├── prop_skeleton.v            (skeleton refinement preserves wf, D4)
│   │   ├── prop_tag_swap.v            (ε-tag equivariance of d_tags /
│   │   │                              d_consis / d_sub and their skeleton
│   │   │                              twins; the per-node ForallL freshening;
│   │   │                              and §4-§5 the tags-BOUND twin
│   │   │                              d_sub_tagsin + the WHOLESALE freshening
│   │   │                              that CST consumes.  ⚠️ read its header:
│   │   │                              the per-node freshening cannot be
│   │   │                              iterated through an induction — that is
│   │   │                              why §4 collects first)
│   │   ├── prop_syntax_directed.v     (d_sd_typing ⇄ d_typing)
│   │   ├── prop_annotation.v / prop_shallow.v
│   │   ├── prop_general_subsumption.v (D1 + D12; CST; FN^n spine machinery —
│   │   │                              is_fn_n / btyp_spine / d_consis_sub_trans /
│   │   │                              d_sub_trans_spine)
│   │   └── prop_stability.v           (order irrelevance d_typing_order_irrel +
│   │                                  structural/stability lemmas)
│   ├── algo_decl/        (⭐ `{{ … }}ad` — the DECLARATIVE rules over an
│   │   │                  ALGORITHMIC context: `a`lgorithmic-context
│   │   │                  `d`eclarative, the paper's app:decl-in-algo-context.
│   │   │                  Same rules as decl/, Θ in place of Γ.  ⚠️ NOT the
│   │   │                  same thing as deco_algo/ below — see the legend in
│   │   │                  frost/notations.v; the two were ONE directory named
│   │   │                  `decorated_algo/` until 2026-08-11, which is exactly
│   │   │                  what made them easy to confuse)
│   │   ├── def_{consis_refine,subtyping,typing}.v     (consistency, refinement, subtyping, precision,
│   │   │                         and — def_typing.v — skeleton
│   │   │                         inference `ad_pat` + syntax-directed typing
│   │   │                         `ad_sd_typing`, which section D is stated over)
│   │   ├── prop_ctx_mono.v      (monotonicity along ctx precision)
│   │   ├── prop_sub_mirrors.v   (the bridges between the paper's [ad_pat_sub]
│   │   │                         and its fuel-indexed mirror [ad_pat_sub_fuel])
│   │   └── prop_conserv.v       (⭐ CONSERVATIVITY: at a FLEXIBLE-FREE Θ the
│   │                             decl-in-algo layer IS the plain declarative
│   │                             system over Γ — the paper's unstated "it is
│   │                             easy to extend them"; + the closing of the
│   │                             run's output context.  ⚠️ Filed under
│   │                             algo/typing/ when written and MOVED here
│   │                             2026-08-11: it relates `d_` to `ad_`)
│   ├── deco_algo/        (⭐ `{{ … }}da` — the paper's DECORATED ALGORITHMIC
│   │   │                  system, app:decorated-algosub: the ALGORITHM's rules
│   │   │                  (a run, with `⊣ Θ'`) over decorated / unresolved
│   │   │                  skeletons `uskl` with a tag context Ψ.  So
│   │   │                  `d → ad` changes the CONTEXT and `a → da` changes
│   │   │                  the SUBJECT; soundness is the chain
│   │   │                  `}}a` ⇒ `}}da` ⇒ `}}ad` ⇒ `}}d`)
│   │   ├── def_decorated.v      (the decorated system's rules)
│   │   └── prop_decorate_sub.v / prop_soundness_sub.v  (decoration of
│   │                             consistency / subtyping;
│   │                             prop_soundness_sub.v holds a_sub_sound.
│   │                             ⚙ the third file, prop_decorate.v, was
│   │                             deleted 2026-08-11: it held nothing but six
│   │                             `pskl_to_uskl` conversion facts, which belong
│   │                             in frost/prop_coercions.v and now live there —
│   │                             the conversion itself moved to coercions.v)
│   └── algo/             (algorithmic system — all admit-free.  Grouped BY
│       │                  JUDGEMENT 2026-08-09; the shared machinery stays
│       │                  FLAT because there is no soundness-only file —
│       │                  soundness is kit for completeness, so a
│       │                  soundness/ vs completeness/ split would lie)
│       ├── def_rules.v          (the algorithmic rules + their notations)
│       ├── def_meta.v           (metasubstitutions κ, a_inc / a_inc_equiv /
│       │                         ⊴, msubst_{ptyp,btyp,pskl,uskl_syn})
│       ├── prop_inc*.v / prop_metasubst.v / prop_compose.v   (θ-algebra)
│       ├── prop_flex.v / prop_normal.v / prop_mono_bridge.v  (flex + monotypes)
│       ├── prop_precise*.v      (precision)
│       ├── prop_swap.v          (EQUIVARIANCE — the one renaming primitive
│       │                         for TYPE variables.  ⚙ its §1 atom layer is
│       │                         `frost/prop_tag.v` §1, imported not copied)
│       ├── prop_pat_sub.v / prop_refine.v / prop_stability.v
│       ├── prop_suffix_erase.v / prop_rename_decl.v
│       ├── prop_wf_preservation.v  (a run's OUTPUT context is well-formed)
│       ├── consis/       (consistency: prop_soundness_consis.v,
│       │                  prop_completeness_consis.v, prop_consis_rename.v,
│       │                  prop_consis_precise.v)
│       ├── sub/          (subtyping — both directions and the collection layer)
│       │   ├── prop_soundness_subtag.v
│       │   ├── prop_looksub.v / prop_solve_sub.v  (collection + solving)
│       │   ├── prop_sub_msubst_equiv.v
│       │   ├── prop_completeness_sub_precise.v (P5)
│       │   ├── prop_completeness_look.v  (P6 FACADE over look/ — read its
│       │   │                              ⚠️ header before pointing a new
│       │   │                              consumer at it)
│       │   ├── prop_completeness_sub_gen.v (P7a+b, the GENERALIZED statement)
│       │   ├── prop_completeness_sub.v     (P7c, the paper's a_sub_complete)
│       │   └── look/    (P6 — the look judgment's completeness, a strict
│       │                 linear chain over a THREE-file shared substrate:
│       │                   prop_rho_relation.v  the ρ relation + inversions
│       │                   prop_solve_ext.v     solve_ext / solve_sub_ext /
│       │                                        cv_mono_concl packages
│       │                   prop_flex_apart.v    flex_apart + Arrow repair
│       │                 then prop_eq_var (Cv) -> prop_eq_cstr (Cs) ->
│       │                 prop_sub_var (Sv) -> prop_sub_cstr (Ss) ->
│       │                 prop_extract (L).  ⚙ The substrate was ONE 6952-line
│       │                 prop_kit.v until 2026-08-09; "kit" named nothing and
│       │                 it was the tree's main source of duplicate names)
│       ├── pat/          (skeleton inference: prop_soundness_pat.v,
│       │                  prop_completeness_pat.v)
│       └── typing/       (type inference — the two theorems, their
│                          reader-facing corollaries, and the files
│                          that serve them and nothing else:
│                          prop_soundness_typing.v
│                          prop_completeness_typing.v  theorem 4
│                          prop_closed.v   the CLOSED-PROGRAM corollaries of
│                                          both — what README.v shows
│                          prop_rigidity.v rigid data survives a run
│                          prop_scope.v    a run's result never mentions the
│                                          suffix it dropped
│                          prop_shape.v    an FN-mode run returns an arrow chain)
├── cex/                  (machine-checked counterexamples + probes; moved
│                          out of algo/ 2026-08-06 — they are findings, not
│                          part of the development)
└── test/                 (benchmark / regression checks)
```

**Naming of the soundness / completeness files** (2026-08-06):
`prop_soundness_<judgment>.v` and `prop_completeness_<judgment>[_<role>].v` —
`prop_soundness_consis.v`, `prop_completeness_consis.v`,
`deco_algo/prop_soundness_sub.v` (the paper's `a_sub_sound`) and
`algo/sub/prop_soundness_subtag.v` (its decorated-run half), and for
subtyping completeness
`prop_completeness_sub_precise.v` (P5), `prop_completeness_look.v` (P6),
`prop_completeness_sub_gen.v` (P7a+b, the GENERALIZED statement) and
`prop_completeness_sub.v` (P7c, the paper's `a_sub_complete`).  The
shared kits (`prop_inc`, `prop_metasubst`, `prop_flex`, `prop_swap`,
`prop_precise`, `prop_pat_sub`, `prop_looksub`, `prop_solve_sub`, …) keep
their topic names.

**Naming of LEMMAS** (2026-08-09):

- **A flagship theorem takes NO suffix.**  It is `a_pat_sound`,
  `a_typing_complete`, `a_sub_sound`, `a_sub_complete` — even though each has
  a dozen row-siblings (`a_typing_complete_var`, `…_app`, …).  ⚙ Four names
  carried a `_thm` suffix that meant nothing (no bare name was ever taken);
  they were renamed, so `_thm` is now free of meaning and must not come back.
- **A fact about a conversion is `<relation>_<conversion>`** — the conversion's
  own name, unabbreviated: `ftvar_ptyp_to_pskl`, `btyp_to_ptyp_open`,
  `lc_bskl_to_pskl`.  ⚠️ NOT `ftvar_in_<target>_<conversion>` and NOT
  `ftvar_in_<conversion>`: the tree accumulated all three and ended up with
  **four names for one fact**.  All such lemmas live in `frost/prop_coercions.v`.
- ⚠️ **A `_<qualifier>` sibling is usually a LAYER, not a size accident.**
  `prop_inc_strengthen.v`, `prop_precise_sub.v`, `prop_precise_recover.v` look
  like small files that want folding into their topical base.  They do not:
  the first two would be import CYCLES (their extra dependencies reach back to
  the base), and the third would put a 5610-line consistency-soundness
  dependency onto the base's 24 consumers.  **Before merging two same-topic
  files, check whether any extra dependency of the smaller one reaches the
  larger** — a five-line reachability script over the `Require` graph — and
  check what the merged dependency surface costs the base's consumers.
  Measured 2026-08-09; each of the three now carries a ⚠️ DO NOT MERGE note.
- ⚠️ **One fact, one name, one file, in its STRONGEST form.**  Duplicated
  top-level names are a correctness hazard, not untidiness: Coq resolves an
  unqualified `apply foo` by import order, so adding one `Require Import` can
  silently switch which `foo` a call site means — this has broken the build
  twice.  Before adding a helper, grep for it.  When two copies differ in
  strength (`=` vs `[=]` vs `[<=]`, general vs variable-instance), keep the
  STRONG one and let the weak uses `rewrite` with it; do not keep both.
  Duplicate count: **0** (audited 2026-08-12; two of the last ten turned out to
  be one fact under THREE names, so grep for the FACT, not just the name).

## Encoding conventions

These are load-bearing decisions — read [`DESIGN.md`](DESIGN.md)
before changing any of them.

- **Pure syntax in `language.ott`, rules in `def_rules.v`.** The ott
  file declares only grammars, substitutions, freevars, and formulas.
  All `Inductive` rules go in the matching `def_rules.v` (`decl/` for
  declarative, `algo/` for algorithmic); the cross-system meta-functions and
  shape predicates go in `frost/def_shapes.v`.  ⚙ All three were called
  `def_extra.v` until 2026-08-12, which named nothing and made "which
  `def_extra.v`?" a routine question.
- **Single `typ` AST with multiple colour / tag flavours of ∀.** Three
  `forall` constructors: `typ_all_col c A` (colour-tagged ∀, with
  `c ∈ {colour_syn, colour_inh}` from the paper), `typ_all_tag ε A`
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
  Imports go through `Metalib.Metatheory`.
- **Binder rules: COFINITE in the declarative layers, EXISTS-FRESH in the
  algorithmic one.**  A declarative rule quantifies over all but finitely many
  atoms (`forall α, α ∉ L -> …`) — the standard LN idiom, and it gives the
  strong elimination the metatheory leans on.  An algorithmic rule describes a
  RUN, and a run opens its binder at one atom of its own choosing, so those
  rules name the atom and constrain it (`x ∉ dom (Ξ ++ Θ1) ∪ dom Θ2 ∪
  fvar_in_exp e`).  The trade is real: cofinite is cheap to USE and expensive
  to BUILD — completeness must regenerate the whole family from the IH's one
  instance, which is exactly what `prop_swap.v` §6's `*_rename_tm` bridges
  exist for — and exists-fresh is the reverse.  Layer by layer:
  - `decl/def_rules.v`, `algo_decl/*` / `deco_algo/*` — cofinite. ✅
  - `algo/def_rules.v` operational judgments (`a_looksub`, `a_solve_*`,
    `a_assign` / `a_unify` / `a_consis`, `a_sub`, `a_typing`) — exists-fresh. ✅
  - `algo/def_rules.v` WELL-FORMEDNESS (`a_wf_ptyp`, `a_scope_pskl`,
    `a_wf_pskl`) — cofinite, deliberately.  These are static judgments, not
    runs; do not "fix" them to match their file-mates.
  - ⚠️ `a_pat`'s four binder rows — still cofinite, the one outstanding
    violation.  `a_typing`'s six were converted 2026-08-08 (`7061d31`);
    `a_pat` was not, because converting it re-opens theorems 1 and 3.  See
    [`docs/REPORT-remech-cleanup-audit.md`](docs/REPORT-remech-cleanup-audit.md) §3.

## Build and workflow

- **Full kernel check**: `make coq` from `mechanization/`. Parallelism
  on by default (`-j 4`); override with `make NJOBS=8 coq` on bigger
  machines. **This is the bar for committing / pushing.**
- **Fast dev iteration**: `make quick` runs in `vos` mode (~3–4× faster).
  ⚠️ **It does not check proof BODIES at all** — `vos` skips everything
  between `Proof` and `Qed`, so it validates statements, imports and name
  visibility *at the statement level* and nothing else. A refactor that
  touches proof scripts (a rename, a dedupe, a moved lemma) can go green
  under `make quick` and still fail `make coq`: on 2026-08-09 three files
  used a moved lemma inside a proof and `quick` passed twice before `coq`
  caught them. Treat `quick` as an interface check; `make coq` is the only
  real gate, and the axiom/admit count is only verified there.
- ⚠️ **Do not write `make coq > log; echo $?`** — with a trailing command the
  shell reports the *echo's* status, so a failed build looks like exit 0.
  (Same trap as piping `make` into `grep`.) Capture with
  `make coq > log 2>&1; rc=$?; …; exit $rc`.
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
  use the notations too. Only relations with no paper counterpart may use
  application form.
  - ⭐ **THE JUDGMENT LEGEND IS IN [`frost/notations.v`](frost/notations.v)** —
    read it before adding or changing any judgment notation. **The SYSTEM is
    the DELIMITER**, and each delimiter is its own notation scope:
    `{{ … }}d` declarative (`frost_d_scope`), `{{ … }}ad` declarative-over-Θ,
    `{{ … }}a` algorithmic, `{{ … }}da` the DECORATED algorithmic system. That frees the turnstile,
    so **SUPERSCRIPT = which copy** (bare types, `⊢ˢ` skeletons, `⊢ˢᵈ`
    syntax-directed) and **SUBSCRIPT = which relation** (`⊢ᵣ`/`⊢ᵣₚ`
    refinement, `⊢ₚᵣ` precision, `⊢ₛ`/`⊢ₑ` the solve layer, and
    `⊢ₚ`/`⊢ᵦ`/`⊢ᵤ`/`⊢ₚₛ`/`⊢ᵤₛ` for well-formedness). One relation's copies
    across systems now differ by the delimiter ALONE —
    `{{ Γ ⨟ Δ ⊢ᵣ Q ⊳ P }}d` vs `{{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad`. The sort is still
    stated ONCE: as the superscript when the system has one relation per
    sort, as the bracket index `N`/`NM` when one relation covers both.
  - ⚠️ **A notation-declaring file must `Open Scope` its own scopes.**
    `Open Scope` is NOT transitive through `Require Import`, and a scope that
    is closed makes Coq report the notation as simply not existing
    ("Unknown interpretation"). Declaring and opening therefore travel
    together — see the note in `frost/notations.v`.
  - ⚠️ **The first slot of a `{{ … }}X` notation carries NO level
    annotation.** Metalib's atom-set singleton is `{{ x }}` (Metatheory.v:41),
    so every `{{`-prefixed rule shares its prefix; camlp5 can only factor them
    when that slot sits at the same entry, and metalib's is plain `constr`.
    Annotate it and the build fills with `notation-incompatible-prefix` and
    one of the two rules silently stops working.
  - ⚙ **Two earlier attempts to carry the system on the TURNSTILE both
    failed the same way** — the system mark competed with the marks the
    judgment itself needs. First (pre-2026-08-09) the system was a SUBSCRIPT
    (`⊢ₐ`), which reads as a sort, and `ᵃ` meant `a_` in `a_wf_pskl` but `ad_`
    in `ad_pat_consis`. Then it was a superscript, which produced three-glyph
    stacks (`⊢ᵣₚᵃᵈ`, `⊢ₛᵃᵈ[`) and forced `ad_sd_typing` to DROP its `ˢ`
    purely to avoid a third mark. Do not reintroduce either.
  - ⚠️ **A mode-generic judgment writes `⦂`, never `⇨`.** `⇨` claims the term
    SYNTHESISES its skeleton, which holds only at `M = TI`; at `TC` the
    skeleton is an input. So `d_pat`/`ad_pat`/`a_pat` read `⊢ₛ[ M ] e ⦂ P`,
    the sort subscript carrying what the arrow used to hint at. The paper
    writes its own mode-generic typing with a plain colon for the same
    reason (`\typp`, `paper/macro.tex:1087`).
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
| Add a meta-function shared by decl + algo | `frost/def_shapes.v` |
| Add a predicate / well-formedness used by both | `frost/def_shapes.v` |
| Add a declarative typing/subtyping rule | `frost/decl/def_rules.v` |
| Prove a declarative metatheorem | `frost/decl/prop_*.v` (flat; pick the matching file by topic) |
| Add an algorithmic rule | `frost/algo/def_rules.v` |
| Add a global notation | `frost/notations.v` (scopes + the judgement legend); a JUDGEMENT's own notation goes on its `Inductive`, via a `where` clause in the matching `def_rules.v` |
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
- ⚙ The two original design specs (`docs/superpowers/specs/2026-05-09-frost-
  mechanization-design.md`, `…-05-10-frost-phase23-design.md`) no longer exist
  in the tree; what survived of them is [`DESIGN.md`](DESIGN.md) Part 2.
