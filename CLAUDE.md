# CLAUDE.md

Onboarding + ground rules for agents (and humans) touching this Coq
mechanization.

⭐ **This repository (`jiangsy/proof_fresco`, branch `main`) is the MAIN
DEVELOPMENT** since 2026-10-10.  It used to be ported from
`impredicative/mechanization/frost/` (the `mech-faithful-wf-refine` worktree);
that tree is now frozen at `884cdc3a` and nothing flows from it any more.
Work here, then sync downward:
- `public` branch — the outside-reader release: the SAME proofs with ALL
  comments removed (since 2026-10-10), no `cex/`, `test/`, `docs/`.
  `README.v` is the only commented file: a short header with the notation
  legend, and one pointer per entry giving the paper's number and name, e.g.
  `(* Lemma C.7 (Completeness and optimality of consistency) *)` — no
  explanations.  To sync: copy every `fresco/` file from `main`, strip Coq
  comments (nested comments + strings handled) and `language.ott`'s
  whole-line `%` comments, regenerate `README.v` from `main`'s (statements
  verbatim, pointers from the paper's numbering — compile the paper with its
  appendices to get current numbers), check every file is token-identical to
  `main` once comments are ignored, `make coq`, commit, push.  Tools:
  `scripts/strip_coq_comments.py`, `scripts/make_public_readme.py` (its
  `POINTER` table maps each README entry to the paper's number and name —
  update it when an entry is added or the paper is renumbered).
- the hosted browser <https://jiang.sy/research/popl2027b/> — repo
  `personal_web`: pin the new `public` commit in `sources.lock.json`
  (`fresco` entry, `localPath` = the `public` checkout), then
  `python3 scripts/export-rocq-navigation.py fresco <public checkout>`,
  `npm run build:fresco && npm test && npm run check`, commit, push.

The paper is NOT in this repository: it lives in the `impredicative`
repository, expected as a sibling checkout (`../impredicative/paper`;
override with `make PAPER_DIR=…`).

## TL;DR

- Rocq mechanization of the **Fresco** calculus from the paper
  *Haunting Bidirectional Typing* (`../impredicative/paper/frost.tex`,
  rendered as `frost.pdf` beside it).
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
    (`algo/basic/prop_suffix_erase.v`) and `lemma:split-refine` COLOURED
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
    premise comes from `algo/typing/prop_typing_scope.v`.
  - ⭐⭐⭐ Subtyping COMPLETENESS: `a_sub_complete` (thm:complete-subtyping),
    with **no residual hypothesis** — `Check`ed and audited in `README.v`.  Its
    generalized bundle `a_sub_complete_bundle_holds`
    (`algo/subtyping/prop_completeness_sub.v`) is deliberately NOT in `README.v`: the
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
    `thm:complete-consistency` is FALSE as literally stated.  (⚙ The
    claim that refinement is NOT transitive is RETRACTED 2026-10-08: its
    counterexample, `cex/cex_refine_not_transitive.v`, rested on the
    mech's old Ghost rule demanding a well-formed fill, which the paper's
    never did; the file now proves only that the rules alone derive an
    ill-formed output, `ad_refine_syn_output_not_wf`.)
  - ✅ **The paper has adopted both algorithm fixes** (paper commit
    `f484dde3`, 2026-10-08): the threaded-`Ξ` `SolE-FlexR` repair and the
    missing `Flex-SkipTmVar` row.  The mechanization already matched both,
    rule for rule.  `SolE-FlexR`'s ghost-subject exclusion (PAPER-GAPS,
    "FINDING 2") is still not in the paper.
  - The per-lemma map and the dated history — including every retraction —
    are in [`PROGRESS.md`](PROGRESS.md); this bullet is deliberately short.

- **Sort discipline (2026-08-06)**: the algorithmic judgements range over one
  category (`pskl`), but the paper's rules are sorted BY METAVARIABLE — `A`/`B`
  mark TYPE positions, `P`/`Q` skeleton ones.  The rules now carry that as a
  `pskl_ghost_free` premise (fresco/def_shapes.v; kit in `fresco/prop_shapes.v`).
  ⚠️ Three positions where the paper sorts a slot but the mech deliberately
  does NOT — each argued in [`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md): the two
  figures disagree on `SI-ForallR`'s subject, `SolS-ForallR`'s LHS `A` is a
  slip (sorting it strands `◇ ≼TC ∀β.B`), and `LS-Check`/`LS-ForallR`'s subject
  is true-but-not-free (the collection's structural lemmas are mode-agnostic).

- ⚙ **Before any performance work, read the `.aux` files** — they record
  `proof_build_time` per proof, so the hot spots are known WITHOUT rebuilding.
  Then narrow a single call with `time "F1" fsetdec`.  The 2026-08-06 pass cut
  the tree 970 s → 608 s serial; `algo/basic/prop_context.v` alone went 133 s → 4.4 s, and
  BOTH culprits were `fsetdec` calls that `grep` would have called innocent
  (one already had a `clear -`, just too wide).
  - ⚠️⚠️ **`.aux` TIMES ARE WALL-CLOCK, SO THEY INFLATE UNDER `-j`** —
    measured 2026-08-22 and it invalidated a whole afternoon's numbers:
    `ext_algo/lifting/prop_lift.v` records **42–64 s compiled ALONE** and **916 s**
    when the same file is built inside `make NJOBS=10` beside the other
    heavy tail files.  ⛔ So NEVER compare `.aux` figures across runs of
    different parallelism, and never build a cost model out of a mix of
    them.  Re-measure the file ALONE before believing any number.
  - ⚙ **The build is CRITICAL-PATH-bound in STRUCTURE** — the chain to
    `README.v` is ~38 files deep and contains most of the heavy files, so a
    full rebuild cannot be parallelised away and `NJOBS` past a handful buys
    little.  ⚠️ A reliable full-gate WALL figure has NOT been established:
    two runs on the same machine gave ~9 min (120 files) and ~38 min
    (49 files, all of them the heavy tail).  Time your own run before
    quoting one.  ⛔ And do not assume a spurious `Require` on the chain is
    a speed-up: removing the most suspicious one in the tree
    (`pat/prop_soundness_pat.v` → `sub/prop_completeness_sub_gen.v`, unused
    by name) SIMULATES TO ZERO, because a parallel chain of the same length
    runs beside it.  Simulate against `.CoqMakefile.d` first; the method is
    in [`docs/REPORT-interface-proofpath-audit.md`](docs/REPORT-interface-proofpath-audit.md)
    Part 3.
  - ⚠️⚠️ **`fsetdec` is NOT MONOTONE in its hypothesis set** (measured
    2026-08-22): narrowing one call's `clear -` list from 6 hypotheses to 5
    made its proof go 25.1 s → **31.4 s**.  A hypothesis can PRUNE the search
    as easily as widen it, so a wide `clear -` is a candidate to MEASURE,
    never a bug to fix on sight.
  - ⭐⭐⭐ **USE `coqc -time`, NOT the profiler and NOT `.aux`.**  It prints one
    line per VERNAC COMMAND — inside a proof that means **per tactic** — with
    no profiler overhead, in a run whose conditions you control.  `.aux` is
    per-PROOF and contaminated by `-j`; `Set Ltac Profiling` inflates ~3×
    (13.8 s profiled vs 4.75 s under `time "TAG" tac`).  Ranking the tree
    with `.aux` and profiling with Ltac once led this file to claim the
    per-proof well was DRY; re-measuring every candidate ALONE with
    `coqc -time` found **226 s in two files** and fixed 172 s of it
    (2026-08-22).
  - ⭐⭐ **THE COST DRIVER IS THE AVOID-SET UNION, not the `clear -` list.**
    A `pick fresh`/`atom_fresh` hypothesis like
    `Fr : β1 ∉ A ∪ B ∪ … ∪ J` (ten sets) makes EVERY `clear - … Fr …;
    fsetdec` decompose all ten — that was 4.6–11.6 s per call, ~57 calls in
    `sub/prop_completeness_sub_gen.v` alone.  ⭐ The cure is already in the
    tree: **`solve_notin_auto`** (the 2026-08-09 ∉-KIT) leads with
    `destruct_notin`, which SPLITS the union first; it is a safe superset of
    `fsetdec` (its last branch *is* `fsetdec`).  That one substitution took
    the file 108.6 s → 40.8 s.
  - ⭐⭐ **An intersection-emptiness goal over ~6+ sets wants an ELEMENTWISE
    proof**, not a bigger `fsetdec`: take `z` in the intersection and derive
    the contradiction in steps, so each residual call sees two or three sets.
    Four such calls (24–30 s each!) took `algo/basic/prop_wf_preservation.v` from
    117.8 s to **13.9 s**.  Worked examples of both cures:
    [`docs/REPORT-interface-proofpath-audit.md`](docs/REPORT-interface-proofpath-audit.md)
    §B8.

- **Read these three docs before touching code**: `CLAUDE.md` (this
  file, ground rules), `DESIGN.md` (calculus + encoding design),
  `PROGRESS.md` (per-lemma status + daily progress log).

## Doc index

| File | Purpose |
|---|---|
| [`CLAUDE.md`](CLAUDE.md) | (this file) ground rules, dirs, tooling, conventions |
| [`DESIGN.md`](DESIGN.md) | **Two parts**: Part 1 — Fresco calculus design (modes, colours, tags, skeletons, freezing); Part 2 — mechanization design (encoding choices, ctyp / `syn_color` / `inh_color`, proof-debugging methodology, gap rationales) |
| [`PROGRESS.md`](PROGRESS.md) | **Two parts**: Part 1 — paper → Coq mapping (every paper Lemma / Theorem with status, statement, location); Part 2 — daily progress log |
| [`README.v`](README.v) | **The compilable paper→Coq HEADLINE index — 34 entries.** Deliberately NOT a catalogue: a paper label is not a reason to appear (the exhaustive map is PROGRESS.md Part 1). Each entry is: the paper's Lemma/Theorem name + label, the statement in the PAPER'S OWN NOTATION (unicode), then `Check` and `Print Assumptions` **together**. So the build tail prints one assumption report per claim and every one must read "Closed under the global context". Adding a claim means adding all three parts. Run via `make coq`. |
| [`Makefile`](Makefile) | ott + lngen + coq pipeline; `coq` / `quick` / `clean` / `sync-paper-refs` targets |
| [`scripts/sync_paper_refs.py`](scripts/sync_paper_refs.py) | Sync paper Lemma / Theorem numbers from `$(PAPER_DIR)/frost.aux` into .v comments and the auto-managed reference-link block in `PROGRESS.md`. Run via `make sync-paper-refs` or `make sync-paper-refs-md`. |
| [`docs/GAPS.md`](docs/GAPS.md) | **The managed, current list of every gap** (paper, implementation, our own to-dos): one entry per finding with a stable ID (G-NN), kind, status re-verified 2026-10-10, evidence and the concrete ask.  Start here; PAPER-GAPS.md is the long-form history it cites as `PG:<line>`.  Update an entry's status here whenever a finding moves. |
| [`docs/PAPER-GAPS.md`](docs/PAPER-GAPS.md) | Canonical registry of everything the paper's authors should see (gaps, prose-completions, refuted statements) |
| [`docs/ghost-capture.tex`](docs/ghost-capture.tex) | **Author-facing note, in the paper's own notation**: the ghost-capture configuration — the consistency rules derive a pair that refinement rejects, so the paper's prose presupposition on skeleton consistency (`declarative.tex:2074`) is load-bearing and not derivable. Two refutations it forced (both since retracted BY the repair, and kept as its justification), and what the repair costs. Build: `make -f Makefile.ghost-capture` from `docs/` |
| [`docs/refutations.tex`](docs/refutations.tex) | **Author-facing note, in the paper's own notation**: the two machine-checked refutations (Lemma E.17 Look completeness; Theorem 4.6 Completeness of subtyping), the shared configuration, the diagnosis (`SolE-FlexR` discards the accumulated pattern) and the suggested repair. Build: `make -f Makefile.refutations` from `docs/`, or `TEXINPUTS=../../impredicative/paper: pdflatex refutations.tex` |
| [`docs/WF-SIDE-CONDITIONS.md`](docs/WF-SIDE-CONDITIONS.md) | **Read before mechanizing any refinement / consistency / subtyping / skeleton-inference lemma.** The paper states well-formedness (and sometimes a further judgment) as an EXTERNAL requirement in prose, and its rules then omit the side conditions it would supply. Several judgments look FALSE until that condition is restored. |
| [`docs/HANDOFF-closed-corollaries-declarative.md`](docs/HANDOFF-closed-corollaries-declarative.md) | **ACTIVE hand-off**: state the closed-program corollaries against `d_sd_typing` / `d_typing` instead of `ad_sd_typing`. ⭐ SOUNDNESS LANDED 2026-08-10 via the conservativity bridge `algo_decl/prop_conservativity.v`. ⭐ 2026-08-11 the TAG-HYGIENE blocker is CLOSED — all four subtyping judgements now read the paper's `fresh Ψ'` the same, GLOBAL way. ⛔ COMPLETENESS still open, blocked by ONE thing: the leaf-valid datum at a ghosty subject (`cex/cex_ad_pat_join_not_leaf_valid.v`) |
| [`docs/HANDOFF-extractable-algo-encoding.md`](docs/HANDOFF-extractable-algo-encoding.md) | **ACTIVE hand-off. ⭐ TODO (1) IS COMPLETE (2026-08-13)** — `fresco/ext_algo/` is a SECOND algorithmic encoding in which no rule's freshness constrains its own output, because a fresh-name SUPPLY is threaded through every component (which is what `type.ml`'s `counter` does). All fourteen judgements are threaded AND bridged to `fresco/algo`'s encoding over the SAME contexts, so the four flagship theorems apply to a threaded run verbatim. ⭐ Two prose-completions became theorems on the way (`AT-Abs`'s and `a_sub__forall_l`'s `uniq` filters on generated blocks). ⭐ **TODO (2) — EXTRACTION — IS COMPLETE (2026-08-14)**: the termination campaign closed (`e_sub_order_total` and `e_consis_order_total`, unconditional, §8b.5–§8b.6), and phase 4 landed a Bove–Capretta runner for EVERY judgement (§8b.7) — `option (sig …)`-shaped, soundness-only, dispatching in the reference implementation's order — so the whole algorithm extracts to clean OCaml. ⚠️ TERMINATION was the paper's own undischarged decidability argument; §7.3 sharpens that into a finding worth sending the authors (filed in PAPER-GAPS) |
| [`docs/HANDOFF-close-consis-unrestricted.md`](docs/HANDOFF-close-consis-unrestricted.md) | **✅ CLOSED 2026-08-17 — HISTORY**: `consis_call_no_ghost` is deleted and the three consistency-runner headlines (`e_assign_impl_complete`, `e_unify_impl_complete`, `e_consis_run_complete`) hold on GHOST-CARRYING skeletons, which is what makes the flagship path reachable. ⭐ It closed by removing the AMBIGUITY rather than solving the two-context problem: `U-FlexL`/`U-FlexR` gained `P0 <> ◇`/`P <> ◇` (the `SE-FlexR` prose-completion again — see PAPER-GAPS), so every ghost cell admits exactly ONE rule; `a_consis_complete` was re-proved by dispatching in the implementation's order (hoist `C-GhostR`, add the mirror `C-Ghost` at a flexible input). ⛔ The file KEEPS its five machine-checked refutations and constraints C1–C6 as the record of why the guard is right — do not restart them |
| [`docs/HANDOFF-close-subtyping-completeness.md`](docs/HANDOFF-close-subtyping-completeness.md) | **ACTIVE hand-off**: close subtyping completeness — decide reachability (TASK A), state+prove the payload invariant (B), make the shield supply total or kill it (C), land it on the motive and discharge `main_forall` (D) |
| [`docs/HANDOFF-p7c-finish.md`](docs/HANDOFF-p7c-finish.md) | **ACTIVE hand-off**: TASKS 1, 2a and 3 are DONE (2026-08-03); what is left is TASK 2b — TASK 0's `sub_shield` for a `P0` with a ∀ below its head, the bundle's one hypothesis |
| [`docs/HANDOFF-section-d.md`](docs/HANDOFF-section-d.md) | **CLOSED 2026-08-08 — HISTORY**: section D (`proofs.tex`) — soundness/completeness of skeleton and type inference.  All four theorems are Qed and axiom-free; the file keeps the exact Coq statement, the design decision and the obstacle found for each of the six lemmas and four theorems, pass by pass.  ⚠️ Three lemmas the paper calls "straightforward induction" are not |
| [`docs/HANDOFF-typ-all-plain-refactor.md`](docs/HANDOFF-typ-all-plain-refactor.md) | Historical hand-off doc from the 2026-05-15 typ_all_plain removal pass |
| [`../impredicative/paper/sections/`](../impredicative/paper/sections/) | Authoritative paper source (mechanize against `declarative.tex`, `syntax-directed.tex`, `algorithmic.tex`, `proofs.tex` only — `*-old.tex` and `*-quantifier-rows.tex` are abandoned drafts) |

## Phase status (current)

| Phase | Scope | Status |
|---|---|---|
| 1 | Syntactic / judgment **definitions** for the declarative system; algorithmic placeholder. | 🟢 **done** |
| 2 | Declarative metatheory (subsumption, subtyping soundness, refinement preserves wf, skeleton validity/safety, stability lemmas). | 🟢 **admit-free** — D1 / D12 and the restored chain are all Qed; `fresco/decl/` has no `admit`/`Admitted` left. See [PROGRESS.md Part 1](PROGRESS.md#part-1-paper--mechanization-mapping). |
| 3 | Algorithmic system definitions and soundness/completeness vs. declarative. | 🟢 **admit-free and axiom-free; both directions of subtyping CLOSED**.  Consistency soundness AND completeness/optimality closed; subtyping soundness (`a_sub_sound`) closed; ⭐⭐⭐ subtyping COMPLETENESS closed and UNCONDITIONAL (`a_sub_complete` in `README.v`, off the generalized bundle `a_sub_complete_bundle_holds`) — P5, all five P6 lemmas and P7a/b/c green.  The remaining work is the PAPER, not the mechanization (hand-off §6 Step 4). |

## Directory map

```text
proof_fresco/
├── README.v                    compilable paper theorem index + assumptions
├── CLAUDE.md / DESIGN.md / PROGRESS.md
├── Makefile / _CoqProject
├── scripts/                    build, paper references and public export
├── docs/                       design notes, findings and historical reports
├── fresco/
│   ├── language.ott            syntax source
│   ├── def_ott.v / prop_ln.v   generated syntax and locally nameless facts
│   ├── def_shapes.v           shared shape predicates and meta-functions
│   ├── prop_shapes.v          shape, closure, opening and substitution facts
│   ├── coercions.v / prop_coercions.v   paint/erase maps and their properties
│   ├── prop_atom_sets.v       disjointness and freshness set algebra
│   ├── prop_tag.v             syntactic tag equivariance
│   ├── notations.v            notation declarations; no proof lemmas
│   ├── ltac_utils.v           shared tactics
│   ├── decl/                  declarative rules and metatheory, over Γ
│   │   ├── def_rules.v
│   │   ├── prop_ctx_mono.v    context monotonicity and weakening
│   │   └── prop_*.v           well-formedness, renaming, subsumption, etc.
│   ├── algo_decl/             declarative rules and metatheory, over Θ
│   │   ├── def_consis_refine.v / def_subtyping.v / def_typing.v
│   │   ├── prop_consistency.v definition folding for skeleton consistency
│   │   ├── prop_ctx_mono.v    context transport, including partial precision
│   │   ├── prop_refinement.v / prop_precision.v / prop_ctx_precision.v
│   │   ├── prop_subtyping.v   structural subtyping and partial-precision facts
│   │   ├── prop_renaming.v / prop_stability.v
│   │   └── prop_conservativity.v   bridges to decl/ at flexible-free contexts
│   ├── algo/
│   │   ├── def_rules.v        algorithmic judgements and their notations
│   │   ├── basic/             shared algorithmic context infrastructure
│   │   │   ├── def_meta.v     metasubstitutions and information increase
│   │   │   ├── prop_context.v context, well-formedness and flexibility facts
│   │   │   ├── prop_inc.v / prop_inc_strengthen.v
│   │   │   ├── prop_metasubst.v / prop_metasubst_composition.v
│   │   │   ├── prop_context_normalization.v   unfolding context definitions
│   │   │   └── prop_*.v       swaps, mode compatibility, suffix erasure, wf
│   │   ├── consistency/
│   │   │   ├── prop_soundness_consis.v
│   │   │   ├── prop_consis_solution.v   measures and solution-side transport
│   │   │   ├── prop_completeness_unify.v / prop_completeness_assign.v
│   │   │   ├── prop_completeness_consis_step.v   consistency induction step
│   │   │   ├── prop_completeness_consis.v        final bundle and corollaries
│   │   │   └── prop_*.v       renaming, precision and monotype equivalence
│   │   ├── subtyping/         subtyping, constraint collection and solving
│   │   │   ├── prop_rigid_substitution.v / prop_solve_extension.v
│   │   │   ├── prop_completeness_solve_eq_var.v    P6-Cv
│   │   │   ├── prop_completeness_lookeq_solve.v    P6-Cs
│   │   │   ├── prop_completeness_solve_sub_var.v   P6-Sv
│   │   │   ├── prop_completeness_looksub_solve.v   P6-Ss
│   │   │   ├── prop_completeness_extract.v        P6-L
│   │   │   ├── prop_completeness_look.v           P6 import interface
│   │   │   └── prop_*.v       soundness, precision and subtyping completeness
│   │   └── typing/            both skeleton inference and term typing
│   │       ├── prop_soundness_pat.v / prop_completeness_pat.v
│   │       ├── prop_soundness_typing.v / prop_completeness_typing.v
│   │       └── prop_typing_{closed,rigidity,scope,shape}.v
│   ├── deco_algo/             decorated algorithmic rules and their bridges
│   └── ext_algo/              supply-threaded rules and executable algorithms
│       ├── notations.v        shared supply-threaded judgement scope
│       ├── basic/             supplies, guessing, decisions and termination
│       ├── consistency/       consistency rules, implementation and proofs
│       ├── subtyping/         collection, solving, extraction and subtyping
│       ├── typing/            skeleton inference and term typing
│       ├── lifting/           bridges from algo/ to supply-threaded judgements
│       │   ├── prop_lift_context.v   context, set and expression relations
│       │   ├── prop_lift_look.v      collection transport
│       │   ├── prop_lift_{solve,consis,sub,split,pat,typing}.v
│       │   └── prop_lift.v           import interface through skeleton inference
│       ├── prop_run_{invariants,complete,corollaries}.v   cross-judgement runners
│       └── extraction/        extraction driver; extracted/ is generated
├── cex/                       checked counterexamples and exploratory probes
└── test/                      examples and regression checks
```

Choose a file by the judgement or object its statement describes, not by
which proof first needed it. In particular, standalone properties of
`ad_*` judgements belong in `algo_decl/`; `algo/consistency/` and
`algo/subtyping/` own the algorithmic soundness/completeness arguments that
consume them. A lemma relating several layers belongs with that bridge.
Shared syntax and atom-set facts stay directly under `fresco/`.

The four `algo/` groups are deliberately only one level deep. `ext_algo/`
uses the same four topic groups, with `lifting/` and the existing
`extraction/` alongside them. Keep each executable judgement's definition,
implementation and correctness proofs in its topic group; the runner
modules at the root connect multiple judgements. Keep a small
file when it has a distinct role (for example, the P6 import interface),
and split long files at judgement or proof-phase boundaries. Do not split
mutual inductions just to meet a line-count target. Generated files are
left intact.


**Naming of the soundness / completeness files** (2026-08-06):
`prop_soundness_<judgment>.v` and `prop_completeness_<judgment>[_<role>].v` —
`prop_soundness_consis.v`, `prop_completeness_consis.v`,
`deco_algo/prop_soundness_sub.v` (the paper's `a_sub_sound`) and
`algo/subtyping/prop_soundness_subtag.v` (its decorated-run half), and for
subtyping completeness
`prop_completeness_sub_precise.v` (P5), `prop_completeness_look.v` (P6),
`prop_completeness_sub_gen.v` (P7a+b, the GENERALIZED statement) and
`prop_completeness_sub.v` (P7c, the paper's `a_sub_complete`).  The
shared kits (`prop_inc`, `prop_metasubst`, `algo/basic/prop_context`, `prop_swap`,
`algo_decl/prop_precision`, `algo_decl/prop_subtyping`, `prop_looksub`, `prop_solve_sub`, …) keep
their topic names.

**Naming of LEMMAS** (2026-08-09):

- **A flagship theorem takes NO suffix.**  It is `a_pat_sound`,
  `a_typing_complete`, `a_sub_sound`, `a_sub_complete` — even though each has
  a dozen row-siblings (`a_typing_complete_var`, `…_app`, …).  ⚙ Four names
  carried a `_thm` suffix that meant nothing (no bare name was ever taken);
  they were renamed, so `_thm` is now free of meaning and must not come back.
- ⚠️ **NEVER name a lemma after the paper's PROOF NUMBERING** (2026-08-12).
  `p6cv_concl`, `p6cs_subject_open`, `cv_mono_wrap`, `a_solve_eq_cv_mono` all
  encoded "this belongs to P6-Cv/P6-Cs" — which the READER cannot decode, which
  the containing FILE already says (`prop_completeness_solve_eq_var.v` *is* Cv), and which the
  judgement prefix already says (`a_solve_eq_` *is* the eq side).  Name for what
  the lemma states: `solve_eq_mono_concl`, `subst_msubst_uskl_syn_open`,
  `a_solve_eq_complete_rsubst_var`.  ⚙ The one place a paper-numbering key IS
  right is `cex/`: a counterexample's whole point is WHICH numbered statement it
  refutes, so `cex_p6cs_*` keeps its key.
- ⚠️ **A greek metavariable is not a lemma name.**  `ρ` is the paper's own
  symbol for the rigid-variable substitution
  (`subtyping-proofs.tex:181`) and stays as a METAVARIABLE — `ρ`, `Δρ`, `Ψρ`,
  and the `Hrho*` hypothesis names.  But lemma names and FILE names spell it
  **`rsubst`** (`uskl_rsubst`, `rsubst_fresh`, `prop_rigid_substitution.v`), which also
  keeps it apart from the metasubstitution `msubst_*` and the meta-level
  `subst_*`.  Renamed 2026-08-12; 39 declarations and one file.
- ⛔ **`_no_loss` means "encoding justification — never delete for being
  unreferenced".**  The eleven `*_no_loss` lemmas (`prop_swap.v` §13b) prove
  that the exists-fresh output premises reject nothing the premise-free rule
  accepts.  Their consumer is the READER, so zero references is what they are
  FOR.  Any lemma whose point is that the ENCODING is admissible takes this
  suffix, and an orphan sweep must skip the family.  ⚠️ More generally, a
  zero-reference lemma is not automatically waste — before deleting, check
  `docs/PAPER-GAPS.md` and `PROGRESS.md` Part 1 as well as the doc comment;
  the reference scan reads only `.v` files and so cannot see a numbered PAPER
  lemma with no consumer (`a_looksub_lookeq_subst_stable{,_rev}` is one) or a
  PAPER-GAPS exhibit.  Rules and worked cases:
  [`docs/REPORT-postclosure-audit.md`](docs/REPORT-postclosure-audit.md) §2.1b.
- **A fact about a conversion is `<relation>_<conversion>`** — the conversion's
  own name, unabbreviated: `ftvar_ptyp_to_pskl`, `btyp_to_ptyp_open`,
  `lc_bskl_to_pskl`.  ⚠️ NOT `ftvar_in_<target>_<conversion>` and NOT
  `ftvar_in_<conversion>`: the tree accumulated all three and ended up with
  **four names for one fact**.  All such lemmas live in `fresco/prop_coercions.v`.
- ⚠️ **A `_<qualifier>` sibling is usually a LAYER, not a size accident.**
  `prop_inc_strengthen.v`, `prop_ctx_precision.v`, `prop_precision_recovery.v` look
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
  ⚠️ The 2026-08-12 audit's "duplicate count 0" was WRONG: a by-statement
  sweep on 2026-10-10 found ~60 more (local copies of Metalib's `uniq_mid` /
  `binds_weaken`, `utags_uskl` = `ftag_in_uskl`, `a_sub_sound_v` =
  `a_sub_sound`, …) and removed most.  A name grep cannot find them —
  normalise the STATEMENT (binder names, argument order, `[=]` vs `=`) and
  compare.

## Encoding conventions

These are load-bearing decisions — read [`DESIGN.md`](DESIGN.md)
before changing any of them.

- **Pure syntax in `language.ott`, rules in `def_rules.v`.** The ott
  file declares only grammars, substitutions, freevars, and formulas.
  All `Inductive` rules go in the matching `def_rules.v` (`decl/` for
  declarative, `algo/` for algorithmic); the cross-system meta-functions and
  shape predicates go in `fresco/def_shapes.v`.  ⚙ All three were called
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
- **Tag context `Ψ`** (declarative) is an exact atom set (`atoms`),
  compared with `[=]`: leaves ask `Ψ [=] empty`, ∀-tag rules
  `Ψ [=] add ε Ψ0`, arrows `Ψ [=] Ψ1 ∪ Ψ2`. `d_tags` adds the paper's `⊎`
  as `Ψ1 ∩ Ψ2 [=] empty`; ForallL's `fresh Ψ'` is a GLOBAL disjointness
  side condition (`Ψ' ∩ Ψ [=] empty`, `Ψ' ∩ ftag(subject) [=] empty`).
- **Skeleton ∀-scope context `Δ`** (an atom set, `atoms`, in every layer —
  the paper's Δ is a set; the declarative list Δ, `delta_agree` and
  `tvars_denv` are gone since 2026-10-09, so the conservativity bridges in
  `algo_decl/prop_conservativity.v` are stated at one Δ), written after the term context: `Γ ⨟ Δ` /
  `Θ ⨟ Δ`. Used in skeleton well-formedness and refinement, which follow
  the paper rule for rule (2026-10-08): a ∀ binds its variable in BOTH the
  context and Δ, the variable rule reads only the context, a ∀◇ body is
  checked at `Γ∖Δ` (`denv_minus` / `aenv_minus`), and the refinement Ghost
  rule asks only `Δ ∩ ftv(fill) = ∅`. Well-formedness of both sides of a
  refinement is the paper's presupposition, carried as a hypothesis — see
  `docs/WF-SIDE-CONDITIONS.md` §1.  There is ONE refinement relation per
  sort: a fill-avoidance set is just part of Δ (the internal `_f` variants
  were removed 2026-10-09), and partial precision follows the paper rule for
  rule too (2026-10-09).  The skeleton consistency / subtyping Ghost rows
  do too, in BOTH layers (no fill-wf premise on `d_pat_consis__ghost`,
  `d_pat_sub__ghost`, `ad_pat_consis__ghost`, `ad_pat_sub{,_fuel}__ghost`,
  2026-10-10): the counterpart's well-formedness is the paper's
  presupposition, and `a_consis_complete` (with the P6-Cs/Ss/L corollaries)
  now TAKES it as a hypothesis (`docs/WF-SIDE-CONDITIONS.md` §2a).  Where the
  join's subject has no plain `◇` — every type painting, every decorated
  skeleton — the target's scope is read off the derivation instead
  (`ad_pat_consis_target_scope`).
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
  instance (that is what the old `*_rename_tm` bridges were for) — and
  exists-fresh is the reverse.  Layer by layer:
  - `decl/def_rules.v`, `algo_decl/*` / `deco_algo/*` — cofinite. ✅
  - `algo/def_rules.v` operational judgments (`a_looksub`, `a_solve_*`,
    `a_assign` / `a_unify` / `a_consis`, `a_sub`, `a_pat`, `a_typing`) —
    exists-fresh. ✅  **`a_pat`'s four binder rows were the last holdout and
    were converted 2026-08-13**, so the discipline now has NO exception among
    the operational judgements ([`docs/REPORT-remech-cleanup-audit.md`](docs/REPORT-remech-cleanup-audit.md) §3
    recommended it; `a_typing`'s six went 2026-08-08, `7061d31`).  It did
    re-open theorems 1 and 3, and the two moved in opposite directions:
    completeness got **shorter** (it no longer regenerates a family, so the
    four `a_pat_rename_tm` calls and the lemma itself are gone), soundness slightly
    longer (it opens the `a_wf_exp` families at the row's own binder, via
    `a_wf_exp_abs_pick` / `a_wf_exp_abs_anno_pick`).  All four flagships are
    Qed and axiom-free after the move.
  - `algo/def_rules.v` WELL-FORMEDNESS (`a_wf_ptyp`, `a_wf_pskl`) —
    cofinite, deliberately.  These are static judgments, not runs; do not
    "fix" them to match their file-mates.  (`a_scope_pskl` is NOT a
    judgement any more: since 2026-10-10 it is the Definition "locally closed
    and every free variable bound", for the few places — a consistency run's
    output inside its own completeness proof, a join target whose subject
    has no plain `◇` — where only scoping is available.  The paper has one
    skeleton wf, `a_wf_pskl`.)

## Build and workflow

- **Full kernel check**: `make coq` from the repository root. Parallelism
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
  the paper's `sections/*.tex` or `frost.aux`.
- Regenerate ott/lngen: `make ott && make lngen` (runs automatically
  as part of `make coq`).
- Clean: `make clean`. Removes `*/def_ott.v`, `*/prop_ln.v`,
  `CoqMakefile`, `.FILE_LIST`.
- `_CoqProject` lists module roots; `CoqMakefile` is regenerated
  from a `find` over the `.v` files whenever that set changes, so just
  adding `.v` files in the right place is enough.

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
  - ⭐ **THE JUDGMENT LEGEND IS IN [`fresco/notations.v`](fresco/notations.v)** —
    read it before adding or changing any judgment notation. **The SYSTEM is
    the DELIMITER**, and each delimiter is its own notation scope:
    `{{ … }}d` declarative (`fresco_d_scope`), `{{ … }}ad` declarative-over-Θ,
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
    together — see the note in `fresco/notations.v`.
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
- **Atom sets never name a module.** `fresco/notations.v` completes what
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
    beside `uskl_rsubst NM Θ Δρ Ψρ ψsub ψa`, where `Δρ`/`Ψρ` are the
    ρ-replaced variables and the tags ρ introduces. So: `κ` is the
    information-increase metasubstitution (`msubst_*`, `a_inc`), `σ` the
    second one (`a_inc_equiv`), `ζ` the composing one (`ζ ∘ κ`); a second
    `κ` in one statement takes ONE prime (`κ'`), never `κ1`/`κ2` as fresh
    bases. Anything spelled `ρ` denotes the paper's ρ (`uskl_rsubst`,
    `rsubst_fresh`, `msubst_uskl` in prop_decorate_sub.v).
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
    comment stand-ins are: `◇` = `ghost`, `◈` = `dot_ghost`, `∀◇` = `univ_ghost`,
    `∀◈` = `dot_univ_ghost` (`□` for `ghost` also survives and is fine). ⚠️ The
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
- Keep `fresco/language.ott` minimal. Resist the
  temptation to put rules into ott just because ott has `defns`
  syntax; we want the rules in Coq where they can be edited /
  debugged interactively.
- After editing `language.ott`, run `make` so `def_ott.v` and
  `prop_ln.v` regenerate. `_CoqProject` and `Makefile.coq` pick up
  new `.v` files automatically via the `find`-based file list.
- Run `git status --short --branch` before and after significant
  edits.
- Do not edit `def_ott.v` or `prop_ln.v` by hand. If a generated
  file is missing a lemma, add the corresponding declaration in
  `language.ott` (or hand-write the lemma in the appropriate shared property module).
- When closing an admit, **always check `Print Assumptions` on the
  flagship theorems** (`d_sd_typing_general_subsumption` /
  `d_sd_typing_general_subsumption_spine` — general subsumption lives on the
  SYNTAX-DIRECTED system since the "Removed base terms" rework; the
  `d_typing`-side versions are corollaries) to ensure you didn't accidentally
  introduce a new transitive axiom. The `make coq` tail prints them all.

## Where things live (cheat sheet)

| Need to … | Edit … |
|---|---|
| Add a new syntactic constructor / sort | `fresco/language.ott` |
| Add a meta-function shared by decl + algo | `fresco/def_shapes.v` |
| Add a predicate / well-formedness used by both | `fresco/def_shapes.v` |
| Add a declarative typing/subtyping rule | `fresco/decl/def_rules.v` |
| Prove a declarative metatheorem | `fresco/decl/prop_*.v` (flat; pick the matching file by topic) |
| Add an algorithmic rule | `fresco/algo/def_rules.v` |
| Add a global notation | `fresco/notations.v` (scopes + the judgement legend); a JUDGEMENT's own notation goes on its `Inductive`, via a `where` clause in the matching `def_rules.v` |
| Prove an atom-set fact | `fresco/prop_atom_sets.v` |
| Prove a syntax-only shape fact | `fresco/prop_shapes.v` |
| Prove a standalone `ad_*` property | the matching `fresco/algo_decl/prop_*.v` module |
| Add a tactic | `fresco/ltac_utils.v` |
| Update the paper → Coq map | `PROGRESS.md` Part 1 (then `make sync-paper-refs-md` if labels moved) |
| Log a closure / refactor / discovery | `PROGRESS.md` Part 2 (dated entry) |
| Explain an encoding choice or methodology | `DESIGN.md` Part 2 |

## References

- Paper: [`../impredicative/paper/frost.tex`](../impredicative/paper/frost.tex)
  (rendered as [`frost.pdf`](../impredicative/paper/frost.pdf) beside it).
- Reference repo for file-organization patterns:
  <https://github.com/jiangsy/proof_worklist_remechnization>
  (different calculus — copy the structure, not the rules).
- ⚙ The two original design specs (`docs/superpowers/specs/2026-05-09-fresco-
  mechanization-design.md`, `…-05-10-fresco-phase23-design.md`) no longer exist
  in the tree; what survived of them is [`DESIGN.md`](DESIGN.md) Part 2.
