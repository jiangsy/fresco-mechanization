# Simplification audit — 2026-10-07

Scope: `mechanization/` at `ab89640`, 165 `.v` files (183k hand-written lines plus
12.8k generated in `fresco/prop_ln.v` and `fresco/def_ott.v`).  The tree is green:
`make coq` passes with no `Admitted` and no axioms, and every `README.v`
assumption report reads "Closed under the global context".  This report lists
what can be removed or consolidated without changing any statement the paper
relies on.  The canonical mechanization is now the private repository
`jiangsy/proof_fresco`: branch `main` is this tree with §1 applied and
`fresco/` renamed `fresco/`, branch `public` is the comment-trimmed copy
published at jiang.sy/research/popl2027b.  This tree only takes the
Makefile change of §3; see the last section.

## 1. Dead top-level names — 208, of which 81 are deletion candidates (2.4k lines)

A glob-based scan (whole-word references across all `.v` files, hint
registrations included) finds 208 top-level declarations referenced nowhere,
`README.v` included.  They split into:

| group | names | lines | verdict |
|---|---|---|---|
| counterexample / test files (`cex/`, `test/`) | 62 | — | self-contained by design; keep |
| exported API corollaries: `*_run_sound`, `*_run_complete*`, `*_impl_complete`, `*_dec`, `*_sound_init`, `frost_infer_complete`, the eleven `*_no_loss` encoding justifications | 39 | 808 | keep (documented interface) |
| `Ltac` helpers (`dom_cov`, `push_var`, `solve_notin_fast`, `solve_notin_flat`) | 4 | — | delete |
| everything else | **81** | **2 433** | **delete or move to `cex/`** |

The 81 are concentrated in a few files; the ten largest alone are 1.2k lines:

```
 281  a_looksub_lookeq_subst_stable_rev     algo/sub/prop_looksub.v
 208  a_looksub_lookeq_subst_stable         algo/sub/prop_looksub.v
 125  a_typing_swap                         algo/prop_swap.v
 106  a_solve_cstr_rel                      ext_algo/prop_solve_rel.v
  96  e_solve_sub_block_in_supply           ext_algo/prop_solve.v
  88  e_solve_sub_block_ftvar               ext_algo/prop_solve.v
  80  e_solve_sub_uniq                      ext_algo/prop_solve.v
  69  swap_aenv_one                         algo/prop_swap.v
  55  rel_pskl_size                         ext_algo/prop_solve_det.v
  52  e_lookeq_uniq                         ext_algo/prop_look.v
```

Three of them are `Check`ed nowhere yet are the kind of fact `README.v` exists
to show (`freeze_no_infer`, `d_consis_join_consis`, `d_consis_join_refine`):
either index them or drop them.  Deleting an orphan can orphan what only it
used, so the sweep should be iterated to a fixpoint (the 2026-08 sweep needed
two passes).  The sweep applied in `proof_fresco` keeps everything README.v
cites, the `*_no_loss` justifications, and the per-judgement
`*_sound` / `*_complete` / `*_run_*` / `*_dec` corollaries; run to a
fixpoint it deleted 104 lemmas / 3.1k lines in four passes (59, 26, 13, 6),
and the tree still builds with every assumption report closed.

## 2. Duplicated Ltac across `ext_algo/` — 26 duplicate names

`ext_algo/` defines the same tactic under the same name in several files:
`env_simp` ×4, `split4` ×4, `select_shape_premises` ×4, `saturate_lc` ×4,
`open_exp_lc` ×3, `saturate_defs` ×2, `kill_sub`, `kill_dec`, `rel4`,
`rel_perm`, `kill_unguarded`, `head_fresh`, `split_eqdec` ×2 each, and
`destr_join` ×2 in `algo/`.  Each copy is identical or near-identical.  One
`ext_algo/ltac_utils.v` (mirroring `fresco/ltac_utils.v`) would hold them once;
the `def_*_impl.v` quartet (`select_shape_premises` / `saturate_lc` /
`saturate_defs`) is the clearest case.  No proof changes.

## 3. Build hygiene

- Six orphaned build artefacts in `cex/` (`.vo/.vok/.vos/.glob` with no `.v`):
  `cex_looksub_not_det`, `probe_bcore_ug2_flexr`, `probe_extract_flexr_ug2_drift`,
  `probe_extract_supply_drift`, `probe_sub_supply_drift`,
  `probe_vacuous_supply_drift`.  `make tidy` removes them.
- The `Makefile` depends on `tree` and a `.FILE_LIST` touch-file to detect new
  sources; `find … | xargs coq_makefile` does the same with no extra tool.
  Applied here.
- `fresco/ext_algo/extraction/extracted/README.v` is untracked but sits inside
  the source tree, so `coq_makefile` compiles it; it should live outside the
  `.v` glob or be tracked.
- Full build: 895 s of proof-checking CPU (sum of `.aux` timings); about 15
  minutes wall at `-j6`.  The three slowest files are
  `ext_algo/prop_lift.v`, `algo/consis/prop_completeness_consis.v` and
  `algo/sub/prop_completeness_sub_gen.v`.

## 4. `cex/` — 17 refutations and 17 probes

The `cex_*` files each refute a statement that does not hold as written and
are cited from `docs/PAPER-GAPS.md`; they belong in a release.  The 17
`probe_*` files record exploratory checks during the proof development
(orientation of alias collapse, supply drift, …).  Nine are cited from the
design documents and none from `.v` files or `README.v`.  They can be moved
out of the Coq build (into `docs/repros/` or deleted) without loss to the
mechanization.

## 5. Comments and documentation

Comments are 20–60 % of most hand-written files and a large share is process
narration rather than documentation: 2 396 editorial emoji, 405 dates, and a
heuristic count of 2 255 comment blocks (11.7k lines) that mention campaign
levels, hand-off section numbers (`§8c.24`), `docs/*.md`, "do not …"
maintainer instructions, user decisions, or superseded designs.  The heaviest
files are `algo/def_rules.v` (689 such lines), `algo/sub/look/prop_sub_cstr.v`
(614), `algo/sub/look/prop_eq_cstr.v` (569), `README.v` (245 of 649).

`docs/` holds 42 files / 45k lines, `PROGRESS.md` is 8 951 lines, and
`CLAUDE.md` 807.  The HANDOFF-* and REPORT-* files are dated records; the
live content a reader needs is `PAPER-GAPS.md`, `WF-SIDE-CONDITIONS.md`,
`DESIGN.md` Part 2, and `refutations.tex`.

## 6. Structural (not applied; see `REPORT-proof-path-audit.md`)

The development climbs the same twelve-judgement ladder three times (paper
algorithm `algo/`, executable runners `ext_algo/`, and the 12.9k-line lift
between them), and the lift's cost is the relational atom pairing `ρ`
(12.3k lines of dedicated machinery).  Collapsing it to a functional renaming
is blocked by one live obstruction (two sibling ∀ openers may pick the same
atom on the `a_` side); the audit report proposes a third cross-half guard
that would make the cheap currency available.  This is the only
simplification with a large payoff, and it is a proof-engineering project,
not a cleanup.

## Where the clean-ups landed

- `jiangsy/proof_fresco`, branch `main` (canonical): the dead-lemma sweep
  of §1 to a fixpoint, the `find`-based Makefile, and the rename of
  `fresco/` and every `frost` identifier to `fresco` (the paper's name).
- Branch `public`: the same code, comments rewritten as documentation
  (§5), without `cex/`, `test/` or `docs/`, with its own README, MIT
  licence and Makefile; it is what jiang.sy/research/popl2027b renders.
- This tree: the Makefile change only.  §2 (shared Ltac) and §6 (the lift's
  relational currency) remain open in both.
