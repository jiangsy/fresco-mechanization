# REPORT — displayed-interface & proof-path audit (2026-08-22)

Scope: the campaign's DISPLAYED SURFACE (README §VI, the extraction
exports, the headline statement shapes) and the PROOF PATH behind it
(`ext_algo/prop_lift.v` §13, `ext_algo/prop_run_corollaries.v`, the
conservativity bridge).  Method: consumer-count greps over `fresco/` +
`README.v`, per-copy duplicate scan, row-size measurement (`awk` over
§13's case markers), `.aux` proof timings.  Every claim below was
CHECKED, not recalled; the commands are one grep away.

Verdicts: **DO** (clear win, low risk) / **OPT** (real win, real cost —
user's call) / **KEEP** (audited and deliberately left alone).

## Part 1 — the displayed interface

### I1. **DO** — the §VI decidability cluster is 4 entries telling 2 stories

| entry | reach | subsumed by |
|---|---|---|
| `e_typing_dec_init` | threaded relation, ALL modes and `P0` | nothing — keep |
| `e_typing_run_complete_decl_infer` | paper judgement, TI at ◇ | `fresco_infer`'s left component + `fresco_infer_complete` |
| `d_typing_infer_dec` | paper judgement, TI at ◇ | the `sumbool` projection of `fresco_infer` |
| `fresco_infer` | paper judgement + extracted artifact | — |

Shrink the README to TWO entries: `e_typing_dec_init` (the general,
threaded claim) and `fresco_infer` (the paper-facing, extracted claim).
The two demoted corollaries STAY in the tree — `…decl_infer` is
`fresco_infer`'s workhorse; `d_typing_infer_dec` should then be
re-derived FROM `fresco_infer` (see P5).  Saves 2 entries ≈ 35 lines of
the file a reader is asked to read in one sitting.  Cost: README-only.

### I2. **DO** — name the entry supply

`ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e` is spelled out
15× in prop_run_corollaries.v and 4× in README.v.  One definition —
`entry_supply P0 e` beside `e_typing_sound_init` (prop_typing.v §2,
which is what CHOOSES this supply) — shrinks every §VI statement to a
readable line.  Extraction: emit it (a one-line OCaml def) or
`Extraction Inline` it; either is clean.  Cost: prop_typing →
run_corollaries → README chain.  This is the biggest per-line win on
the displayed surface.

### I3. **OPT** — hypothesis uniformity across §1–§6

§1/§2 (`e_typing_run_sound_infer/_check`) still hypothesize
`{{ nil ⊢ᵉ e }}a` (+ `a_wf_ptyp`); §5/§6 take the declarative
`{{ nil ⊢ᵉ e }}d` (+ `d_wf_ptyp`).  Switching §1/§2 to the d-side is a
3-line prelude each (the nil bridges) and makes the file's interface
uniform.  Cost: statement churn on two landed corollaries; no ripple
(`fresco_infer` derives its own a-side wf).  Not displayed in README
(prose-cited only), hence OPT not DO.

### I4. **KEEP** (with one note) — the undisplayed and the unconsumed

- `e_typing_run_complete_decl_check`: 0 consumers, prose-cited in
  README.  It is the check-mode RECORD of §5; fine as tree-level.
- `fresco_infer_complete`: prose-cited; the left-completeness guarantee
  is reader-facing (McTT keeps its analogue undisplayed too).
- ⚠️ `a_wf_exp_to_d` (prop_conserv.v): ZERO consumers anywhere.  It is
  the conservativity CONVERSE, there because §2 of that file proves
  both directions for every sort — an encoding-justification lemma in
  the `*_no_loss` sense (its consumer is the reader).  Add the
  standing one-line "do not orphan-sweep" note; do not delete.

### I5. **KEEP** — `fresco_infer`'s run-equation field

Costs ~4 display lines; buys provenance (the answer IS the runner's)
and composability (any theorem about `e_typing_run` applies to the
left payload via the recorded equation).  Litigated 2026-08-22.
OPT variant if display-minimal is ever wanted: a named predicate
`decl_types_run e r := exists ζ, …` halves the sig text at the price
of one indirection.

### I6. **OPT** — §VI prose

The discharged-scope history block (~14 lines) can compress to ~4 +
a pointer at hand-off §8c.24/§8c.47.  Taste; history-in-README was
deliberate.

### I7. **KEEP** — the Extract.v export list

Verified: dependencies are auto-emitted (`e_typing_impl`,
`e_sub_impl` appear in the `.mli` without being roots), so the
12-runner list adds nothing to REACHABILITY — but it documents the
per-judgement surface the differential test against `type.ml` needs.
Keep; a one-line "roots, not closure" comment would prevent a future
false shrink.

## Part 2 — proof path and intermediate definitions

### P1. **DO** — the `ptyp_to_pskl_close{,_rec}` duplicate (pre-existing)

One fact, TWO files: `ext_algo/prop_solve_det.v` AND
`algo/typing/prop_completeness_typing.v` — the tree's own comment at
prop_solve_det.v:1006 already says it belongs in
`fresco/prop_coercions.v` (the designated home, beside
`ptyp_to_pskl_open`).  Consumers today: prop_lift ×3, prop_solve_rel
×1, plus in-file uses.  Action: move to prop_coercions.v, delete both
copies; names are identical so no consumer edits.  Cost: ⚠️
prop_coercions is upstream of ~everything → one FULL rebuild.  Risk:
low (identical statements; removes an import-order hazard rather than
adding one).  This also un-stales the 2026-08-12 "duplicate count 0"
audit claim.

### P2. **OPT** — §13's four `_check` rows are pairwise ~95% clones

Measured: checkstep 539 + checkbase 472 + annostep 539 + annobase 620
= **2170 lines**, the step pair differing only in the subject
constructor and e-rule name, the base pair additionally by the consis
stage.  Two factorings, in the order to do them:

  a. Shared BLOCK helpers first (small blast radius, pays at every
     rung): the restrict-prelude (`remember (restrict_l (dom Ξ) ρ)` +
     its 8 asserts) appears **10×** across prop_lift — one
     `restrict_l_setup` bundle ≈ −250 lines; the `HΞ2`-apartness and
     `Hdel` deleted-pair blocks similarly.
  b. One `lift_typing_check_step_core` serving both step rows
     (S-ForallR parameterized by the subject) ≈ −450 lines; the base
     pair keeps its consis fork.

Everything here is Qed and the campaign is CLOSED — the benefit is
maintenance, the cost is a prop_lift rebuild and regression risk in
working proofs.  Matches TODO.md's "clean over-designed proof path".

### P3. **OPT-small** — `lift_typing_abs_core` returns a derivable conjunct

Its post now carries the joined `rel_aenv … (Ξ ++ Θc) (Ξ2 ++ Θc2')`
AND the two split halves; joined = `rel_aenv_app` of the halves.
Drop the joined conjunct, patch its 2 consumers (the abs rows).
Bundle with any §13 touch.

### P4. **OPT** — prop_lift.v is 12,813 lines / 161 s serial

Hotspots: `e_guess_mono_lift_n` 10.3 s, `a_typing_rel_e` 7.0 s,
`a_sub_sub_flex_rel_e` 6.8 s — no pathological proof, just bulk.  A
§-aligned file split (currency / sub / split+pat / typing) would make
editing §13 stop re-checking §1–12.  Check the Require-reachability
rule before splitting (the ⚠️ DO-NOT-MERGE doctrine, run in reverse).
Matches TODO.md's "build time optimization"; measure first — 161 s is
mid-pack, not the tree's tail.

### P5. **DO** (bundle with I1) — derive `d_typing_infer_dec` from `fresco_infer`

Its current proof re-runs `fresco_infer`'s case analysis (destruct the
runner, re-derive both branches).  Three lines via `fresco_infer` make
the dependency DAG linear: `…decl_infer` → `fresco_infer` →
`d_typing_infer_dec`.

### P6. **KEEP** — audited and load-bearing, do not "clean"

- The lift motive's 17 hypotheses: each was FORCED by a named rung
  (hand-off §8c.28–§8c.46); the 10-rung validation is the asset.
- Side 2's wf-freedom; the exists-fresh discipline; route (A)'s
  premise-free flex-reflects.
- `a_typing_fvar_binds` (sharp; its `a_pat` twin is FALSE).
- `e_typable` (consumed by both dec corollaries).

### P7. Documentation debt (no code)

`d_wf_exp`, `fresco_infer`, and the decidability composition have no
PROGRESS.md Part 1 rows yet; `a_wf_exp_to_d` needs its keep-note (I4).

## STATUS (updated 2026-08-22, after execution)

| item | verdict | outcome |
|---|---|---|
| I1 README 4 → 2 entries | **DONE** | `ab916f3`; 36 → 34 entries, −22 lines |
| I2 name the entry supply | **DONE** | `ab916f3`; 19 sites → `entry_supply`, and the extracted OCaml reads better for it |
| P5 derive `d_typing_infer_dec` | **DONE** | `ab916f3`; §6/§7 swapped, 3 lines off `fresco_infer` |
| P1 `ptyp_to_pskl_close` duplicate | **DONE** | `ab916f3`; moved to `prop_coercions.v`, both copies gone |
| P4 split `prop_lift.v` | **DONE** | §13 → `prop_lift_typing.v`; see B4 |
| I3 §1/§2 hypothesis uniformity | OPEN (OPT) | not done — statement churn on two landed corollaries |
| I6 §VI prose compression | DONE-ish | folded into I1 |
| P2a restrict-prelude factoring | **DROPPED** | measured at −69 lines (0.5%); see B5 |
| P2b row-core merge | OPEN (OPT) | ~450 lines; the only part of P2 whose size justifies the risk |
| P3 drop the derivable conjunct | OPEN (OPT-small) | bundle with any future §13 touch |
| P7 documentation debt | OPEN | PROGRESS.md Part 1 rows for `d_wf_exp` / `fresco_infer` |

## Suggested batches

- **Batch A** (interface, one commit, cheap): I2 + I1 + P5 (+I6).
  Rebuild: prop_typing → run_corollaries → README.
- **Batch B** (dedup, one commit, one full rebuild): P1.
- **Batch C** (refactor campaign, optional): P2a → P3 → P2b; P4
  separately, measured.

---

# Part 3 — BUILD TIME (added 2026-08-22, measured)

Prompted by "why 35 min?".  Answer: **it is not** — that figure was
folklore carried in the hand-off instructions, not a measurement.  What
follows is measured, from the `.aux` per-proof timings plus the
`.CoqMakefile.d` dependency graph.

### B1. The numbers

| quantity | value |
|---|---|
| total recorded proof time, whole tree | **944 s** |
| total work incl. ~2 s/file elaboration | ~1310 s |
| perfect `-j10` floor (if the graph were flat) | ~131 s |
| **critical-path floor** (the real bound) | **~420–475 s** |
| measured wall clock, `make NJOBS=10 coq`, full rebuild | **~8–9 min** |

⭐ **The build is CRITICAL-PATH-bound, not CPU-bound.**  Ten cores are
already more than the graph can use: the chain to `README.v` is 37 files
deep and carries ~450 s of work by itself.  More parallelism buys
nothing; only shortening or lightening the CHAIN does.

### B2. The chain, and its weights

The heavy links (proof-time, in path order): `prop_ln.v` 62 s
(lngen-GENERATED — not ours to optimise) → `prop_soundness_consis.v`
35 s → `prop_completeness_consis.v` 30 s → `prop_eq_var.v` 31 s →
`prop_eq_cstr.v` 21 s → `prop_look_pair.v` 34 s → `prop_lift.v` 52 s →
`README.v` (~39 s WALL, almost all of it 34 × `Print Assumptions`
walking each constant's closure — and it is the LAST file, so it is
pure serial tail).

### B3. ⛔ REFUTED: cutting a single dependency edge

`algo/pat/prop_soundness_pat.v` requires
`algo/sub/prop_completeness_sub_gen.v` (78 s, the tree's heaviest
proof file) and uses NOTHING from it by name — a soundness file
depending on a completeness file, which looks like the classic spurious
edge.  **Simulated removal: 0 s saved.**  The graph is WIDE: a parallel
chain of the same length runs through `prop_look_pair.v` /
`prop_sub_complete.v` / `prop_pat_complete.v`.  ⚙ The edge is still
worth removing on hygiene grounds, but do not sell it as a speed-up.
(This is why the simulation is worth running BEFORE the edit — the
"obvious" cut was worth exactly nothing.)

### B4. What would actually help, in value order

1. ✅ **DONE — split `prop_lift.v` (12,814 lines) at §13.**  Measured
   after the split: `prop_lift.v` (§1–§12, 9,113 lines) **45.4 s**,
   `prop_lift_typing.v` (§13, 3,787 lines) **9.9 s**.  So editing the
   typing rung went from recompiling the monolith (≈55 s, the two
   summed) to **9.9 s — an 82% cut** on the iteration a developer
   actually pays for.  It does NOT shorten the full gate (the parts
   stay in sequence).  The boundary was verified clean BEFORE the move:
   §13 exports exactly one name to the outside (`a_typing_rel_e`), and
   exactly one file requires `prop_lift` at all
   (`prop_run_corollaries.v`) — so there is no cycle and no consumer
   churn beyond one added `Require`.
2. **Profile the four heaviest single proofs** —
   `a_sub_flex_complete_skip` 19.9 s, `consis_complete_core` 17.3 s,
   `a_assign_unify_consis_sound` 15.9 s, `a_lookeq_solve_complete_gen`
   13.9 s.  All are mutual-bundle cases on the chain.  The 2026-08-06
   precedent (970 s → 608 s, from two `fsetdec` calls) says one
   `Set Ltac Profiling` run per file can pay for itself — but these are
   big honest inductions, not obvious hotspots, so budget it as
   exploration, not as a known win.
3. **Nothing to do about `prop_ln.v` (62 s) or `README.v` (39 s)**: the
   first is generated by lngen, the second is the assumption audit that
   is the point of the file.

### B5. ⚠️ CORRECTION to Part 2's P2a estimate

Part 2 costed the restrict-prelude factoring at "≈ −250 lines".
**Measured: −69 lines (0.5% of the file).**  The 10 preludes occupy 99
lines of PURE `restrict_l` facts (the five that a bundle lemma can
serve); the rest of each prelude is object-dependent (`HrΘ0`, `Hagr0`,
`Hinj0`, `Hfun0`, `Hcov0`) and needs a second, differently-shaped
lemma to reach ~100 lines total.  **Recommendation: SKIP P2a** — 0.5%
of a file, against touching ten closed proofs.  P2b (the row-core
merge, ~450 lines) is the only part of P2 whose size justifies the
risk, and even it is optional now that the campaign is closed.

### B6. ⛔ THE PER-PROOF WELL IS DRY — profiled, not guessed (2026-08-22)

After the split, the sensitivity analysis says exactly where cutting a
file's proof time would move the path (**if this file were free, the
path drops by**):

| file | proof time | path gain if free |
|---|---|---|
| `fresco/prop_ln.v` | 59.6 s | **59.6 s** — but lngen-GENERATED |
| `ext_algo/prop_lift.v` | 42.4 s | 31.2 s |
| `consis/prop_soundness_consis.v` | 33.1 s | **33.1 s** |
| `sub/look/prop_eq_var.v` | 28.5 s | **28.5 s** |
| `consis/prop_completeness_consis.v` | 27.7 s | **27.7 s** |
| `sub/prop_completeness_sub_gen.v` | 75.6 s | only 23.3 s (a parallel chain caps it) |

Two of the full-gain files were then `Set Ltac Profiling`-ed.  **Both
say the same thing: `fsetdec` is 97–98% of the proof, spread over 124
(consis) / 259 (eq_var) calls that are ALREADY tightly `clear -`-scoped,
with exactly ONE ~5 s outlier each.**  62% of fsetdec's own time is
Coq's `Tauto.simplif` preprocessing, not the set reasoning.

⚠️ **And the outlier is not a scoping mistake.**  `prop_eq_var.v`'s
(`Hsubeq1b`, measured at **4.75 s** with `time` — the Ltac profiler
inflates it to 13.8 s, ~3×, so profile numbers are for RANKING only,
never for costing) survived three attempts:

- scoped 6 → 3 hypotheses: **fails** (the bridge is not where the goal's
  shape suggests — `Htags0`'s tag set is not `Ψa`);
- scoped 6 → 5: compiles, and the proof got **SLOWER, 25.1 s → 31.4 s**.
  ⭐ `fsetdec` is NOT monotone in its hypothesis set: a hypothesis can
  prune the search as easily as widen it.  Never "optimise" a
  `clear -` list without measuring;
- split at the bridge (the §8c documented cure): the first half is
  **not derivable**, so the split is unsound as drawn.

⚙ Also ruled out by measurement: `Require Import` costs **0.3 s** in a
40 s file, so import trimming is not a build-time lever here.

**What is left, sized honestly.**  87 `fsetdec` calls on the critical
path are scoped to ≥6 hypotheses (of 10,537 tree-wide, 181 of them
wide) — but per the middle bullet above, "wide" does not imply "slow",
so this is a list to MEASURE, not a list to fix.  The one lever with
real headroom is structural rather than local: since 62% of the cost is
`Tauto`'s preprocessing, a lighter decision tactic for the common goal
shapes would cut the DISTRIBUTED cost, which is where the time actually
is.  The tree already did exactly this once, for `x ∉ S`
(`solve_notin_auto`, the 2026-08-09 ∉-KIT); extending that treatment to
`[<=]` / `[=]` goals is a project-sized piece of work, and it is the
only remaining thing that would move the full gate meaningfully.

**Recommendation: stop here.**  The full gate is ~8–9 min, the
incremental cost of the file under active development was cut 82%, and
the remaining per-proof work is genuinely distributed.

### B7. ⛔⛔ CORRECTION — §B1's absolute numbers are UNSOUND (same day)

⚠️⚠️ **`.aux` `proof_build_time` is WALL-CLOCK, so it inflates under
`-j` contention.**  Measured: `ext_algo/prop_lift.v` records **42–64 s
compiled alone** and **916 s** for the same file inside
`make NJOBS=10` next to the other heavy-tail files; tree-wide the same
`.aux` scan read 944 s before such a run and **3902 s** after one.

What that costs the analysis above:

- ⛔ **§B1's "944 s total / ~450 s critical path / ~8–9 min full gate"
  is WITHDRAWN.**  It was computed from a MIX of `.aux` entries — some
  written by uncontended single-file compiles I had just run, some by
  earlier parallel builds — which is exactly the comparison this
  finding forbids.  Two honest wall observations on the same machine:
  ~9 min for a 120-file rebuild, ~38 min for a 49-file one whose files
  were all the heavy tail.  **No reliable full-gate figure is
  established; time your own run.**
- ✅ **What SURVIVES**, because each was measured within one run or
  between two comparable single-file compiles: the split's benefit
  (monolith 45–64 s vs §13 alone 9.9 s), fsetdec's non-monotonicity
  (25.1 s vs 31.4 s, both single-file), the profiler's ~3× inflation
  (13.8 s profiled vs 4.75 s under `time`, same run), `Require` costing
  0.3 s of a 40 s file (same run), and every LINE count.
- ✅ The **structural** claim also survives, since it does not depend on
  absolute times: the chain to `README.v` is ~38 files deep and holds
  most of the heavy files, so the gate cannot be parallelised away —
  and the ⛔ zero-gain edge-cut simulation stands (it compares two
  paths under one weighting).

⚙ **The lesson is the deliverable here.**  A perf model assembled from
`.aux` files is only valid if every entry came from a run with the same
parallelism.  Re-measure a file ALONE before believing its number.

### B8. ⭐⭐⭐ THE REAL HOTSPOTS, FOUND WITH `coqc -time`, AND FIXED

§B6's "the well is dry" was WRONG, and it was wrong for a methodological
reason worth stating: it ranked with `.aux` (per-PROOF, contaminated by
`-j`) and profiled with `Set Ltac Profiling` (3× inflation).  ⭐ The right
instrument is **`coqc -time`**: it prints one line per VERNAC COMMAND —
which inside a proof means **per tactic** — with no profiler overhead, in
a run whose conditions you control.  Re-measuring every candidate file
ALONE with `-time` produced a completely different picture.

**TRUE RANKING (uncontended, `coqc -time`, sum of commands):**

| file | before | after | cut |
|---|---|---|---|
| `algo/prop_wf_preservation.v` | **117.8 s** | **13.9 s** | **−88%** |
| `algo/sub/prop_completeness_sub_gen.v` | **108.6 s** | **40.8 s** | **−62%** |
| `ext_algo/prop_lift.v` | 64 s | — | (next) |
| `fresco/prop_ln.v` | 60 s | — | lngen-GENERATED |
| `algo/consis/prop_soundness_consis.v` | 47.1 s | 44.7 s | −5% |
| `algo/consis/prop_completeness_consis.v` | 35.8 s | 33.1 s | −8% |
| `algo/typing/prop_completeness_typing.v` | 23.0 s | — | |

**Measured total across the four: 309.3 s → 132.5 s (−177 s, −57%).**
⚙ The two consis files gained only ~5%: the ∉-KIT substitution helps in
proportion to how big that proof's `Fr` union is, and theirs are far
smaller than `sub_gen`'s ten-set one.  ⚠️ Their residual 4.5–5.5 s calls
were NOT located: `coqc -time`'s `Chars` offsets did not align with
either byte- or character-indexing of the source in that file, so the
attribution was abandoned rather than guessed at.  To pursue them, tag
the calls (`time "F<n>" fsetdec`) and read the names back — do not trust
the offsets.

Both fixes are **−172 s of proof time**, on the two heaviest files, and
both were four-to-ten instances of ONE shape.

#### FIX 1 — `prop_wf_preservation.v`: four `fsetdec`s of 24–30 s each

`a_consis_output_wf`'s ∀ rows each prove
`(add α Δ1 ∪ add α Δ2) ∩ pskl_shielded_ftv (open P α) [=] empty` from five
hypotheses in ONE `fsetdec` — ~7 set variables, i.e. far past the
documented cliff.  Replaced by the ELEMENTWISE argument (take `z` in the
intersection, derive `z ≠ α` from `Hdo`+`HαΘ0`, push through `Hup`, and
contradict `Hsh`), so every `fsetdec` sees at most three sets.  Four
sites, one shape.

#### FIX 2 — `prop_completeness_sub_gen.v`: a TEN-SET `Fr`

⭐ **The cost driver is the size of the avoid-set union**, not the
`clear -` list.  This file's `destruct (atom_fresh (…)) as [β1 Fr]` builds

    Fr : β1 ∉ dom Θ1 ∪ ftvar_in_aenv Θ1 ∪ ftvar_in_pskl P1 ∪ dom Ξ
              ∪ dom Θ0 ∪ ftvar_in_aenv Θ0 ∪ ftvar_in_aenv Ξ
              ∪ ftvar_in_pskl P0 ∪ {α} ∪ {β}

— ten sets — and every `clear - … Fr …; fsetdec` made `fsetdec` decompose
all ten.  The cure was already in the tree: **`solve_notin_auto`** (the
2026-08-09 ∉-KIT) leads with `destruct_notin`, which SPLITS that union
before the set reasoning starts.  57 sites changed `fsetdec` →
`solve_notin_auto`; it is a safe superset (its last branch *is*
`fsetdec`).

⚠️ **One shortcut failed and is worth recording**: at the single 11.59 s
site the goal is `α ∉ dom Ξj ∪ dom Θ1` and the context already holds
`HαΞj : α ∉ dom Ξj` and `HαΘ1 : α ∉ dom Θ1` — so dropping `Fr` looked
obviously right.  `fsetdec` then FAILED.  Eyeballing what an `fsetdec`
needs is unreliable (cf. §B6's non-monotonicity finding); route it
through the kit instead of narrowing it.

#### THE RULE THIS GIVES

1. Rank files with `coqc -time`, one file at a time, never `.aux` across
   a `-j` run.
2. In the hot file, the top few COMMANDS are usually one repeated shape.
3. If the shape is `fsetdec` over a `pick fresh`/`atom_fresh` hypothesis,
   reach for `solve_notin_auto` FIRST — splitting the union is what
   helps, not trimming the hypothesis list.
4. If the goal is an intersection-emptiness with ~6+ sets, go
   elementwise; each residual call then sees two or three.
