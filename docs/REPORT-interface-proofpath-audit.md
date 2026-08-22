# REPORT — displayed-interface & proof-path audit (2026-08-22)

Scope: the campaign's DISPLAYED SURFACE (README §VI, the extraction
exports, the headline statement shapes) and the PROOF PATH behind it
(`ext_algo/prop_lift.v` §13, `ext_algo/prop_run_corollaries.v`, the
conservativity bridge).  Method: consumer-count greps over `frost/` +
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
| `e_typing_run_complete_decl_infer` | paper judgement, TI at ◇ | `frost_infer`'s left component + `frost_infer_complete` |
| `d_typing_infer_dec` | paper judgement, TI at ◇ | the `sumbool` projection of `frost_infer` |
| `frost_infer` | paper judgement + extracted artifact | — |

Shrink the README to TWO entries: `e_typing_dec_init` (the general,
threaded claim) and `frost_infer` (the paper-facing, extracted claim).
The two demoted corollaries STAY in the tree — `…decl_infer` is
`frost_infer`'s workhorse; `d_typing_infer_dec` should then be
re-derived FROM `frost_infer` (see P5).  Saves 2 entries ≈ 35 lines of
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
(`frost_infer` derives its own a-side wf).  Not displayed in README
(prose-cited only), hence OPT not DO.

### I4. **KEEP** (with one note) — the undisplayed and the unconsumed

- `e_typing_run_complete_decl_check`: 0 consumers, prose-cited in
  README.  It is the check-mode RECORD of §5; fine as tree-level.
- `frost_infer_complete`: prose-cited; the left-completeness guarantee
  is reader-facing (McTT keeps its analogue undisplayed too).
- ⚠️ `a_wf_exp_to_d` (prop_conserv.v): ZERO consumers anywhere.  It is
  the conservativity CONVERSE, there because §2 of that file proves
  both directions for every sort — an encoding-justification lemma in
  the `*_no_loss` sense (its consumer is the reader).  Add the
  standing one-line "do not orphan-sweep" note; do not delete.

### I5. **KEEP** — `frost_infer`'s run-equation field

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
`frost/prop_coercions.v` (the designated home, beside
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

### P5. **DO** (bundle with I1) — derive `d_typing_infer_dec` from `frost_infer`

Its current proof re-runs `frost_infer`'s case analysis (destruct the
runner, re-derive both branches).  Three lines via `frost_infer` make
the dependency DAG linear: `…decl_infer` → `frost_infer` →
`d_typing_infer_dec`.

### P6. **KEEP** — audited and load-bearing, do not "clean"

- The lift motive's 17 hypotheses: each was FORCED by a named rung
  (hand-off §8c.28–§8c.46); the 10-rung validation is the asset.
- Side 2's wf-freedom; the exists-fresh discipline; route (A)'s
  premise-free flex-reflects.
- `a_typing_fvar_binds` (sharp; its `a_pat` twin is FALSE).
- `e_typable` (consumed by both dec corollaries).

### P7. Documentation debt (no code)

`d_wf_exp`, `frost_infer`, and the decidability composition have no
PROGRESS.md Part 1 rows yet; `a_wf_exp_to_d` needs its keep-note (I4).

## Suggested batches

- **Batch A** (interface, one commit, cheap): I2 + I1 + P5 (+I6).
  Rebuild: prop_typing → run_corollaries → README.
- **Batch B** (dedup, one commit, one full rebuild): P1.
- **Batch C** (refactor campaign, optional): P2a → P3 → P2b; P4
  separately, measured.
