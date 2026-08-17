# HANDOFF — close consistency-runner completeness WITHOUT the hole-free restriction

**✅ CLOSED (2026-08-17).  `consis_call_no_hole` is GONE from the motive,
and all three headline corollaries — `e_assign_impl_complete`,
`e_unify_impl_complete`, `e_consis_run_complete` — are unrestricted, Qed
and assumptions-closed.**

⭐ **HOW IT CLOSED, and it was not by solving the problem this file is
about.**  The problem was: at two cells the rules admit BOTH a ghost row
and a flex row, at different output contexts, so completeness had to
RELATE the runner's context to the derivation's.  Five candidate
relations are machine-checked refuted (§4), and the fragment escape too
(§5's R2).  The resolution was to remove the AMBIGUITY instead:
`U-FlexL` / `U-FlexR` now carry `P0 <> ◇` / `P <> ◇`
(`frost/algo/def_rules.v`), which renders the reference implementation's
ghost-first dispatch — the same prose-completion the tree already makes
for `SE-FlexR` via `nonghost_pskl`.  Then

- every ghost cell admits exactly ONE rule, so
  `ext_algo/prop_consis_inc.v` §3's two divergent-cell inversions
  collapse from disjunctions to single-rule statements;
- the six case-kills the restriction bought became ordinary cases, each a
  three-line `do_ghost_cell` against those inversions;
- `a_consis_complete` was RE-PROVED with the guards, by dispatching in the
  implementation's order — `C-GhostR` hoisted above the two flexible
  layers, plus the mirror `C-Ghost` node at a flexible input (its one real
  obligation discharged by the same `consis_precise_via_refine` the
  `C-FlexR` branch uses).

⛔ **The two-context problem is therefore MOOT, not solved.**  Constraints
C1–C6 and the five refutations below are kept as the record of why the
guard is the right fix and what it cost to find out; do not restart any of
them.  Filed for the authors in `docs/PAPER-GAPS.md`.

---

Campaign context: `HANDOFF-extractable-algo-encoding.md` §8c.10 (level 5),
§8c.10b (the refutation that created the restriction), §8c.12 / §8c.12a–c
(this work).  Read those only if this file is not enough; it is meant to be
self-contained.

---

## 1. The goal, exactly

`frost/ext_algo/prop_consis_complete.v` proves

```coq
Lemma e_consis_call_impl_complete : forall S0 Θ c, consis_call_complete S0 Θ c.
```

whose motive (§6 of that file) carries the restriction

```coq
    consis_call_no_hole c ->        (* ← DELETE THIS *)
```

**The task is to delete that premise** and repair the proof, which then
lifts the three headline corollaries (`e_assign_impl_complete`,
`e_consis_run_complete`; `e_unify_impl_complete` is already unrestricted)
onto ghost-carrying skeletons — the inputs subtyping and typing actually
hand consistency, which is what makes the flagship path reachable.

⚙ The restriction buys exactly SIX case-kills, at
prop_consis_complete.v:1824, 2006, 2112, 2209, 2292 and 2402 (`destruct
Hnh0.` / `destruct Hnh1.`).

---

## 2. What is already Qed — do not rebuild any of it

### `frost/algo/consis/prop_consis_inc.v`

| lemma | statement |
|---|---|
| `a_assign_unify_consis_isub` | **the trio only adds information** — `Θ0 ⊴ Θ1`, for assign / unify / consis |
| `a_assign_unify_consis_lc` | the output context is locally closed |
| `a_assign_unify_consis_defs_lc` | every definition in the output is locally closed |
| `a_consis_isub_wf` | the same under `a_wf_aenv`, recovering `a_consis_sound`'s first conjunct |

Helpers added there: `a_isub_solve_head`, `a_isub_weaken_suffix2`,
`a_isub_strengthen_suffix_src`, `a_wf_aenv_defs_lc`, and the
`lc_aenv` / `aenv_defs_lc` plumbing.

### `frost/ext_algo/prop_consis_inc.v`

`e_assign_isub`, `e_unify_isub`, `e_consis_isub`, `e_assign_nil_isub` (the
`e_` faces, by composition with prop_consis.v §4's bridge), plus §3's four
GHOST-ROW INVERSIONS: `e_consis_inv_hole_subject`,
`e_consis_inv_hole_pattern`, `e_consis_inv_hole_flex_pattern`,
`e_consis_inv_flex_subject_hole`.

⭐ **Everything above is a statement at a SINGLE context**, so it is
independent of how the two-context question in §4 is eventually settled.
None of it is at risk.

---

## 3. The case analysis, settled

Of the six kills, **four need nothing new** — one rule fires and the
inversions in §2 already give it:

| cell | why it is unique |
|---|---|
| pattern `1`/`→`/`∀`/`⫯`, subject `◇` | only `U-Ghost`; `U-UnivGhostR` wants a GUARDED subject and `◇` is not guarded (`guarded_pskl` is `1 \| α \| A → B` and nothing else) |
| pattern `β̂` RIGID, subject `◇` | only `U-Ghost`; `U-FlexR` would need `β̂` flex-bound, which `e_assign_target_flex` forbids |
| pattern `◇`, subject not a flexible var | only `U-GhostR`; at `(◇, ◇)` `U-Ghost` also fires but returns the SAME triple |

**Two cells diverge**, and they are mirror images:

```
  pattern β̂ FLEXIBLE, subject ◇     U-Ghost   vs  U-FlexR
  pattern ◇, subject α̂ FLEXIBLE     U-GhostR  vs  U-FlexL
```

At BOTH, the runner answers with its input context UNCHANGED
(def_consis_impl.v:759-763 for the hole pattern; the `pskl_hole` subject arm
of each pattern clause, :770, :808, :938, :989, :1056, :1134).  The
derivation may instead run an assignment walk.  §2's increase is exactly the
measure of that walk.

---

## 4. THE OPEN PROBLEM, and four dead ends

The divergence is local, but it PROPAGATES: `U-Arrow`'s second premise runs
at the first's output, so from there on the runner's context and the
derivation's differ.  The motive must therefore relate two DIFFERENT
contexts.  Four candidate relations have been tried.

| # | relation | refuted by | why |
|---|---|---|---|
| 1 | renaming (`swaps_aenv ps Θd = cs_ctx r`) | `cex/probe_consis_ghost_flex.v` | the divergence is information-free but is not a renaming |
| 2 | `⊴` (identity increase) | `cex/probe_isub_too_strong.v` | `a_isub`'s SECOND conjunct wants definitions preserved SYNTACTICALLY; the derivation's `β̂ ≔ γ̂` is an alias where the runner committed to `β̂ ≔ 1` |
| 3 | bare `a_inc` | `cex/probe_inc_head_blind.v` | `a_inc` is blind to the HEAD, and the assign judgement dispatches on it — the two walks agree on neither the rule nor the number of steps |
| 4 | a POSITIONAL structural refinement (`ctx_ref`: same / solved-in-place / fresh-insert) | `cex/probe_assign_migrates.v` | `Assign-Depend` + `Assign-SolveM` move a mentioned flexible from ABOVE the target to BELOW it, so the contexts cannot be walked in lockstep |
| 5 | the ALIAS-COLLAPSE **function** (`collapse1`), as an exact transport | `cex/probe_collapse_orientation.v` | at the alias entry a walk must take `Assign-Assign`, which converts it to a CONSIS; when the payload is the alias variable itself that consis is a UNIFY, and `Flex-Flex-R` orients the new definition the OPPOSITE way from the collapsed walk's `SolveM` — `(α̂ ≔ γ̂, γ̂)` versus `(γ̂ ≔ α̂, α̂)` |

⭐ **The constraints, which is what this section is really for.**  Any
working relation `R Θr Θd` must satisfy all of:

- **C1 composable** — preserved along `U-Arrow`'s threading, so the two
  halves chain (`a_inc_compose` / `a_isub_trans` are available).
- **C2 produced by the ghost cells** — must hold between `Θ` and the output
  of `Θ ⊲[nil] α̂ ≔ ◇`; §2's increase gives `⊴`, hence also `a_inc`.
- **C3 not syntactic on definitions** (dead end 2) — the derivation reaches
  a value through a fresh ALIAS chain; only the equational theory sees the
  agreement.
- **C4 head-determining enough** to predict the assign walk's rule (dead
  end 3).
- **C5 migration-tolerant** — no positional lockstep (dead end 4).
- **C6 orientation-tolerant** (NEW, dead end 5) — when the two sides
  create the same equivalence class of variables, they may pick DIFFERENT
  REPRESENTATIVES: one side derives `α̂ ≔ γ̂`, the other `γ̂ ≔ α̂`.  The two
  are related by a transposition, but of names that are NOT fresh, so the
  motive's swap chain (`a,b ∉ S0`) cannot absorb it.

**C4 and C5 pull against each other, and that tension IS the open
problem.**  C4 wants structure the walk can be read off; C5 says the walk
destroys exactly that structure.  ⚠️ **C6 additionally rules out any
relation that is a FUNCTION of the context** (dead end 5 was exactly
that), because the orientation is chosen by the derivation, not
determined by the input.  C3 + C5 + C6 together point at EQUI-GENERALITY
(`a_inc` in both directions) — i.e. the successor is no longer a
bookkeeping relation but the statement that *the algorithm is
representation-independent*.  ⚙ Scope and cost that before attempting
it; it is a substantially bigger theorem than anything levels 1–5
needed, and it should be weighed against simply reporting the
restriction as a documented limitation of the mechanized result.

---

## 5. Directions worth trying, best first

### (R1) ⭐ PRE-NORMALISE one side — the campaign's own precedent

Level 4 hit a structurally similar hazard ("one atom in two roles breaks
`flex_agree_rel`") and solved it NOT by strengthening the relation but by
**pre-normalising side 1** — a hygienic rederivation — see §8c.9 and
`remech-buried-forall-settled-and-peel`.  The analogue here: instead of
relating the runner's context to an arbitrary derivation's, first replace the
derivation by a normalised one whose alias chains are collapsed, then compare.
⚠️ §8c.9 also records that a RUNNER-RERUN normalisation is CIRCULAR — read
that note before designing this.

⭐ **Sharpened by R2's refutation analysis (2026-08-17): this is now the
lead, and the reason it can work where designs 1–4 failed is the QUANTIFIER
STRUCTURE.**  Concretely: (i) a normalisation lemma — every `e_consis`
derivation yields a GHOST-PREFERRING one (take `U-Ghost`/`U-GhostR`
wherever they fire, i.e. the runner's dispatch order) — and (ii) a main
induction that runs the runner against the NORMALISED derivation in
LOCKSTEP, where the two-context problem never arises because a
ghost-preferring derivation makes the runner's choices.  The two-context
transport then lives inside (i) at `U-Arrow` only: premise 2's derivation
sits at the un-normalised premise-1 output `Θd`, and must be replayed at
the normalised output `Θn`.  ⭐ The crucial difference from dead ends 2–4:
in that transport BOTH sides are DERIVATIONS, and the replayed side may
CHOOSE ITS RULES FREELY — C4 (head-determinism) was only ever needed to
predict the RUNNER's single admissible rule, so it evaporates, and the
relation `Θn R Θd` can be as semantic as C3/C5 want (alias-extension /
`a_inc`-shaped).  What (i) owes is therefore an ALIAS-ELIMINATION
transport, the exact thing probe_consis_ghost_flex.v's header already
named.  ⚠️ Costs to budget: the transport is still an induction over the
derivation with a two-context motive (the head-blindness trap does not
bite, but the migration one — C5 — still constrains how R is stated), and
the normalised derivation's OUTPUTS differ from the original's, so the
motive of (ii) consumes R once more at the very end (the flagship
corollaries' conclusions must tolerate it, which §2's ⊴-increase face is
shaped for).

⚙ **Candidate for R, to try first: `a_inc` AT THE ALIAS-COLLAPSE κ.**
The divergence only ever ADDS an alias block — `α̂ ≔ ε̂` with `ε̂` fresh
and unconstrained — so the two contexts differ by a KNOWN substitution
(collapse each alias `ε̂` back to its target `α̂`) plus entry deletion.
Head-blindness (dead end 3) refuted `a_inc` as an IH for predicting the
RUNNER's rule; with derivations on both sides that role is gone, and
`a_inc` scores on every remaining constraint: composable (C1,
`a_inc_compose`), produced by the ghost cells (C2, §2's increase),
semantic on definitions (C3), non-positional (C5).  State the transport
with the alias SET tracked explicitly and κ fixed by it, not
existentially quantified — the existential is what made dead end 3's
motive unusable.

### (R1) BUILD STATE (2026-08-17, session 2) — steps 1–2 LANDED

`frost/ext_algo/prop_consis_alias.v`, Qed and assumptions-closed:

- **Step 1, `e_assign_hole_out`** (+ the mutual
  `e_assign_unify_consis_hole_walk`): the `◇`-payload walk's output is
  EXACTLY `alias_insert_out` — unchanged (an inner `U-GhostR` stops it),
  or ONE undefined flexible `γ̂` replaced in place by `γ̂ ≔ ε̂, ε̂` with
  `ε̂` fresh.  ⚙ `◇` has no free variables, so `Assign-Depend` never
  fires: the insertion is POSITIONAL even though walks in general
  migrate.  ⚠️ `a_flex_tvar` admits DEFINED targets, so the walk
  alias-CHASES (`Assign-Assign` at `β = α` re-enters at the definition's
  image); the insertion lands at the END of the chase — the lemma
  existentially quantifies the solved variable.
- **Step 2, `collapse1 γ ε := rename_aenv γ ε ∘ aenv_remove γ`** (the
  directed rename is right here: a collapse MERGES `ε̂` into `γ`, no
  transposition can say that), with `collapse1_insert`: collapsing the
  insertion recovers the input — the runner's answer at the cells.

⭐ **Step 3's ABSORPTION lemma also LANDED** (`prop_consis_alias.v` §3,
Qed): `e_assign_absorb` / `e_assign_absorb_nil` — a NIL-blocked walk at
`Ξ ++ Θ` IS the `Ξ`-blocked walk at `Θ`, when every entry of `Ξ` is an
undefined flexible the payload mentions (which is exactly the block's own
invariant, since `Ξ` grows only by `Assign-Depend`).  ⭐ This is the
piece §8c.12c predicted would be needed ("an ABSORPTION lemma for
insert-headed walks") and it is INDEPENDENT of the refuted relation — it
is a statement about one side.  It is what makes the re-walk that
`Assign-Assign` triggers harmless.

⛔ **Step 3 AS AN EXACT TRANSPORT IS REFUTED** —
`cex/probe_collapse_orientation.v`, dead end 5 in §4's table.  Do not
retry it.  The killer configuration is small: context `(γ̂ ≔ ε̂, ε̂, α̂)`,
walk target `α̂`, payload the ALIAS VARIABLE `γ̂`.  The alias entry forces
`Assign-Assign`, whose substitution turns the payload into `ε̂` — so the
premise is a consistency between TWO FLEXIBLES, i.e. a UNIFY, and
`Flex-Flex-R` records `ε̂ ≔ α̂`.  The collapsed side has no alias entry,
so it simply walks: `Assign-Depend` then `SolveM`, recording `α̂ ≔ γ̂`.
Collapsing the first gives `(γ̂ ≔ α̂, α̂)`; the second is `(α̂ ≔ γ̂, γ̂)`,
and the probe proves that output is UNIQUE (both steps inverted).  Same
equivalence class, opposite representative.

**Step 3 — WHAT A SUCCESSOR MUST DO** (open, and now known to need C6).
The statement below is kept because it is the shape any successor still
has, but its conclusion must relate the outputs SEMANTICALLY (§4's C3 +
C5 + C6) rather than by the collapse function:

    is_alias γ ε Θ := binds γ (γ ≔ ε̂-var) Θ  (ε̂ the alias name)
    D : {{S0 ↝ S1 ⊨ Θ ⊢[Δ1|Δ2|P0] P ∼ Q ⊣ Θ1}}  ∧  is_alias γ ε Θ
      ⇒ {{S0 ↝ S1 ⊨ collapse1 γ ε Θ ⊢[Δ1|Δ2|cP0] cP ∼ cQ
           ⊣ collapse1 γ ε Θ1}}   ∧  is_alias γ ε Θ1
    (c• := subst by γ for ε̂; SAME supplies both sides — the transported
     derivation re-uses the original's draws)

  Discoveries from this session's design pass, to build on:
  - ⚠️ **The two sides do NOT peel walks in lockstep.**  At the alias
    entry the original walk MUST take `Assign-Assign` (defined heads have
    no skip row), which CONVERTS the walk to a consis judgement at the
    tail — and `U-FlexL` inside that consis RESTARTS a walk from the top
    of the dumped block.  The collapsed side keeps peeling.  So the
    transport cannot be a rule-for-rule simulation; organize it as a
    derivation-sided induction that freely RECONSTRUCTS the collapsed
    derivation (inversion kits + the two enablers below).
  - ⭐ **Below the alias entry the collapse is a pure SWAP.**  `γ` cannot
    occur below its own entry (wf points mentions downward), so
    `rename ε̂→γ` on the tail = `swap γ ε̂` — and §3's chain equivariance
    (`e_consis_swap`/`e_consis_swaps`) already transports derivations
    along swaps.  The above-the-alias part is a genuine κ-image (entries
    above may mention BOTH `γ` and `ε̂` — a merge), and only there does
    the induction have real content.
  - ⚠️ **The chase can hit the alias itself** (`α = γ` as walk target):
    the original's continuation retargets `ε̂` while the collapsed side
    keeps target `γ`; the two continuations are again swap-related.
  - ⭐ **`is_alias` survives the run** via the landed ⊴-increase
    (`e_assign_isub` et al.): `a_isub`'s definition clause preserves
    definitions SYNTACTICALLY.
  - ⚙ Closest precedent for the mechanics: prop_consis_rename.v L9
    (`a_assign_unify_consis_rename_tvar`) — mid-entry surgery over the
    trio, with `binds_mid_swap` / `a_flex_tvar_mid_swap`; but L9's entry
    is RIGID and its walk skips it verbatim, while the alias entry is
    where the action is.
  - The transport will need wf-strength hypotheses (γ-below-freshness is
    a wf fact); `algo/prop_wf_preservation.v` supplies preservation.
  - ⚙ **Scouted (session 2): the statement TYPECHECKS and the scheme
    runs** — all 28 rows enumerated (scratch, not in tree; re-create from
    the statement in this section).  Two corrections the rows forced
    immediately: (i) name-SLOTS (the walk's target, unify's pair) must go
    through the atom-MERGE `if α == ε̂ then γ else α`, NOT `swap_atom` —
    the swap would send `γ` to `ε̂` in slots where `γ` legitimately
    occurs; skeleton/payload slots keep the subst-image `cpskl`.
    (ii) rows that dispatch on `ε̂`'s own entry need a hypothesis pinning
    its SHAPE (undefined until the run defines it) — package it with the
    wf invariant rather than ad hoc.  Also visible: `Flex-Flex-L/R` can
    DEFINE `α ≔ ε̂-var` mid-run, so κ-images on definition payloads are
    live in every row, and the SolveM/skip rows want the collapse1
    app/cons computation algebra first (`collapse1_app`, per-entry
    clauses) — build exactly those, they are no longer speculative.

**Step 4 — assembly** (after step 3): extend the motive's conclusion from
`swaps_aenv ps Θd = cs_ctx r` to `swaps_aenv ps (collapse_chain als Θd) =
cs_ctx r` (collapse-then-swap normal form; supply clause drops the alias
names; out clause takes the collapse image), re-close the six kill sites
— the two divergent cells via `e_consis_inv_flex_subject_hole` +
`e_assign_hole_out` + `collapse1_insert`, the four unique ones unchanged
— and thread `U-Arrow` by transport-then-swap.  Then re-derive the three
headlines with the weakened (but alias-tolerant) conclusion.

### (R2) ⛔ REFUTED (2026-08-17): weaken the FRAGMENT instead of solving the general problem

**Dead — `cex/probe_pat_presents_hole_flex.v`.**  The question this
direction turned on — do subtyping and typing ever actually PRESENT a hole
opposite a flexible? — has answer YES, and the probe machine-checks it.
The program `(λf. f (λy. f y)) (λz. z)` composes three innocent moves:

1. `AT-Abs` GUESSES a λ-binder's type from its split skeleton, and
   `e_guess_mono` MIRRORS the skeleton's structure — a fresh flexible at
   each `◇`.  An abstraction applied to an unannotated abstraction has
   binder skeleton `⫯(◇→◇)`, so `f : δ̂1→δ̂2`, an arrow of UNDEFINED
   flexibles.
2. `AT-App` re-runs skeleton inference on its argument at pattern `◇` in
   that context, and under the argument's own λ, `AP-AbsCheck` binds `y`
   at SKELETON `◇`, which `e_sub__ghost` echoes back out — so the body
   run for `f y` types `f` at the NAKED pattern `◇ → ◇`.
3. `AP-Var` + `Arrow` pair that pattern componentwise against `f`'s type:
   `consis(pattern ◇, subject δ̂1)` — the divergent cell.

The probe exhibits that pat call with TWO derivations whose output
contexts differ in LENGTH (U-GhostR leaves Θ; U-FlexL solves `δ̂1 ≔ ε̂`),
so no swap chain relates them and no restriction can both hold at the
flagship's calls and exclude the divergent cells.  ⇒ §4's tension MUST be
resolved.  ⚙ Worth keeping from the analysis: the cell is reached only
through `◇`-carrying PATTERNS meeting guessed arrow TYPES — every other
pairing in the sweep was absorbed safely (FlexL at a `⫯`-rooted pattern
assigns the whole payload and `guess^TY` fills its `◇`s; `Ghost`/`GhostR`
at a non-flex opposite are unique).

### (R3) Derivation-sided induction for the two-context part

The runner-sided doctrine (§8c.9) forbids stating a level over two arbitrary
derivations — but it has one sanctioned exception, `e_guess_mono_rel`,
justified because `guess^TY` is syntax-directed.  Ask whether the
two-context step has the same justification.  ⚠️ Do not weaken the doctrine
casually; it is what kept levels 1–5 tractable.

### (R4) A relation indexed by the pending block

C5's migration only ever moves entries that are IN the block `Ξ`, which is a
PARAMETER of the assign judgement.  A relation that relates `(Ξr ++ Θr)` to
`(Ξd ++ Θd)` while tracking the blocks separately might tolerate migration
and still determine the head.  ⚙ Untried; no probe either way.

---

## 6. Dead ends already paid for — do not re-run these

- **`a_consis_complete`'s optimality conjunct does NOT close it** (§8c.12b).
  The pieces fit — `a_consis_sound` concludes exactly what
  `a_consis_complete` consumes, at `κ = identity` — but its conclusion
  EXISTENTIALLY quantifies the derivation, so it says *some* algorithmic
  derivation is optimal, not that *the runner's* is.  Connecting those is
  the very thing level 5 proves.  Circular.
- **Runner monotonicity** ("the runner at `Θ` is `⊑`-below the runner at any
  `⊑`-larger `Θd`") meets dead end 3 identically: it reads `Θd`'s head for
  its own dispatch.
- **A syntactic alias relation** was already tried and rejected in §8c.10b
  ("not closed").

---

## 7. Mechanics that will bite

- ⚠️⚠️ **An unknown constant inside a tactic fails SILENTLY.**  Half a
  case-script sat "unprovable" for rounds this session because one lemma had
  been dropped in a refactor.  Verify the lemma EXISTS before believing a
  case is hard.
- ⚠️⚠️ **`eapply` of a lemma with a list-valued index leaves an evar that a
  structural tactic explores forever.**  `eapply a_isub_strengthen_suffix_src`
  left `a_suffix ?Ξ` and `a_suffix_app` ran past 900 s, twice.  Pin the index
  from the IH with `match goal`, then `apply` explicitly.
- ⚠️ **`repeat split` dives into `a_non_flex`** (itself a conjunction), and
  into the motive's `In`-quantified conjunct.  Spell the splits out.
- ⚠️ `lc_abind` sends `flex_mono_def τ` to `True` — `lc_aenv` constrains NO
  definition payload.  That is why `aenv_defs_lc` exists.
- ⚠️ `simp` is the wrong tool at the consistency clause (its recursive call
  sits at the same clause pattern); rewrite with `_13`'s own equation.
- ⚠️⚠️ fsetdec cliff: disjointness goals hang at ≥6 set variables, and the
  cliff is the GOAL's variable count, not the context's, so `clear -` does
  not help.  Spell the derivation out.
- ⚙⚙ **The technique that made §8c.12 tractable**: after a mutual induction,
  close the easy rows with `all: try (now …)` and then
  `all: match goal with |- ?G => idtac "REMAINS:"; idtac G end` — `coqc`
  prints every surviving goal, so ONE run gives the exact open-row list.  It
  took the increase from 28 rows to 0 in seven measured steps.

---

## 8. Gate

`make coq > log 2>&1; rc=$?; exit $rc` — never pipe or chain — then VERIFY
`.vo` TIMESTAMPS MOVED.  For the assumption report, `touch README.v` and
re-run: it must print 32 × "Closed under the global context".  ZERO
`Admitted`/`Axiom`; `Print Assumptions` on everything new.  **Never commit a
partial induction** — abort with a RESTART NOTE instead.  Scratch files stay
out of the tree; commit tag `[mech]`.
