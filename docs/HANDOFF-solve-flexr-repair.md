# HANDOFF — propagate the authors' `SolE-FlexR` repair

**Branch**: `solve-flexr-repair-wip` (branched off `remech`, which was
fast-forwarded to `d5f9169`). Nothing pushed. Commits so far:

| commit | what |
|---|---|
| `26558b8` | definitions + `prop_swap` + `prop_solve_sub` + `prop_looksub` |
| `af5dfe0` | the two soundness-side findings, recorded |
| `c86a706` | `dec_ext_guess_source` — the eq-side decoration path |
| `af89c1b` | ⭐ **subtyping soundness Qed + axiom-free under the repair** |
| `d0a3432` | completeness cluster started; the weakening finding |

**Read `docs/refutations.tex` first** if you have not — it is the
author-facing note that diagnosed `SolE-FlexR` and proposed the repair, and
it ends with exactly the checklist this campaign is working through.

---

## 1. The task

The co-authors accepted the refutation and proposed this rule:

```
  nonflex(P)      guess^TY(P) = (Ξ; P')
  ─────────────────────────────────────
        solveeq P α̂ ⤳ Ξ ⨾ P'
```

with the note *"Thread the fresh suffix Ξ through all constraint-solving
judgements, add it to Look's output suffix, and update the corresponding
specification and proofs. The current look-completeness is broken."*

The old row was `solveeq P α̂ ⤳ α̂`, which **discards the accumulated
pattern**. That is the whole defect behind both machine-checked refutations
(Lemma E.17 look-completeness, Theorem 4.6 completeness of subtyping).

### Why the old rule fails — keep this in mind, it explains most repairs

The solve is a **fold**: `P` is the pattern accumulated so far about the
`SI-ForallL` instantiation, starting at `◇`. `P'` lives **under the binders
the solve itself opened**, and `SS-ForallL` **closes over them**. Returning
α̂ — declared *outside* that ∀ — erases the bound variable's *occurrences*,
so the close re-binds a **vacuous** binder `∀_.α̂`, and α̂ can never be
instantiated to anything mentioning the rigid. The reachable set from
`∀_.α̂` does not contain `∀γ.γ→γ`. This is why the continuation gets stuck
at `Assign-SkipRigid`: the escape check firing on information the solve
moved out of scope.

`guess^TY` rather than `P` verbatim because the result is destined for an
**assignment**, and `U-Assign-SolveM` rejects ghosts. `guess^TY` turns each
"unknown" from a **ghost** (untouchable) into a **fresh flexible**
(assignable) — the same move `LE-FlexR` already makes on the collection
side. It does **not** strip `∀`s. Those fresh flexibles are the `Ξ`.

---

## 2. The definitional change (done — `frost/algo/def_extra.v`)

- `a_solve_sub : aenv -> mode -> pskl -> pskl -> aenv -> pskl -> Prop`
  — `Θ ⊢ₛ P ≼[m] Q ⤳ Ξ ⨾ P'`
- `a_solve_eq : aenv -> pskl -> pskl -> aenv -> pskl -> Prop`
  — `Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P'`
- `a_solve_cstr : aenv -> a_cstrs -> pskl -> aenv -> pskl -> Prop`
  — `Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ Q`
- `a_extract`'s suffix has **three** blocks: `Ξ ++ Ξs ++ Ξ'`
  (collection, solving, final guess), each stage's avoid-input being
  everything generated before it.

Two decisions beyond the sketch, both **forced** — do not undo them:

1. **The four ∀-CLOSING rows (and `SS-ForallR`) run their premise at
   `(β ~ abind_tvar) ++ Θ`.** The solve used to generate no names; now a
   guess can fire below such a binder and a generated β would be captured by
   the `close`. With β in the context, `β ∈ ftvar_in_aenv` — which
   `a_guess_mono`'s hole row already avoids — so "the block is apart from β"
   is *derivable*.
2. **The sibling-premise rows THREAD**: second premise at `Ξ1 ++ Θ`, output
   `Ξ2 ++ Ξ1` (`SS-Arrow`, `SS-GhostLF`, `SE-Arrow`, and `a_solve_cstr__eq`
   where it is forced by the pattern fold). Run both at `Θ` and the two
   blocks can pick the same atom, conflating two independently-invented
   flexibles.

---

## 3. What is green (Qed, `Closed under the global context`)

`def_extra` · `prop_swap` · `prop_solve_sub` · `prop_looksub` ·
`prop_sub_sound` · `prop_decorate_sub` · `prop_decorate_key`.

⭐ **`a_sub_sound_thm` — subtyping soundness holds under the repaired rule,
and its STATEMENT DID NOT MOVE.** Every new obligation is absorbed inside
the proof out of wf premises the theorem already had. The repair costs
nothing at the interface.

### The example-based check (do not lose this)

A scratch probe (not yet landed as a `cex/` file) machine-checks, axiom-free,
that at the refuting configuration of `cex/probe_double_occ_run.v`:

- `new_extract` — the extract now returns `∀γ.γ→γ`, not the vacuous `∀_.f̂`;
- `new_run_exists` — a full `a_sub` run **EXISTS** there, the direct negation
  of `probe_no_run`.

**TASK: land this as `frost/algo/cex/probe_flexr_repair.v`.** It only needs
modules upstream of `algo/def_extra.v`. Reconstruct it from
`cex/probe_solve_flexr.v`'s `run_exists_at_correct_instantiation` prefixed by
`a_sub__forall_l` with `P1 := ∀γ.γ→γ`, `Ξ := nil`.

---

## 4. The idioms this campaign discovered — reuse them

### (a) The witness-move is a SWAP, not a rename

**This is the single most important thing to know.** The freshness-campaign
proofs move a rule's binder `b` out of the way by a double RENAME, whose
side condition is "the source dodges the context". `b` now sits **in** the
premise's context, so that can never hold — it was never a rename.
Equivariance has no such condition (it carries the context along), and that
is harmless because every consumer quantifies the context universally.

Already packaged in `prop_solve_sub.v`:

- `a_solve_eq_move_binder` (both slots opened)
- `a_solve_eq_move_binder_tophole_l` / `_tophole_r` (one slot is `∀◇P`)
- `a_solve_sub_move_binder_l` (`SS-ForallL`) / `_r` (`SS-ForallR`)

The moved premise runs at `(α0 ~ tvar) ++ swap_aenv b α0 Θ` and nobody has to
care. Supporting: `swap_pskl_as_subst`, `swap_aenv_one_tvar` (`prop_swap.v`).

`a_solve_{sub,eq}_rename_var` were re-derived from equivariance: **540 lines
became 15.**

### (b) `pskl_top_guarded` is the wf discipline that pays for everything

The repaired row can return a `∀` where the old one returned a variable.
Wherever a proof needed "the output is guarded-headed", route through the
**SUBJECT** instead, where `pskl_top_guarded (∀◇P)` gives it. This is not a
new side condition: `a_wf_pskl_top_guarded` derives it from the paper's own
"a `∀◇` is well-formed only over a guarded body".

### (c) The `Ξ` scoping kit (`prop_solve_sub.v`)

- `a_solve_*_decls` — the block is undefined flexibles only, so
  `ftvar_in_aenv Ξ = dom Ξ`: a block can never be ill-scoped, only mis-named.
- `a_solve_*_generated_fresh` — **the master invariant**: a generated name
  dodges `ftvar_in_aenv Θ`. Gives at once: no capture at the closing rows
  (`_generated_apart_binder`), sibling disjointness, and disjointness from
  `Θ0`/`Ξl` in `a_extract`.
- `a_solve_*_generated_ftvar`, `a_solve_*_generated_occurs`
  (`dom Ξ ⊆ ftv P'` — turns `β ∉ dom Ξ` obligations into the `β ∉ ftv P'`
  every call site already has).
- ⚠️ `uniq Ξ` is **not** derivable, and the obstruction is *inherited*:
  `a_guess_mono__arrow` runs both halves at the same `Θ`, exactly as
  `a_looksub__arrow` does. Colliding blocks are filtered downstream by
  `a_sub__forall_l`'s `uniq (Ξ ++ Θ0)`. Do not try to fix this here.

---

## 5. Findings for the authors (record any new ones in `docs/PAPER-GAPS.md`)

1. **`solve_eq_guarded_r_head` is FALSE** and is deleted. It said solving
   against a *guarded target* yields a guarded-headed output; its entire
   content was `SolE-FlexR` (a guarded target can only be a variable, which
   the old row returned). Now `∀γ.γ→γ ∼ β̂` outputs `∀γ.γ→γ`. The
   guarded-**subject** twin survives via `a_guess_mono_guarded`.
2. **The repair owes `dec_ext_guess_source`** — *a decoration of the guess is
   a decoration of the source* — ⭐ **PROVED** (`prop_decorate_key.v`). It
   holds because `guess^TY` only ever loses information. The decorated
   system already had the row to fire (`SEq-FlexR`), so no new decorated rule
   was needed.
3. **Weakening the solve by a rigid entry now needs `β ∉ dom Ξ`** — ⭕ stated,
   **not yet proved**. See §6.

---

## 6. NEXT STEPS, in order

### Step 1 — `prop_look_complete.v`, resume at `a_solve_eq_weaken_tvar_size`

The file is mid-repair and does **not** compile. Everything before that
lemma is done (`a_solve_sub_eq_ctx_change` with its new fourth condition
`ftvar_in_aenv Θ' ⊆ ftvar_in_aenv Θ`, the `a_flex_*` push/strip/app kit, both
`strengthen_tvar` lemmas). A ⚠️-marked comment at the lemma states the
finding in full.

Repaired statement:

```coq
Θ0 ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P'  ->  β `notin` dom Ξ  ->
((β ~ abind_tvar) ++ Θ0) ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P'
```

False without the side condition: pushing β onto `Θ0` enlarges
`ftvar_in_aenv Θ0`, so a run that generated the atom β cannot be replayed —
`guess^TY`'s hole row fails at exactly that α. Consumers get it free from
`a_solve_eq_generated_occurs`.

The proof needs: the swap idiom for the colliding-witness case, an
**adjacent-rigid EXCHANGE** (immediate from `a_solve_sub_eq_ctx_change`, both
directions since `dom`/`ftvar_in_aenv` are equal and the flex facts are
symmetric), and — ⚠️ **decide this deliberately** — the swap's
`swap_aenv b δ Θ0` only collapses to `Θ0` given `b ∉ ftvar_in_aenv Θ0`, which
is *stronger* than the rules' `b ∉ dom Θ0`. Either strengthen the solve's ∀
side conditions to `ftvar_in_aenv` (cheap: it only shrinks the judgment, and
completeness *constructs* these derivations so it can always pick such a β),
or carry the difference. **Recommendation: strengthen the rules.** It is the
same avoid-input discipline `a_guess_mono__forall` and the look rules already
use, and it makes this and later proofs uniform.

### Step 2 — the rest of the completeness cluster

`prop_look_complete.v` (4.8k) → `prop_look_complete_var.v` (P6-Cv) →
`prop_look_complete_cstr.v` (P6-Cs) → `prop_look_complete_sub_var.v` (P6-Sv)
→ `prop_look_complete_sub_cstr.v` (P6-Ss) → `prop_look_complete_extract.v`
(P6-L).

⭐ **The real content here is NOT threading `Ξ`.** Every P6 statement
produces a metasubstitution `κ` with `κ ∷ Θ0 ⊑ Θ`, and that `κ` must now be
**extended over the new flexible block**. The template already exists:
`a_guess_ty_witness` (`prop_look_complete_extract.v` §9) builds exactly such
an extension for the final guess's `Ξ'`, with an avoid-set parameter `L` and
a `Hfr'` output. Copy its shape for the solve's block. The
homogeneous-flex REORDER KIT in `prop_look_complete_cstr.v` moves between
block orders (all three blocks are undefined flexibles, so order is
semantically immaterial but not syntactically so).

### Step 3 — `prop_sub_complete_thm.v` / `prop_sub_complete_dispatch.v`

Mostly consumers; expect `a_extract`'s three-block suffix and the P6
statements' new `κ` extension to ripple.

### Step 4 — the `cex/` suite: **RETRACTIONS**

These are now **FALSE** and must be retracted, not repaired:

- `cex/probe_double_occ_run.v` — `probe_no_run`,
  `p6l_look_completeness_fails`, `probe_motive_instance_false`,
  `probe_main_forall_false`, `probe_main_forall_hyp_false`. The run EXISTS
  now; `probe_solve` yields `∀γ.γ→γ` instead of `∀_.f̂`.
- `cex/cex_thm_complete_subtyping.v` — same configuration.
- Rewrite each file's header to say what it USED to show and under which
  rule, and point at `probe_flexr_repair.v`. Keep them as history; the
  paper's `docs/refutations.tex` cites them by name.

### Step 5 — P6-L itself

`a_extract_complete_gen` (`prop_look_complete_extract.v`) — the paper's
`lemma:complete-look` (`subtyping-proofs.tex:2730`). With the repair the
counterexample to it is gone; re-prove it and check whether the `sub_shield`
premise can be **weakened or dropped**, since `sub_shield` was invented as
the mech's repair *of this very lemma*. That is the pay-off of the whole
campaign — see whether `main_forall` (the one hypothesis of
`a_sub_complete_bundle_holds`) becomes discharge-able.

### Step 6 — the paper

`paper/sections/appendices/full-algo-spec.tex`: the `SolE-FlexR` rule
(`:1371`), the `Ξ` suffix on all three solving judgements
(`fig:constraint-solving`), Look's output suffix, and
`lemma:complete-look`. Also `docs/refutations.tex` §"Suggested repair" —
record that soundness IS now checked, and the three findings.

---

## 7. Hazards (all cost real time this session)

- ⚠️ **No `ltac:()` in a partially-applied IH or lemma.** The evars are
  unresolved when the tactic runs, so `fsetdec`/`lia` see a goal with
  metavariables. Use an explicit `assert` first. (This is already in
  `MEMORY.md`; it bit three times anyway.)
- ⚠️ **`econstructor` on `SS-ForallR` leaves the witness an evar** — its
  output passes *through*, so nothing determines β. Name it:
  `apply a_solve_sub__forall_r with (β := b)`.
- ⚠️ `Set Implicit Arguments` means the packaged move-binder lemmas need
  `@name _ _ _ _ _ _ α0 H ...`, not `(α0 := α0)`.
- ⚠️ `dom Θ` vs `ftvar_in_aenv Θ` is now load-bearing everywhere. A
  flexible's payload may mention an atom, so `dom` is the wrong avoid-set
  for anything touching the guess.
- ⚙️ After changing `prop_solve_sub.v` or `prop_swap.v`, rebuild
  `prop_looksub` → `prop_sub_sound` → `prop_decorate_sub` →
  `prop_decorate_key` before the file you are working on, or you get
  "makes inconsistent assumptions over library".
- ⚙️ Iterate with `coqc -R . src -w -deprecated-hint-without-locality,-omega-is-deprecated frost/algo/<file>.v`
  on the single file; `make NJOBS=10 -k coq` only for the whole-tree picture.
- ⚙️ To see what a blanket tactic left open:
  `all: match goal with |- ?g => idtac "LEFT>>>" g end.` before the bullets,
  or `Show.` for the first goal with its context.
