# HANDOFF — propagate the authors' `SolE-FlexR` repair

**Branch**: `solve-flexr-repair-wip` (branched off `remech`, which was
fast-forwarded to `d5f9169`). Nothing pushed.

| commit | what |
|---|---|
| `26558b8` | definitions + `prop_swap` + `prop_solve_sub` + `prop_looksub` |
| `af5dfe0` | the two soundness-side findings, recorded |
| `c86a706` | `dec_ext_guess_source` — the eq-side decoration path |
| `af89c1b` | ⭐ **subtyping soundness Qed + axiom-free under the repair** |
| `d0a3432` | completeness cluster started; the weakening finding |
| `0618301` | this hand-off |
| `20ada0f` | ⭐ **`probe_flexr_repair.v`**; the two rule strengthenings; retractions; docs |
| `b2a528c` | the wf layer of the completeness cluster |
| `ae3ae0b`/`9322ea5`/`a5fb27a` | ⭐ `a_guess_ty_witness_mono` and its first sites |
| `f50154a` | ⭐⭐ **`prop_look_complete.v` IS GREEN** — the arrow-case κ-merge |
| `3faccba` | ⭐⭐ `a_guess_mono_ctx_change` + the flex-block WEAKENING, both moved up |
| `486b668`…`d5a3e31` | WIP P6-Cv: SE-FlexR, the arrow merge, the Θw thread |
| `3e44c4d` | ⭐⭐ **P6-Cv IS GREEN** — the ∀-row payload-scope obligation CLOSED |
| `1eb82c2`…`19f0a57` | P6-Cs: the statement FINAL, five rows through, the arrow row analysed |
| `f6b5cc1` | ⭐⭐ **P6-Cs IS GREEN** — the arrow merge, the five ∀ rows and the corollary |
| `a73af9b` | P6-Sv started: `solve_sub_ext` kit + the FINAL statement |
| `ece5b52` | ⭐⭐ **P6-Sv IS GREEN** |
| `6b67d7b` | ⭐⭐ **P6-Ss IS GREEN** |
| `e1ab396` | ⭐⭐⭐ **P6-L IS GREEN — the whole cluster closed** |
| *(latest)* | Step 2 done (`prop_sub_complete_thm`); ⭐⭐ the repair RETIRES two of our own cex |

**Read `docs/refutations.tex` first** if you have not — it is the
author-facing note, and it now ends with a §"Status" recording what the
repair costs. `docs/PAPER-GAPS.md` has the same three findings in registry
form.

---

## 0. ⛔ DO NOT TOUCH `paper/` — USER DIRECTIVE (2026-08-04)

Defer **all** paper edits until the mechanization has proved the affected
statements. Not the one rule, not a marked-provisional figure, nothing.
A partially-threaded `fig:constraint-solving` is worse than an unchanged
one. The mech's job mid-campaign is to *report* — via `docs/PAPER-GAPS.md`
and `docs/refutations.tex`, which are the mech's own documents — not to edit
the spec. **Step 6 below is LAST and gated on the proofs.**

---

## 1. The task

The co-authors accepted the refutation and proposed:

```
  nonflex(P)      guess^TY(P) = (Ξ; P')
  ─────────────────────────────────────
        solveeq P α̂ ⤳ Ξ ⨾ P'
```

with the note *"Thread the fresh suffix Ξ through all constraint-solving
judgements, add it to Look's output suffix, and update the corresponding
specification and proofs. The current look-completeness is broken."*

The old row was `solveeq P α̂ ⤳ α̂`, which **discards the accumulated
pattern** — the whole defect behind both machine-checked refutations.

### Why the old rule fails — keep this in mind, it explains most repairs

The solve is a **fold**: `P` is the pattern accumulated so far about the
`SI-ForallL` instantiation, starting at `◇`. `P'` lives **under the binders
the solve itself opened**, and `SS-ForallL` **closes over them**. Returning
α̂ — declared *outside* that ∀ — erases the bound variable's *occurrences*,
so the close re-binds a **vacuous** binder `∀_.α̂`, and α̂ can never be
instantiated to anything mentioning the rigid.

`guess^TY` rather than `P` verbatim because the result is destined for an
**assignment**, and `U-Assign-SolveM` rejects ghosts. `guess^TY` turns each
"unknown" from a **ghost** (untouchable) into a **fresh flexible**
(assignable) — the same move `LE-FlexR` already makes on the collection
side. It does **not** strip `∀`s. Those fresh flexibles are the `Ξ`.

---

## 2. The definitional change (DONE — `frost/algo/def_extra.v`)

- `a_solve_sub : aenv -> mode -> pskl -> pskl -> aenv -> pskl -> Prop`
  — `Θ ⊢ₛ P ≼[m] Q ⤳ Ξ ⨾ P'`
- `a_solve_eq : aenv -> pskl -> pskl -> aenv -> pskl -> Prop`
  — `Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P'`
- `a_solve_cstr : aenv -> a_cstrs -> pskl -> aenv -> pskl -> Prop`
  — `Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ Q`
- `a_extract`'s suffix has **three** blocks: `Ξ ++ Ξs ++ Ξ'`
  (collection, solving, final guess), each stage's avoid-input being
  everything generated before it.

**Four decisions beyond the sketch, all forced — do not undo them.**

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
3. ⭐ **The five binder rows avoid `ftvar_in_aenv Θ`, not `dom Θ`**
   (2026-08-04). A flexible's PAYLOAD `α̂ ≔ τ` may mention an atom that is in
   no domain, so `dom` is the wrong avoid-set for anything touching the
   guess — and SE-FlexR now does. It is the same set `a_guess_mono__forall`
   and every `a_looksub`/`a_lookeq` binder row already carry. **Payoff**:
   `swap_aenv b δ Θ = Θ` becomes available at a binder row (that swap is the
   witness-move, §4a), and `a_solve_sub_eq_ctx_change` collapses to ONE
   condition. Cost to rebuild the whole soundness chain: **one line**
   (`a_solve_sub_eq_ftv`'s SS-ForallR arm needed `dom_subset_ftvar_in_aenv`).
4. ⭐ **SE-FlexR's subject must be `nonghost_pskl`** (2026-08-04) — a
   FINDING on the authors' own rule, see §5.

---

## 3. What is green (Qed, `Closed under the global context`)

`def_extra` · `prop_swap` · `prop_solve_sub` · `prop_looksub` ·
`prop_sub_sound` · `prop_decorate_sub` · `prop_decorate_key` ·
`test_examples` · `cex/cex_solve_sub_wf_leak` ·
⭐ **`cex/probe_flexr_repair`**.

⭐ **`a_sub_sound_thm` — subtyping soundness holds under the repaired rule,
and its STATEMENT DID NOT MOVE.** Every new obligation is absorbed inside
the proof out of wf premises the theorem already had.

⭐⭐ **`cex/probe_flexr_repair.v` — the repair WORKS at the refuting
configuration** (Qed, axiom-free, and self-contained: it rests on nothing
but `algo/def_extra.v`, so it stays checkable while the cluster is broken):

| lemma | negates |
|---|---|
| `new_solve` — the solve yields `∀γ.γ→γ`, not `∀_.f̂` | `probe_solve_det` |
| `new_extract` — the extract returns it, empty suffix | `probe_extract_det` |
| `new_run_exists` — a full `a_sub` run EXISTS | `probe_no_run` |

The decisive step: `guess^TY(β→β) = (·; β→β)` — no ghosts, so nothing is
invented and nothing is lost, and the close re-binds a REAL occurrence.

### Retracted (Coq text at `d5f9169`)

⚙ These files' bodies were replaced by retraction HEADERS at the time; the
headers themselves were removed 2026-08-06 (`18cc7e4`) once they were the
whole file.  Their narrative now lives in **`docs/PAPER-GAPS.md`, "WHERE THE
RETRACTED FILES WENT"**; the proof text is still at `d5f9169`.

- `cex/probe_double_occ_run.v` — everything in it, including
  `p6l_look_completeness_fails`, `probe_no_run`,
  `probe_motive_instance_false`, `probe_main_forall_false`.
- `cex/cex_thm_complete_subtyping.v` — `thm_complete_subtyping_false`.
- `cex/probe_solve_flexr.v` — SUPERSEDED, not false: its
  `run_exists_at_correct_instantiation` is literally the TAIL of
  `new_run_exists`.

⭕ **`main_forall` is therefore OPEN again**, not known-false. That is the
whole point of §6 Step 3.

---

## 4. The idioms this campaign discovered — reuse them

### (a) The witness-move is a SWAP, not a rename

**The single most important thing to know.** The freshness-campaign proofs
move a rule's binder `b` out of the way by a double RENAME, whose side
condition is "the source dodges the context". `b` now sits **in** the
premise's context, so that can never hold — it was never a rename.
Equivariance has no such condition (it carries the context along), and that
is harmless because every consumer quantifies the context universally.

Packaged in `prop_solve_sub.v`: `a_solve_eq_move_binder`,
`a_solve_eq_move_binder_tophole_l` / `_tophole_r`,
`a_solve_sub_move_binder_l` / `_r`. The moved premise runs at
`(α0 ~ tvar) ++ swap_aenv b α0 Θ` — and with §2(3) that context collapses to
`Θ`, since the rule now gives `b ∉ ftvar_in_aenv Θ`. Supporting:
`swap_pskl_as_subst`, `swap_aenv_one_tvar`, `swap_aenv_fresh_id`
(`prop_swap.v`). `a_solve_{sub,eq}_rename_var` were re-derived from
equivariance: **540 lines became 15.**

### (b) `pskl_top_guarded` is the wf discipline that pays for everything

The repaired row can return a `∀` where the old one returned a variable.
Wherever a proof needed "the output is guarded-headed", route through the
**SUBJECT** instead, where `pskl_top_guarded (∀◇P)` gives it. Not a new
side condition: `a_wf_pskl_top_guarded` derives it from the paper's own
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

## 5. Findings for the authors (all now in `docs/PAPER-GAPS.md`)

1. **Soundness survives with its statement unchanged** — the repair costs
   nothing at that interface. `dec_ext_guess_source` (the one real
   obligation) holds because `guess^TY` only ever loses information.
2. ⚠️ **`nonflex(P)` must also exclude a GHOST subject.** Under the old row
   the overlap with SE-GhostL was harmless — `◇ ∼ α̂` gave `α̂` either way.
   Under the repair they DISAGREE: `guess^TY(◇)` invents a FRESH `α̂1`, so
   FlexR returns `α̂1` where GhostL returns the target, and the sharing that
   puts the marker's solution on `α̂` is lost. The reference implementation
   never takes that branch — `solve_eq` is a **match**, and both ghost rows
   (`Ghost, q` at `type.ml:412`; `UGhost p, q when is_guarded q` at `:457`,
   and `is_guarded (MFlex _) = true`) precede FlexR at `:466`. Rendered as
   the premise `nonghost_pskl P` (`frost/def_extra.v`). It costs
   completeness nothing and it keeps `a_solve_eq_hole_subject_inv` — the
   fact the paper uses silently in every `P_i = □` subcase — TRUE.
3. **The binder rows need `ftvar(Θ)`, and the sibling rows must thread** —
   §2(2), §2(3).
4. `solve_eq_guarded_r_head` is FALSE and is deleted (its entire content was
   the old `SolE-FlexR`). The guarded-**subject** twin survives via
   `a_guess_mono_guarded`.

### Cleanup done this session (user asked for it)

- **`a_solve_eq_weaken_tvar{,_size}` DELETED** — a ~130-line size induction
  with **zero consumers**, and none at the pre-repair baseline `d5f9169`
  either. What the tree actually calls is the MID-BLOCK twin
  `a_solve_sub_eq_weaken_mid_flex_size` (P6-Cs), a different statement.
  A `RESTART NOTE` at the old site records the repaired statement it would
  need (`β ∉ dom Ξ`, else FALSE) if a consumer ever appears.
- **`a_solve_sub_eq_ctx_change` lost its `dom Θ' ⊆ dom Θ` premise** — after
  §2(3) nothing in the solve cluster reads `dom Θ`, so it was dead weight.
  The lemma is now strictly stronger; the two `strengthen_tvar` corollaries
  lost a bullet each.
- **`probe_solve_flexr.v` retired as SUPERSEDED** — subsumed by
  `new_run_exists`, and it sat behind the completeness cluster where the
  replacement does not.

⭕ **Still to reconsider at Step 3 below**: `sub_shield`, `flex_apart_walk`,
`flex_apart_deep`, and the whole `ss_walk` machinery. These were invented as
the mech's repair of `lemma:complete-look` — *the very lemma the repaired
rule may now make provable as stated*. Do not delete them speculatively;
delete them when P6-L goes through without them.

---

## 6. NEXT STEPS, in order

### Step 0 — SETTLED: the guess stays `guess^TY`

Follow the authors' row literally.  A sort-parametric `guess^N` (degenerating
at `SK` to the pattern verbatim) was considered and **rejected**: there is no
evidence of a problem, only the observation that `guess^SK` is the identity
while `SolE-FlexR` names `TY` unconditionally, and the `SK` + bare-flexible-
target case has never been shown reachable.  Nothing goes to
`docs/PAPER-GAPS.md` for this — speculation is not a finding.

⚙️ Keep it in the back of your mind while doing Step 1 only in this sense:
**if** the P6 construction actually gets stuck because a solve output at
`N = SK` has been partly monomorphised (ghosts filled with fresh flexibles,
`∀◇` dropped) where the ideal keeps them, that is the concrete obstruction,
and indexing the three solve judgements by `N` is the ready fallback.  Until
then, no action.

### Step 1 — the P6 cluster — ✅ **DONE.  ALL FIVE LEMMAS GREEN.**

`make coq` is clean.  P6-Cv, P6-Cs, P6-Sv, P6-Ss and P6-L are all `Qed` and
`Closed under the global context` under the authors' repaired rule, and so is
Step 2 (`prop_sub_complete_thm.v`).  **The front is now Step 3.**

#### ⭐ What the cluster cost, in one place

ONE new premise everywhere: `ftvar_in_uskl ψa [<=] dom Θ` (at the fixed `Θw`
in the generalized statements).  The repaired `SolE-FlexR` reads the SOLVE
block's payloads off the ideal guess, so they are well-formed only if it is,
and it is NOT derivable — when α does not occur in `κR` the subject never
mentions ψa.  Registered in `docs/WF-SIDE-CONDITIONS.md`.
⚠️ It is **not invariant in P6-Sv** (whose ForallL row moves the guess to
`open ψsrc β`, β a fresh rigid absent from `Θw`) and P6-Sv does not need it.
Its ρ-side companion `Δρ ∩ dom Θw = ∅` IS invariant everywhere, and is the
only handle making the SOLVE block's payloads Δρ-clean.

#### ⚠️⚠️ THE ONE TRAP THAT COST THE MOST TIME — read before writing a call

`L` is the LAST ∀-bound variable of every repaired statement.  A premise slot
filled by `ltac:(… fsetdec)`, or reached through a `solve [… fsetdec …]` list,
therefore runs against a goal whose `?L` is still an EVAR — and **fsetdec on a
goal with a set metavariable does not terminate in any useful time**.
Measured: one such call took `prop_look_complete_sub_cstr.v` from 5 s to
>200 s; a second pair took it to >900 s; the same shape with `eapply
ad_ppre__arrow`'s tag evars hung a three-lemma probe outright.  Fixes:
(i) NAME the avoid-set in an `assert` before the call, so `exact` instantiates
`?L` structurally; (ii) put `exact HLav` FIRST in every `solve` list;
(iii) PIN evar-valued tag sets — `apply ad_ppre__arrow with (Ψ1 := …)`.
Related: never use `simpl; clear - H; fsetdec` as a `solve` alternative —
a one-step lemma (`in_dom_app_r`) replaced eleven of them and took another
file from minutes back to 20 s.

#### ⭐⭐ THE REPAIR RETIRES TWO OF OUR OWN COUNTEREXAMPLES

`cex_p6_flex_counterpart.v` and `cex_p6sv_forall_flex.v` both refuted a
`-var` lemma by the SAME step — the old row discarded the accumulated
pattern, forcing the answer to be the flexible.  The repaired row returns
`guess^TY(P)`, and at both configurations `P` is ghost-free, so the answer IS
the pattern: `c → ⟨⟩` instead of `β̂` (the obligation becomes reflexivity),
and `∀β.β→β` instead of the vacuous `∀_.f̂`.  Machine-checked in
⭐ `cex/probe_flexr_neutralises_p6.v` (Qed, axiom-free, self-contained); both
files now carry retraction headers, their proof text at `d5f9169`.
Recorded in `docs/PAPER-GAPS.md` and `docs/refutations.tex` §Status ¶5.

⛔ **This does NOT license dropping `sub_shield`** — it was invented as the
repair of the second of these, and P6-Sv/P6-Ss/P6-L still carry it.  A dead
witness is not a proof.  It does make Step 3 much more likely to succeed, and
it tells you WHERE to start: re-prove P6-Sv without the premise and see what
the ∀-over-flexible row actually needs now.

⭐⭐ **P6-Cs (`prop_look_complete_cstr.v`) IS GREEN** — `Qed`, `Closed under
the global context`, both the generalized theorem and the paper-facing
corollary. What the arrow merge and the ∀ rows cost is recorded in
"HOW P6-Cs WAS CLOSED" below; the five ∀ rows there are the TEMPLATE for
P6-Sv's and P6-Ss's, which have the same shape line for line.

#### ⭐ HOW P6-Cs WAS CLOSED (2026-08-05) — the reusable half

**The arrow row.** Its right IH runs at `Ξs1 ++ Ξc1 ++ Θ0` under
`κs1 ++ κc1 ++ κ`, not at `Ξc1 ++ Θ0`: `Pa1` is the LEFT SOLVE's output and
mentions the flexibles solve invented, so the precision the right branch
consumes is stated under all three blocks, and the only context at which that
is an `a_inc` is `Hinc1` verbatim. Everything it returns is permuted into the
conclusion's `Ξs2 ++ Ξs1` / `Ξc1 ++ Ξc2` order; **the permutation is free**,
because `binds` over an append is plain membership — `binds_rot_app`,
`binds_rot_app_rev`, `binds_app_perm5`, all proved by `analyze_binds` alone.
The `a_inc` is REBUILT from `Hκ` by four `a_inc_flex_prefix_build` steps
rather than permuted, and the precision's κ-reordering is a lookup-level
identity on pairwise-disjoint blocks (new `msubst_lookup_app_congr` +
`msubst_lookup_ftv_app`, both in `prop_look_complete_cstr.v` §1).

⭐ **ONE NEW PREMISE, forced by that row and by nothing else:**
`Δρ ∩ dom Θw [=] empty`. The right IH must re-establish the shielded-ftv
premise under the bigger metasubstitution, i.e. that a ρ-replaced variable
misses every image. For `κc1` that is the `Forall … ∩ Δρ = ∅` CONCLUSION; the
SOLVE block has no such conjunct **and cannot get one** — the LE-Var row reads
`κs` off P6-Cv, whose package carries no ftv bound at all — so the only handle
is its payloads' well-formedness at the FIXED `Θw`. Δρ and Θw are both
constant inside P6-Cs, so it threads unchanged; vacuous at the ρ = identity
corollary; P6-Ss's Sub-ForallL maintains it because the fresh rigid it adds to
Δρ is picked fresh for Θ ⊇ Θw. **Add this premise to P6-Sv and P6-Ss too.**
A proof-construction fact, not a paper finding.

**The ∀ rows (five, incl. the two ε-tagged mirrors).** `Θw` does NOT move;
keeping it fixed is exactly what lets β be stripped from the `a_inc`, since
the SOLVE payloads' only β-freeness argument is `a_wf_ptyp Θw` plus
`β ∉ dom Θw` (`aenv_binds_dom_sub Hmon`). Their IH runs at `add β L`, which is
what makes `β ∉ dom Ξs` available — needed both by `HβPa` (the solve's ftv
bound now carries a `dom Ξs` term) and by the strip.
`a_inc_strip_tvar_mid` peels BOTH blocks at once (`Ξ := Ξs ++ Ξc`,
`κa := κs ++ κc`).

**The corollary** gained the avoid-set parameter `L` and one further
paper-external wf side condition, `ftvar_in_uskl ψa [<=] dom Θ`: the repaired
`SolE-FlexR` reads the solve block's payloads off the ideal guess, and when α
does not occur in `κR` the subject does not mention ψa at all, so the
subject-wf premise says nothing about it. Registered in
`docs/WF-SIDE-CONDITIONS.md`.

#### ⭐ THE `solve_sub_ext` KIT (new, `prop_look_complete.v`)

The SUBTYPING twin of `solve_ext`, with the glue lemmas `solve_sub_ext_nil` /
`_step` / `_post` / `_post_solve` / `_of_eq`. Two differences from the eq one:
the judgment carries a MODE, and **the package includes the OUTPUT's
well-formedness at `Ξ ++ Θ0`** — on the sub side that is a genuine conclusion
of the completeness lemma rather than a derivable fact (there is no "solving
preserves wf" once SS-ForallR is faithful: `cex/cex_solve_sub_wf_leak.v`).
`_of_eq` lifts a whole eq package through SolS-Check in one step, which is
what P6-Sv's Check row wants.

#### ⚠️ FOUR TRAPS THE P6-Sv CONVERSION HIT (they will recur in P6-Ss)

1. **The five binder rows avoid `ftvar_in_aenv Θ`, not `dom Θ`** (§2(3)), so
   every ltac pattern `?b `notin` (dom _ `union` _)` stops matching. Match
   `?b `notin` ?S` with a `match S with context [ftvar_in_aenv _] => idtac end`
   guard, and derive "a context variable is not this binder" through
   `dom_subset_ftvar_in_aenv` (packaged as `solve_binder_apart_dom`).
2. **The binder rows and the threading rows run their premise at a GROWN
   context**, so an `β0 ∈ dom Θ` premise has to be weakened. Use the one-step
   `in_dom_app_r` — ⚙️ `solve [ … | simpl; clear - H; fsetdec | … ]` at eleven
   sites turned the file into a **multi-minute** build.
3. **`a_solve_{eq,sub}_ftv`'s bounds grew a `dom Ξ` term**, and at every
   consumer it must be ELIMINATED, not absorbed: a generated name dodges
   everything the context MENTIONS. Packaged as `solve_eq_generated_not_dom`.
4. **A new SE-FlexR case appears in every induction over the solve** — the
   output is `guess^TY`'s PAINT. `pskl_shielded_ftv_ptyp_to_pskl` (a paint
   shields nothing) closes it in the unshielded lemma; elsewhere the paint's
   hole-freedom is the useful fact.

#### What is green and committed

`prop_look_complete.v`, ⭐ **`prop_look_complete_var.v` (P6-Cv)** and ⭐⭐
**`prop_look_complete_cstr.v` (P6-Cs)** all compile, `Qed`, `Closed under the
global context`. `a_sub_sound_thm` and the whole soundness chain are unchanged
and still green
(`make -j10 -f CoqMakefile frost/algo/prop_decorate_key.vo`, ~15 s warm).

#### ⭐⭐ HOW THE ∀-ROW PAYLOAD-SCOPE OBLIGATION WAS CLOSED — read this first

It is the one thing the previous hand-off got wrong, and the correction is
reusable in every downstream file.

The witness reports the extension's payloads well-formed in `Θw`; a row has
the counterpart monotype only at `Θ`, which under a ∀ row is `Θw` plus bound
rigids. The transport is three steps, and **the point is that both ftv bounds
are over the context's DEFINITIONS, never over a domain** — a rigid binder
carries no definition, so it can never enter either bound:

```
  ftv (ψa1 → ψa2) ⊆ ftv (Q1 → Q2) ∪ dom Θw   consis_subject_ftv_defs_bound
  ftv (Q1 → Q2)   ⊆ dom Θw                   ad_refine_mono_paint_ftv_bound
  a_wf_ptyp Θ τ + ftv τ ⊆ dom Θw ⟹ a_wf_ptyp Θw τ
                                             a_wf_ptyp_mono_strengthen_dom
```

⚠️ **The route through `dom Θr` this hand-off used to prescribe does NOT
work.** "A ∀ row's binder joins Θtv, never Θr" is false: `forall_syn_tagged`
puts its binder on the Θr side (`aenv_split_cons_r`, `prop_look_complete_var.v`
≈ 2250), so `dom Θr ⊆ dom Θw` is not invariant. `dom Θw` is what both bounds
actually land in, and the middle lemma is what shuts the refinement's hole
rule — whose fill is only `dom Θ`-scoped, and a mono paint has no hole.

⚠️ **And the prescribed new premise `κ ∷ Θ0 ⊑ Θw` is NOT invariant either** —
a ∀ row's binder is rigid in the extended `Θ0` but absent from `Θw`, and
`a_inc__tvar` cannot produce it. What IS invariant, and is the premise the
theorem now carries, is the weaker IMAGE bound

```coq
  (forall α, a_flex_tvar Θ0 α ->
     ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θw)
```

preserved by `a_flex_tvar_strip_tvar`, and at the top-level call just
`a_inc_lookup_flex_ftv_dom` on `Hκ` with `Θ = Θw` — so the paper-facing
statement pays nothing. **Add this premise, in this form, to every downstream
P6 statement that carries `Θw`.**

#### ⚙️ Three things the ∀ rows cost, beyond the obligation

1. **The IH's avoid-set is `add β L`, not `L`.** The block is emitted OUTSIDE
   the ∀ and the fold renames the binder, so the row's own binder must be
   dodged — otherwise `α ∉ dom Ξ` (needed by `FOLD`, and by
   `msubst_pskl_subst_var`) is unavailable. It costs nothing: the IH's
   avoid-set premise is `ftvar_in_aenv ((β ~ tvar) ++ Θ0) [<=] L`, which needs
   `β ∈ L` anyway.
2. **The ∀ rows no longer call `a_solve_eq_strengthen_tvar`.** SE-Forall,
   SE-GhostForall and SE-ForallGhost run their premise at `(β ~ tvar) ++ Θ`
   now (decision §2(1)), so the IH's output IS the rule's premise. SE-UnivGhost
   has no binder of its own and still needs the strengthening.
3. **Every binder row's avoid-set needs `ftvar_in_aenv Θ0`**, not just
   `dom Θ0` — §2(3). Add it to each `pick fresh` union; the failure mode is a
   bare `Not solvable by [solve_notin]` on the rule's freshness premise.

#### The FOLD generalization (both ∀ blocks, and every downstream twin)

`FOLD` takes the body's extension `κ0` as a parameter and runs under
`κ0 ++ κ`. The two facts it needs of the prefix are read straight off the
package's `Forall` component: local closure via `msubst_lc_app_wf`, and
`dom Θ`-scoping via `forall_wf_mono_images_dom` + `aenv_binds_dom_sub`
(`dom Θw ⊆ dom Θ`).

#### ⭐ The five reusable pieces that now live in `prop_look_complete.v`

Read these before touching any downstream file; four of the five did not
exist when the campaign started, and they are what makes the remaining work
mechanical.

| name | what it buys |
|---|---|
| `solve_ext` + `solve_ext_nil` / `_step` / `_post` / `_post_solve` | the κ-extension package as ONE definition parameterised by a post-condition. Every P6 statement is `solve_ext … Post`; the glue lemmas cover every row that is not the arrow merge or SE-FlexR itself. `_post_solve` keeps the SOLVE derivation in hand (P6-Cv's var row reads hole-freedom off it). |
| ⭐ `a_guess_mono_ctx_change` | `guess^TY` reads its context ONLY as an avoid-set, so it transports to a **growing** context too, provided the block it generated dodges what the new context mentions. `a_guess_mono_ctx_shrink` had only the shrinking half. The ∀ case re-picks by SWAP. |
| ⭐ `a_solve_sub_eq_weaken_mid_flex_size` (+ `a_solve_eq_weaken_flex_block`) | moved up from `prop_look_complete_cstr.v` and repaired: the block threads, there is a NEW premise `dom Ξm ∩ dom Ξ = ∅`, and the six ∀ rows re-freshen by `a_solve_*_move_binder*` instead of the double rename. |
| `a_inc_flex_prefix_split` / `_build`, `all_flex_mono_decls`, `all_flex_mono_ftvar_in_aenv`, `a_wf_aenv_prepend_flex_block` | prepend an aligned wf-mono block to an `a_inc` and to its source context. |
| ⭐ `ad_pat_consis_mono_subject_wf` | where the κ-extension's wf obligation comes from: a mono-paint consistency SUBJECT is wf in the context, because consistency's `var` row carries `a_binds_tvar` and its `flex_l` row carries the definition. **No new external side condition.** |
| ⭐⭐ `consis_subject_ftv_defs_bound`, `ad_refine_mono_paint_ftv_bound`, `a_wf_ptyp_mono_strengthen_dom`, `a_binds_tvar_strengthen` | the Θw TRANSPORT (2026-08-04) — the three-step chain above. Write the same three lines inside each downstream file's own `FLEX` block. |
| `aenv_binds_dom_sub`, `forall_wf_mono_images_dom`, `a_inc_lookup_flex_ftv_dom`, `msubst_lc_app_wf` | reading the package: domain inclusion from binds inclusion, the payloads' `dom Θ`-scoping, the top-level supply of the new image-bound premise, and local closure of `κ0 ++ κ`. `msubst_lc_app_wf` MOVED UP from `prop_look_complete_extract.v` §8 (the copy there is deleted). |

#### ⭐ TWO IDIOMS THE ARROW CASE CAN USE — pick the cheaper one

The two branches of an arrow must end up at DIFFERENT contexts, because
`SE-Arrow` threads (`Θ` and `Ξ1 ++ Θ`).

1. **Re-parameterise** the second IH over `Θ0` — what `a_solve_eq_cv_mono`
   does. Costs `a_inc_flex_prefix_build`, `a_wf_aenv_prepend_flex_block`,
   `a_wf_pskl_app_weaken` and a `ftvar_in_aenv` bound. Use it when the IH
   already quantifies the context and carries few context-indexed premises.
2. ⭐ **Weaken the second branch's SOLVE** with
   `a_solve_eq_weaken_flex_block` — what P6-Cv's CORE does. Much cheaper
   when the statement carries many context-indexed premises
   (`aenv_split`, `flex_apart`, `rho_fresh`, …), because NONE of them move.
   **Prefer this in the four remaining files.**

Either way the avoid-sets are the same: the first IH runs at
`L ∪ ftv Pi1 ∪ ftv Pi2 ∪ ftv P01 ∪ ftv P02`, the second at that `∪ dom Ξ1`;
the merged block is `Ξ2 ++ Ξ1`, the merged extension `κb ++ κa`, and the two
`msubst_pskl_mid_skip` equations are read off `a_solve_eq_ftv`.

#### ⭐ TWO FACTS ABOUT THE REPAIR THAT KEEP RECURRING

- **`guess^TY`'s output is a PAINT, hence hole-free.** So its precision is
  Δ-MONOTONE (`ad_ppre_no_hole_subject_delta_mono`) and no Δ-freshness side
  condition is needed at an SE-FlexR node. It is also why
  `a_solve_eq_no_hole_p0` is still true — for a better reason than before.
- **A ghost subject pins the block to `nil`** (`a_solve_eq_hole_subject_inv`,
  true only because of finding 2's `nonghost_pskl`). Every `Pi = □` row is
  therefore a `solve_ext_nil` row, and its extension is `nil` too — get that
  from `keys κ' = keys nil` by `destruct κ'; [ | discriminate ]`.

#### ⭐ THE ∀ ROWS' PAYLOAD SCOPE — ✅ SETTLED AND CLOSED

A P6 ∀ row runs its body at `(α ~ tvar) ++ Θ`, but the block the body
generates is emitted **outside** the ∀ — the solve's ∀ rows pass `Ξ` through
unchanged — so a payload mentioning the bound rigid would be ill-scoped, and
`a_inc_flex_prefix_build` could never rebuild the increase.  (Do NOT weaken
the package's wf component to dodge this; P6-L needs it.)

**Design (committed, green):** `solve_ext`'s second context is the
WELL-FORMEDNESS context `Θw`, and it stays FIXED as the construction goes
under binders.  `a_guess_ty_witness_mono`, `cv_mono_concl`,
`a_solve_eq_cv_mono` and `a_solve_eq_cv_var` all carry it, next to the two
conditions that say `Θ` is `Θw` under a stack of rigids — binds-monotonicity
one way, "adds only rigid binders" the other.  Supporting: `a_def_chain_wf_at`,
`forall_wf_mono_weaken`.

⭐ And the target's own wf premise is a DISJUNCTION —
`a_wf_ptyp Θw τ ∨ (τ is a rigid variable of Θ)` — because at a ∀ row the
target can be the BOUND rigid, which is in no `Θw`.  It costs nothing: every
branch that consumes the premise first unfolds a definition chain out of `τ`,
and a rigid has none (`a_def_chain_rigid_var_inv`).  The disjunction
PROPAGATES along a chain (`a_def_chain_wf_or_rigid`) and is DISCHARGED at the
arrow rows.  P6-Cv's var row supplies it straight from `ad_pat_consis__var`.

✅ **The residual derivation is CLOSED (2026-08-04)** — but *not* by the route
this section used to prescribe, which was wrong twice over: the `dom Θr` chain
is not invariant (`forall_syn_tagged` puts its binder on the Θr side) and
neither is the premise `κ ∷ Θ0 ⊑ Θw` (a ∀ row's binder is rigid in the extended
`Θ0` but absent from `Θw`).  See **"HOW THE ∀-ROW PAYLOAD-SCOPE OBLIGATION WAS
CLOSED"** at the top of this Step for the version that works, and copy that
into each downstream file's `FLEX` block.

✅ **`prop_look_complete_cstr.v` (P6-Cs) IS GREEN — see "HOW P6-Cs WAS
CLOSED" at the top of this Step.**  Its conclusion carries a SECOND block `Ξs`
beside `Ξc`, at `Ξs ++ Ξc ++ Θ0`, with the extensions stacked the same way and
an avoid-set parameter `L`; the order is forced by `a_extract__solve`
(`def_extra.v:764`), P6-L's consumer.  Three things had to be added beyond the
first design, each from a concrete obstruction rather than a guess:

| addition | forced by |
|---|---|
| the **`Θw` pack** (wf, the two binds conditions, the κ-image bound) | the ∀ rows strip β from the `a_inc` with `a_inc_strip_tvar_mid`, whose `Forall (β ∉ ftv)` premise `κc` gets from its `ftv ⊆ ftv ψa` conjunct and `κs` has no analogue for.  Hence also ⭐ **`a_solve_eq_complete_var_at`** — the paper-facing `a_solve_eq_complete_var` pins `Θw := Θ` and is unusable under a binder |
| `ftvar_in_uskl ψa [<=] dom Θw` | the flexible-P0 row: there `ψa` is the mono paint `syn τψ` and `τψ` IS the κs payload |
| `all_flex_mono Ξs`, `uniq Ξs`, and ⭐ `Δρ ∩ dom Θw [=] empty` | the arrow row rebuilds `a_wf_aenv (Ξs ++ Ξc ++ Θ0)` for its right branch (`uniq Ξ` is not re-derivable, §4c) and must re-establish the shielded-ftv premise under `κs1 ++ κc1 ++ κ` |

⭐ **The flexible-P0 row — the only place `SE-FlexR` itself fires** — is the
template for the downstream files: `WIT` wraps `a_guess_ty_witness_mono` at
`κ := (α1, τψ) :: κ`, and `msubst_pskl_prepend_fresh` is what lets the fresh
`α1` be prefixed without moving `msubst κ Pi`.  ⚠️ The `Pi` grid is **six**
ways, not two: unit / arrow / ∀ take SE-FlexR at the guess; a VARIABLE takes
SE-Var; `◇` takes SE-GhostL and returns the TARGET — the sharing
`nonghost_pskl` protects; and `∀◇P` peels by SE-GhostGuarded onto a body that
wf forces GUARDED, hence nonghost, so one peel always lands on a
SE-FlexR/SE-Var node.  That peel needs the precision unfolded and re-folded
along a DEFINITION CHAIN — `ad_ppre_tophole_subject_chain_inv` one way, the
new `ad_ppre_def_chain_fold` the other.

The nine moved-up copies are deleted (one `⚙️ MOVED UP` note in their place),
and the four lemmas that stay there are threaded —

| lemma | what changed |
|---|---|
| `a_solve_cstr_app` | threads: the second half runs at the first's block, outputs concatenate `Ξ2 ++ Ξ1` |
| `a_solve_cstr_ctx_change` | threads; its condition is `ftvar_in_aenv`, not `dom`, and the eq row's tail needs the two new `a_flex_tvar_app_mono` / `a_flex_app_anti` lifts |
| `a_solve_cstr_weaken_mid_flex` | threads + the new `dom Ξm ∩ dom Ξ = ∅` premise |
| `a_solve_cstr_strip_tvar_mid` | threads |

New upstream, for P6-Cs and everything below it: `a_solve_cstr_decls` /
`a_solve_cstr_generated_fresh` (`prop_solve_sub.v`) and
`a_decls_all_flex_mono` (`prop_look_complete.v`).

⚠️ `aenv_app_assoc` (= `list_app_assoc`) is `(X ++ Y) ++ Z = X ++ (Y ++ Z)`,
the OPPOSITE orientation to the stdlib `app_assoc` metalib shadows here; a
bare `rewrite app_assoc` fails with "found no subterm".  Use the named one
with explicit arguments — that is what the whole arrow row does.

#### The rest of the cluster

`prop_look_complete_sub_var.v` (P6-Sv, THE FRONT) →
`prop_look_complete_sub_cstr.v` (P6-Ss) → `prop_look_complete_extract.v`
(P6-L).

### Step 1 (original notes; the plan above supersedes the status lines)

`prop_look_complete.v` (4.8k) → `prop_look_complete_var.v` (P6-Cv) →
`prop_look_complete_cstr.v` (P6-Cs) → `prop_look_complete_sub_var.v` (P6-Sv)
→ `prop_look_complete_sub_cstr.v` (P6-Ss) → `prop_look_complete_extract.v`
(P6-L). Nothing downstream of `prop_look_complete.v` has been compiled since
the change; `make -k coq` stops there.

⭐ **The real content is NOT threading `Ξ`.** Every P6 statement produces a
metasubstitution `κ` with `κ ∷ Θ0 ⊑ Θ`, and that `κ` must now be
**extended over the solve's new flexible block**. A conclusion of the shape

```coq
exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\ Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψ ] ψa
```

becomes, positionally,

```coq
exists Ξ Pa κ',
  Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa /\
  all_flex_mono Ξ /\ uniq Ξ /\ keys κ' = keys Ξ /\
  (forall α, α `in` dom Ξ -> α `notin` L) /\
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
  Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψ ] ψa
```

**The template already exists**: `a_guess_ty_witness`
(`prop_look_complete_extract.v` §9) builds exactly such an extension for the
final guess's `Ξ'`, with an avoid-set parameter `L` and a `Hfr'` output, and
its ∀ case shows why the `L` must be fixed *before* the witness is picked.
Copy its shape for the solve's block; the homogeneous-flex REORDER KIT in
`prop_look_complete_cstr.v` moves between block orders (all three blocks are
undefined flexibles, so order is semantically immaterial but not
syntactically so).

#### ✅ `a_guess_ty_witness_mono` IS PROVED — what is left is plumbing it

**Done** (commit `9322ea5`): the lemma below is `Qed`, together with
`ad_ppre_mono_refl` (precision is reflexive at a monotype), `a_def_chain_wf`
(wf transports along a definition chain) and `list_app_assoc`. The
κ-extension kit (`keys`, `keys_eq_dom`, `all_flex_mono`, `all_flex_mono_app`,
`msubst_pskl_mid_skip`, `msubst_lookup_mid_skip`,
`msubst_pskl_lookup_congr_ftv`) was **moved upstream** to
`frost/algo/prop_metasubst.v` — both its old homes sat *below* the file that
now needs it.

**In progress**: `a_solve_eq_cv_mono` is restated (`cv_mono_concl` names the
new conclusion; `cv_mono_nil` / `cv_mono_wrap` are the packaging helpers) and
three of its twelve sites are converted, including ⭐ the SE-FlexR one that
motivated the whole lemma. It currently fails at the `P0 = arrow` case,
whose two IHs must have their extensions MERGED — the merge is line-for-line
the one already written in the witness's own arrow case (`Heq1`/`Heq2` via
`msubst_pskl_mid_skip`, disjointness from the second IH's widened avoid-set);
copy it. The remaining ~8 sites are `∀◇` pass-throughs, which is exactly what
`cv_mono_wrap` was written for.

⚠️ Two mechanical traps that cost time here: `Set Implicit Arguments` is on
in this file, so partially-applied lemmas want `@name ...`; and `/\` at the
END of a line inside a Python heredoc is a line-continuation — it silently
eats the conjunction. Edit with a raw string or keep `/\` mid-line.

#### The lemma, for reference — `a_guess_ty_witness_mono`

Established by working the first three sites (2026-08-04).  The κ-extension
is **not** needed uniformly; it is needed exactly where `SE-FlexR` fires with
a subject that can carry a ghost.  Concretely:

* `p6cv_close_leaf` — closes by SE-Var. `Ξ := nil`. ✅ **DONE**
* `a_solve_eq_cv_unit` — target `1`, so the subject is `1`/var/◇/∀◇.
  `guess^TY(1) = (·; 1)`. `Ξ := nil`. ✅ **DONE**, and the repair made it
  *simpler*: the old proof's witness was the flexible `α̂` and needed the
  whole `ad_refine_inh_unit_ppre` detour through the refinement; the new
  witness is `1` and the obligation collapses to `ad_ppre__unit`.
* `a_solve_eq_cv_mono` — ⛔ **HERE IT BITES.**  In the `Pi = Pi1 → Pi2`,
  `P0 = β̂` branch, `SE-FlexR` is the *only* applicable rule (SE-Var needs a
  variable subject, SE-Arrow needs an arrow target), and `guess^TY` of an
  arrow subject genuinely invents flexibles for its holes.

So write this first — everything downstream is a consumer of it:

```coq
Lemma a_guess_ty_witness_mono : forall n Θ0 Θ κ Δ Ψi τ Pi,
  size_pskl Pi <= n ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> κ ∷ Θ0 ⊑ Θ -> mono_ptyp τ ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ) ->
  forall L, exists Ξ A κ',
    (forall Θg, ftvar_in_aenv Θg [<=] L -> a_guess_mono Θg Pi Ξ A) /    all_flex_mono Ξ /\ uniq Ξ /\ keys κ' = keys Ξ /    (forall α, α `in` dom Ξ -> α `notin` L) /    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /    Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) (ptyp_to_pskl A))
            ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τ).
```

It is `a_guess_ty_witness` (`prop_look_complete_extract.v` §9) with the
precision judgment `⊑ᵖ` in place of `⊳`/`⊑`, and it should be *easier*: the
target is a MONOTYPE, so at a `◇` the extension reads the monotype off that
position and the obligation becomes reflexivity-at-mono
(`ptyp_to_pskl τ0 ⊑ᵖ[∅] ptyp_to_uskl_syn τ0`) rather than a refinement
step.  `ad_ppre__hole` (a ghost is precise into ANYTHING, at `Ψ = ∅`) is what
licenses the descent.  Copy §9's shape — the `L`-bounded context
quantification is what makes the ∀ case provable, and the freshness output is
what lets the arrow case merge two extensions without them colliding.

Then the statements become

```coq
exists Ξ Pa κ', Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa /\ <the Ξ/κ' package above> /  Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi ] …
```

and the arrow case of `a_solve_eq_cv_mono` merges the two IHs' extensions,
which is exactly where the freshness component earns its keep.

**Known repair sites in `prop_look_complete.v`** (the IDE lists them as
`Syntax error: '⨾' expected`, which is a reliable way to enumerate them):

| lemma | what changes |
|---|---|
| `a_solve_eq_hole_subject_inv` | ✅ DONE — now `Ξ = nil /\ P' = P`; stays true only because of finding 2 |
| `a_solve_eq_wf` | ⛔ statement must move to `(Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P'` — the output may mention the generated block. Needs a new `a_guess_mono_wf : a_guess_mono Θ P Ξ A -> Θ ⨟ Δ ⊢ₚₛᵃ P -> (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ (ptyp_to_pskl A)`; the ∀ case needs an `a_wf_pskl` *strengthening* that drops a rigid already present in `Δ` |
| `p6cv_close_leaf` and the five `exists Pa, …` statements at (pre-edit) lines 1393/1574/2396/2601/2670/4662 | the κ-extension above; all six close by SE-Var, so `Ξ := nil`, `κ' := nil` — they are the CHEAP ones, do them first to fix the shape |

⚙️ A general lemma worth writing early, because it subsumes
`a_guess_mono_ctx_shrink` and is what the whole guess kit really says —
**`a_guess_mono` reads its context ONLY as an avoid-set**:

```coq
Lemma a_guess_mono_ctx_change : forall n Θ Θ' P Ξ A,
  size_pskl P <= n -> a_guess_mono Θ P Ξ A ->
  (forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ') ->
  a_guess_mono Θ' P Ξ A.
```

Size induction; the ∀ case re-picks δ fresh for
`ftvar_in_aenv Θ' ∪ ftv P ∪ dom Ξ ∪ ftv A ∪ {b}` and moves the witness by
swap (`swap_aenv b δ Ξ = Ξ` by (K3) + `_generated_fresh_binder`;
`swap_ptyp b δ A = [δ/b]A`; `close δ ([δ/b]A) = close b A`). Note the IH's
target is arbitrary, so `swap_aenv b δ Θ` never has to collapse — this one
does **not** need §2(3).

### Step 2 — ✅ **DONE** (`prop_sub_complete_thm.v`)

It was a two-line ripple in the end: P6-L's new guess-scope premise at the
two call sites, supplied by the new local `uskl_wf_ftv_dom` (the guess's own
well-formedness, re-read as an ftv bound).  `prop_sub_complete_dispatch.v`
and `cex/probe_payload_reachability.v` needed nothing — the whole tree
builds (`make coq` clean).

### Step 3 — ✅ **DONE, AND IT WENT ALL THE WAY: SUBTYPING COMPLETENESS IS
###            UNCONDITIONAL** (2026-08-05)

`a_sub_complete_bundle_holds` and `a_sub_complete_thm` no longer take
`forall n, main_forall n`.  Both are in `README.v`.  `make coq` clean.

| lemma | premise before | after |
|---|---|---|
| P6-Cv | `flex_apart` | **gone** |
| P6-Sv | `flex_apart_walk` | **gone** |
| P6-Cs | `flex_apart_deep` | unchanged — one genuine consumer, below |
| P6-Ss | `sub_shield` (2 conjuncts) | `flex_apart_deep` alone, **derivable** |
| P6-L | `sub_shield` | **gone** — discharged internally |
| P7b ForallL rows | TASK 0's `sub_shield` gate | **gone** |
| the bundle / the theorem | `forall n, main_forall n` | **gone** |

#### The chain, in four steps

1. **P6-Cv stopped consuming `flex_apart`.**  SE-FlexR went through `FLEXMONO`
   (`uskl_rho_mono_target`: ρ is CONGRUENT at every constructor and
   non-trivial only at a bare VARIABLE, itself a monotype, so a mono-paint
   ρ-IMAGE forces a mono-paint GUESS) plus `a_guess_ty_witness_mono_gen`,
   whose payloads are Θw-scoped POSITION-WISE (`ppre_hole_payload_wf`:
   `guess^TY` invents only at `Pi`'s HOLES, which `ad_ppre__hole` already
   keeps Δ-apart).  SE-GhostL gets its cleanliness from that same rule.
2. **P6-Sv stopped needing `flex_apart_walk`** — every use was a relay into
   P6-Cv's premise.
3. **`sub_shield` lost its guess-descending conjunct**, leaving the
   Δρ-CONSTANT half, which is derivable from `flex_apart_deep`
   (`flex_apart_deep_sub_shield`).
4. ⭐⭐⭐ **`sub_shield_empty`**: that half at **Δρ = ∅** — exactly how P6-L
   and P7b's two ForallL rows instantiate it — is UNCONDITIONALLY TRUE.  The
   walk's growth condition `Δρ' ∩ ftv ψa ⊆ Δρ` reads as cleanliness there, so
   every reachable state is `fa_clean`.

⚠️ **Step 4 was FALSE before step 3.**  `fa_walk`'s `fastep_all_r` GROWS Δρ,
so from Δρ = ∅ the guess-descending half reached a state where the opened
binder sits in Δρ and `fa_clean` is blocked.  That is precisely the
double-occurrence refutation — now reversed
(`p7_sub_shield_double_occ_holds`).

#### ⚠️ Retractions, so they are not lost

- `probe_main_forall_false` / `probe_motive_instance_false` /
  `probe_no_run` — the refutation of `main_forall`.  It ran through the
  double-occurrence configuration, where the OLD `SolE-FlexR` discarded the
  accumulated pattern so no `a_sub` run existed.  The repaired row returns
  `guess^TY(P)` and the run exists (`cex/probe_flexr_repair.v`).
- `sub_shield_forall_flex_p0_fails`, `p7_sub_shield_double_fails` — both went
  through the retired conjunct.  Their stuck-shape lemmas stand.

#### ⭐⭐ The reusable lesson

An earlier revision of this section said the move "cannot come out" because
P6-Ss's Sub-Arrow row has nothing to descend on.  True — but only of the
GUARDED conjunct: `fa_step` has no guess-fixed arrow descent (deliberately;
it made the walk unsatisfiable).  `flex_apart_deep` closes over `p0_step`,
which DOES have `p0step_arrow_l/_r`.  **When a premise is a closure, ask
WHICH WALK it closes over before concluding it cannot be derived — two
conjuncts of one definition had opposite answers.**

#### ⛔ What is left in the tree

`flex_apart_deep`, P6-Cs's premise, for ONE site: the **collection-side
`LE-FlexR`** row (`prop_look_complete_cstr.v` ≈ 2185).  Not for the mono-ness
— that transfers by the same `uskl_rho_mono_target` route — but for the
**κ-IMAGE Δρ-CLEANLINESS**: LE-FlexR invents a fresh flexible whose κ-image is
the whole guess, and P6-Cs's conclusion carries
`Forall (ftv (snd p) ∩ Δρ = ∅) κc`, which a partly-dirty guess violates; that
conjunct feeds the arrow row's shielded-ftv premise.

⚠️ This does NOT weaken `a_sub_complete_thm`: P7 instantiates Δρ = ∅, where
the premise is free.  It is an internal premise of P6-Cs's ρ-generalized
statement, paid for at every call site.  Nothing indicates `LE-FlexR` is
wrong — there is no witness against it.

**NEXT.**  Step 4 (the paper) is no longer gated by the proofs — see §0 for
the user directive that still holds.  `docs/WF-SIDE-CONDITIONS.md` is the
list of what `a_sub_complete_thm` carries beyond the paper's own premises.

---

### Step 3 (ORIGINAL, superseded above — kept for the `sub_shield` map)

P6-L itself is **re-proved and green** (`a_extract_complete_gen` /
`a_extract_complete`, the paper's `lemma:complete-look`,
`subtyping-proofs.tex:2730`).  What is left is the premise it still carries.

**WHERE THE PREMISE ACTUALLY LIVES.**  ⚠️ `sub_shield` is **P6-Ss's**
premise (`a_looksub_solve_complete_gen` / `_leaf`,
`prop_look_complete_sub_cstr.v:220`-ish) and **P6-L's**
(`prop_look_complete_extract.v:1036`, `:1286`).  P6-Sv does **not** take it —
it takes `flex_apart_walk Θ0 Δρ P0 ψa` (`prop_look_complete_sub_var.v:2053`),
and P6-Cs takes `flex_apart_deep`.  `sub_shield` is the CLOSURE that supplies
both along an `ss_walk`, through exactly three lemmas:

| lemma | yields | who consumes it inside P6-Ss |
|---|---|---|
| `sub_shield_here` (guarded on `α ∈ ftv R`) | `flex_apart_walk` | the `P = α` leaf → P6-Sv |
| `sub_shield_here_p0` (unguarded) | `flex_apart_deep` | the Check row → P6-Cs, and the Arrow row's LEFT branch |
| `sub_shield_step` | the descents | the ∀ / arrow / ghost rows |

**START HERE.**  ⭐ The repair has already killed the witness `sub_shield`
was invented for — `cex_p6sv_forall_flex.v`'s ∀-over-flexible configuration
now solves to `∀β.β→β` (`cex/probe_flexr_neutralises_p6.v`).  So the concrete
first move is to attack the CLOSURE, not the leaves: in
`prop_look_complete_sub_cstr.v`, replace the `sub_shield` premise by the two
things its consumers actually take — `flex_apart_walk Θ0 Δρ P0 ψa` and
`flex_apart_deep Θ0 Δρ P0 ψa` — and see whether the descents still go through
(`flex_apart_walk_step` / `flex_apart_deep_step` are the replacements for
`sub_shield_step`; both already exist and are used elsewhere in the file).
The three `sub_shield_*` grep hits above are the complete list of rows that
owe anything.  If it comes out, propagate to P6-L (which takes it verbatim)
and then delete `ss_walk`, `sub_shield` and their kit
(`prop_look_complete_sub_cstr.v` §§ near the top, and
`prop_sub_shield_supply.v` whole).  ⚠️ Do NOT delete speculatively — delete
when the files go through without them, which is what §5's cleanup list
already says.

⚠️ And keep `cex/cex_p7_shield_double_occ.v` in view: it refutes the
POSITIONAL `sub_shield` at a node the algorithm reaches, which is a
*different* question from whether P6-Ss needs the premise at all.  That
witness is about `main_forall`'s SUPPLY, and it has not been re-checked
against the repaired rule.

Then `main_forall` — now OPEN rather than refuted (§3) — and whether it
becomes discharge-able, which would make `a_sub_complete_bundle_holds` and
`a_sub_complete_thm` unconditional and put them in `README.v`.

⚙️ Before touching anything, re-read `cex/probe_flexr_neutralises_p6.v`'s
header: it says precisely what the two dead witnesses do and do not settle.

### Step 4 — the paper (⛔ GATED, see §0)

Only after Step 3. `full-algo-spec.tex`: the `SolE-FlexR` rule (`:1371`,
with `nonghost`), the `Ξ` suffix on all three solving judgements
(`fig:constraint-solving`), Look's output suffix, and `lemma:complete-look`.
`macro.tex` needs `\nonghost` and `\uniq`.

---

## 7. Hazards (all cost real time)

- ⚠️ **No `ltac:()` in a partially-applied IH or lemma.** The evars are
  unresolved when the tactic runs, so `fsetdec`/`lia` see a goal with
  metavariables. Use an explicit `assert` first.
- ⚠️ **`econstructor` on `SS-ForallR` leaves the witness an evar** — its
  output passes *through*, so nothing determines β. Name it:
  `apply a_solve_sub__forall_r with (β := b)`.
- ⚠️ **`a_solve_cstr__eq` and the arrow rows now SPLIT their output block**,
  so `eapply` cannot unify `?Ξ2 ++ ?Ξ1` with `nil`. Either pass
  `with (Ξ1 := nil) (Ξ2 := nil)` or `change nil with (nil ++ nil)` first.
  Same for `a_extract__solve`'s three blocks — but leave `Ξ'` to
  unification, since the final guess genuinely generates one at some sites
  (see `test_examples.v` for both patterns).
- ⚠️ `Set Implicit Arguments` means the packaged move-binder lemmas need
  `@name _ _ _ _ _ _ α0 H ...`, not `(α0 := α0)`; and `a_wf_pskl__all` needs
  `with (L := …)`.
- ⚠️ `dom Θ` vs `ftvar_in_aenv Θ` is load-bearing everywhere.
- ⚙️ After changing `prop_solve_sub.v` or `prop_swap.v`, rebuild
  `prop_looksub` → `prop_sub_sound` → `prop_decorate_sub` →
  `prop_decorate_key` before the file you are working on, or you get
  "makes inconsistent assumptions over library". `make -j10 -f CoqMakefile
  frost/algo/prop_decorate_key.vo` does the whole chain in ~110 s.
- ⚙️ Iterate with `coqc -R . src -w -deprecated-hint-without-locality,-omega-is-deprecated frost/algo/<file>.v`
  on the single file; `make NJOBS=10 -k coq` only for the whole-tree picture.
- ⚙️ To see what a blanket tactic left open:
  `all: match goal with |- ?g => idtac "LEFT>>>" g end.` before the bullets,
  or `Show.` for the first goal with its context (works under `coqc` too —
  that is how the codomain block of `probe_flexr_repair.v` was debugged).
