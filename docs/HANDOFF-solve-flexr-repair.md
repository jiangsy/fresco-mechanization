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
| *(latest)* | ⭐ **`probe_flexr_repair.v`**; the two rule strengthenings; retractions; docs |

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

### Retracted (headers rewritten; Coq text at `d5f9169`)

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
`flex_apart_p0`, and the whole `ss_walk` machinery. These were invented as
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

### Step 1 — the P6 cluster (THE work; ~32k lines, NOT started)

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

#### ⭐ THE ONE LEMMA THAT UNBLOCKS THE REST — `a_guess_ty_witness_mono`

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

### Step 2 — `prop_sub_complete_thm.v` / `prop_sub_complete_dispatch.v`

Mostly consumers; expect `a_extract`'s three-block suffix and the P6
statements' new `κ` extension to ripple. Also re-check
`cex/probe_payload_reachability.v` (TASK A's positive half) — it reasons
about `a_sub` outputs' mode-spine and `a_guess_mono`, both of which the
repair touches.

### Step 3 — ⭐ THE PAY-OFF: P6-L, `sub_shield`, and `main_forall`

`a_extract_complete_gen` (`prop_look_complete_extract.v`) — the paper's
`lemma:complete-look` (`subtyping-proofs.tex:2730`). **With the repair the
counterexample to it is gone.** Re-prove it and check whether the
`sub_shield` premise can be **weakened or dropped**, since `sub_shield` was
invented as the mech's repair *of this very lemma*. Then see whether
`main_forall` — now OPEN rather than refuted — becomes discharge-able, which
would make `a_sub_complete_bundle_holds` and `a_sub_complete_thm`
unconditional and put them in `README.v`.

This is where the cleanup listed at the end of §5 gets decided.

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
