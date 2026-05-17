# δ-encoding Admit Cleanup — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use `superpowers:subagent-driven-development` (recommended) or `superpowers:executing-plans` to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

## Status (after first execution attempt)

**Phase 0 complete (2026-05-17):** build is green. The 4 leaking axioms reaching D1/D12 are documented placeholders, no longer build errors.

**Phases 1-3 reassessed as NOT one-session-sized.** Initial investigation (see "Findings" below) revealed that the 4 leaking axioms — and the 12 other δ-NEW admits — share a coupled dependency on broken invariants 4/5/6 (see §"The reasoning chain's invariants" below). Each shortcut lemma's call sites use its conclusion as a load-bearing equation in downstream proof steps; refactoring individual call sites doesn't compose. The real fix requires either:
  - **(a) Restructuring the SPLIT helpers** (`d_typing_abs_value_to_subsumption_split_d_sub`, `_abs_anno_split_d_sub`) and `d_sub_gen_trans` to be polymorphic-body-aware, removing reliance on the broken invariants. Significant proof restructure.
  - **(b) Adding precondition restrictions** at the entry points (e.g. forcing mono binding types at D12's `__abs` call site), cascading the restriction upward — which may reach D12's signature.

This is a multi-session effort. Phase 0 leaves the codebase in a clean intermediate state.

## The reasoning chain's invariants

The OLD chain (pre-δ) relied on:

| # | Invariant | δ-status |
|---|---|---|
| 1 | Colour discipline (syn from mode_ti, inh to mode_tc) | ✅ intact |
| 2 | ε-tag accounting (`typ_all_etag ε T` carries Δ; `typ_all_col` doesn't) | ✅ intact |
| 3 | syn_color / inh_color disagree on `ctyp_all` paint colour, so `syn_color T = inh_color X` forces both ctyp_all-free | ✅ intact (property of FUNCTIONS, not d_consis) |
| 4 | **d_consis with syn-LHS ↔ inh-RHS forces mono** | ❌ **broken** by `d_consis__forall_inh_untagged` (LHS colour_syn ↔ RHS colour_inh at polytype, no ε) |
| 5 | **d_consis with empty Δ ⇒ LHS = RHS** | ❌ broken (same reason) |
| 6 | **d_sub at `mode_fn _` with wf LHS forces arrow shape** (`__forall_l_tagged` vacuous via non-wf LHS) | ❌ **broken** by `d_sub__forall_l_untagged` (wf `typ_all_col colour_syn` LHS now possible) |

Invariants 4 / 5 / 6 are USED LOAD-BEARINGLY at many sites:
- `d_consis_syn_inh_mono` / `_gen_syn_inh_mono` — extract mono from d_consis; 4 call sites in SPLIT helpers.
- `d_consis_gen_lhs_syn_eq` — extract `T = A` equation; 8 call sites.
- `d_sub_gen_trans __forall_l_untagged` — transitivity at `mode_fn _` reaches this inner case.
- `d_consis_compose` / `d_consis_gen_trans` / `d_consis_extends_d_consis_gen` — wholesale-admitted, original bodies in `(* ... *)` comments awaiting restoration.

## Goal (revised)

Phase 0 (now done): green build + clear documentation. **Subsequent phases need their own design pass first.**

**Original goal preserved for reference:**

Close the 16 new admits introduced by the δ-encoding refactor (commit `0bf2815`) so the build is green again and the flagship theorems `d_typing_general_subsumption_via_gen` / `_gen` are once more "Closed under the global context."

**Architecture.** The refactor added 5 new rule constructors (`d_sub__forall_l_untagged`, `d_consis__forall_inh_untagged`, `d_pat_sub__forall_l_untagged`, `d_pat_consis__forall_inh_untagged`, `d_pat_consis__forall_syn_untagged`) plus 2 predicate-grammar entries (`is_utyp__pall`, `is_uskel__pall`). Each case-splitting lemma needs a new bullet; six lemmas become provably false unless their precondition is strengthened; three lemmas were wholesale-admitted with their original body in `(* ... *)` comments awaiting restoration. Pre-existing 17 admits (research-grade Phase 2.D / 2.E / paper-flagged) are OUT OF SCOPE.

**Tech stack.** Coq + ott + lngen. Build via `make coq` from `mechanization/` (uses `tree`-derived FILE_LIST). Hammer / sauto available via `frost/ltac_utils.v`. Notations: `Δ ⨟ Γ ⊨ T ≈ A` (`d_consis`), `Γ ⊢[ M ; Δ ] T ⊑ A` (`d_sub`). Skill methodology: read DESIGN.md §6 "colour/mode discipline" before patching any provably-false lemma — the strengthening pattern almost always surfaces a call-site contract already present implicitly.

---

## Scope checklist (16 δ-NEW admits)

**Provably-false (6 lemmas, 7 admit sites):**
1. `d_consis_LHS_mono_wf` (`subtyping/prop_consis_trans.v:331,333`) — 2 sub-case admits closed by strengthening.
2. `d_consis_LHS_is_typ_mono` (`subtyping/prop_consis_trans.v:376,378`) — 2 sub-case admits closed by strengthening.
3. `d_sub_mono_RHS_eq` (`typing/prop_subsumption_aux.v:127`) — 1 sub-case admit.
4. `d_consis_gen_lhs_syn_eq` (`typing/def_gen.v:246`) — 1 sub-case admit.
5. `d_consis_empty_eq` (`subtyping/prop_sub_sound.v:64`) — 1 sub-case admit.
6. `d_sub_sound` `__forall_l_untagged` case (`subtyping/prop_sub_sound.v:121`) — 1 sub-case admit.
7. (No `d_sub_LHS_mono_wf` admit found in current source — survey suggests it was already closed via `inversion`. Verify.)

**Wholesale admits (3 lemmas, 7 sites — admit + Admitted in each):**
1. `d_consis_compose` (`subtyping/prop_consis_trans.v:95,290`).
2. `d_consis_gen_trans` (`typing/def_gen.v:754,790`).
3. `d_consis_extends_d_consis_gen` (`typing/def_gen.v:1095,1206,1265` + `typing/prop_subsumption_aux.v:561,562`).

**Sub-case admits (8 sites in 5 lemmas):**
1. `d_pat_consis_preserves_wf` (`prop_wellformed.v:1023`) — `__forall_syn_untagged` case (also `__forall_inh_untagged`).
2. `d_pat_sub_preserves_wf` (`prop_wellformed.v:1078`) — `__forall_l_untagged`.
3. `d_pat_sub_implies_is_syn_skel` (`prop_wellformed.v:1116`) — `__forall_l_untagged`.
4. `d_consis_gen_extends_d_sub_nil` (`typing/prop_subsumption_aux.v:217`) — `__forall_l_untagged`.
5. `d_consis_sub_trans` (`subtyping/prop_consis_sub_trans.v:208`) — `__forall_l_untagged`.

Plus the live build error at `typing/prop_subsumption_aux.v:395` (a bullet-structure error, not an admit — but Phase 0 must fix it before any of the above is provable).

---

## Phase 0: Get the build green

The build halts at `prop_subsumption_aux.v:395` with `Wrong bullet +: Expecting *`. The proof of `d_sub_gen_trans` `mode_fn m` case inverts the inner `d_sub`, which now has an extra constructor `d_sub__forall_l_untagged` between `__forall_l_tagged` (line 393) and the next `+` (line 395). Add the missing `*` bullet.

### Task 0.1: Repair the `d_sub_gen_trans` bullet structure

**Files:**
- Modify: `frost/decl/typing/prop_subsumption_aux.v:393-395`

- [ ] **Step 1: Inspect the inversion context**

The inner inversion at line 380 produces three cases for `d_sub (mode_fn m) nil Γ A B`:
- `__arg` (line 382, `*`)
- `__forall_l_tagged` (line 393, `*`) — closed by `inversion HwfA` (`typ_all_etag` not wf at top level)
- `__forall_l_untagged` (NEW) — LHS `typ_all_col colour_syn T` IS wf, must reason

- [ ] **Step 2: Add a placeholder `*` case for `__forall_l_untagged`**

For now, admit it (provably-false-style — `mode_fn m` requires `m <> mode_ti`, satisfied; but we need actual reasoning here). Insert between line 394 (`inversion HwfA.`) and line 395 (`+`):

```coq
      * (* d_sub__forall_l_untagged: A = typ_all_col colour_syn T0 (IS wf). δ-NEW. *)
        admit.
```

Also change the `Qed.` at line 406 to `Admitted.` if needed (verify after build runs).

- [ ] **Step 3: Run the build to surface the next error**

```bash
make coq 2>&1 | tail -40
```

Expected: either successful compilation of `prop_subsumption_aux.v` and progression to next file, or a new bullet-mismatch error in a later file.

- [ ] **Step 4: Cascade-fix until build is green**

Repeat: read the error, identify which inductive's case-split is missing the new constructor, add a `case + admit.` placeholder, re-run. Target files (in expected dependency order):

- `prop_subsumption_aux.v`
- `prop_consis_trans.v` / `prop_consis_sub_trans.v` / `prop_sub_sound.v` (already partially patched per survey)
- `def_gen.v`
- `prop_general_subsumption.v`
- `prop_weakening.v`
- `prop_skeleton.v`
- `prop_typing.v` (umbrella)
- `prop_subtyping.v` (umbrella)
- `algo/*.v` (probably not affected since algo defs are separate)

Estimate: 10-30 mechanical bullet additions across these files.

- [ ] **Step 5: Verify green build**

```bash
make coq 2>&1 | tail -5
```

Expected: no `Error:` lines; build completes. Admits remain (and will be the next phases' work).

- [ ] **Step 6: Commit**

```bash
git add -u frost/decl/
git commit -m "$(cat <<'EOF'
mech: δ-cascade Phase 0 — add missing bullets to restore green build

Adds placeholder * / admit. bullets for d_sub__forall_l_untagged,
d_consis__forall_inh_untagged, d_pat_*_untagged across the case-splitting
proofs that the δ-refactor broke. No semantic content yet — every new
bullet is `admit.`. Subsequent phases close them.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Phase 1: Strengthen provably-false lemmas

Each lemma has a precondition strong enough that the troublesome new constructor's LHS is excluded. For the 6 lemmas below, add a `is_utyp A` (or `is_typ A`, depending on which excludes the offending shape) hypothesis, then patch every call-site to discharge it.

**Strengthening rationale (the colour-discipline lens, per DESIGN.md §6):** every existing call-site of these lemmas already operates in a context where the LHS shape is restricted. The strengthening surfaces that contract explicitly. If a call-site CANNOT discharge it, then either (a) the new untagged-syn case really is a counter-example to the lemma at that call, in which case the call-site itself needs restructuring; or (b) there's an upstream invariant we can route through.

### Task 1.1: `d_consis_LHS_mono_wf` + `d_consis_LHS_is_typ_mono` strengthening

**Files:**
- Modify: `frost/decl/subtyping/prop_consis_trans.v:295-340` (`d_consis_LHS_mono_wf`)
- Modify: `frost/decl/subtyping/prop_consis_trans.v:345-384` (`d_consis_LHS_is_typ_mono`)
- Modify (call-sites, surface via `git grep`): expect 2-4 sites each, mostly in the same file or `prop_consis_sub_trans.v` / `typing/def_gen.v`.

- [ ] **Step 1: Read both lemmas and their immediate context**

`Read prop_consis_trans.v` lines 290-390 to see both statements and the inversion chain.

- [ ] **Step 2: Add `~ is_utyp__pall A` strengthening**

A precise strengthening: add a hypothesis that excludes the `is_utyp__pall` constructor. The cleanest way: add an `is_utyp` precondition (excludes `typ_all_col colour_inh`) PLUS an explicit `forall T, A <> typ_all_col colour_syn T` clause. OR easier: add the syn-colour predicate `is_syn_color A` so the untagged-syn LHS goes away.

If `is_syn_color` isn't already defined, prefer adding a `is_typ A` precondition (which excludes all `typ_all_col` flavours), then either:
- check call-sites have `is_typ A` available — often they do from a wf chain.

Concrete strengthened signature (try first):
```coq
Lemma d_consis_LHS_mono_wf : forall Δ Γ A B,
    Δ ⨟ Γ ⊨ A ≈ B ->
    is_typ A ->                 (* NEW — excludes typ_all_col / typ_all_etag *)
    mono_typ A.
```

If `is_typ` is too strong (a call-site provides only `d_wf_typ`), back off to a custom not-pall predicate.

- [ ] **Step 3: Patch the lemma body**

The new `__forall_inh_untagged` and `__forall_syn` cases close by `inversion H_is_typ.` (or whichever name the new hypothesis takes). The other cases need the hypothesis threaded into their IH or discharged structurally.

- [ ] **Step 4: Patch each call-site**

```bash
git grep -n "d_consis_LHS_mono_wf\b" frost/decl/
git grep -n "d_consis_LHS_is_typ_mono\b" frost/decl/
```

For each site, add the new argument. If a site can't supply it, follow the colour-discipline lens: check whether the surrounding lemma also needs strengthening (often the chain propagates up cleanly).

- [ ] **Step 5: Build, fix, build**

```bash
make coq 2>&1 | grep -E "(Error|Admitted)" | head -10
```

Repeat until clean.

- [ ] **Step 6: Verify the two admits at line 331/333 (and 376/378) are gone**

```bash
grep -n "admit\." frost/decl/subtyping/prop_consis_trans.v
```

Expected: lines 331, 333, 376, 378 admits removed.

- [ ] **Step 7: Commit**

```bash
git add -u frost/decl/
git commit -m "$(cat <<'EOF'
mech: δ-cascade Phase 1.1 — strengthen d_consis_LHS_mono_wf / _is_typ_mono

Adds [is_typ A] precondition to both lemmas, ruling out the
typ_all_col colour_syn LHS that is_utyp now admits (via is_utyp__pall).
Call-sites discharge via wf chain.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 1.2: `d_sub_mono_RHS_eq` strengthening

**Files:**
- Modify: `frost/decl/typing/prop_subsumption_aux.v:99-129` (`d_sub_mono_RHS_eq`)
- Modify: `frost/decl/typing/prop_subsumption_aux.v:131-157` (`d_sub_gen_mono_RHS_eq` — mirrors `d_sub_mono_RHS_eq` and likely needs the same fix)
- Modify (call-sites): `git grep -n "d_sub_mono_RHS_eq\b" frost/decl/`

- [ ] **Step 1: Read the current statement**

Current:
```coq
Lemma d_sub_mono_RHS_eq : forall m Γ A B,
    Γ ⊢[ m ; nil ] A ⊑ B ->
    d_wf_typ Γ A ->
    mono_typ B ->
    A = B.
```

The `__forall_l_untagged` case has LHS `typ_all_col colour_syn T` (wf), so `inversion HwfA` does NOT close it. Falsified by: `A = typ_all_col colour_syn (typ_var_b 0)`, `B = typ_unit`, `ph = typ_unit` ⇒ `d_sub ... A B` derivable, but `A ≠ B`.

- [ ] **Step 2: Add `is_typ A` precondition**

```coq
Lemma d_sub_mono_RHS_eq : forall m Γ A B,
    Γ ⊢[ m ; nil ] A ⊑ B ->
    is_typ A ->                 (* NEW — excludes all typ_all_col / typ_all_etag *)
    d_wf_typ Γ A ->
    mono_typ B ->
    A = B.
```

Then the new `__forall_l_untagged` case closes by `inversion H_is_typ.` (same as the existing `__forall_l_tagged` case which closes by `inversion HwfA` since `typ_all_etag` isn't wf).

- [ ] **Step 3: Apply same fix to `d_sub_gen_mono_RHS_eq`**

The gen variant's `__embed` case delegates to `d_sub_mono_RHS_eq`, so it needs the same `is_typ A` precondition to thread.

- [ ] **Step 4: Patch all call-sites**

```bash
git grep -n "d_sub_mono_RHS_eq\b\|d_sub_gen_mono_RHS_eq\b" frost/decl/
```

Expected sites: 1-3, mostly in `prop_subsumption_aux.v` itself and possibly `prop_general_subsumption.v` (D12's SPLIT helpers).

- [ ] **Step 5: Build, fix, commit**

```bash
make coq 2>&1 | grep -E "(Error|Admitted)" | head -10
```

Commit message: `mech: δ-cascade Phase 1.2 — strengthen d_sub_mono_RHS_eq with is_typ A`.

### Task 1.3: `d_consis_gen_lhs_syn_eq` strengthening

**Files:**
- Modify: `frost/decl/typing/def_gen.v:240-247` (and surrounding)
- Modify (call-sites): `git grep -n "d_consis_gen_lhs_syn_eq\b" frost/decl/`

The `__forall_inh_untagged` case: LHS `typ_all_col colour_syn T`, RHS `typ_all_col colour_inh A`. Conclusion `T = A` fails (colour mismatch).

- [ ] **Step 1: Read the current statement and decide on the strengthening**

Likely the lemma equates the LHS shape of d_consis to its RHS shape under some colour invariant. Strengthen with `is_syn_typ A` (RHS is syn-painted) or restate as "T and A have the same `erase` shape" (use `erase A = erase B` for colour-blind equality).

- [ ] **Step 2: Patch lemma + call-sites + build**

Same pattern as Task 1.2.

- [ ] **Step 3: Commit**

`mech: δ-cascade Phase 1.3 — strengthen d_consis_gen_lhs_syn_eq`.

### Task 1.4: `d_consis_empty_eq` strengthening

**Files:**
- Modify: `frost/decl/subtyping/prop_sub_sound.v:55-89`
- Modify (call-sites): `git grep -n "d_consis_empty_eq\b" frost/decl/`

The `__forall_inh_untagged` case: T = `typ_all_col colour_syn _`, A = `typ_all_col colour_inh _`, conclusion `T = A` fails.

- [ ] **Step 1: Read & strengthen**

Most likely strengthening: `is_syn_typ A` AND `is_syn_typ T`, or use the colour-blind equality. The lemma is `(nil ⨟ Γ ⊨ T ≈ A) → T = A` which is asserting that with empty tag context, consistency degenerates to equality. With the new untagged rule, this fails on colour-mixing. The closest paper-faithful fix is `erase T = erase A` instead of `T = A`.

If the call-sites can survive with `erase T = erase A`, prefer that. Otherwise add `is_syn_typ A` to forcibly exclude the bad case.

- [ ] **Step 2: Patch + build + commit**

`mech: δ-cascade Phase 1.4 — strengthen d_consis_empty_eq`.

### Task 1.5: `d_sub_sound` `__forall_l_untagged` case

**Files:**
- Modify: `frost/decl/subtyping/prop_sub_sound.v:121` (admit) + surrounding `Lemma d_sub_sound`

**The shape of the gap:**

The existing `d_sub__forall_l_tagged` case routes through `d_shallow_sub__forall_l` with `d_wf_typ Γ ph` from the `d_wf_ttyp` premise (with `Δ' = nil` discharged). The new `__forall_l_untagged` case: same shape but LHS is `typ_all_col colour_syn`, which `d_shallow_sub` DOES accept (it has a general `forall_l` rule for `typ_all_col c`).

- [ ] **Step 1: Try the parallel route**

Replace the `admit.` with the `__forall_l_tagged` case's proof script, adapted for the untagged LHS. Specifically: `apply d_shallow_sub__forall_l`; use the `ph` witness from the rule premises; close the recursive `d_shallow_sub` via the IH.

- [ ] **Step 2: If the IH doesn't directly apply** (because `is_typ A` precondition of `d_sub_sound` doesn't compose cleanly with the substituted `open_typ_wrt_typ T ph`):

Add a helper lemma: `is_typ (open_typ_wrt_typ T ph) → is_typ ph → is_typ T`. Probably already exists; if not, prove via induction on `T`.

- [ ] **Step 3: Build, commit**

`mech: δ-cascade Phase 1.5 — close d_sub_sound __forall_l_untagged via parallel route`.

---

## Phase 2: Restore wholesale-admitted lemmas

Three lemmas have their original body preserved as `(* ... *)` comments. Restore the body, then patch each new case (mechanical or substantive).

### Task 2.1: `d_consis_compose` restoration

**Files:**
- Modify: `frost/decl/subtyping/prop_consis_trans.v:95-290` (the wholesale-admitted lemma)

- [ ] **Step 1: Read the entire lemma + comment-buried body**

```bash
sed -n '80,290p' frost/decl/subtyping/prop_consis_trans.v
```

The original body is in `(* ... *)` between line 95 (`admit.`) and line 290 (`Admitted.`).

- [ ] **Step 2: Restore the proof body**

Remove the surrounding `(* ... *)`. Change `Admitted.` to `Qed.` (it will fail until the new cases are added).

- [ ] **Step 3: Build and identify new failing cases**

```bash
make coq 2>&1 | tail -30
```

Expected: bullet-mismatch errors. Add new bullets for:
- LHS `__forall_inh_untagged` × RHS `__forall_inh_*` (cross-colour composition)
- LHS `__forall_syn` × RHS `__forall_inh_untagged` (new top-level case appearing on the right)
- Other combinations as surfaced by Coq

- [ ] **Step 4: Close each new case**

The body of `__forall_inh_untagged` is structurally parallel to `__forall_inh_tagged` — copy the latter's tactic, adapt for the missing `ε :: Δ` (the untagged form has no ε to track).

For cross-colour cases (e.g. `__forall_syn` LHS × `__forall_inh_untagged` RHS): the substitution under the cofinite binder needs the renamed-α to match across both derivations. Apply `pick fresh X for L1 \u L2`, then compose via the IH on the opened bodies.

- [ ] **Step 5: Verify `Qed.`**

```bash
grep -n "Qed\.\|Admitted\." frost/decl/subtyping/prop_consis_trans.v | head -10
```

`d_consis_compose` should now read `Qed.`. Sub-case admits at 158, 195, 262, 671, 678 should also be closed (they were sub-cases of `d_consis_compose`'s body).

- [ ] **Step 6: Commit**

`mech: δ-cascade Phase 2.1 — restore d_consis_compose (Qed)`.

### Task 2.2: `d_consis_gen_trans` restoration

**Files:**
- Modify: `frost/decl/typing/def_gen.v:750-790`

Same pattern as Task 2.1. The gen variant of `d_consis_compose`; same new cases apply at the gen layer.

- [ ] **Step 1: Read the lemma + buried body**
- [ ] **Step 2: Restore body, build, identify new cases**
- [ ] **Step 3: Close each — parallel to Task 2.1 cases**
- [ ] **Step 4: Verify Qed**
- [ ] **Step 5: Commit**

`mech: δ-cascade Phase 2.2 — restore d_consis_gen_trans (Qed)`.

### Task 2.3: `d_consis_extends_d_consis_gen` restoration

**Files:**
- Modify: `frost/decl/typing/def_gen.v:1090-1265`
- Modify: `frost/decl/typing/prop_subsumption_aux.v:555-562` (a sub-case admit that mirrors the same lemma)

Same pattern. This lemma is the bridge from `d_consis` to `d_consis_gen` — needs a new `__forall_inh_untagged` case (lift the untagged rule to the gen relation).

- [ ] **Step 1-5: Same as Task 2.2**
- [ ] **Step 6: Commit**

`mech: δ-cascade Phase 2.3 — restore d_consis_extends_d_consis_gen (Qed)`.

---

## Phase 3: Sub-case admits

Eight sub-case admits across five lemmas. Each is a parallel-rule pattern: copy the `tagged` case's tactic, drop the ε-tracking, adjust for `typ_all_col colour_syn` LHS.

### Task 3.1: `prop_wellformed.v` — 3 sub-case admits

**Files:**
- Modify: `frost/decl/prop_wellformed.v:1023` (`d_pat_consis_preserves_wf` — `__forall_syn_untagged` case)
- Modify: `frost/decl/prop_wellformed.v:1078` (`d_pat_sub_preserves_wf` — `__forall_l_untagged`)
- Modify: `frost/decl/prop_wellformed.v:1116` (`d_pat_sub_implies_is_syn_skel` — `__forall_l_untagged`)

- [ ] **Step 1: For each, read the parallel `_tagged` case's proof**

```bash
sed -n '990,1130p' frost/decl/prop_wellformed.v
```

- [ ] **Step 2: Adapt and close**

Each new case is structurally parallel to its `_tagged` sibling but without the `ε` premise (`~ List.In ε Δ`). The cofinite-α handling is identical.

- [ ] **Step 3: Build & commit**

`mech: δ-cascade Phase 3.1 — close 3 sub-case admits in prop_wellformed.v`.

### Task 3.2: `prop_subsumption_aux.v` — `d_consis_gen_extends_d_sub_nil` sub-case

**Files:**
- Modify: `frost/decl/typing/prop_subsumption_aux.v:217` (the admit in `__forall_l_untagged` case)

Parallel to the `__forall_l_tagged` case (line ~213). Copy its tactic, drop the `ε`-related bookkeeping.

- [ ] **Step 1-2: Read parallel case + adapt**
- [ ] **Step 3: Build & commit**

### Task 3.3: `prop_consis_sub_trans.v` — `d_consis_sub_trans` sub-case

**Files:**
- Modify: `frost/decl/subtyping/prop_consis_sub_trans.v:208` (the admit)

The `__forall_l_untagged` case of `d_sub` requires the composition `d_consis ... typ_all_col colour_syn T0 → d_sub __forall_l_untagged → d_consis ... B`. Compose by inverting the `d_consis` (it must be `__forall_syn` or `__forall_syn_tagged`), then use the IH on the opened body.

May need a new helper: `d_consis_subst_ttyp` (substitute a `d_wf_ttyp` term, not just a mono term — the existing `d_consis_subst_mono` only handles mono). If so:

- [ ] **Step 1: State and prove `d_consis_subst_ttyp`**

```coq
Lemma d_consis_subst_ttyp : forall Δ Δ' Γ X T A ph,
    Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ T ≈ A ->
    Δ' ⨟ Γ ⊢ₜₜ ph ->
    list_disjoint Δ Δ' ->
    (Δ ++ Δ') ⨟ Γ ⊨ (subst_typ_in_typ ph X T) ≈ (subst_typ_in_typ ph X A).
```

By induction on the `d_consis` derivation; each case re-applies the same `d_consis` constructor on the substituted bodies.

- [ ] **Step 2: Use the helper in the `__forall_l_untagged` case**
- [ ] **Step 3: Build & commit**

`mech: δ-cascade Phase 3.3 — close d_consis_sub_trans __forall_l_untagged + helper`.

---

## Phase 4: Verification

### Task 4.1: Re-verify `Print Assumptions`

**Files:**
- Inspect: `frost/decl/typing/prop_general_subsumption.v` (D1 and D12 sites)

- [ ] **Step 1: Run README.v**

```bash
make coq 2>&1 | grep -A 2 "Print Assumptions"
```

Or directly:

```bash
coqc -R . src frost/decl/typing/prop_general_subsumption.v 2>&1 | tail -30
```

- [ ] **Step 2: Confirm both are "Closed under the global context"**

`Print Assumptions d_typing_general_subsumption_via_gen.`
`Print Assumptions d_typing_general_subsumption_gen.`

If NOT closed, the offending axiom name appears. Trace it back via `git grep` to find which lemma still leaks an admit.

- [ ] **Step 3: If not closed, identify and close the leaking admit**

The most likely culprits are leftover wholesale admits or a strengthened lemma whose new precondition can't be discharged at a D12 call-site. Diagnose by looking at the axiom name and the chain.

### Task 4.2: Update `PROGRESS.md`

**Files:**
- Modify: `mechanization/PROGRESS.md` — status banner + add a closure entry under Part 2 dated 2026-05-17

- [ ] **Step 1: Update status banner**

Change `🔴 RED` to `🟢 GREEN` (verify with `make coq` first).
Change the δ-refactor uncertainty paragraph to a closure summary.
Update admit counts: `15 base + 16 δ-NEW` → `15 base + 0 δ-NEW` (or whatever remains).

- [ ] **Step 2: Add a new Part 2 entry**

A dated entry "2026-05-17 — δ-encoding refactor closure" describing what was closed, the strengthening patterns applied, and the `Print Assumptions` outcome.

- [ ] **Step 3: Commit the doc update**

```bash
git add mechanization/PROGRESS.md
git commit -m "mech: PROGRESS.md — δ-refactor cascade closed, flagship theorems re-verified"
```

---

## Self-review

**Spec coverage:** Every δ-NEW admit (16 sites in 12 lemmas) is addressed by a task above. Pre-existing admits (research-grade) are explicitly OUT OF SCOPE.

**Risk:** The provably-false lemma strengthenings cascade to call-sites. If a call-site cannot discharge the new precondition, the cascade may force strengthening of that caller too — keep an open mind and follow the colour-discipline lens.

**Verification gate:** the plan is NOT complete until `Print Assumptions d_typing_general_subsumption_via_gen` reports `Closed under the global context` AGAIN.

**Frequency of commits:** one per task. Don't batch — commits make incremental rollback possible if a phase goes sideways.
