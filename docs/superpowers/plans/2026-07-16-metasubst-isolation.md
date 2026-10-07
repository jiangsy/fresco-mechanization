# Metasubst Isolation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extract the ~54 completeness-side metasubstitution / `a_inc_equiv` / downarrow lemmas out of `prop_consis_complete.v` into a new pure-metasubst module `prop_metasubst.v`, and collapse the obvious duplication families.

**Architecture:** New file `fresco/algo/prop_metasubst.v`, sibling to `prop_consis_sound`, directly below `prop_consis_complete`. It imports only the base metasubst/wf files (no `def_decl_algo`/`def_decorated`), so the module graph enforces isolation from consistency. The `prop_inc_strengthen → prop_consis_sound` cycle is broken first so the metasubst layer has no transitive consistency dependency.

**Tech Stack:** Coq (Rocq) + Metalib, built with `coqc`. No unit tests — the "test" for every task is that `coqc` compiles the changed file **and its downstream consumers** green, with the `prop_consis_complete.v` admit count unchanged at **12** and `skip_tm_var_case` still `Closed under the global context`.

## Global Constraints

- Work in `/Users/jiangsy/Documents/HKU/Research/impredicative/mechanization` (all paths below are relative to it; all `coqc` runs from it).
- Compile command (verbatim): `coqc -R . src -w -deprecated-hint-without-locality,-omega-is-deprecated fresco/algo/<file>.v`
- Downstream chain to re-verify after every task: `fresco/algo/prop_consis_complete.v` then `fresco/algo/prop_consis_exist.v`. Both must exit 0.
- Admit-count invariant: `grep -c 'admit\.' fresco/algo/prop_consis_complete.v` must stay `12` after every task.
- No statement of a lemma that consistency relies on may be *weakened*; generalization may only *strengthen* (add generality) and every consumer must still compile.
- `prop_metasubst.v` MUST NOT import `def_decl_algo`, `def_decorated`, `prop_refine`, `prop_consis_sound`, `prop_precise`, `prop_precise_recover`, or `prop_mono_bridge` (the consistency-side files). Enforced by `coqc` — a moved lemma that references a consistency symbol will fail to compile there, which means it is a *bridge* lemma and stays in `prop_consis_complete.v`.
- Commit tag: `[mech]` for code, `[docs]` for docs. End commit messages with `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.
- Spec: `docs/superpowers/specs/2026-07-16-metasubst-isolation-design.md`.

## File structure

- **Create** `fresco/algo/prop_metasubst.v` — the completeness-side metasubst theory (§A `a_inc_equiv`, §B downarrow ⇓, §C msubst/is_id basics). One responsibility: pure metasubstitution reasoning used by optimality.
- **Modify** `fresco/algo/prop_consis_complete.v` — remove the ~54 moved lemmas; add `Require Import src.fresco.algo.prop_metasubst.`; keep optimality defs, the ~5 bridge lemmas, `skip_tm_var_case`, the theorem + corollary.
- **Modify** `fresco/algo/prop_inc_strengthen.v` — drop the `prop_consis_sound` import (cycle fix).
- **Modify** `_CoqProject` / build file if it enumerates files explicitly (check in Task 1).
- **Modify** memory `remech-*`/dir-notes if a path map exists (final task).

---

### Task 1: Break the `prop_inc_strengthen → prop_consis_sound` cycle

**Files:**
- Modify: `fresco/algo/prop_inc_strengthen.v` (its `Require Import` block + possibly relocate one lemma)
- Inspect: `fresco/algo/prop_consis_sound.v`

**Interfaces:**
- Produces: a `prop_inc_strengthen.v` that does **not** import `prop_consis_sound`, so downstream `prop_metasubst.v` can import it without pulling in consistency.

- [ ] **Step 1: Identify what `prop_inc_strengthen` uses from `prop_consis_sound`.**

Run:
```bash
cd /Users/jiangsy/Documents/HKU/Research/impredicative/mechanization
# names referenced in prop_inc_strengthen that are DEFINED in prop_consis_sound
comm -12 \
  <(grep -oE '\b[a-zA-Z_][a-zA-Z0-9_]*\b' fresco/algo/prop_inc_strengthen.v | sort -u) \
  <(grep -oE '^(Lemma|Theorem|Definition|Corollary|Fixpoint|Inductive) [a-zA-Z_][a-zA-Z0-9_]*' fresco/algo/prop_consis_sound.v | awk '{print $2}' | sort -u)
```
Expected: a short list (0–3 names). If **empty**, the import is dead — go to Step 2a. If non-empty, note each name and whether it is metasubst-level (its statement mentions only `a_inc`/`a_tyequiv`/`a_isub`/`msubst`/wf, not `ad_pat_consis`) — go to Step 2b.

- [ ] **Step 2a (import is dead): remove it.**

Edit `fresco/algo/prop_inc_strengthen.v`: delete the line
```coq
Require Import src.fresco.algo.prop_consis_sound.
```

- [ ] **Step 2b (import is used): relocate the needed lemma(s) down.**

For each metasubst-level lemma `L` the list reported: cut `L` (statement + proof) out of `prop_consis_sound.v` and paste it into the lowest base file that already has its dependencies — `prop_inc.v` if `L` only needs `a_inc`/`def_meta`, else `prop_flex.v`/`prop_compose.v`. Then delete the `prop_consis_sound` import from `prop_inc_strengthen.v`. If any reported name is genuinely consistency-level (mentions `ad_pat_consis`/`ad_wf_pskl`), STOP and report — the cycle is real and needs its own design; do not force it.

- [ ] **Step 3: Verify `prop_inc_strengthen` compiles without the import.**

Run:
```bash
coqc -R . src -w -deprecated-hint-without-locality,-omega-is-deprecated fresco/algo/prop_inc_strengthen.v; echo rc=$?
```
Expected: `rc=0`.

- [ ] **Step 4: Verify the whole downstream chain still compiles and the invariant holds.**

Run:
```bash
for f in prop_consis_sound prop_consis_complete prop_consis_exist; do
  coqc -R . src -w -deprecated-hint-without-locality,-omega-is-deprecated fresco/algo/$f.v; echo "$f rc=$?"
done
grep -c 'admit\.' fresco/algo/prop_consis_complete.v
```
Expected: all `rc=0`; admit count `12`.

- [ ] **Step 5: Commit.**

```bash
git add fresco/algo/prop_inc_strengthen.v fresco/algo/prop_consis_sound.v fresco/algo/prop_inc.v fresco/algo/prop_flex.v fresco/algo/prop_compose.v 2>/dev/null
git commit -m "$(printf '%s\n' '[mech] break prop_inc_strengthen -> prop_consis_sound import cycle' '' 'Metasubst-layer strengthening no longer transitively depends on consistency,' 'unblocking a clean prop_metasubst.v import set.' '' 'Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>')"
```

---

### Task 2: Create `prop_metasubst.v` and move §C (msubst / is_id basics)

**Files:**
- Create: `fresco/algo/prop_metasubst.v`
- Modify: `fresco/algo/prop_consis_complete.v` (remove §C lemmas; add import)

**Interfaces:**
- Produces: `prop_metasubst.v` exporting the §C basics (`msubst_compose_app`, `msubst_lc_compose`, `is_id_msubst_values_lc`, `msubst_compose_id_ptyp`, `msubst_compose_id_pskl`, `metasubst_dom_empty`, `msubst_lookup_mid_drop`, `msubst_pskl_ftv_lower`, `msubst_lookup_app_in`, `msubst_pskl_open_rec_lc_local`, `msubst_pskl_open_lc_local`, `a_inc_msubst_lc`, `a_tyequiv_strengthen_tvar_cons`, `a_pskl_tyequiv_strengthen_tvar_cons`, `binds_strengthen`, `binds_sub_cons`, `aenv_mid_split`, `a_assign_subject_flex_local`) with unchanged signatures.
- Consumes: base files (`def_meta`, `prop_inc`, `prop_compose`, `prop_normal`, `prop_flex`, `prop_inc_strengthen`, `def_extra`).

- [ ] **Step 1: Create the module skeleton with the isolated import set.**

Create `fresco/algo/prop_metasubst.v` with exactly:
```coq
Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.predicates.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_stability.
Require Import src.fresco.algo.prop_decorate.
Require Import src.fresco.algo.prop_flex.
Require Import src.fresco.algo.prop_compose.
Require Import src.fresco.algo.prop_normal.
Require Import src.fresco.algo.prop_inc_strengthen.
Set Implicit Arguments.

(* ==================== §C  msubst / is_id basics ==================== *)
(* (lemmas pasted here in Step 3) *)
```
Note: this list is `prop_consis_complete`'s imports **minus** `def_decorated`, `def_decl_algo`, `prop_refine`, `prop_consis_sound`, `prop_precise`, `prop_precise_recover`, `prop_mono_bridge`. If a moved lemma fails to compile for a missing base symbol, add the *base* file that defines it (never a consistency file); if it needs a consistency symbol, it is a bridge — leave it in `prop_consis_complete.v`.

- [ ] **Step 2: Register the new file with the build (if enumerated).**

Run:
```bash
grep -rl "prop_consis_complete" _CoqProject Makefile* 2>/dev/null
```
If a file lists `.v` files explicitly, add `fresco/algo/prop_metasubst.v` on the line **before** `fresco/algo/prop_consis_complete.v`. If the build globs `fresco/**/*.v`, no change needed.

- [ ] **Step 3: Move the §C lemmas.**

For each §C lemma listed in the Interfaces block: locate it in `fresco/algo/prop_consis_complete.v` (`grep -n '^Lemma <name>' fresco/algo/prop_consis_complete.v`), cut its full `Lemma … Qed.` (including its leading comment) out, and paste it under the §C header in `prop_metasubst.v`, preserving order-of-dependency (a lemma must appear after the lemmas it uses). `a_assign_subject_flex_local` uses `a_assign` (from `def_extra`, not consistency) — it belongs here; keep it. If its proof references a `prop_consis_sound` lemma, leave it in `prop_consis_complete.v` instead and drop it from this task.

- [ ] **Step 4: Add the import to `prop_consis_complete.v`.**

In `fresco/algo/prop_consis_complete.v`, add after the existing `Require Import src.fresco.algo.prop_inc_strengthen.` line:
```coq
Require Import src.fresco.algo.prop_metasubst.
```

- [ ] **Step 5: Compile the new module, then the downstream chain.**

Run:
```bash
coqc -R . src -w -deprecated-hint-without-locality,-omega-is-deprecated fresco/algo/prop_metasubst.v; echo "meta rc=$?"
for f in prop_consis_complete prop_consis_exist; do
  coqc -R . src -w -deprecated-hint-without-locality,-omega-is-deprecated fresco/algo/$f.v; echo "$f rc=$?"
done
grep -c 'admit\.' fresco/algo/prop_consis_complete.v
```
Expected: all `rc=0`; admit count `12`. If a moved lemma fails in `prop_metasubst.v` on a missing symbol, move that missing base lemma too or (if consistency) revert that one lemma back to `prop_consis_complete.v`.

- [ ] **Step 6: Commit.**

```bash
git add fresco/algo/prop_metasubst.v fresco/algo/prop_consis_complete.v _CoqProject Makefile 2>/dev/null
git commit -m "$(printf '%s\n' '[mech] prop_metasubst.v: extract metasubst/is_id basics (section C)' '' 'Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>')"
```

---

### Task 3: Move §B (downarrow ⇓ theory)

**Files:**
- Modify: `fresco/algo/prop_metasubst.v` (add §B section)
- Modify: `fresco/algo/prop_consis_complete.v` (remove §B lemmas)

**Interfaces:**
- Consumes: §C basics (Task 2), base files.
- Produces: `msubst_ptyp_mono_pointwise`, `aenv_msubst_image_mono`, `aenv_msubst_image_wf`, `aenv_msubst_image_ftv_closed`, `a_wf_ptyp_msubst_mono`, `mono_ftv_wf`, `mono_downarrow`, `a_wf_ptyp_downarrow_mono`, `msubst_ptyp_ftv`, `downarrow_ftv_closed`, `downarrow_app_agree_ptyp`, `aenv_msubst_flex_head`, `aenv_msubst_flex_def_head`, `mono_downarrow_from_var`, `a_tyequiv_to_downarrow_mono`, `a_tyequiv_to_downarrow`, `msubst_downarrow_tyequiv`, `msubst_compose_downarrow_tyequiv`, `msubst_pskl_compose_downarrow_tyequiv`, `aenv_msubst_dom_inv`, `a_wf_aenv_app_r`, `a_wf_ptyp_ftv_dom`, `Ltac wk`.

- [ ] **Step 1: Add the §B header** to `prop_metasubst.v` under §C:
```coq
(* ==================== §B  downarrow (⇓) theory ==================== *)
```

- [ ] **Step 2: Move the §B lemmas** listed in Interfaces from `prop_consis_complete.v` to under the §B header, in dependency order (`a_wf_aenv_app_r` and `downarrow_app_agree_ptyp` early; `mono_downarrow`/`a_wf_ptyp_downarrow_mono` before their users; `a_tyequiv_to_downarrow_mono` before `a_tyequiv_to_downarrow`; the `*_downarrow_tyequiv` after `a_tyequiv_to_downarrow`). Move `Ltac wk` too (it is used by §B proofs). Keep `a_wf_ptyp_ftv_dom` here (it is pure wf; if it is already defined in a base file, delete the duplicate instead of moving).

- [ ] **Step 3: Compile module + chain + invariant.**
```bash
coqc -R . src -w -deprecated-hint-without-locality,-omega-is-deprecated fresco/algo/prop_metasubst.v; echo "meta rc=$?"
for f in prop_consis_complete prop_consis_exist; do
  coqc -R . src -w -deprecated-hint-without-locality,-omega-is-deprecated fresco/algo/$f.v; echo "$f rc=$?"
done
grep -c 'admit\.' fresco/algo/prop_consis_complete.v
```
Expected: all `rc=0`; admit count `12`. NOTE: `join_pskl_downarrow_mono_scoped` uses `ad_pat_consis` — it is a **bridge**, do NOT move it; it stays in `prop_consis_complete.v` and now depends on the moved §B lemmas via the import.

- [ ] **Step 4: Commit.**
```bash
git add fresco/algo/prop_metasubst.v fresco/algo/prop_consis_complete.v
git commit -m "$(printf '%s\n' '[mech] prop_metasubst.v: extract downarrow (⇓) theory (section B)' '' 'Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>')"
```

---

### Task 4: Move §A (`a_inc_equiv` theory)

**Files:**
- Modify: `fresco/algo/prop_metasubst.v` (add §A section)
- Modify: `fresco/algo/prop_consis_complete.v` (remove §A lemmas)

**Interfaces:**
- Consumes: §B, §C, base files.
- Produces: `a_inc_equiv_refl`, `a_inc_dom_sub`, `is_id_inc_unique`, `opt_axiom_factor`, `a_inc_equiv_msubst_mono`, `a_inc_equiv_msubst_ptyp`, `a_inc_equiv_msubst_pskl`, `a_inc_id_mid_strip`, `a_inc_equiv_uniq_l`, `a_inc_equiv_uniq_r`, `a_inc_equiv_mid_insert_flex`, `a_inc_equiv_mid_insert_var`, `a_inc_strip_decls_prefix`, `a_inc_var_mid_strip_id`, `a_inc_equiv_tvar_inv`, `a_inc_equiv_var_typ_inv`, `a_inc_equiv_var_skl_inv`, `a_inc_equiv_suffix_target`, `a_inc_equiv_inc_peel_suffix`, `a_inc_equiv_trans`, `a_inc_equiv_compose`, `msubst_compose_id_compose`, `a_inc_equiv_glue`, `a_inc_self_downarrow`, `a_inc_equiv_self_downarrow`, `msubst_compose_cons_l_id`, `msubst_compose_is_id_r`.

- [ ] **Step 1: Add the §A header** at the *top* of the sections in `prop_metasubst.v` region (or below §B — order inside the file only matters for dependency; `a_inc_equiv_*` depend on §B/§C so put §A last):
```coq
(* ==================== §A  a_inc_equiv theory ==================== *)
```

- [ ] **Step 2: Move the §A lemmas** in dependency order (`a_inc_equiv_refl`, `a_inc_dom_sub`, `is_id_inc_unique` first; the `_inv`/`uniq` lemmas; then `a_inc_equiv_trans`/`compose`/`glue`; `mid_insert_flex` needs `a_inc_mid_strip_flex` from `prop_inc_strengthen` (available); `a_inc_self_downarrow`/`a_inc_equiv_self_downarrow` need §B). `opt_axiom_factor`, `msubst_compose_cons_l_id`, `msubst_compose_is_id_r`, `msubst_compose_id_compose` move too.

- [ ] **Step 3: Compile module + chain + invariant** (same commands as Task 3 Step 3). Expected: all `rc=0`; admit `12`. `consis_downarrow_subject` and `ad_pat_consis_strengthen` are bridges — verify they stayed in `prop_consis_complete.v`.

- [ ] **Step 4: Sanity — `prop_consis_complete.v` is now consis-only.**
```bash
grep -c '^Lemma ' fresco/algo/prop_consis_complete.v
grep -c '^Lemma \(msubst\|a_inc\|a_tyequiv\|a_pskl_tyequiv\|aenv_msubst\|mono_downarrow\|downarrow\|is_id\)' fresco/algo/prop_consis_complete.v
```
Expected: total lemma count dropped by ~54; the metasubst-named count is now only the bridge lemmas (≤ ~3, all mentioning `ad_pat_consis`/`ad_wf_pskl`).

- [ ] **Step 5: Commit.**
```bash
git add fresco/algo/prop_metasubst.v fresco/algo/prop_consis_complete.v
git commit -m "$(printf '%s\n' '[mech] prop_metasubst.v: extract a_inc_equiv theory (section A); consis_complete is now consis-only' '' 'Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>')"
```

---

### Task 5: Generalize the inert-binder mid-insert

**Files:**
- Modify: `fresco/algo/prop_metasubst.v`

**Interfaces:**
- Consumes: `a_inc_equiv_mid_insert_var` (Task 4), `a_inc_equiv__var/var_skl/tvar` constructors (`def_meta`).
- Produces: `a_inc_equiv_mid_insert_binder` — one lemma inserting an inert `abind` middle (var_typ / var_skl / tvar; NO metasubst entry) at the `Ξ | Θ0` boundary of an `a_inc_equiv`, with `a_inc_equiv_mid_insert_var` re-derivable from it (or deleted in favor of it).

- [ ] **Step 1: Read `a_inc_equiv_mid_insert_var`** (its structure is the template) and the three inert `a_inc_equiv__var/__var_skl/__tvar` constructors in `def_meta.v` to confirm they share the shape `((y~b)++Θ) ≤ρ (Ξv ++ (y~b') ++ Θ')` with `Θ' ⊢ b'≡ b`-style middle and no metasubst consumption.

- [ ] **Step 2: State the general lemma.** Add to `prop_metasubst.v` (§A):
```coq
(* One inert-binder mid-insert, parameterized over the boundary binding.
   Instantiates to var_typ (=old a_inc_equiv_mid_insert_var), var_skl, tvar. *)
Lemma a_inc_equiv_mid_insert_binder :
  forall Ξ x Θ0 Θ' Ξv (mkΘ mkΘ' : abind) ρ1 ρ2 σ1 σ2,
  a_decls Ξ ->
  uniq (Ξ ++ Θ0) ->
  dom ρ1 [=] dom Ξ -> dom σ1 [=] dom Ξ ->
  (* the constructor-specific inert middle premise for (mkΘ, mkΘ') over Θ' and ρ2 *)
  (* ... fill from the concrete constructor family ... *)
  a_suffix Ξv ->
  a_inc_equiv (Ξ ++ Θ0) (ρ1 ++ ρ2) (σ1 ++ σ2) Θ' ->
  a_inc_equiv (Ξ ++ (x ~ mkΘ) ++ Θ0) (ρ1 ++ ρ2) (σ1 ++ σ2)
              (Ξv ++ (x ~ mkΘ') ++ Θ').
```
Because the three constructors differ in the *middle premise* (`≡ᵗ` for var_typ, `≡ˢ` for var_skl, none for tvar), the clean generalization is either (a) a lemma **per relation** but one for var_typ+var_skl if you thread the middle as a hypothesis, or (b) three thin corollaries of the flex-free induction. Prefer whichever removes the most copy-paste while keeping every call site typed. If a single statement is awkward, keep `a_inc_equiv_mid_insert_var` and ADD `a_inc_equiv_mid_insert_var_skl` + `a_inc_equiv_mid_insert_tvar` by copying the proof with the constructor swapped — but factor the shared induction body into a local `Ltac` so it is written once.

- [ ] **Step 3: Rewrite `skip_tm_var_case`'s call site** (in `prop_consis_complete.v`) to use the generalized lemma if the var-typ instance name changed; otherwise no change.

- [ ] **Step 4: Compile module + chain + invariant** (Task 3 Step 3 commands). Expected: `rc=0`; admit `12`.

- [ ] **Step 5: Commit.**
```bash
git add fresco/algo/prop_metasubst.v fresco/algo/prop_consis_complete.v
git commit -m "$(printf '%s\n' '[mech] prop_metasubst: unify inert-binder mid-insert (var_typ/var_skl/tvar)' '' 'Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>')"
```

---

### Task 6: Make `msubst_downarrow_tyequiv` the single downarrow-tyequiv primitive

**Files:**
- Modify: `fresco/algo/prop_metasubst.v`

**Interfaces:**
- Consumes: `msubst_downarrow_tyequiv` (`Θt ⊢ B ≡ᵗ ⇓ᵗ[Θ]B`), `a_tyequiv_to_downarrow`, `a_tyequiv_pskl`, `msubst_ptyp_compose`, `downarrow_app_agree_ptyp`.
- Produces: `msubst_compose_downarrow_tyequiv` and `msubst_pskl_compose_downarrow_tyequiv` re-proved as *derivations* (not fresh inductions), same signatures.

- [ ] **Step 1: Re-prove `msubst_compose_downarrow_tyequiv`** as: for `X ∈ dom ρ`, `msubst_lookup (compose (aenv_msubst Θ) ρ) X = ⇓ᵗ[Θ](ρ X)` and `≡ ρ X` by `msubst_downarrow_tyequiv` on the image; for `X ∉ dom ρ`, both sides are `X`. Keep the current induction only if the derivation is longer; the goal is one shared primitive, not necessarily fewer lines. If it does not shrink, leave a comment `(* primitive: msubst_downarrow_tyequiv *)` and move on — do not regress.

- [ ] **Step 2: Re-prove `msubst_pskl_compose_downarrow_tyequiv`** by lifting the ptyp version through `a_tyequiv_pskl` at the `pskl_var` leaves (it already does this at the var case; ensure it *calls* `msubst_compose_downarrow_tyequiv`/`msubst_downarrow_tyequiv` rather than re-deriving `⇓τ≡τ`).

- [ ] **Step 3: Compile module + chain + invariant.** Expected: `rc=0`; admit `12`.

- [ ] **Step 4: Commit.**
```bash
git add fresco/algo/prop_metasubst.v
git commit -m "$(printf '%s\n' '[mech] prop_metasubst: derive compose/pskl downarrow-tyequiv from one primitive' '' 'Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>')"
```

---

### Task 7: Factor the shared self-downarrow induction (only if clean)

**Files:**
- Modify: `fresco/algo/prop_metasubst.v`

**Interfaces:**
- Consumes: `a_inc_self_downarrow`, `a_inc_equiv_self_downarrow`.
- Produces: a shared `Ltac self_downarrow_case` (or a shared helper lemma) used by both, OR — if factoring is not clean — an unchanged pair with a cross-reference comment.

- [ ] **Step 1: Diff the two proofs** (`a_inc_self_downarrow` vs `a_inc_equiv_self_downarrow`). They share the `Θpre`-threaded induction and the flex/flex_def/var/var_skl/tvar case dispatch; they differ only in the constructor applied (`a_inc__*` vs `a_inc_equiv__*`) and the extra `≡` premise. Extract the common per-case bookkeeping (the `HwfΘ'`, `Hdd`, `simpl_env`/`replace` reassociation) into `Ltac self_downarrow_prep := …`.

- [ ] **Step 2: Rewrite both proofs to call the Ltac.** If the Ltac makes both proofs materially shorter and both still `Qed`, keep it. If it is fragile or barely helps, revert Step 1–2 and instead add a one-line comment on `a_inc_equiv_self_downarrow`: `(* twin of a_inc_self_downarrow; same Θpre-threaded induction *)`. Do not force it.

- [ ] **Step 3: Compile module + chain + invariant.** Expected: `rc=0`; admit `12`.

- [ ] **Step 4: Commit.**
```bash
git add fresco/algo/prop_metasubst.v
git commit -m "$(printf '%s\n' '[mech] prop_metasubst: share the self-downarrow induction skeleton' '' 'Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>')"
```

---

### Task 8: Full build + axiom check + notes

**Files:**
- Verify: whole `fresco/` subtree
- Modify: memory/dir-notes if a path map exists

- [ ] **Step 1: Full build.**
```bash
cd /Users/jiangsy/Documents/HKU/Research/impredicative/mechanization
make coq 2>&1 | tail -15; echo "make rc=${PIPESTATUS[0]}"
```
Expected: build succeeds (or the same pre-existing failures as before this work — compare against `git stash`-clean baseline if unsure). If `make coq` is not the target, use the repo's documented build command.

- [ ] **Step 2: Axiom check on the flagship + moved keystones.**
```bash
cat > /tmp/axck.v <<'EOF'
Require Import src.fresco.algo.prop_consis_complete.
Print Assumptions skip_tm_var_case.
Print Assumptions a_inc_self_downarrow.
Print Assumptions consis_downarrow_subject.
EOF
coqc -R . src -w -all /tmp/axck.v 2>&1 | grep -A1 "Assumptions\|Closed"
```
Expected: `skip_tm_var_case` and `a_inc_self_downarrow` are `Closed under the global context`.

- [ ] **Step 3: Update the dir map / memory** if `mechanization/docs/*` or the project memory records file responsibilities — add `prop_metasubst.v` (= the completeness-side metasubst theory: `a_inc_equiv` + ⇓ + msubst) and note `prop_consis_complete.v` is now consis-only.

- [ ] **Step 4: Commit.**
```bash
git add -A
git commit -m "$(printf '%s\n' '[mech][docs] metasubst isolation complete: full build green, notes updated' '' 'Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>')"
```

---

## Execution outcome (2026-07-16)

- **Task 1** — DONE (commit 10d5860). Cycle broken: `Scheme`/`Combined Scheme
  a_assign_unify_consis_mutind` → `def_extra.v`; `a_flex_tvar_weaken_prefix`
  → `prop_inc.v`. `prop_inc_strengthen` now imports no consis file.
- **Tasks 2–4** — DONE (commit 037097c). `prop_metasubst.v` created (1790 lines,
  0 admits, consis-free): 72 lemmas (a_inc_equiv / ⇓ / msubst basics).
  `prop_consis_complete.v` = optimality defs + consis↔metasubst bridge + flagship
  only (admit=12, unchanged). Also relocated `a_wf_aenv_uniq` → `prop_flex.v`
  and dropped a duplicate `mono_ptyp_to_pskl_guarded` from `prop_consis_sound`.
- **Task 5** — NO-OP. Premise false: only two mid-insert lemmas exist
  (`a_inc_equiv_mid_insert_flex`, `_var`); no `_skl`/`_tvar` variants. The two
  are structurally different (flex binder + metasubst mid-entry vs. inert var
  binder + target-aenv suffix growth) and each is used once; merging would force
  an artificial disjunction, not remove duplication.
- **Task 6** — ALREADY SATISFIED. `msubst_downarrow_tyequiv` is already the single
  primitive; both `msubst_compose_downarrow_tyequiv` and its pskl mirror invoke
  it. The ptyp/pskl split cannot collapse further — `pskl` carries holes (□) not
  in the image of `ptyp_to_pskl`, so the pskl induction is not derivable from the
  ptyp one.
- **Task 7** — DONE (commit dd11f87). `a_inc_self_downarrow_bundle` proves the
  a_inc + a_inc_equiv conjunction by one 6-case induction; the two originals are
  `proj1`/`proj2` wrappers (call sites unchanged). All three Closed; build green.
- **Task 8** — DONE. Full `make coq` green; `skip_tm_var_case`,
  `a_inc_self_downarrow`, `consis_downarrow_subject`, and the bundle/projections
  all Closed under the global context; flagship corollaries depend only on the
  pre-existing admitted `a_assign_unify_consis_optimal` (no new axioms);
  `prop_consis_complete` admit count 12 throughout.

## Self-review notes

- **Spec coverage:** layering (Task 2 imports enforce it), §A/§B/§C partition (Tasks 2–4), bridge stays (verified in Tasks 3–4 Step 3 notes), generalizations 1–3 (Tasks 5–7), cycle fix (Task 1 — moved first, per the transitive-dep finding), incremental green-per-commit (every task Steps compile the chain + check admit=12). All covered.
- **Escape hatches are explicit, not placeholders:** each "if a lemma references a consistency symbol → it's a bridge, leave it" is a concrete decision rule with the grep to detect it; each generalization has a "if it doesn't shrink/clean up, keep the pair + Ltac/comment" fallback so no step is open-ended.
- **Invariant is uniform:** every task ends by recompiling `prop_consis_complete` + `prop_consis_exist` and asserting admit `12`, so a regression is caught at the task that caused it.
