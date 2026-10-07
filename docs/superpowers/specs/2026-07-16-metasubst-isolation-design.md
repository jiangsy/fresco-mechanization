# Design — isolate the metasubstitution theory into `prop_metasubst.v`

Date: 2026-07-16. Branch: `re-mech`.

## Problem

`fresco/algo/prop_consis_complete.v` has grown to ~3.6k lines and 89 top-level
lemmas, of which **58 are pure metasubstitution / `a_inc` / `a_inc_equiv` / `≡ᵗ` /
downarrow lemmas** with no dependency on consistency. They accreted there because
the optimality development (the GMM ⇓-normalizing factoring) was written inline.
This makes the file hard to navigate, hides the real layering, and forces
special-case lemmas (e.g. `a_inc_equiv_mid_insert_flex` vs `…_var`, three separate
`*_downarrow_tyequiv` inductions, `a_inc_self_downarrow` vs
`a_inc_equiv_self_downarrow`).

By contrast `prop_consis_sound.v` (5.6k lines) defines **zero** metasubst lemmas
and references only the *base* metasubst layer (`a_inc_*`, `≡ᵗ`, `a_isub` via
`def_meta` + `prop_inc`). It never touches `a_inc_equiv`, `aenv_msubst`/⇓, or
`msubst_compose`. This is not accidental: **soundness builds/inverts increments;
optimality/completeness compares a competing increment against the algorithm's**,
and that comparison (factoring) is exactly what `a_inc_equiv` and the downarrow
normalization exist for. So the deep metasubst theory is *completeness-side only*.

## Goal

Extract the completeness-side metasubst theory into a single new module
`fresco/algo/prop_metasubst.v`, sibling to `prop_consis_sound` and directly below
`prop_consis_complete`, so:

```
def_meta ─┬─ prop_inc (a_inc, ≡ᵗ) ──────────────────────────── prop_consis_sound
          └─ prop_compose ─ prop_normal ─ prop_metasubst (NEW) ─ prop_consis_complete
                       (a_inc_equiv, ⇓ downarrow, msubst compose)
```

The module graph *enforces* the isolation: `prop_metasubst.v` imports only
`def_meta` + the base metasubst/wf files, and **must not** import `def_decl_algo`
or `def_decorated` (the consistency definitions).

## Non-goals

- Not merging the existing base files `prop_inc` / `prop_compose` / `prop_normal`
  into `prop_metasubst.v` — they are already correctly isolated below consistency
  and are not the source of the bloat.
- Not the invasive `_ptyp`/`_pskl`/`_btyp`/`_bskl` unification via a shared
  `MSubstable` abstraction over the four ASTs. (Deferred; see "Later".)
- No new results and no weakening of any lemma consistency relies on — this is
  relocation plus generalization that only *strengthens* interfaces.

## `prop_metasubst.v` contents

Three labelled sections. The categorization rule: a lemma **moves** iff it does
not mention `ad_pat_consis` / `ad_wf_pskl` / the optimality `*_post` defs;
otherwise it **stays** (see Bridge).

- **§A — `a_inc_equiv` theory.** `a_inc_equiv_refl`, `a_inc_dom_sub`,
  `is_id_inc_unique`, `a_inc_equiv_uniq_l/r`, `a_inc_equiv_{tvar,var_typ,var_skl}_inv`,
  `a_inc_equiv_suffix_target`, `a_inc_equiv_inc_peel_suffix`, `a_inc_equiv_trans`,
  `a_inc_equiv_compose`, `a_inc_equiv_glue`, `a_inc_equiv_msubst_{ptyp,pskl}`,
  `a_inc_equiv_mid_insert_flex`, `a_inc_equiv_mid_insert_var`,
  `a_inc_strip_decls_prefix`, `a_inc_id_mid_strip`, `a_inc_var_mid_strip_id`,
  `a_inc_self_downarrow`, `a_inc_equiv_self_downarrow`, `opt_axiom_factor`,
  `msubst_compose_cons_l_id`, `msubst_compose_is_id_r`, `msubst_compose_id_compose`.
- **§B — downarrow ⇓ theory.** `msubst_ptyp_mono_pointwise`,
  `aenv_msubst_image_{mono,wf,ftv_closed}`, `a_wf_ptyp_msubst_mono`, `mono_ftv_wf`,
  `mono_downarrow`, `a_wf_ptyp_downarrow_mono`, `msubst_ptyp_ftv`,
  `downarrow_ftv_closed`, `downarrow_app_agree_ptyp`, `aenv_msubst_flex_head`,
  `aenv_msubst_flex_def_head`, `mono_downarrow_from_var`,
  `a_tyequiv_to_downarrow_mono`, `a_tyequiv_to_downarrow`, `msubst_downarrow_tyequiv`,
  `msubst_compose_downarrow_tyequiv`, `msubst_pskl_compose_downarrow_tyequiv`,
  `aenv_msubst_dom_inv`, `a_wf_aenv_app_r`.
- **§C — msubst / is_id basics.** `a_inc_msubst_lc`, `is_id_msubst_values_lc`,
  `msubst_lc_compose`, `msubst_pskl_open_{rec_,}lc_local`,
  `msubst_compose_id_{ptyp,pskl}`, `metasubst_dom_empty`, `msubst_lookup_mid_drop`,
  `msubst_compose_app`, `msubst_pskl_ftv_lower`, `msubst_lookup_app_in`,
  `a_tyequiv_strengthen_tvar_cons`, `a_pskl_tyequiv_strengthen_tvar_cons`,
  `a_assign_subject_flex_local` (metasubst-adjacent; if it needs `a_assign` it may
  stay — decide at move time), `aenv_mid_split`, `binds_strengthen`,
  `binds_sub_cons`.

(Exact membership is finalized during execution by the "no consis symbol" grep;
the lists above are the expected partition.)

## Bridge — stays at the top of `prop_consis_complete.v`

The lemmas that genuinely mention `ad_pat_consis` / `ad_wf_pskl`:
`join_pskl_downarrow_mono_scoped`, `consis_downarrow_subject`,
`ad_pat_consis_strengthen`, `ad_wf_pskl_strengthen`, `a_binds_tvar_strengthen`
(+ the `str_forall` Ltac). After extraction `prop_consis_complete.v` holds only:
optimality defs (`a_consis_problem`/…/`*_optimal_post`), this bridge, the case
lemma `skip_tm_var_case`, and the theorem `a_assign_unify_consis_optimal` +
corollary.

## Opportunistic generalization (the "common lemma, not special-case" pass)

Approved to change statements where it kills duplication; every consumer is
re-verified by recompiling the downstream chain.

1. **Inert-binder mid-insert.** Keep `a_inc_equiv_mid_insert_flex` (it splices a
   *metasubst* entry). Replace the per-binding var/var_skl/tvar inserts with one
   `a_inc_equiv_mid_insert_binder` parameterized over the inert `abind` (no
   metasubst entry), so the pending SkipTmVar(skl)/SkipRigid mirrors need no new
   lemma. `a_inc_equiv_mid_insert_var` becomes a thin instance (or is subsumed).
2. **Downarrow-tyequiv primitive.** Make `msubst_downarrow_tyequiv` (`Θt ⊢ B ≡ᵗ
   ⇓ᵗ[Θ]B`) the single primitive; **derive** `msubst_compose_downarrow_tyequiv`
   and its pskl mirror from it + `a_tyequiv_to_downarrow` + `a_tyequiv_pskl`,
   instead of three separate inductions.
3. **Self-downarrow.** `a_inc_self_downarrow` and `a_inc_equiv_self_downarrow`
   share the Θpre-threaded induction skeleton; factor the shared per-case reasoning
   if it comes out clean, otherwise leave a cross-reference. Do not force it.

## Backwards-dependency fix

`prop_inc_strengthen.v` imports `prop_consis_sound` — a metasubst-layer file
depending on consistency (a cycle-shaped smell). Check which symbol it needs; if
it is metasubst-level, relocate that symbol and drop the import. If it genuinely
needs a soundness fact, leave it and note why. (Bounded; do last.)

## Execution & verification

Strictly incremental on a green build:
1. Create `prop_metasubst.v` with the correct imports; move §C first (leaf
   basics), `coqc prop_metasubst.v` then `coqc prop_consis_complete.v` +
   `prop_consis_exist.v`; `git commit`.
2. Move §B, recompile chain, commit. Then §A, recompile, commit.
3. Apply each generalization (1–3) as its cluster lands; recompile; commit.
4. `prop_inc_strengthen` fix; full `make` (or the affected subtree); commit.
Every commit is green with the admit count on `prop_consis_complete` unchanged
(currently 12). Update `docs/CLAUDE`-style dir notes / memory if a path map exists.

## Risks

- **Import cycles.** `prop_metasubst` must sit below `prop_consis_complete` but a
  moved lemma might (wrongly) reference a consis symbol — caught immediately by
  `coqc` failing on a missing reference; fix = it's a bridge, keep it.
- **Notation scope.** `≡ᵗ`/`≡ˢ`/`⇓ᵗ`/`⇓ˢ`/`≤[ρ]` notations must be in scope in
  `prop_metasubst.v` (they come from `def_meta` / `prop_normal`).
- **Generalization breakage.** A generalized statement may not unify at an old
  call site; recompiling the chain after each move surfaces it before commit.
- **`Set Implicit Arguments` drift.** Moved lemmas keep the same implicit-args
  behavior (same `Set` at the top of the new file).

## Later (out of scope now)

- The `_ptyp`/`_pskl`/`_btyp`/`_bskl` unification via a `MSubstable`/section
  abstraction, once the layer is isolated and visible whole.
- Folding `prop_inc`/`prop_compose`/`prop_normal` into `prop_metasubst` for a
  single metasubst module, if desired.
