> ## ⛔ SUPERSEDED — HISTORY ONLY (marked 2026-08-09)
>
> This hand-off describes the May-2026 removal of `typ_all_plain` from a
> single `typ` grammar, with a parallel colourless `ctyp`.  **Both `typ` and
> `ctyp` are gone.**  The Phase-A type-hierarchy refactor replaced them with
> six sorts — `ptyp` / `btyp` / `utyp` / `pskl` / `bskl` / `uskl` — and
> `grep -rn 'typ_all_plain\|\bctyp\b' frost/` now returns nothing.  The
> "Build RED" status below refers to a tree that no longer exists.
>
> Kept because it records *why* the plain ∀ had to leave the decorated
> universe — the argument that Phase A then generalised.  Do not follow its
> instructions.

# Handoff — typ_all_plain removal refactor (in progress)

**Status as of this commit:** Build RED. Foundation laid (commits `7bd8962`, `acfbd03`); decl-side proof cascade ~5% done.

## What's done

1. **language.ott** — `typ_all_plain` removed from `typ` grammar; `ctyp`
   inductive added (parallel to `typ` but with no decoration: ctyp_unit,
   ctyp_var_f, ctyp_arrow, ctyp_all, ctyp_hole, ctyp_tophole).
2. **Makefile** — added sed pass: `Notation ctypvar := typvar.` so
   ott/lngen-generated `ctypvar` (alias of `var`) becomes definitionally
   identical to `typvar`. Without this, `eq_dec` picks distinct
   typeclass instances and `destruct (eq_var X Y); reflexivity.` fails
   to discharge both sides of equations. Verified working.
3. **frost/def_ott.v** + **frost/prop_ln.v** — regenerated via
   `make ott lngen`. ctyp gets full lngen instrumentation.
4. **frost/def_extra.v** — `is_utyp__pall` and `is_uskel__pall`
   dropped (typ_all_plain shapes gone).
5. **frost/ltac_utils.v** — `discharge_category` Ltac: dropped
   `H : is_X (typ_all_plain _) |- _ => inversion H` patterns.
6. **frost/decl/def_extra.v** — major rule-definition surgery:
   - Hand-written ctyp infra removed (now ott-generated).
   - `erase` Fixpoint: dropped `typ_all_plain` case.
   - WF predicates (`d_wf_skel`, `d_wf_utyp`, `d_wf_uskel`): dropped
     `*_plain` / `__pall` constructors.
   - `d_consis`: DROPPED `__forall_inh_untagged`, `__forall_syn_untagged`
     (paper-unfaithful cross-world rules — paper's `bid{T}` LHS
     grammar admits syn-tagged + inh but NOT untagged syn). ADDED
     `__forall_syn` (mirror of `__forall_inh` for typ_all_col
     colour_syn LHS=RHS) — this is **the key rule** that closes the
     D12 `__app` admit once the cascade is green.
   - `d_sub`: dropped `__forall_l_untagged`.
   - `d_refine`: rewrote rule conclusions to use
     `typ_all_col colour_syn` instead of `typ_all_plain` (paper's
     untagged-syn forall role transferred to colour_syn).
   - `d_pat_consis`: dropped `__forall_inh_untagged`,
     `__forall_syn_untagged`.
   - `d_pat_sub`: dropped `__forall_l_untagged`; dropped the
     `SS <> typ_all_plain _` guard in `__univ_ghost_r`.
7. **frost/decl/prop_basic.v** — fully repaired:
   - Deleted vacuous `is_*_inv_plain` inversion lemmas (6 of them).
   - Deleted `syn_color_not_plain` / `inh_color_not_plain`.
   - `syn_color_t` / `inh_color_t` Fixpoint defs: dropped typ_all_plain
     case.
   - `is_utyp_lc`, `is_uskel_lc`, `is_utyp_subst`, `is_uskel_subst`:
     dropped `__pall` bullets.
   - `syn_color_t_*` / `inh_color_t_*` lemmas: dropped one bullet each
     (the typ_all_plain bullet in induction over typ).

## What's left (~6+ hours of focused editing)

### frost/decl/prop_wellformed.v (in-progress, partial)
22 references to fix. Pattern: drop bullets for `__pall` / `*_plain`
cases in `induction H`, where `H` is now over a smaller relation.
Started — first two `d_wf_*_weakening` and `d_wf_utyp_tvar_morph` done.
Remaining: 15+ similar bullet drops, plus the `d_refine`-wf proof at
lines 767+ which now produces `typ_all_col colour_syn` outputs (apply
`d_wf_skel__all_col colour_syn` instead of `d_wf_skel__all_plain`).

### frost/decl/prop_subtyping.v
17 references. Many proofs case-split on `d_consis` / `d_sub` (which
lost rules). Drop those bullets. Comments mentioning typ_all_plain can
be left or updated.

### frost/decl/prop_typing.v (5000 lines, largest)
24 direct references plus indirect cascade. Key targets:
- `d_consis_gen` Inductive (around line 944): drop
  `__forall_inh_untagged`, `__forall_syn_untagged`; ADD `__forall_syn`
  mirror (parallel to the one in d_consis).
- `d_consis_gen__embed` lemma (~line 994): update for the new rule set.
- `d_consis_gen_to_d_consis` (~line 4391): update for the new rule set.
- Hundreds of bullet drops in proofs that case-split on
  `d_consis` / `d_sub` / `d_consis_gen`.

### frost/decl/prop_skeleton.v
5 references. `d_refine_*_split` lemmas: signatures change from
`d_refine ... (typ_all_plain P) Q` to
`d_refine ... (typ_all_col colour_syn P) Q`, similarly for outputs.

### frost/algo/def_extra.v
19 references. Same surgery applied to algo rules:
`a_wf_typ`, `a_non_flex`, `a_non_flex_poly`, `a_guess_mono`,
`a_pre_sub`, `a_pre_join`, `a_unify`, `a_consis` untagged variants,
`a_broom`. Drop typ_all_plain shapes; for genuinely-needed
"untagged-syn polytype" role, replace with `typ_all_col colour_syn`.

### frost/algo/prop_soundness.v + prop_completeness.v
Cascade from algo def_extra.

### Final: close D12 admits
With the cascade green, the new `__forall_syn` rule unlocks:
- `d_consis_gen_refl` (build via __forall_syn for typ_all_col colour_syn).
- D12 `__app` admit (function-side mode-shift via
  `d_consis_gen Δ Γ A0_arg P'` with `P'` syn-painted polytype, now
  derivable via __forall_syn).
- D12 `__abs / __abs_anno` (m_new = mode_fn k) admits — similar
  function-side closure.
- After D12 is fully Qed, `d_typing_general_subsumption_via_gen`
  (paper D1, Lemma 3.1) is Qed via the wrapper.

## Build-resume recipe

```sh
cd /Users/jiangsy/Documents/HKU/Research/impredicative/mechanization
make coq 2>&1 | tail -20   # see next error
```

Fix file-by-file. For proofs that genuinely break (rule they depended
on is gone with no replacement), `Admitted.` with a comment "post
typ_all_plain refactor — needs restating" is acceptable as a
checkpoint.

## Why this refactor was right

User's design insight: "plain_all and colored_all are never mixed
used, so they can be separated." Confirmed by audit:

- Paper's `bid{T}` grammar (syntax-directed.tex:14–19) admits LHS for
  typconsis as `syn{∀^ε α.}T`, `syn{∀α.}T`, or `inh{∀α.}T`. Mech's
  `typ_all_plain T` (untagged-syn) lived in the same AST as
  `typ_all_col colour_*` (decorated), but the cross-world `__forall_*_untagged`
  rules treating typ_all_plain LHS as untagged-syn input to coloured-world
  judgments were paper-unfaithful.
- After the refactor: typ has only decorated shapes; ctyp (paper's
  plain forall) lives separately; the painted `typ_all_col colour_syn`
  plays paper's "untagged-syn" role faithfully.
- The 5th rule (`d_consis__forall_syn`) the previous
  `[paper-mismatch-flag 2026-05-16]` anticipated is now real.

## Commit log

- `7bd8962` — Foundation: ctyp to def_ott, drop typ_all_plain, drop
  unfaithful d_consis/d_sub/d_pat rules, add __forall_syn.
- `acfbd03` — prop_basic.v cascade fix.
