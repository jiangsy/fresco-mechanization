# Frost Mechanization — Progress

Coordination file for the Phase 2 + Phase 3 push. Read this before starting
any sub-agent task; the controller updates it after every dispatch and merge.

**Spec:** [`docs/superpowers/specs/2026-05-10-frost-phase23-design.md`](../docs/superpowers/specs/2026-05-10-frost-phase23-design.md)
**Phase 1 spec (predecessor):** [`docs/superpowers/specs/2026-05-09-frost-mechanization-design.md`](../docs/superpowers/specs/2026-05-09-frost-mechanization-design.md)

## Status legend

- 🔴 pending
- 🟡 in progress
- 🟠 blocked
- 🟢 done (merged into `mech`)

## Phase 1 (definitions only)

🟢 Complete. End state: every paper rule from `paper/sections/declarative.tex` has a corresponding `Inductive` constructor in `mechanization/frost/decl/def_extra.v`, full clean build, no `Admitted`. **Bug audit** of declarative rules against `paper/frost.pdf` performed `2026-05-10` and 9 fixes applied (commit `6b5f7c3`). Mutual block reduced to just `d_typing` ↔ `d_pat` (Phase 2.0 refactor, commit `721fded`).

## Phase 2 — Declarative metatheory

| Track | File | Status | Worktree | Notes |
|---|---|---|---|---|
| 2.A Foundation | `frost/decl/prop_basic.v` | 🟢 done | (mech) | Merged at mech@ddb7011. Exports: list_disjoint algebra (10 lemmas), lc_/subst preservation for 8 category predicates, ttyp→utyp / tskel→uskel embeddings, inversion lemmas for 8 categories, mutual induction principle d_typing_pat_mut, expanded discharge_category. |
| 2.B Wellformedness | `frost/decl/prop_wellformed.v` | 🟢 done (partial) | (mech) | Merged at mech@b990689. Exports: `d_wf_denv` + inversions, weakening (6 judgments), `d_wf_*_lc` helpers (6), substitution-preservation (6; `d_wf_skel_subst` needs `guarded_typ B`; `ttyp`/`utyp`/`tskel`/`uskel` per plan), `d_wf_skel_psi_weakening` / `_psi_incl` monotonicity, `d_wf_typ_strengthening` helpers, `ttyp→utyp` / `tskel→uskel` embeddings, `d_refine_preserves_wf` (paper:1380), `d_refine_syn_preserves_wf`, `d_wf_denv_binds_typ` / `_binds_skel`, `d_typing_pat_preserves_wf` (mutual; cross-track admits — see Open Admitted). |
| 2.C Subtyping | `frost/decl/prop_subtyping.v` | 🟢 done (partial) | (mech, direct) | Exports: `d_consis_refl_mono`, `d_sub_refl_mono`, `d_consis_weakening`/`_head`, `d_sub_weakening`, `d_consis_compose` (partial), `d_consis_extends_d_sub` (partial), `d_consis_empty_eq` (clean), `d_consis_empty_to_shallow_sub` (clean), `d_sub_sound` (clean, strictified to `is_typ A`), `d_shallow_sub_mono` (defined), `d_sub_complete_mono` (partial), `d_sub_no_guess_uniqueness` (admitted, paper-flagged). Closes Phase 2.B's `d_typing__sub` cross-track admit via new `d_consis_preserves_wf` (admitted var case) and `d_sub_preserves_wf` (clean) in `prop_wellformed.v`. |
| 2.D Typing + stability | `frost/decl/prop_typing.v` | 🔴 pending | (worktree TBA) | parallel after 2.B |
| 2.E Skeleton | `frost/decl/prop_skeleton.v` | 🟢 done (partial) | (mech, direct) | Exports: `d_pat_consis_preserves_wf` (narrowed; side wf hypothesis), `d_pat_sub_preserves_wf` (narrowed), splitting/inversion family (`d_refine_*_split` ×4 and `d_refine_syn_*_split` ×4 — all clean), `d_pat_preserves_skel_wf` (projection of `d_typing_pat_preserves_wf`), `d_pat_validity` (paper:1981; admitted), `d_pat_safety` (paper:1986; admitted). Phase 2.B `d_pat__sub` admit STAYS OPEN — see Open Admitted. |

## Phase 3 — Algorithmic system

| Track | File | Status | Worktree | Notes |
|---|---|---|---|---|
| 3.A Algo defs | `frost/algo/def_extra.v` | 🔴 pending | (worktree TBA) | parallel with 2.C-E (no decl-prop dep) |
| 3.B Algo soundness | `frost/algo/prop_soundness.v` | 🔴 pending | (worktree TBA) | sequential after 3.A + 2.{C,D,E} |
| 3.C Algo completeness | `frost/algo/prop_completeness.v` | 🔴 pending | (worktree TBA) | parallel with 3.B, same deps |

## Open Admitted

`prop_wellformed.v` — `d_typing_pat_preserves_wf` (mutual): partial. Most cases proven. Pending cases:

- `d_typing__sub` — CLOSED via `d_sub_preserves_wf` (Phase 2.C, mech@9ba2cf9..).
- `d_pat__sub` — blocked on `d_pat_sub_preserves_wf` (Phase 2.E).
- `d_typing__app` / `d_pat__app` — need refinement-side wf interaction (Phase 2.D / 2.E).
- `d_typing__abs` / `d_typing__abs_anno` / `d_pat__anno` / `d_pat__abs` / `d_pat__abs_check` / `d_pat__abs_anno` / `d_pat__abs_anno_check` — regularity gap. The rules provide `is_inh_typ A` / `is_inh_skel P` but not `d_wf_typ Γ A` / `d_wf_skel nil Γ P`. Fix in Phase 2.D / 2.E by threading explicit wf premises through the rules, or by proving a regularity lemma deriving wf from `is_*` plus context wf.

`prop_wellformed.v` — `d_consis_preserves_wf` (var case): admitted. `d_consis__var` lacks a `binds` premise so `d_wf_typ Γ (typ_var_f X)` cannot be derived. Close by either strengthening `d_consis__var` with a binds premise or by passing `d_wf_utyp Δ Γ T` as a precondition. Paper-flagged.

`prop_skeleton.v` — Phase 2.E admits:

- `d_pat_consis_preserves_wf` — NARROWED. The ghost rule [`d_pat_consis__ghost`] outputs a [`no_forall_typ P`] which does NOT imply [`d_wf_skel`] (free variables without binding). The forall-cases additionally need a Γ↔Ψ "move" lemma (same as the deferred typ→skel bridge). Narrowing: take [`d_wf_skel nil Γ P`] as a side hypothesis. Callers at the consumption sites have this in scope. Status: lemma exposed in narrowed form; proper structural version blocked by paper-level tensions.
- `d_pat_sub_preserves_wf` — NARROWED (same shape as above). Additional structural concern: [`d_pat_sub`]'s forall-l rules operate on [`typ_all_etag`] inputs ([`d_wf_uskel`] kind), whereas the conclusion of [`d_pat__sub`] in [`d_typing_pat_preserves_wf`] is [`d_wf_skel`] ([`typ_all_col c`] kind). No mechanical bridge between the two for the etag case. **Phase 2.B's `d_pat__sub` admit therefore stays open.**
- `d_pat_validity` (paper declarative.tex:1981) — admitted. Depends on Phase 3 refinement reflexivity on guarded skeletons, on inversion of [`d_pat_sub`] / [`d_pat_consis`] (the consis-side has the same paper-level issue as the ghost case), and on anti-symmetry interaction with [`d_typing__sub`].
- `d_pat_safety` (paper declarative.tex:1986) — admitted. Stronger than validity. The universal "refines every type" claim depends on a principal-skeleton construction (join operation on skeletons under refinement) which sits at the same maturity as the deferred algorithmic-side lemmas.

Paper-level tensions (do NOT attempt to fix mechanically; flag for paper revision):

- `d_pat__abs_check` produces [`(typ_tophole typ_hole) → Q`]. [`d_wf_skel`] doesn't admit [`typ_tophole typ_hole`] (paper declarative.tex line 1191 explicitly forbids it). The rule produces shapes the wf predicate rejects. Phase 2.B `d_pat__abs_check` admit remains for this reason.
- `d_pat__abs_anno_check` similarly produces [`typ_tophole A`] which may not be wf depending on [A]. Phase 2.B `d_pat__abs_anno_check` admit remains for this reason.

**Did the typ→skel bridge work?** No. Phase 2.B left [`d_wf_typ → d_wf_skel`] deferred to 2.E pending a "move from Γ to Ψ" lemma [`d_wf_skel Ψ ((X~dbind_tvar)++Γ) A → d_wf_skel (X::Ψ) Γ A`]. That move-lemma is the same one needed by the ghost / forall cases of [`d_pat_consis_preserves_wf`]. Establishing it requires a richer notion of variable scope split between Γ and Ψ; not attempted in Phase 2.E. The 2.B `d_pat__anno` / `d_pat__abs_anno` admits relating to the bridge therefore stay open.

`prop_subtyping.v` — strictifications:

| File:Line | Lemma | Status | Reason |
|---|---|---|---|
| prop_subtyping.v | `d_consis_refl_mono` | strictified | Original "d_consis_refl on is_typ" too strong: `d_consis` is asymmetric (utyp LHS, typ RHS). Narrowed to `mono_typ`, where LHS/RHS forms coincide. |
| prop_subtyping.v | `d_sub_refl_mono` | strictified | Follows reflexivity of `d_consis` — restricted to monotypes for the same reason. |
| prop_subtyping.v | `d_consis_compose` | partial | Arrow case requires a `d_consis_permutation` lemma — `(Δ1++Δb1)++(Δ2++Δb2)` vs `Δ1++Δ2++Δb1++Δb2` differ only by permutation; `d_consis` lacks a permutation lemma. Paper-flagged. |
| prop_subtyping.v | `d_consis_extends_d_sub` | partial | Three pending sub-cases: `d_sub__infer` (needs `Δ0 = nil` narrowing), `d_sub__check` (needs compose arrow + forall_l_* dispatch), `d_sub__arg` (same Δ-permutation issue as compose). |
| prop_subtyping.v | `d_consis_empty_eq` | CLEAN | Empty-Δ consistency on `is_typ` reduces to syntactic equality. Closed. |
| prop_subtyping.v | `d_sub_sound` | CLEAN (strictified) | Headline soundness result for [d_sub mode_tc nil Γ A B] → [d_shallow_sub Γ A B]. Strictified with `is_typ A` precondition (LHS in `typ_all_col` flavour matches `d_shallow_sub` LHS shape); without this, `d_sub__forall_l_*` cases produce LHS shapes outside `d_shallow_sub`'s grammar. |
| prop_subtyping.v | `d_sub_complete_mono` | partial (research-flagged) | Bruno's reviewer-suggested completeness wrt monotype-only shallow subtyping. Three admits: refl (needs `mono_typ` narrowing); forall_r (`d_sub__forall_r` only emits `colour_inh`, `d_shallow_sub_mono__forall_r` ranges over any colour); forall_l (LHS `typ_all_col` in `d_shallow_sub_mono` doesn't match `typ_all_etag/plain` in `d_sub__forall_l_*` — needs colour-to-tag translation, a research design question). |
| prop_subtyping.v | `d_sub_no_guess_uniqueness` | admitted (paper-flagged) | Strict equality ph1 = ph2 of two instantiations producing the same conclusion. The paper's loose form (declarative.tex:1102) was flagged sketchy. A concrete counter-example is documented inline: ph could absorb into nested `forall_l_tagged` chains. The right form likely needs a confluence/canonicity argument — flagged for paper revision rather than mechanization. |

## Discovered blockers / open questions

(none yet)

## Track-specific notes

### 2.A — Foundation

Scope (per design doc §3.A): mutual induction principles via `Scheme` for `d_typing` ↔ `d_pat`; `list_disjoint` algebra; locally-closed lemmas not auto-generated by lngen; substitution composition; category-preservation under substitution; inversion lemmas for category predicates; refinements to `discharge_category` ltac as needed.

### 2.B — Wellformedness

Scope: Refinement-preserves-wf (paper Lemma at declarative.tex:1380), skeleton wf preservation (1970), wf preservation under substitution / opening / context-extension; tag-context freshness lemmas; stability of wf judgments (paper proofs.tex §1).

### 2.C — Subtyping

Scope: Soundness of subtyping (paper Lemma at declarative.tex:1095) — `d_sub TC nil Γ A B → d_shallow_sub Γ A B`; consistency-extends-subtyping (proofs.tex `lemma:consis-sub`); strictified "no guessing of polytypes" (paper:1102); completeness vs. monotype-only shallow subtyping; reflexivity of `d_sub`.

### 2.D — Typing + stability

Scope: General subsumption (paper:574); weakening, narrowing, type substitution, term substitution; structural rules (proofs.tex `lemma:structural` SuffixMoving); Stability lemmas S1 (argument-permutation, see design §3.D anchor) and S2 (application-restructuring); Expressiveness benchmark E1 (Church-encoded existentials: three concrete typing theorems).

### 2.E — Skeleton

Scope: refinement preserves wf interaction with `d_pat`; validity of skeleton inference (paper:1981); safety of skeleton inference (paper:1986); skeleton wf preservation (1970); splitting refines (proofs.tex `lemma:split-refine`).

### 3.A — Algorithmic defs

Scope: Extend `language.ott` with flex-mono / flex-poly type variables; define algorithmic context `aenv` and information-increase relation `aenv_extends`; algorithmic typing / subtyping / skeleton inference rules.

### 3.B — Algo soundness

Scope: For each algorithmic judgment, prove the transferred-output declarative counterpart holds. Follows paper proofs.tex §"Type Inference".

### 3.C — Algo completeness

Scope: For every declarative derivation, exhibit an algorithmic derivation. Hardest track; partial results acceptable per design.
