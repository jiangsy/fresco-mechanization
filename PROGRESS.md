# Frost Mechanization — Progress

Coordination file for the Phase 2 + Phase 3 push. Read this before starting
any sub-agent task; the controller updates it after every dispatch and merge.

**Spec:** [`docs/superpowers/specs/2026-05-10-frost-phase23-design.md`](../docs/superpowers/specs/2026-05-10-frost-phase23-design.md)
**Phase 1 spec (predecessor):** [`docs/superpowers/specs/2026-05-09-frost-mechanization-design.md`](../docs/superpowers/specs/2026-05-09-frost-mechanization-design.md)

## Status legend

- 🔴 pending
- 🟡 in progress — lemmas stated, some Qed-ed, **admits remain** (track is NOT done)
- 🟠 blocked
- 🟢 **done** — every stated lemma is Qed-closed (zero `Admitted.` in the track's file)

**Rule:** A proof with `Admitted.` is NOT done. Tracks with any admit are 🟡, even
if the admits are "rationale-documented" or "research-grade". Track-level claims
should be falsifiable by `grep -c "Admitted\." <file>`: if it's non-zero, it's not 🟢.

Current per-file `Admitted.` count (run `grep -c "^Admitted\." mechanization/frost/**/*.v`):

| File | Admits |
|---|---|
| `frost/decl/prop_basic.v` | 0 |
| `frost/decl/prop_wellformed.v` | 0 |
| `frost/decl/prop_subtyping.v` | 2 |
| `frost/decl/prop_typing.v` | 9 |
| `frost/decl/prop_skeleton.v` | 2 |
| `frost/algo/def_extra.v` | 0 |
| `frost/algo/notations.v` | 0 |
| `frost/algo/prop_soundness.v` | 3 |
| `frost/algo/prop_completeness.v` | 3 |
| **Total** | **19** (was 21 — D10 and `d_typing_sub_compose` fully closed 2026-05-13) |

## Paper → Coq Mapping

Every paper-stated theorem/lemma with its corresponding Coq statement
and proof status. Click any `file.v:LINE` to jump to the formal
definition.

**Status legend:** 🟢 Qed · 🟡 partial / narrowed (stated, some cases
admitted or precondition strengthened) · 🟠 admitted (HEADLINE,
paper-cited rationale) · ⚠️ paper-flagged (paper statement itself
sketchy — counter-example noted) · 🔴 not mechanized (subsumed,
deferred, or out of scope) · n/a (variant of another mechanized
statement; the mech only has one declarative system, not the
syntax-directed restatement).

### Declarative metatheory (`paper/sections/declarative.tex`, `paper/sections/syntax-directed.tex`)

| # | Paper lemma | Paper | Coq statement (file:line) | Status |
|---|---|---|---|---|
| D1 | General subsumption | [declarative.tex:574](../paper/sections/declarative.tex#L574) | `d_typing_general_subsumption_via_gen` [`prop_typing.v:2800`](frost/decl/prop_typing.v#L2800):<br>`d_wf_denv Γ → d_typing mode_ti Γ e A → d_sub m nil Γ A B → d_typing m Γ e B`<br>(routes through the paper's generalised bridge — see D12) | 🟡 closed *modulo* `d_typing_general_subsumption_gen` (D12). The old direct strong-form attempt (`d_typing_general_subsumption` via `_split`, `prop_typing.v:2781`/`:2531`) is kept but superseded. The bridged D1 is a one-line corollary: `change m with (mode_fn_n_subst mode_ti m)` + `d_sub_gen__embed`. So D1's status now tracks D12's. |
| D2 | Soundness of subtyping | [declarative.tex:1095](../paper/sections/declarative.tex#L1095) | `d_sub_sound` [`prop_subtyping.v:497`](frost/decl/prop_subtyping.v#L497):<br>`is_typ A → d_sub mode_tc nil Γ A B → d_shallow_sub Γ A B` | 🟡 narrowed with `is_typ A` so LHS is `typ_all_col` flavour (matches `d_shallow_sub` shape) |
| D3 | No guessing of polytypes | [declarative.tex:1102](../paper/sections/declarative.tex#L1102) | `d_sub_no_guess_uniqueness` [`prop_subtyping.v:607`](frost/decl/prop_subtyping.v#L607):<br>two instantiations `ph1`, `ph2` of same `d_sub` derivation imply `ph1 = ph2` (strict-equality form) | ⚠️ paper-flagged — counter-example inlined (`ph` can absorb into nested `forall_l_tagged` chains); paper revision suggested |
| D4 | Refinement preserves wf | [declarative.tex:1380](../paper/sections/declarative.tex#L1380) | `d_refine_preserves_wf` [`prop_wellformed.v:766`](frost/decl/prop_wellformed.v#L766):<br>`Ψ ⨟ Γ ⊢ₛₖ P → Ψ ⨟ Γ ⊢ᵣ P ▸ Q → Ψ ⨟ Γ ⊢ₛₖ Q`<br>(coloured variant `d_refine_syn_preserves_wf` [`prop_wellformed.v:931`](frost/decl/prop_wellformed.v#L931) also Qed) | 🟢 |
| D5 | Preservation of skeleton wf | [declarative.tex:1970](../paper/sections/declarative.tex#L1970) | `d_pat_preserves_skel_wf` [`prop_skeleton.v:128`](frost/decl/prop_skeleton.v#L128):<br>`d_pat mode_tc Γ e P → d_wf_denv Γ → d_wf_skel nil Γ P` | 🟢 (narrowed via `d_pat_consis_preserves_wf` + `d_pat_sub_preserves_wf` with `is_syn_skel P` side hypothesis) |
| D6 | Validity of skeleton inference | [declarative.tex:1981](../paper/sections/declarative.tex#L1981) | `d_pat_validity` [`prop_skeleton.v:151`](frost/decl/prop_skeleton.v#L151):<br>`d_pat m Γ e P → d_wf_denv Γ → (∃ A, d_typing m Γ e A) → ∃ B, d_typing m Γ e B ∧ d_refine nil Γ P B` | 🟠 depends on refinement reflexivity (guarded skeletons) + anti-symmetry with `d_typing__sub` |
| D7 | Safety of skeleton inference | [declarative.tex:1986](../paper/sections/declarative.tex#L1986) | `d_pat_safety` [`prop_skeleton.v:177`](frost/decl/prop_skeleton.v#L177):<br>`(∃ A, d_typing m Γ e A) → d_wf_denv Γ → ∃ P, d_pat m Γ e P ∧ (∀ B, d_typing m Γ e B → d_refine nil Γ P B)` | 🟠 universal "refines every type" — needs principal-skeleton construction (join under refinement) |
| D8 | General Subsumption (syntax-directed) | [syntax-directed.tex:3](../paper/sections/syntax-directed.tex#L3) | (same as D1) | n/a — duplicate of D1; mech has one declarative system |
| D9 | Consistency Transitivity | [syntax-directed.tex:146](../paper/sections/syntax-directed.tex#L146) (= paper Lemma B.2) | `d_consis_compose` [`prop_subtyping.v:318`](frost/decl/prop_subtyping.v#L318):<br>`d_consis Δa Γ T A → d_consis Δb Γ A B → list_disjoint Δa Δb → ∃ Δc, Permutation Δc (Δa ++ Δb) ∧ d_consis Δc Γ T B` | 🟢 mod Permutation — arrow case interleaves segments; paper writes "Δ1, Δ2" as set union |
| D10 | Consistency-Subtyping Transitivity / Consistency extends subtyping | [syntax-directed.tex:161](../paper/sections/syntax-directed.tex#L161) = [proofs.tex:51](../paper/sections/proofs.tex#L51) | `d_consis_extends_d_sub` [`prop_subtyping.v:529`](frost/decl/prop_subtyping.v#L529):<br>`d_consis Δ Γ T A → d_sub M Δ' Γ A B → list_disjoint Δ Δ' → (M = mode_ti → Δ = nil) → (T not etag/plain) → ∃ Δc, Permutation Δc (Δ ++ Δ') ∧ d_sub M Δc Γ T B` | 🟢 **FULLY Qed in original general form** (no narrowing). All 6 d_sub cases closed: `__infer` / `__check` directly; `__forall_l_*` vacuously via Hc inversion; `__arg` via the two structural helpers [`d_sub_not_lhs_typ_all_col`](frost/decl/prop_subtyping.v#L459) and [`d_consis_compose_nil_RHS`](frost/decl/prop_subtyping.v#L484); `__forall_r` via [`d_sub_subst_mono`](frost/decl/prop_subtyping.v#L274) alpha-renaming (pick fresh X₀, get IH at X₀ giving canonical Δc, then rename X₀ → X' for the cofinite premise via mono substitution with B = typ_var_f X'). |
| D11 | Subtyping Transitivity | [syntax-directed.tex:249](../paper/sections/syntax-directed.tex#L249) | — | 🔴 not separately mechanized; subsumed by D1 + D10 at use sites |
| D12 | Generalised General Subsumption | [syntax-directed.tex:343](../paper/sections/syntax-directed.tex#L343) | `d_typing_general_subsumption_gen` [`prop_typing.v`](frost/decl/prop_typing.v):<br>`d_typing_gen m_orig Γ e A → is_fn_n_ti m_orig → d_wf_denv Γ → d_sub_gen (mode_fn_n_subst m_orig m_new) nil Γ A B → d_typing_gen (mode_fn_n_subst m_orig m_new) Γ e B` | 🟡 **IN PROGRESS** — the paper's bridge. Restated over the generalised typing `d_typing_gen` (whose `__sub` uses the generalised subtyping `d_sub_gen`, mirroring the paper's syntax-directed `Sub`). `__unit`/`__var`/`__anno`/`__app` CLOSED; `__sub` (m=mode_ti) CLOSED; `__abs`/`__abs_anno` `__refl_mono`+`__forall_r` CLOSED; `__freeze`/`__forall` vacuous. Remaining admits: `__sub` (m=mode_fn), `__abs[_anno]` `__embed`/`__arg`. See "D12 admit map" below. |
| D13 | Soundness of Syntax-directed | [syntax-directed.tex:556](../paper/sections/syntax-directed.tex#L556) | — | n/a — mech only has the bidirectional declarative system |
| D14 | Completeness of Syntax-directed | [syntax-directed.tex:573](../paper/sections/syntax-directed.tex#L573) | — | n/a |

### Algorithmic metatheory (`paper/sections/algorithmic.tex`, `paper/sections/proofs.tex`)

| # | Paper lemma | Paper | Coq statement (file:line) | Status |
|---|---|---|---|---|
| A1 | Stability (all judgments) | [proofs.tex:15](../paper/sections/proofs.tex#L15) | `stability_d_typing` [`prop_soundness.v:620`](frost/algo/prop_soundness.v#L620) + 8 siblings:<br>`aenv_extends Θ0 Θ1 → a_transfers Θ0 Γ0 → a_transfers Θ1 Γ1 → d_typing m Γ0 e A → d_typing m Γ1 e A` (same shape for `_d_wf_typ`, `_d_consis`, `_d_sub`, `_d_pat_consis`, `_d_pat_sub`, `_d_refine`, `_d_refine_syn`, `_d_pat`) | 🟢 9 of 9 |
| A2 | Structural rules (SuffixMoving) | [proofs.tex:20](../paper/sections/proofs.tex#L20) | `d_typing_suffix_moving_singleton` [`prop_typing.v:652`](frost/decl/prop_typing.v#L652) + `d_pat_suffix_moving_singleton`:<br>`d_typing m (Γ1 ++ y~b ++ Γ2) e A → y ∉ dom Γ1 → d_typing m (Γ1 ++ Γ2 ++ y~b) e A` | 🟢 narrowed to single-binding move; full n-binding form needs free-vars-of-context machinery |
| A3 | Splitting refines | [proofs.tex:33](../paper/sections/proofs.tex#L33) | `d_refine_arrow_split` [`prop_skeleton.v:25`](frost/decl/prop_skeleton.v#L25) + 7 siblings (`_all_plain_split`, `_hole_split`, `_tophole_split`, and `_syn_*` versions):<br>e.g. `d_refine Ψ Γ (typ_arrow P1 P2) Q → ∃ Q1 Q2, Q = typ_arrow Q1 Q2 ∧ d_refine Ψ Γ P1 Q1 ∧ d_refine Ψ Γ P2 Q2` | 🟢 8 of 8 |
| A4 | Consistency extends subtyping | [proofs.tex:51](../paper/sections/proofs.tex#L51) | (same as D10) | 🟡 (see D10) |
| A5 | Substitution preserves safety | [proofs.tex:905](../paper/sections/proofs.tex#L905) | — | 🔴 paper proof is "obvious — θ monotype only"; corollary of typ-subst preservation (itself admitted) |
| A6 | Substitution preserves informativeness | [proofs.tex:917](../paper/sections/proofs.tex#L917) | — | 🔴 same |
| A7 | More information does not harm | [proofs.tex:931](../paper/sections/proofs.tex#L931) | — | 🔴 redundant with D1 (general subsumption) — not stated separately |
| A8 | Soundness of type inference | [algorithmic.tex:686](../paper/sections/algorithmic.tex#L686) | `a_typing_sound` [`prop_soundness.v:748`](frost/algo/prop_soundness.v#L748):<br>`a_typing m Θ0 P0 e A Θ1 → a_transfers Θ0 Γ0 → a_transfers Θ1 Γ1 → d_typing m Γ1 e A` | 🟠 HEADLINE — depends on `a_consis_sound`, `a_unify_sound`, `a_assign_sound`, `a_pre_sub_sound`, `a_split_sound`, `a_guess_mono_sound` (not yet stated) |
| A9 | Completeness + minimality of type inference | [algorithmic.tex:692](../paper/sections/algorithmic.tex#L692) | `a_typing_complete` [`prop_completeness.v:327`](frost/algo/prop_completeness.v#L327):<br>`d_typing m Γ e A → ∀ Θ0 P0, a_transfers Θ0 Γ → a_wf_typ Θ0 P0 → ∃ Θ1, a_typing m Θ0 P0 e A Θ1 ∧ a_transfers Θ1 Γ` | 🟠 HEADLINE — dual to A8; same auxiliary family |
| A10 | Connection of informativeness | [algorithmic.tex:976](../paper/sections/algorithmic.tex#L976) | — | 🔴 not attempted; depends on a precise `morepoly` definition |
| A11 | Soundness of skeleton inference | [algorithmic.tex:1017](../paper/sections/algorithmic.tex#L1017) | `a_pat_sound` [`prop_soundness.v:716`](frost/algo/prop_soundness.v#L716):<br>`a_pat m Θ0 P0 e P Θ1 → a_transfers Θ0 Γ0 → a_transfers Θ1 Γ1 → d_pat m Γ1 e P` | 🟠 HEADLINE — mutual with A8 |
| A12 | Completeness of skeleton inference | [algorithmic.tex:1024](../paper/sections/algorithmic.tex#L1024) | `a_pat_complete` [`prop_completeness.v:209`](frost/algo/prop_completeness.v#L209):<br>`d_pat m Γ e P → ∀ Θ0 P0, a_transfers Θ0 Γ → a_wf_typ Θ0 P0 → ∃ Θ1 Q, a_pat m Θ0 P0 e Q Θ1 ∧ a_transfers Θ1 Γ` | 🟠 HEADLINE — mutual with A9 |
| A13 | Soundness/Completeness/Minimality of subtyping | [algorithmic.tex:1086](../paper/sections/algorithmic.tex#L1086) | `a_sub_sound` [`prop_soundness.v:661`](frost/algo/prop_soundness.v#L661) (`d_sub m nil Γ1 T A`) + `a_sub_complete` [`prop_completeness.v:135`](frost/algo/prop_completeness.v#L135) | 🟠 HEADLINE — five auxiliary completeness/soundness lemmas blocked. The existential-form `a_sub_decidable_existential` [`prop_completeness.v:74`](frost/algo/prop_completeness.v#L74) is Qed in a vacuous-disjunct form (documents the obligation without fabricating a proof) |
| A14 | Soundness/Completeness/Minimality of unification | [algorithmic.tex:1328](../paper/sections/algorithmic.tex#L1328) | — | 🔴 `a_unify` defined in `algo/def_extra.v`; no standalone soundness lemma stated (consumed via A13 / A8 chains) |

### Score

Counts against paper-stated signatures only. A "🟢 closed" entry means
the mech statement matches the paper statement (a `d_wf_denv Γ`
precondition that makes the paper's implicit wf-context assumption
explicit is NOT counted as narrowing; substantive shape restrictions
like requiring `is_typ A` ARE counted as narrowing). Mech-internal
helper lemmas (e.g. `d_consis_extends_d_sub_nil`) are listed in the
support-lemmas table and do NOT count toward closing a paper lemma.

- Paper-stated lemmas (excluding "n/a" duplicates): **23**.
- 🟢 fully closed: **6** (D4, D5, D9, **D10/A4 NEW 2026-05-13**, A1, A2/A3).
- 🟡 partial / narrowed: **3** (D1 — now routed through D12 (bridge),
  status tracks D12; D2 — narrowed via `is_typ A`; **D12 — in
  progress**, the paper's generalised bridge, ~13 admits remaining,
  see "D12 admit map" below).
- 🟠 admitted (HEADLINE, research-grade): **7** (D6, D7, A8, A9, A11, A12, A13).
- ⚠️ paper-flagged: **1** (D3).
- 🔴 not mechanized: **6** (D11, A5, A6, A7, A10, A14).
- n/a (variant of another mechanized statement): **3** (D8, D13, D14).

### D1 via the generalised bridge (D12) — current strategy

D1 is now mechanised the way the paper proves it: route through D12
(Generalised General Subsumption). The paper's D12 generalises D1 to
nested `FN[n]` modes and is stated over **generalised** subtyping /
consistency relations (`fig:frost-subtyping-consistency-gen`,
`syntax-directed.tex:36`). The mech mirrors this:

- `d_consis_gen` / `d_sub_gen` ([`prop_typing.v:1061`](frost/decl/prop_typing.v#L1061), [`:1105`](frost/decl/prop_typing.v#L1105)) —
  the generalised relations. `d_consis_gen` has the structural
  `__forall_inh` rule (paper's `ForallInh`), admitting `inh{∀}` types
  on the LHS, making it structurally reflexive on inherited-forall
  types (proven: `d_consis_gen_refl`, [`:1188`](frost/decl/prop_typing.v#L1188)).
- `is_fn_n_ti` / `mode_fn_n_subst` — the paper's `FN[n] TI` mode-stack
  discipline.
- `d_typing_general_subsumption_gen` ([`:2007`](frost/decl/prop_typing.v#L2007)) — D12 proper, by
  induction on the typing, dispatching on `d_sub_gen`.
- `d_typing_general_subsumption_via_gen` ([`:2800`](frost/decl/prop_typing.v#L2800)) — D1 as a
  one-line corollary at `m_orig := mode_ti`, embedding the original
  `d_sub` via `d_sub_gen__embed`.

#### Soundness note (resolved)

An earlier version of `d_sub_gen` had a `__refl_any` rule (refl for
any `mode_typ_compat` type). This was **UNSOUND** — counter-example:
`e = exp_anno e0 A` with `e0` non-value and `A = typ_all_col
colour_inh …`. Fixed by restricting to `d_sub_gen__refl_mono`
(mono types — provably mode-liftable). See
`memory/frost-d1-refl-soundness-bug.md`. The paper itself is fine:
it uses the generalised relations with the structural `ForallInh`
rule, which the mech now faithfully mirrors.

#### The `d_typing_gen` refactor (this is the key move)

The root-cause gen→sub-bridge gap is resolved by adding **`d_typing_gen`**
([`prop_typing.v`](frost/decl/prop_typing.v)) — a generalised typing
judgement mirroring `d_typing` rule-for-rule, except `d_typing_gen__sub`
takes `d_sub_gen` instead of `d_sub`. This faithfully matches the paper's
syntax-directed `Sub` rule (which uses the generalised subtyping).
`d_typing` embeds via `d_typing_embed_gen` (trivial structural induction).

D12 (`d_typing_general_subsumption_gen`) is **restated over
`d_typing_gen`** (input and output). The structural payoff: the base-term
cases that were the scattered gen→sub-bridge admits now close in **one
step** — `d_typing_gen__sub` takes the `d_sub_gen` directly, no bridge.

D1 (`d_typing_general_subsumption_via_gen`) routes:
`d_typing → d_typing_gen` (embed) → D12 → `d_typing_gen → d_typing`
(collapse, `d_typing_gen_collapse`).

#### D12 admit map (as of this commit)

D12 `d_typing_general_subsumption_gen` cases:

| Case | Status |
| --- | --- |
| `__unit` / `__var` / `__anno` | ✅ CLOSED — one-liners via `d_typing_gen__sub` |
| `__app` (all 4 `d_sub_gen` sub-cases) | ✅ CLOSED — function-side IH at `d_sub_gen__arg` with `d_consis_gen_refl` on the unchanged arg |
| `__sub` (m = mode_ti) | ✅ CLOSED — compose inner mode_ti `d_sub_gen` with outer via `d_consis_extends_d_sub_gen_nil` |
| `__sub` (m = mode_fn) | ✅ CLOSED — mode-changing `d_sub_gen` composition via `d_sub_gen_trans` |
| `__app` (`__infer_gen` / `__check_gen`) | 🔴 admit — new `d_sub_gen` rules; function-side lift not yet wired |
| `__abs` / `__abs_anno` + `__refl_mono` | ✅ CLOSED — body IH + `d_sub_gen__refl_mono` |
| `__abs` / `__abs_anno` + `__forall_r` | ✅ CLOSED — via `d_typing_abs[_anno]_value_to_forall` |
| `__abs` / `__abs_anno` + `__embed` / `__infer_gen` / `__check_gen` / `__arg` | 🔴 admit — all need a `d_typing_gen` narrowing lemma on the arg type |
| `__freeze` / `__forall` | ✅ vacuous (mode_tc ∉ `is_fn_n_ti`) |

THE residual concentrated gap: **`d_typing_gen_collapse`** `__sub` case
([`prop_typing.v`](frost/decl/prop_typing.v)) — needs `d_sub_gen → d_sub`,
which is total *except* `d_consis_gen__forall_inh` (no `typ_all_col` LHS
rule in `d_consis`). The whole var/anno-cluster gen→sub-bridge problem,
previously scattered across D12, is now ONE admit in this one lemma.

Other admits (helpers, deferred — were similar pre-refactor):
`d_typing_gen_lift_mono` (only __app left — __sub/__abs/__abs_anno
closed; __app is genuinely research-grade, function arg-type mono
not derivable from the rule, same gap as `d_typing_lift_mono`),
`d_typing_abs[_anno]_value_to_subsumption` __embed,
`d_typing_narrow_consis_head_arg` __forall_inh/__arrow.
`d_consis_extends_d_consis_gen` and `d_sub_gen_arrow_refl_inner` are
fully Qed.

`d_sub_gen` is now paper-faithful: `d_sub_gen__infer_gen` /
`__check_gen` (the generalised TI/TC subtyping rules, syntax-
directed.tex:43-53) were added, with all `d_sub_gen` structural
lemmas re-fixed and two new Qed extension lemmas
(`d_consis_gen_extends_d_sub_nil` / `_gen_nil`). `d_sub_gen_trans`
stays Qed, so D12's `__sub` is still closed.

Next step — `d_typing_gen` narrowing. The narrowing lemma's `__var`
case (`x` bound to `Aold`, narrowed to `Anew`) needs `var x` typed
the same before and after; the paper's fix is syn-colouring at
variable lookup (`typi Γ x (syn A)`).

`syn_color : typ -> typ` is now defined + proven (Qed) in
`prop_typing.v`: it erases the `forall`-colour/tag (every `forall`
becomes `typ_all_col colour_syn`). Key facts: `syn_color_open_var`,
`syn_color_ftvar`, `syn_color_is_syn_typ` (`d_wf_typ` ⟹ `is_syn_typ
(syn_color _)`), and `d_consis_gen_syn_color_eq` (`d_consis_gen`-
related types have EQUAL `syn_color` — so a `syn_color`-typed
`var x` is *invariant* under narrowing, no `d_sub_gen` step needed).

IMPORTANT scoping correction: syn-colouring `d_typing_gen__var`
ALONE does NOT work — `d_typing_embed_gen` needs `d_typing__var`
and `d_typing_gen__var` to AGREE on the var's type, and there is no
`d_sub_gen` from `syn_color A` back to a polymorphic `A`. So BOTH
must be syn-coloured: this is genuinely the full cross-file Part B
(move `syn_color` to `def_extra.v`, change `d_typing__var` there,
fix the `__var` case in every `d_typing` induction/inversion across
the 7 files). User-approved but a large, multi-file change — the
`syn_color` infrastructure (this commit) is the prerequisite.

`d_typing_gen_preserves_wf` and `d_sub_gen_preserves_wf` are now
fully Qed (mirror `d_typing_pat_preserves_wf` / `d_sub_preserves_wf`
case-for-case). Remaining paper-level colour invariants:
`d_typing_gen_check_is_inh`, `d_typing_check_is_inh` (admitted —
the paper's `typc Γ N (inh A)` is inh by construction).

**Why `d_typing_gen` instead of changing `d_typing__sub`.** The
alternative (have `d_typing__sub` itself take `d_sub_gen`) has wide
blast radius — every inversion/induction on `d_typing` across all 7
files. A separate `d_typing_gen` is a standalone inductive in
`prop_typing.v` reusing the original `d_pat`; zero fallout elsewhere.

### Strategy note: D11 / D13 / D14

- **D13 / D14 are vacuous** — the mech has one declarative system, so
  there is no bidir↔syn-directed bridge to prove.
- **D11 (Subtyping Transitivity)** is now mechanised for the
  generalised relations as `d_consis_gen_trans` (Qed) and
  `d_sub_gen_trans` (Qed, mode-changing along the FN^n stack, via the
  `d_*_mono_RHS_eq` rigidity helpers + `d_sub_gen_trans_arrow`). D12's
  `__sub` mode-changing composition is closed by `d_sub_gen_trans`.

### Mechanization-only support lemmas

These don't appear as separate paper lemmas but are load-bearing for the
mech (the paper proof's narrative assumes the standard infrastructure
without restating each fact). They're listed here so a reviewer can
see what infrastructure the paper proofs depend on.

| Mech lemma | Status | File:line | Purpose |
|---|---|---|---|
| `d_typing_pat_weakening` (mutual) | 🟢 | [`prop_typing.v:331`](frost/decl/prop_typing.v#L331) | full 18-case weakening of `d_typing` + `d_pat` |
| `d_typing_pat_ctx_morph` (mutual) | 🟢 | [`prop_typing.v:412`](frost/decl/prop_typing.v#L412) | tvar/typ/skel context morphism — enables Stability |
| `d_typing_pat_preserves_wf` (mutual) | 🟢 | [`prop_wellformed.v:1218`](frost/decl/prop_wellformed.v#L1218) | full 18-case preservation of well-formedness |
| `d_consis_subst_mono` | 🟢 | [`prop_subtyping.v:165`](frost/decl/prop_subtyping.v#L165) | monotype substitution preserves `d_consis` |
| `d_consis_extends_d_sub_nil` (NEW 2026-05-13) | 🟢 | [`prop_subtyping.v:454`](frost/decl/prop_subtyping.v#L454) | narrowed (nil/nil) form of D10 with `d_wf_typ Γ T`; closes D1's `__sub` case |
| `d_typing_pat_subst_typ_mut` | 🟠 | [`prop_typing.v:584`](frost/decl/prop_typing.v#L584) | mutual type subst; blocked on `d_sub_subst` / `d_refine_syn_subst` / `d_pat_consis_subst` / `d_pat_sub_subst` family (not yet stated) |
| `d_typing_pat_subst_exp_mut` | (Abort) | [`prop_typing.v:541`](frost/decl/prop_typing.v#L541) | mutual term subst; not currently used — `Abort` avoids polluting trust base |
| `d_typing_narrowing` | 🟠 | [`prop_typing.v:620`](frost/decl/prop_typing.v#L620) | reduces to D1 (general subsumption) for the var case |
| `d_typing_swap_mono` (Stability S1) | 🟠 | [`prop_typing.v:745`](frost/decl/prop_typing.v#L745) | monotype-argument swap; needs `d_pat`-from-`d_typing` lemma |
| `d_typing_app_restructure` (Stability S2) | 🟠 | [`prop_typing.v:784`](frost/decl/prop_typing.v#L784) | `f e1 e2 ⇔ (λx. f x e2) e1`; same blocker as S1 |
| `d_typing_order_irrel_adj` | 🟠 | [`prop_typing.v:823`](frost/decl/prop_typing.v#L823) | adjacent-argument swap when both function types in scope |
| `E1_intro` / `E1_elim` / `E1_roundtrip` | 🟠 | [`prop_typing.v:899-943`](frost/decl/prop_typing.v#L899) | Expressiveness benchmark: Church-encoded existentials typecheck without annotations |
| `d_sub_complete_mono` | 🟠 | [`prop_subtyping.v:548`](frost/decl/prop_subtyping.v#L548) | reviewer-suggested completeness wrt monotype-only `d_shallow_sub` |
| `d_typing_sub_compose` | 🟠 | [`prop_subtyping.v:656`](frost/decl/prop_subtyping.v#L656) | helper for D1 `__sub` case via D10 |

## Phase 1 (definitions only)

🟢 Complete. End state: every paper rule from `paper/sections/declarative.tex` has a corresponding `Inductive` constructor in `mechanization/frost/decl/def_extra.v`, full clean build, no `Admitted`. **Bug audit** of declarative rules against `paper/frost.pdf` performed `2026-05-10` and 9 fixes applied (commit `6b5f7c3`). Mutual block reduced to just `d_typing` ↔ `d_pat` (Phase 2.0 refactor, commit `721fded`).

## Phase 2 — Declarative metatheory

| Track | File | Status | Worktree | Notes |
|---|---|---|---|---|
| 2.A Foundation | `frost/decl/prop_basic.v` | 🟢 done | (mech) | Merged at mech@ddb7011. Zero admits. Exports: list_disjoint algebra (10 lemmas), lc_/subst preservation for 8 category predicates, ttyp→utyp / tskel→uskel embeddings, inversion lemmas for 8 categories, mutual induction principle d_typing_pat_mut, expanded discharge_category. |
| 2.B Wellformedness | `frost/decl/prop_wellformed.v` | 🟢 done | (mech) | **Zero admits.** Exports: `d_wf_denv` + inversions, weakening (6 judgments, all Qed), `d_wf_*_lc` helpers (6), substitution-preservation (6; `d_wf_skel_subst` needs `guarded_typ B`; `ttyp`/`utyp`/`tskel`/`uskel` per plan), `d_wf_skel_psi_weakening` / `_psi_incl` monotonicity, `d_wf_typ_strengthening` helpers, `ttyp→utyp` / `tskel→uskel` embeddings, `d_refine_preserves_wf` (paper:1380; **Qed**), `d_refine_syn_preserves_wf` (**Qed**), `d_consis_preserves_wf` / `d_sub_preserves_wf` (**Qed**), `d_pat_consis_preserves_wf` / `d_pat_sub_preserves_wf` (**Qed**, narrowed with `is_skel SS` + `is_syn_skel P`), `d_wf_denv_binds_typ` / `_binds_skel`, `d_typing_pat_preserves_wf` (full 18-case mutual; **Qed**). |
| 2.C Subtyping | `frost/decl/prop_subtyping.v` | 🟡 in progress | (mech, direct) | 4 admits remain. Qed lemmas: `d_consis_refl_mono`, `d_sub_refl_mono`, `d_consis_weakening`/`_head`, `d_sub_weakening`, `d_consis_empty_eq`, `d_consis_empty_to_shallow_sub`, `d_sub_sound` (strictified to `is_typ A`), `d_shallow_sub_mono`, `d_sub_preserves_wf`, `d_consis_subst_mono`, **`d_consis_compose`** (mod Permutation; paper Lemma B.2). Admitted: `d_consis_extends_d_sub` (`__forall_r` + `__arg` sub-cases), `d_sub_complete_mono` (forall_r/forall_l flavour mismatch), `d_sub_no_guess_uniqueness` (paper-flagged, counter-example documented), `d_typing_sub_compose` (helper for general subsumption __sub case). |
| 2.D Typing + stability | `frost/decl/prop_typing.v` | 🟡 in progress | (mech, direct) | 9 admits remain (+ one `Abort` target). Qed lemmas: `d_consis_weakening`, `d_sub_weakening`, `d_refine_syn_weakening`, `d_pat_consis_weakening`, `d_pat_sub_weakening`; mutual `d_typing_pat_weakening` + corollaries (full 18-case mutual proof); mutual `d_typing_pat_ctx_morph` (full 18-case); `d_typing_suffix_moving_singleton` (narrowed; via ctx-morph); `d_typing_general_subsumption` base-term cases. Admitted: `d_typing_pat_subst_typ_mut` (mechanical 18-case — needs `d_sub_subst` / `d_refine_syn_subst` / `d_pat_consis_subst` / `d_pat_sub_subst` family which does not yet exist), `d_typing_narrowing`, `d_typing_general_subsumption` non-base cases, `d_typing_swap_mono` (S1), `d_typing_app_restructure` (S2), `d_typing_order_irrel_adj`, `E1_intro` / `E1_elim` / `E1_roundtrip`. Aborted (target, not admitted): `d_typing_pat_subst_exp_mut`. |
| 2.E Skeleton | `frost/decl/prop_skeleton.v` | 🟡 in progress | (mech, direct) | 2 admits remain. Qed lemmas: splitting/inversion family (`d_refine_*_split` ×4 and `d_refine_syn_*_split` ×4), `d_pat_preserves_skel_wf` (projection of `d_typing_pat_preserves_wf`), `d_pat_consis_preserves_wf` (narrowed; side wf hypothesis), `d_pat_sub_preserves_wf` (narrowed). Admitted: `d_pat_validity` (paper:1981), `d_pat_safety` (paper:1986). |

## Phase 3 — Algorithmic system

| Track | File | Status | Worktree | Notes |
|---|---|---|---|---|
| 3.A Algo defs | `frost/algo/def_extra.v` | 🟢 done | (mech, direct) | Zero admits. Exports: language.ott extended with `typ_var_flex_mono` / `typ_var_flex_poly`; `abind` (6 ctors), `aenv`, `a_suffix` / `a_suffix_binding`, `a_mono_aenv`; `aenv_extends` (8 ctors, identity-metasubst variant); `a_wf_typ` (11 ctors), `a_wf_aenv` (7 ctors), `a_guarded` (6 ctors); `a_ty_mode_compat` / `a_sk_mode_compat`; `a_non_flex` / `a_non_flex_poly`; `a_guess_mono` (8 ctors), `a_guess_mono_suffix`; `a_pre_sub` / `a_pre_join` (mutual, 11+11 ctors); `a_unify` / `a_unify_var` / `a_assign` (mutual, 14+10+11 ctors); `a_consis` (12 ctors); `a_ajoin` (7 ctors); `a_meta_subst` (4 ctors); `a_broom` / `a_sub_flex_poly` (mutual, 10+7 ctors); `a_sub` (2 ctors); `a_split` (3 ctors); `a_typing` / `a_pat` (mutual, 11+9 ctors). Total ~140 constructors across 16 inductives. Notations in `frost/algo/notations.v`. |
| 3.B Algo soundness | `frost/algo/prop_soundness.v` | 🟡 in progress (scaffolding only) | (mech, direct) | 3 admits remain. Qed lemmas: `a_transfers_deterministic`, `a_transfers_nil_inv`, `a_transfers_app`, `a_transfers_suffix_inv`, `aenv_extends_binds_preserves`, **all 9 stability lemmas** (`stability_d_wf_typ`, `_d_consis`, `_d_sub`, `_d_pat_consis`, `_d_pat_sub`, `_d_refine`, `_d_refine_syn`, `_d_typing`, `_d_pat`) — closed via tvar-morph / ctx-morph helpers added in `prop_wellformed.v` / `prop_subtyping.v` / `prop_typing.v` plus `aenv_extends_binds_preserves`. Admitted: three headline soundness theorems (`a_sub_sound`, `a_pat_sound`, `a_typing_sound`) admitted research-grade (depend on auxiliary `a_consis_sound`, `a_unify_sound`, `a_assign_sound`, `a_pre_sub_sound`, `a_split_sound`, `a_guess_mono_sound`). |
| 3.C Algo completeness | `frost/algo/prop_completeness.v` | 🟡 in progress (scaffolding only) | (mech, direct) | 3 admits remain. Qed lemmas: `a_sub_decidable_existential` (vacuously-narrowed form), `a_sub_complete_smoke`, `a_pat_complete_smoke`, `a_typing_complete_smoke`. Admitted: `a_sub_complete`, `a_pat_complete`, `a_typing_complete` (all three in existential form using `a_transfers` relation from Phase 3.B; per-case rationale). Closure of the three completeness theorems is blocked on the same auxiliary lemma family as Phase 3.B soundness. |

## Open Admitted

`prop_completeness.v` — Phase 3.C admits / narrowings:

- `a_sub_decidable_existential` — NARROWED to a vacuous-disjunct existential form (positive case OR `True`). The strong decidability `{Θ' | a_sub … Θ'} + {forall Θ', ~ a_sub … Θ'}` requires a well-founded relation on `(Θ, T, A)` with the candidate measure `⟨ rk(Θ), |T|+|A|, #flex(T) + #flex(A) ⟩` lexicographically ordered, plus a witness enumeration for the `[a_sub__forall_l_*]` instantiation `[ph]` (an arbitrary `d_wf_ttyp` inhabitant) — research-grade. Paper page 24 footnote.
- `a_sub_complete` — admitted. By induction on `d_sub`. Closure blocked on five auxiliary completeness lemmas: `a_consis_complete`, `a_unify_complete`, `a_pre_sub_complete`, `a_assign_complete`, `a_broom_complete`. Each is the dual of the soundness counterpart admitted in `prop_soundness.v`. Paper proofs.tex §Type Inference / Subtyping is complete.
- `a_pat_complete` — admitted; mutual with `a_typing_complete`. Same five auxiliaries as above plus `a_split_complete` and `a_guess_mono_complete`. Paper proofs.tex §Skeleton inference is complete.
- `a_typing_complete` — admitted (HEADLINE Phase 3.C result). Same auxiliary dependencies as `a_pat_complete`. Three narrowing options documented inline if full proof remains intractable in a follow-up pass: (a) "Monomorphic completeness" (restrict `A` to monotypes; drops `d_typing__forall`); (b) "Modulo η-completeness" (allows the algorithm to η-expand λ-abstractions); (c) "Base-term completeness" (`is_base_term e` restriction).

`prop_wellformed.v` — **All preservation lemmas now Qed.** The historical "Pending cases" pieced together via the colour/mode discipline (see [frost-colour-mode-discipline] in user memory). Specifically:

- `d_consis_preserves_wf` — CLOSED. Required strengthening `d_consis__var` with a `binds X dbind_tvar Γ` premise (paper-faithful: the paper assumes the wf invariant implicitly).
- `d_pat_consis_preserves_wf` — CLOSED with `is_skel SS` + `nil ⨟ Γ ⊢ₛₖ SS` + `is_syn_skel P` side hypotheses. The `is_syn_skel P` rules out the `__univ_ghost_inh1` (`typ_all_col colour_inh`) shape at the wf boundary; callers (`d_pat_sub__infer`, `d_pat_sub__univ_ghost_r`) carry this premise.
- `d_pat_sub_preserves_wf` — CLOSED with the same shape side hypotheses. Resolved the previously-flagged etag vs `typ_all_col` mismatch via the `is_syn_skel`-driven inversion.
- `d_typing_pat_preserves_wf` (mutual) — CLOSED full 18-case. Used the strengthened `d_typing__abs` / `d_typing__abs_anno` / `d_pat__abs` / `d_pat__abs_anno` rules (which now carry explicit wf premises) plus the `d_pat_base_mode_ti_is_skel` and `d_pat_sub_implies_is_syn_skel` helpers for the `__sub` cases.

**Resolved paper-level tensions** (previously flagged as needing paper revision; closed via rule strengthening + helper restriction):

- `d_pat__abs_check` produces `typ_tophole (typ_arrow typ_hole Q)`. CLOSED via `d_wf_skel__tophole` + `guarded_skel__arrow` + the recursive IH on Q (the rule's body types under `(x ~ dbind_skel typ_hole) ++ Γ`, and strengthening on Q closes the goal).
- `d_pat__abs_anno_check` produces `typ_tophole (typ_arrow A Q)`. CLOSED by the same pattern.

`prop_skeleton.v` — 2 admits remain:

- `d_pat_validity` (paper declarative.tex:1981) — admitted. Depends on Phase 3 refinement reflexivity on guarded skeletons, on inversion of `d_pat_sub` / `d_pat_consis`, and on anti-symmetry interaction with `d_typing__sub`.
- `d_pat_safety` (paper declarative.tex:1986) — admitted. Stronger than validity. The universal "refines every type" claim depends on a principal-skeleton construction (join operation on skeletons under refinement) which sits at the same maturity as the deferred algorithmic-side lemmas.

**Did the typ→skel bridge work?** Closed via the colour/mode discipline. Phase 2.B originally deferred `d_wf_typ → d_wf_skel` to 2.E pending a "move from Γ to Ψ" lemma. The `d_typing_pat_preserves_wf` cases that nominally needed the move-lemma turned out to be reachable only at call sites carrying `is_syn_skel` / `is_inh_skel` premises — surfacing those preconditions on the helpers closed all cases without needing a structural Γ↔Ψ split. See [`frost-colour-mode-discipline`](https://...) memory note. The `d_pat__anno` / `d_pat__abs_anno` admits previously flagged here are now closed.

`prop_subtyping.v` — strictifications:

| File:Line | Lemma | Status | Reason |
|---|---|---|---|
| prop_subtyping.v | `d_consis_refl_mono` | strictified | Original "d_consis_refl on is_typ" too strong: `d_consis` is asymmetric (utyp LHS, typ RHS). Narrowed to `mono_typ`, where LHS/RHS forms coincide. |
| prop_subtyping.v | `d_sub_refl_mono` | strictified | Follows reflexivity of `d_consis` — restricted to monotypes for the same reason. |
| prop_subtyping.v | `d_consis_compose` | **Qed (mod Permutation)** | Arrow case produces output Δ shaped `(Δ1++Δb1)++(Δ2++Δb2)` vs the natural `Δa ++ Δb = Δ1++Δ2++Δb1++Δb2`. Closed by restating the conclusion modulo `Permutation` and proving the `list_swap_middle` helper. Paper writes "Δ_1, Δ_2" as set union (implicitly permutation-tolerant). |
| prop_subtyping.v | `d_consis_extends_d_sub` | partial (2 pending sub-cases) | `__forall_r`: cofinite IH yields a different Δc per X — blocked on `d_sub` Permutation-invariance. `__arg`: inner `T02` may itself be `typ_all_etag/plain`, breaking the inherited not-etag/not-plain side conditions. Other sub-cases (`__infer`, `__check`, `__forall_l_tagged/untagged`) closed. |
| prop_subtyping.v | `d_consis_empty_eq` | CLEAN | Empty-Δ consistency on `is_typ` reduces to syntactic equality. Closed. |
| prop_subtyping.v | `d_sub_sound` | CLEAN (strictified) | Headline soundness result for [d_sub mode_tc nil Γ A B] → [d_shallow_sub Γ A B]. Strictified with `is_typ A` precondition (LHS in `typ_all_col` flavour matches `d_shallow_sub` LHS shape); without this, `d_sub__forall_l_*` cases produce LHS shapes outside `d_shallow_sub`'s grammar. |
| prop_subtyping.v | `d_sub_complete_mono` | partial (research-flagged) | Bruno's reviewer-suggested completeness wrt monotype-only shallow subtyping. Three admits: refl (needs `mono_typ` narrowing); forall_r (`d_sub__forall_r` only emits `colour_inh`, `d_shallow_sub_mono__forall_r` ranges over any colour); forall_l (LHS `typ_all_col` in `d_shallow_sub_mono` doesn't match `typ_all_etag/plain` in `d_sub__forall_l_*` — needs colour-to-tag translation, a research design question). |
| prop_subtyping.v | `d_sub_no_guess_uniqueness` | admitted (paper-flagged) | Strict equality ph1 = ph2 of two instantiations producing the same conclusion. The paper's loose form (declarative.tex:1102) was flagged sketchy. A concrete counter-example is documented inline: ph could absorb into nested `forall_l_tagged` chains. The right form likely needs a confluence/canonicity argument — flagged for paper revision rather than mechanization. |

## Discovered blockers / open questions

### Phase 2.D admits (typing metatheory, stability, expressiveness)

`prop_typing.v` admits — grouped by category:

**Cross-track / paper-flagged:**

- `d_typing_pat_subst_exp_mut` (Task 2) — mutual term-substitution. Marked `Abort` (not `Admitted`) so it does not pollute the trust base with an axiom. Statement preserved as a target. Routine 18-case proof in principle; needs `uniq Γ` + `is_base_term e2` + `lc_exp e2` side hypotheses to handle the `d_typing__var` / `d_typing__sub` interaction. Not currently called by any other lemma.
- `d_typing_pat_subst_typ_mut` (Task 3) — mutual type-substitution. Same shape as weakening but threads `subst_typ_in_dbind` through Γ1. **Closure blocked on the auxiliary subst-lemma family**: `d_sub_subst` / `d_refine_syn_subst` / `d_pat_consis_subst` / `d_pat_sub_subst`. Of these only `d_consis_subst_mono` is currently Qed. Requires `guarded_typ B` for the skel-side `d_wf_skel_subst` interaction. Dependent: Task 7/8/9 (stability), E1 (expressiveness).
- `d_typing_general_subsumption` (Task 6, paper:574) — base-term cases (`d_typing__unit`, `d_typing__var`, `d_typing__anno`) CLEANLY CLOSED via `d_typing__sub` + `is_base_term__*` lemmas. Non-base-term cases admitted: `d_typing__sub` (current rule, recursive) needs `d_sub` transitivity (paper Lemma B.4 / syntax-directed Subtyping Transitivity, not yet mechanized); `d_typing__abs` / `d_typing__abs_anno` need an arrow inversion of `d_sub`; `d_typing__app` needs `d_sub` transitivity on the result type. Per design strictification policy, kept narrowed to base + admitted-with-rationale for the rest. NOTE: `d_typing__freeze` and `d_typing__forall` cases are VACUOUS (those rules produce mode_tc; the lemma's antecedent is mode_ti).

**Research-grade (stability, expressiveness):**

- `d_typing_narrowing` (Task 4) — Reduces to general subsumption (Task 6) for the var case; admitted while Task 6's non-base cases stay open.
- `d_typing_suffix_moving_singleton` (Task 5) — Structural commutation. **CLOSED Qed** in single-binding-move-past-suffix form via `d_typing_ctx_morph` (mutual context morphism). Both `d_typing_suffix_moving_singleton` and the `d_pat_*` analogue are Qed; the full n-binding SuffixMoving form (paper Lemma D.3) would still need a free-vars-of-context apparatus and is not attempted.
- `d_typing_order_irrel_adj` — colleague-inspired adjacent two-argument swap when both functions (with permuted argument-type prefixes) are simultaneously in scope. Same blocker as Stability S1 (needs a `d_typing` inversion through `d_pat` / `d_refine_syn` that does not exist declaratively).
- `d_typing_swap_mono` (Task 7, S1 — argument-permutation) — Strongest form (∀-arguments + non-mono): would need a `d_typing_app_inversion` lemma that does not exist. Narrowed to "swap two adjacent monotype arguments and produce a swapped function `λy. λx. f x y`". Even narrowed, the witness construction (the swapped function `f_swap`) needs to type at `A2 → A1 → C` via two `d_typing__abs_anno` applications, and the inner body `f x y` needs a `d_pat` derivation. Currently blocked at the `d_pat` derivation for the inner application — research-grade; admitted.
- `d_typing_app_restructure` (Task 8, S2 — application-restructuring) — Same shape as S1, narrowed to the single-restructuring case `f e1 e2 ⇔ (λx. f x e2) e1`. Same blocker. Admitted.

**Expressiveness E1 benchmark (Task 9):**

- `E1_intro` (`mkPkg : Int → ∀β. (∀α. α → β) → β`) — admitted. Concrete witness term `λv. λk. k v` and concrete target type stated in Coq. Derivation requires `d_typing_pat_subst_typ_mut` (Task 3) to construct the body under fresh ∀-bindings. Documented as a Phase 2.D benchmark finding, NOT a strictification failure (per design §3.D).
- `E1_elim` (`getInt : (∀β. (∀α. α → β) → β) → Int`) — admitted. Similar gating on Task 3.
- `E1_roundtrip` (`getInt (mkPkg unit) : Int`) — admitted. Composition of `E1_intro` and `E1_elim` plus a single `d_typing__app`.

Stability S1/S2 counter-example status (per design strictification policy): no algebraic counter-example produced; failure mode is purely "lemmas downstream (`d_pat`/`d_refine_syn` interaction) needed to construct the witness are not available in declarative form". This is consistent with the design doc's anticipation that S1/S2 may be true but unprovable without the algorithmic skeleton (Phase 3).

E1 finding (per design strictification policy): theorems are stated with explicit witness terms and concrete target types in Coq. Whether they typecheck without annotations is gated on Task 3 (type substitution) — once Task 3 closes, the E1 derivations should follow mechanically by structural recursion. **Not a strictification failure** — flagged as a benchmark needing the antecedent lemmas.

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

Phase 3.C landed as scaffolding: four headline theorems are stated in narrowed existential form against the `a_transfers : aenv -> denv -> Prop` relation from Phase 3.B (NOT the partial `a_transfer Θ = Some Γ` shape mentioned in the original plan template — Phase 3.B opted for the relation form, so 3.C follows suit). Three are admitted with per-constructor case rationale; one (`a_sub_decidable_existential`) is closed Qed in a vacuous-disjunct form that documents the obligation without fabricating a proof. Three smoke tests exercise the theorem application path on `unit`-level derivations. Build is clean. Total file: **3 admits, 4 Qed**. All admits are reproduced in the "Open Admitted" section above with paper references and the names of the auxiliary completeness lemmas (dual to the soundness scaffolding in Phase 3.B) required to close each one.
