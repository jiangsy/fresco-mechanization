# RESTART NOTE — make `a_unify` / `a_consis` mutual (and fix all three `unify` sites)

**Status:** definitions DONE and compiling, on branch **`remech-mutual-consis-unify`**
(commit `0f324de`, BUILD RED — proof layer untouched). `re-mech` is green and does
NOT contain this work.

**Why aborted rather than pushed through:** the refactor does not just re-prove the
`a_unify` lemmas — it *invalidates some of their statements* (below). That is past
what could be landed without admits, so it was parked per the no-admits rule.

---

## The defect

`a_unify__flex_assign` recursed into `a_unify` (the var-only `unifyvar`) where the
paper recurses into **CONSISTENCY**. The mechanized algorithm therefore gets STUCK
the moment a definition is a non-variable monotype — machine-checked in
`algo/cex_unify_stuck.v` (`a_unify_stuck_on_arrow_definition`, Qed, axiom-free).

The reading is settled and author-confirmed. **full-algo-spec.tex:1440-1442**:

> "We write `Θ₀ ⊢ P ∼ P₀ ⊣ Θ₁` for `Θ₀ ⊢[P₀] P ∼ Q ⊣ Θ₁` **when the output Q is
> not used**."

So the two-slot `A ∼ B` is consistency: **SUBJECT `A`, INPUT `B`, output dropped**.
`Δ₁∣Δ₂` are omitted, which per :1472-1473 means **both empty**. See
`docs/PAPER-GAPS.md` and the memory note `frost-unify-means-consis-notation`.

## Why MUTUAL

Consistency's `Flex` rule calls `a_unify`; `a_unify`'s `Flex-Flex-Assign` calls back
into consistency. **The paper says so itself** — consistency-proofs.tex:1562:

> "By **mutual induction on the algorithmic consistency derivation together with the
> two auxiliary judgements of variable unification and assignment**."

(Completeness says the same at :2257.) So the mechanization will end up *mirroring*
the paper's proof organisation, not diverging from it.

---

## What is already DONE (on the branch, `def_extra.v` compiles)

1. `a_unify` and `a_consis` merged into one `Inductive … with …`.
   `a_assign` left STANDALONE and defined first — see the open question below.
2. **`a_unify`'s subjects are now ATOMS**, matching the paper's hatted
   `unifyvar{α̂}{β̂}`. General `ptyp` subjects only ever existed to encode
   `a_split__flex`'s arrow — which was itself the bug.
3. `a_unify__flex_assign`'s premise → consistency (subject `α̂[τ/γ̂]`, input
   `β̂[τ/γ̂]`, output existential, both Δs empty).
4. `a_split__flex`'s premise → consistency (subject `α̂`, input `β̂ → γ̂`). **This is
   the site that could never have been `unifyvar`** — its input is an ARROW. It is
   the cleanest confirmation of the whole reading.

## What REMAINS — and note these are STATEMENT changes, not just proofs

| lemma | fate |
|---|---|
| `a_unify_var_inv` | **DELETE.** Subjects are atoms now; it is vacuous. (It never was a theorem about the system — it was a symptom of the bug.) |
| `a_unify_dom` (`dom Θ₁ [=] dom Θ₀`) | **NOW FALSE — delete.** Unification can GROW the context: consistency → FlexL/FlexR → `a_assign` → `Assign-SolveM` → fresh `β̄` from `guess^TY`. This is CORRECT; the paper's part-2 soundness only claims an information increase `⊑{Θ₀}{Θ₁}`, which permits growth. Every USE of `a_unify_dom` must be reworked to an ⊑-based argument. |
| `a_unify_sound`, `a_unify_preserves_wf`, `a_unify_preserves_inv`, `a_unify_subjects_flex`, `a_unify_sym` | become **MUTUAL** with their `a_consis` counterparts (`Scheme` + `Combined Scheme`). |
| `a_consis_sound_aux` | must be **RESTORED as a direct 14-case induction**. It was collapsed into a corollary of `a_consistag_sound_aux` — but that lemma's Flex case needs `a_unify_sound`, which now needs consistency soundness. **Circular.** Recover the deleted proof from `d6ba637^`. |
| `a_consistag_sound_aux` | stays a PLAIN induction, sitting ABOVE the mutual bundle and using its results. `a_consistag` is not in the cycle (nothing calls back into it). |

Suggested shape of the mutual bundle (one `Combined Scheme` over `a_unify` +
`a_consis`), each side proving its full conjunction:

- `a_unify`: `Θ₀ ⊴ Θ₁` ∧ `a_wf_aenv Θ₁` ∧ invariants ∧ `Θ₁ ⊢ α̂ ≡ᵗ β̂`
- `a_consis`: `Θ₀ ⊴ Θ₁` ∧ `a_wf_aenv Θ₁` ∧ invariants ∧ `∃Qt, …` ∧ refinement

`a_assign_sound` can stay separate (see below).

## OPEN QUESTION — `a_assign` and the `F` set

The paper puts **assignment in the cycle too**: `Assign-Assign`'s premise
(:1754) is `unify{α̂[τ/β̂]}{P[τ/β̂]}`, i.e. CONSISTENCY over `Ξ ++ Θ₀` with subject
`α̂` and input `P[τ/β̂]`. The mech instead CONTINUES the assignment — a workaround
whose stated justification ("`P` is a general skeleton, so monotype-level `unify`
does not apply") rests on the SAME misreading, since consistency does take
skeletons.

It was left alone on the branch because of a genuine tension: `a_assign` carries a
used-names set `F` (a prose-completion for `Assign-SolveM`'s "fresh β̄", already in
PAPER-GAPS). Routing `Assign-Assign` through consistency → FlexL restarts assignment
with `F = ∅` and `Ξ` merged into the context, **losing the accumulated `F`** and
weakening the freshness side condition. `a_consis` has no `F` to thread it through.

Decide this before finishing: either (a) thread `F` through `a_consis` too, or
(b) keep the current `a_assign` workaround and document it as a deliberate,
provably-equivalent departure, or (c) find a different freshness discipline.
Unlike `a_unify`, the `a_assign` workaround causes **no known incompleteness** — no
stuck state has been exhibited — so it is not urgent.

## Also

`algo/cex_unify_stuck.v` becomes OBSOLETE once this lands (the bug is fixed).
Convert it into a REGRESSION TEST: show the corrected rule *succeeds* on
`Θ₀ = (α̂ ≔ unit → unit), β̂` — substituting gives subject `unit → unit`, and
consistency's FlexR assigns `β̂ ≔ unit → unit`.
