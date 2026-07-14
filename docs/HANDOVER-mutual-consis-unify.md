# Handover prompt — finish the mutual `a_unify` / `a_consis` refactor

*(Paste the block below into a fresh session.)*

---

Continue the Frost/Fresco mechanization in `/Users/jiangsy/Documents/HKU/Research/impredicative`.

## Task

Finish the **mutual-recursion refactor** of `a_unify` / `a_consis`. Work on branch
`remech-mutual-consis-unify` (currently **RED**, HEAD `d27d3da`). Branch `re-mech`
is **green** and must stay untouched until this lands.

Read first, in order:
1. `mechanization/docs/RESTART-mutual-consis-unify.md` — the plan
2. `mechanization/docs/PAPER-GAPS.md` — entry "the `unify` premise IS consistency"
3. `mechanization/frost/algo/prop_mono_bridge.v` — what's already proved

## Why (settled, author-confirmed — do not relitigate)

The paper's `Flex-Flex-Assign` premise `unify{α̂[τ/γ̂]}{β̂[τ/γ̂]}` is the **CONSISTENCY**
judgment, not `unifyvar`. full-algo-spec.tex:1440-1442 says outright:

> "We write `Θ₀ ⊢ P ∼ P₀ ⊣ Θ₁` for `Θ₀ ⊢[P₀] P ∼ Q ⊣ Θ₁` **when the output Q is not used**."

So the two-slot form is consistency: **SUBJECT `A`, INPUT `B`, output existential**;
`Δ₁∣Δ₂` omitted means **both empty**. The mechanization recursed into `a_unify`
instead, which makes the algorithm get **stuck** whenever a definition is a
non-variable monotype (machine-checked: `algo/cex_unify_stuck.v`, Qed).

Hence `a_unify` and `a_consis` are **mutually inductive** — which is how the paper
organises its own proof (consistency-proofs.tex:1562: *"by mutual induction on the
algorithmic consistency derivation together with the two auxiliary judgements of
variable unification and assignment"*).

## Already DONE on the branch (all Qed, zero admits)

- **Definitions** (`def_extra.v`, compiles): `a_unify`/`a_consis` mutual;
  `a_unify` subjects are **atoms** (the paper's hatted `unifyvar{α̂}{β̂}`);
  `a_unify__flex_assign` and `a_split__flex` both recurse into **consistency**.
  (`a_split__flex`'s input is an ARROW — it could never have been `unifyvar`, and
  forcing it through `a_unify` is what made `a_unify` take general monotypes.)
- **`prop_mono_bridge.v`** — 12 lemmas. The **forward bridge** is the key one:
  `consis_refine_mono_tyequiv` : from consistency's coloured JOIN `Qt` plus a
  refinement, recover `Θ ⊢ A ≡ᵗ B` on monotypes. This is exactly what
  `flex_assign` needs, and it was the only genuinely new mathematics.
  Also: `consis_mono_refl`, `consis_mono_sym`, `consis_mono_psi_empty`.
- `a_unify_var_inv` **DELETED** (vacuous — subjects are atoms).
- `a_unify_dom` **DELETED** — it is now **FALSE**: unification can GROW the context
  (consistency → FlexL/FlexR → `a_assign` → `Assign-SolveM` → fresh `β̄`). Correct:
  part-2 soundness only claims an information increase.

## What to do, in order

1. **`consis_mono_trans`** — consistency is transitive on monotype paintings.
   This is PLUMBING, not mathematics. Same nested-induction shape as
   `ad_refine_syn_trans` (`prop_precise.v`): OUTER induction on the second
   derivation, INNER on the first to peel `flex_l` (unfolds the SUBJECT while the
   right stands still); `flex_r` unfolds the JOIN and falls to the outer IH.
   **Trap that cost the last session:** both derivations' indices must stay
   VARIABLES across the two inductions. `syn{A}` is not a variable, so carry the
   subject as `Sa` with `Sa = syn{A}` on the side, and `remember` the join. A bare
   `subst` silently EATS that side equation — shield it (`revert HeqA. … intros HeqA.`).
2. **`tyequiv_mono_consis`** (converse bridge): `A ≡ᵗ B ⟹ syn{A} ≈ syn{B}`, by
   induction on `≡` using refl/sym/trans. Needed by `a_unify_sound_consis`.
3. **The mutual soundness bundle**. `Scheme` + `Combined Scheme` over `a_unify` +
   `a_consis` (already verified Coq accepts it). Restore `a_consis_sound_aux`'s
   14-case proof from `d6ba637^` — it was collapsed into a corollary of
   `a_consistag_sound_aux`, whose Flex case needs `a_unify_sound`. Circular.
   `a_consistag_sound_aux` stays a PLAIN induction ABOVE the bundle.
   The invariant conjuncts must be generalised to `∀Δ` (the consistency premise
   inside `flex_assign` has `Δ₁=Δ₂=∅`, so a `Δ₁∪Δ₂`-only statement is useless there).
4. Rework the remaining `a_unify_*` lemmas (`_sound`, `_preserves_wf`,
   `_preserves_inv`, `_subjects_flex`, `_sym`) onto the bundle. `a_unify_sym` is
   probably FALSE now (consistency is not symmetric — subject vs input); use
   symmetry of `≡` instead.
5. `cex_unify_stuck.v` becomes OBSOLETE — convert it into a REGRESSION TEST showing
   the corrected rule SUCCEEDS on `Θ₀ = (α̂ ≔ unit → unit), β̂`.
6. Merge to `re-mech` only when `make coq` is green with **zero admits**.

## Open question (flagged, not decided)

The paper puts **assignment in the cycle too** (Assign-Assign's premise is also
consistency), but the mech's `a_assign` carries a used-names set `F` for
`Assign-SolveM`'s freshness. Routing Assign-Assign through consistency → FlexL
restarts assignment with `F = ∅`, losing it. `a_assign` was left standalone. Unlike
`a_unify`, its workaround causes **no known incompleteness**, so it is not urgent —
but decide before claiming full faithfulness.

## House rules

- **Zero admits in any commit.** If it cannot be finished, abort with a RESTART NOTE.
- `make coq` green before committing. Commit tag `[mech]`.
- Never change the paper's definitions/lemma statements: a broken proof STEP gets
  your own repair + a `[paper-gap]` note; a genuinely FALSE statement (with a
  counter-example) → STOP and flag to the user.
- Before calling anything false, check `docs/WF-SIDE-CONDITIONS.md` — the paper
  states well-formedness as an EXTERNAL prose requirement, and several judgments
  look false until that is restored.
