# External well-formedness side conditions (the paper's "required separately")

**Read this before mechanizing any lemma over the refinement, consistency,
subtyping, or skeleton-inference judgments.**

The paper repeatedly defines a judgment and then states — in *prose*, outside
the rules — that its arguments are additionally required to be well-formed (and
sometimes to satisfy a further judgment). The rules themselves then legitimately
omit side conditions that well-formedness would have supplied.

A Coq `Inductive` has no such notion of an "external condition". So every one of
these becomes a proof obligation somewhere, and there are exactly two places to
put it:

- **(A) In the rule.** Add the condition as a premise of the constructor.
  Cheap when it transports through the existing structural lemmas.
- **(B) In the statements.** Leave the rules verbatim and carry the condition as
  an explicit hypothesis of every lemma over the judgment.

**Try (A) first — it is less bookkeeping. But (A) is not always available**: a
premise must survive every transport lemma (weakening, strengthening,
Δ-monotonicity, ⊴-stability, renaming, and — the killer — the fill-hygiene
`strip` lemmas, which *remove a context entry*). If it doesn't, fall back to (B).
See the refinement entry below for a worked example of (A) failing and (B)
succeeding.

---

## 1. Refinement — wf of BOTH sides. **[load-bearing; resolved via (B)]**

> declarative.tex:1427 — "We require well-formedness of **both** `inh{P}` and
> `bid{Q}` under Γ as well-formedness conditions of the refinement judgement."

So `Γ ⨟ Δ ⊢ᵣ inh{P} ⊳ bid{Q}` is only ever considered when the **output** is
well-formed too. This is what the GhostForall rule's inline comment
(declarative.tex:1501, "It's fine to keep Δ since we already required
well-formedness separately") is pointing back at.

**Why it matters.** Without it the judgment is genuinely broken: GhostForall binds
its variable in Γ but keeps Δ, while the Ghost rule's side condition only tests Δ
— so a ghost nested under a GhostForall can be filled with the very variable
GhostForall binds:

    □ ⊳ syn(⊤.(□→□))            (Ghost — the fill is well-formed)
    ⊤.(□→□) ⊳ ∀α. ⊤.(α→α)       (GhostForall, then two Ghost fills at α)
    but NOT  □ ⊳ ∀α. ⊤.(α→α)

Refinement is therefore **not transitive** — machine-checked in
`algo/cex_refine_not_transitive.v` (`ad_refine_syn_not_transitive`, Qed,
axiom-free) — which kills `lemma:precision-preserves-refinement`
(full-algo-spec.tex:716) and with it completeness.

The external wf condition is exactly the escape: `∀α. ⊤.(α→α)` is well-formed in
**no** context at all (`Pres_not_wf`) — skeleton wf binds a quantifier's variable
in Δ, while a ⊤-ghost's body must be well-formed at the EMPTY Δ. So that
derivation was never in the judgment's domain.

**(A) was tried and REJECTED.** Adding the output's wf as a premise of
`*__tophole_fill` works through weakening / strengthening / Δ-monotonicity /
⊴-stability / subst / same_tvar (all five decl+algo files were fixed cleanly),
but it **does not survive `ad_refine_*_f_strip`**: that lemma removes a context
rigid `α` (with `α ∈ F`, `α ∈ Δ`), and a ⊤-ghost body inside the output may
legitimately mention `α` justified *by that very context binding* — `α ∈ Δ`
cannot rescue it, because ⊤-ghost bodies are checked at the EMPTY Δ. So the
premise is not transportable and the soundness proof's ∀-cases break.

**(B) is what we do.** Rules verbatim; wf carried in the statements. Mechanized in
`algo/prop_precise.v` (all Qed, axiom-free):

| lemma | content |
|---|---|
| `ad_refine_syn_syn_l` | a syn-headed refinement lands in a syn painting — **shape only**; no wf is derivable and none is needed |
| `ad_wf_pskl_delta_shrink` | Δ-variables the skeleton does not mention may be dropped |
| `ad_wf_pskl_empty_delta_free` | wf at the empty Δ ⇒ Δ-free (Δ is fresh for Θ) |
| `ad_refine_syn_syn_delta_free` | a syn LHS never fires the `all` rule, so Δ never grows and Δ-freeness propagates |
| `ad_refine_syn_syn_l_wf` | **the crux**: *assuming* the result is well-formed, it is a syn painting of a skeleton well-formed at the EMPTY Δ — precisely what re-applying the Ghost rule needs |

---

## 2. Skeleton consistency — wf of both sides **AND a refinement premise**. `[WATCH]`

> declarative.tex:2074 — "Skeleton consistency `Ψ ⨟ Γ ⊨ syn{S} ≈ bid{P}` requires
> well-formedness of `syn{S}` and `bid{P}` under Γ **as well as the refinement
> judgement `Γ ⊢ ⌊S⌋ ⊳ P`**."

Note the second half: **consistency presupposes refinement.** The mechanized
`d_pat_consis` / `ad_pat_consis` do **not** carry this. It has not bitten yet
(appendix-B soundness went through without it), but any consistency lemma that
needs to know the two sides are related beyond what the rules say must add it as
a hypothesis. Check here first when a consistency lemma looks unprovable.

---

## 3. Guardedness comes from wf, not from a premise

> declarative.tex:1911 — "well-formedness implicitly guarantees that `P` is
> guarded"

Here the mechanization took route **(A)**: `*__tophole_keep` carries
`guarded_bskl P` explicitly. Keep it that way — it transports fine, and it is far
cheaper than re-deriving guardedness from wf at every use.

---

## 4. Skeleton inference — wf of the term and the skeleton, plus mode compatibility

> declarative.tex:1595 — "We require well-formedness of `M` and `bid{P}` under Γ
> … as well as the compatibility between bidirectional skeletons and modes
> `skmod{bid{P}}{M}`."

`skmod` is already a rule premise in the mech (route **A**). The wf of `M` and
`bid{P}` is route **B** — carry it in the statements.

---

## 5. Algorithmic judgments — all inputs well-formed

> algorithmic.tex:233 — "As usual, we require all inputs to be well-formed."
> algorithmic.tex:915 — "In addition to well-formedness of all inputs, we require
> `skmod{P₀}{M}`."
> full-algo-spec.tex:1463 — "assuming well-formedness of `P₀` and `P`, we use two
> auxiliary contexts `Δ₁` and `Δ₂`."

This is why `a_consis_sound_aux` / `a_consistag_sound_aux` take
`Θ₀ ⨟ ∅ ⊢ₚₛᵃ P₀` and `Θ₀ ⨟ ∅ ⊢ₚₛᵃ P` as premises, and why the `Δ₁ ∣ Δ₂`
auxiliary contexts exist at all. Route **B**, already done.

---

## 6. Solution target — wf of the increment's TARGET context. **[optimality; via (B)]**

> algorithmic.tex:89 — the increment is "a finite map θ from flexible variables
> in Θ to **well-formed monotypes in Θ′**" — so the target context Θ′ of any
> solution is **well-formed by construction**.

The mechanized increment `Θ ≤[θ] Θ′` (`a_inc`) does **not** enforce this: its
`a_inc__empty` / `a_suffix` base cases can rest on ill-formed definitions, and
`a_wf_aenv Θ′` is **not** derivable from `Θ ≤[θ] Θ′` alone. So the wf of a
solution's target is an external side condition, carried on the statements
(route **B**), not a weakening.

**Where it lands (`algo/prop_consis_complete.v`).** Each of
`a_{consis,unify,assign}_solution` gains a final conjunct `a_wf_aenv Θ1` (the
target), and each `*_optimal_post` induction motive gains a hypothesis
`a_wf_aenv Θ` on the *competing* solution's target. The top-level corollaries
thread it straight from the competing solution's own new conjunct.

**Machine-checked necessity (C-Unit).** Inverting the competing join
`empty ⨟ Θ ⊨ₛᵃ uskl_unit ≈ Qb` produces a `flex_r` branch in which Θ holds a
defined flex `α ≔ τ` and `Qb = bskl_var_f α`; the residual goal
`pskl_unit ⊑ pskl_var_f α` is dischargeable **only** by `consis_mono_join`,
which requires `a_wf_aenv Θ`. Without the side condition the case is stuck.
(Validated 2026-07-15, `[paper-gap]`.)

---

## Rule of thumb

When a metatheory lemma over one of these judgments looks **structurally
unprovable**, before suspecting the calculus:

1. Check this file — the paper may have an external condition the mech dropped.
2. Try route **(A)** (premise on the rule). If it survives every transport lemma,
   take it.
3. If it dies in a transport lemma — especially a `strip`, which removes a context
   entry — take route **(B)** and thread it through the statements.

This is the well-formedness analogue of the colour/mode discipline: the condition
that makes the bad derivation impossible usually lives *outside* the rule.
