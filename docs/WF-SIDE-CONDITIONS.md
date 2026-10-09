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
Δ-monotonicity, ⊴-stability, renaming, and — the killer — the `strip`
lemmas, which *remove a context entry*). If it doesn't, fall back to (B).
See the refinement entry below for a worked example of (A) failing and (B)
succeeding.

---

## 1. Refinement — wf of BOTH sides. **[load-bearing; resolved via (B); rules verbatim since 2026-10-08]**

> declarative.tex:1427 — "We require well-formedness of **both** `inh{P}` and
> `bid{Q}` under Γ as well-formedness conditions of the refinement judgement."

So `Γ ⨟ Δ ⊢ᵣ inh{P} ⊳ bid{Q}` is only ever considered when the **output** is
well-formed too. This is what the GhostForall rule's inline comment
(declarative.tex:1501, "It's fine to keep Δ since we already required
well-formedness separately") is pointing back at.

**The rules are now the paper's, rule for rule (2026-10-08, commit
`51122ada`).** All four refinement relations (`d_refine_syn`,
`d_refine_pskl`, `ad_refine_syn`, `ad_refine_pskl`) and all three skeleton-wf
relations (`d_wf_pskl`, `d_wf_uskl`, `a_wf_pskl`) follow declarative.tex
("Well-formedness of skeletons", "Skeleton refinement") and its
algorithmic-context reading:

- **wf:** the variable rule reads only the context (`Γ ∋ α` / `a_binds_tvar`);
  a quantifier binds its variable in BOTH the context and Δ; a ∀◇ body is
  checked guarded at `Γ∖Δ | ·` (`denv_minus` / `aenv_minus`).
- **refinement:** the variable rule has no premise; the ∀ rule extends the
  context AND Δ; the Ghost rule asks only `Δ ∩ ftv(fill) = ∅` — it no longer
  checks the fill's well-formedness; keeping a ∀◇ no longer re-checks
  guardedness; GhostForall is unchanged (binds in Γ, keeps Δ).

The presupposition — wf of both sides — is therefore not a premise of any
rule; it is carried as a hypothesis by the lemmas that need it (route **B**).

**Why it matters.** The rules alone derive ill-formed outputs. GhostForall
binds its variable in Γ but keeps Δ, while the Ghost rule's side condition only
tests Δ — so a ghost nested under a GhostForall can be filled with the very
variable GhostForall binds:

    ∀◇(□→□) ⊳ ∀α. ∀◇(α→α)       (GhostForall, then two Ghost fills at α)

The source is well-formed; the output is well-formed in **no** context
(`Pres_not_wf`): the ∀ puts α into Δ, and the ∀◇ body is checked at `Γ∖Δ`,
where α is no longer bound. Machine-checked as `ad_refine_syn_output_not_wf`
(`cex/cex_refine_not_transitive.v`, Qed, axiom-free). So "refinement preserves
well-formedness" cannot be read off the rules; it needs the presupposition.

⚠️ **RETRACTED 2026-10-08 — refinement is NOT shown non-transitive.** This
entry used to say that refinement is not transitive (`ad_refine_syn_not_transitive`,
via `□ ⊳ syn(∀◇(□→□))` then the step above, but NOT `□ ⊳ ∀α. ∀◇(α→α)`), and
that this killed `lemma:precision-preserves-refinement` (full-algo-spec.tex:716)
without the wf condition. The refutation rested on the mech's OLD Ghost rule,
which demanded a well-formed fill (`Θ ⨟ ∅ ⊢ P`) — something the paper's rule
never did. Under the paper's Ghost rule the composite is derivable in one step
(`ghost_to_Bres`: the fill is closed, so it avoids Δ), and the refutation is
gone. The file keeps its name; it now proves only the ill-formed-output fact
above. Transitivity is PROVED under the presupposition (`ad_refine_syn_trans`,
below); whether it holds outright has not been established either way.

⚙ **(A) was tried and REJECTED** (2026-07, under the OLD rules, kept as the
worked example the preamble promises). Adding the output's wf as a premise of
`*__univ_ghost_fill` survived weakening / strengthening / Δ-monotonicity /
⊴-stability / subst / same_tvar, but **not `ad_refine_*_f_strip`**: that lemma
removes a context rigid `α`, and a ∀◇-ghost body inside the output may
legitimately mention `α` justified by that very context binding.

**(B) is what we do.** What the development actually uses now
(`algo/prop_precise.v` unless noted; all Qed, axiom-free):

| lemma | content |
|---|---|
| `ad_refine_syn_syn_l` | a syn-headed refinement lands in a syn painting — **shape only**; no wf is derivable and none is needed |
| `ad_refine_syn_syn_delta_free` | a syn LHS never fires the `all` rule, so Δ never grows and Δ-freeness of the fill propagates — given that no flexible is a Δ-variable and no flexible definition mentions one |
| `ad_refine_syn_ghost_l` | **the crux**: whatever a Δ-free syn painting refines to, `◇` refines to as well — one Ghost step, **no wf needed** (the Ghost rule only asks Δ-freeness) |
| `ad_refine_syn_trans` / `_trans_gen` | transitivity, **assuming the result is well-formed** (`Θ ⨟ Δ ⊢ₚₛ ⌊Qr⌋`, the presupposition); every ghost-left case goes through `ad_refine_syn_ghost_l` |
| `ad_precise_preserves_refine` | `lemma:precision-preserves-refinement`, a corollary of transitivity (precision IS refinement between inherited paintings) |
| `a_wf_pskl_empty_delta_free` | wf at the empty Δ ⇒ Δ-free, when Δ is fresh for Θ (used by `consis/prop_consis_precise.v`) |

⚙ Deleted in the 2026-10-09 cleanup as unused: `ad_refine_syn_syn_l_wf` (the
old crux, which recovered a skeleton wf at the EMPTY Δ from wf of the result),
`a_wf_pskl_delta_shrink` and `ad_refine_syn_ghost_l_target_wf` (a refinement
out of `◇` moving the target's wf from `Δ = ∅` to any `Δ` — an instance of
`a_wf_pskl_delta_mono`).  The `_gen` forms took the plain names
`ad_refine_syn_ghost_l` / `ad_refine_syn_syn_delta_free`.

⚠️ **Δ-monotonicity now SHRINKS Δ.** Under the paper's Ghost rule a larger Δ is
harder (a fill may mention an added variable), and under the paper's ∀◇ wf rule
too (`∀◇.α` is wf at `Θ = α, Δ = ∅` but not at `Δ = {α}`). So
`ad_refine_syn_delta_mono` / `ad_refine_pskl_delta_mono` take `Δ [<=] Δ0`, and
`a_wf_pskl_delta_mono` takes the agreement form (every free variable of `P` in
the new Δ was in the old one). A caller that GROWS Δ must show the added
variables are not free in the skeleton — usually from an existing
`Δ ∩ ftv … [=] empty` side condition or the presupposition.

## 1a. Precision target — wf of the TARGET on `lemma:precision-sub`. **[registered 2026-10-08; via (B)]**

> algorithmic.tex:535 — "This is exactly what `Θ ⊢ inh{P} ⊳ inh{Q}` means."

Precision `Θ ⊢ P ⊑ Q` is DEFINED as refinement between the two inherited
paintings, so §1's presupposition applies to it: the precision target `Q` is
well-formed.

`ad_precise_extends_pat_sub` (`lemma:precision-sub`,
`algo/sub/prop_completeness_sub_precise.v`, `Check`ed in `README.v`) now carries
it as `{{ Θ ⨟ Δ ⊢ₚₛ P }}a` for its precision target `P` (in `P' ⊑ P`). This is
the ONE `README.v` statement that changed in the 2026-10-08 rewrite. Why: the
lemma converts the precision to `⊑ᵤ` (`uskl_precise_of_ad_precise`), whose
`upre__ghost` row needs its fill well-formed — which the refinement used to
supply through the old Ghost rule's wf check and no longer does. Its one caller
(`ad_ctx_precise_pat`'s Var row, `algo/prop_precise_sub.v`) supplies it from the
context entry's stored wf (`a_wf_aenv_binds_var_{typ,skl}_wf`), so nothing
propagates.

---

## 2. Skeleton consistency — wf of both sides **AND a refinement premise**. ✅ `[CARRIED 2026-08-11]`

> declarative.tex:2074 — "Skeleton consistency `Ψ ⨟ Γ ⊨ syn{S} ≈ bid{P}` requires
> well-formedness of `syn{S}` and `bid{P}` under Γ **as well as the refinement
> judgement `Γ ⊢ ⌊S⌋ ⊳ P`**."

Note the second half: **consistency presupposes refinement.** The mechanized
`d_pat_consis` / `ad_pat_consis` do **not** carry this.

✅ **IT BIT, AND IS NOW CARRIED (2026-08-11).** This entry used to read "it has
not bitten yet (appendix-B soundness went through without it)". That is retired: the
deferral is exactly what blocks the completeness half of the closed-program
corollaries, and it is not a bookkeeping premise — it is **not derivable from
the consistency rules**. At subject `∀α.◇` and counterpart `∀ˢα.α` the rules
derive the consistency (`C-ForallSyn` puts `α` into Γ, so `C-Ghost` may fill the
ghost with it) while refinement rejects it (`R-Forall` puts `α` into Δ, and
`R-Ghost`'s fill must avoid Δ). Both halves machine-checked:
`cex/cex_ad_pat_join_not_leaf_valid.v`; the two consequences for skeleton
inference in `cex/cex_d_pat_bridges_false.v`.

⭐ **ROUTE (A), DONE.** `ad_pat_sub_fuel` had always carried it — at each
consistency LEAF of a subtyping derivation, which is where consistency actually
occurs. `d_pat_sub`'s three consistency-bearing rows (`Infer`, `UnivGhostR`, the
`Arrow` domain) now carry it too, over the new uncoloured `d_refine_pskl`
(`decl/def_rules.v`; the paper defines that sort at `declarative.tex:1516`). The
`d` and `ad` skeleton-inference judgements therefore agree row for row, which is
what made `d_pat_to_ad` / `d_sd_typing_to_ad` hypothesis-free. Kit: three
structural lemmas mirroring `d_refine_syn`'s (`_weakening`, `_subst_unit`,
`_same_tvar`) plus the ⇄ bridge in `prop_conserv.v` §5. Full statement, in the
paper's notation: [`ghost-capture.tex`](ghost-capture.tex).

⭐ **THE TWO ARE NOW ONE RELATION (2026-08-22).** Carrying the presupposition
as a *separate* premise made it possible, in principle, to insert one without
the other. It is now a single judgement — **the JOIN** —

```coq
Definition d_consis_join Ψ Γ R Q :=            (* {{ Ψ ⨟ Γ ⊢ˢ R ∼ᵣ Q }}d  *)
  {{ Ψ ⨟ Γ ⊢ˢ R ∼ Q }}d /\ {{ Γ ⨟ nil ⊢ᵣₚ ⌊R⌋ˢ ⊳ ⌊Q⌋ }}d.
Definition ad_consis_join Ψ Θ R Q :=           (* {{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad *)
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad /\ {{ Θ ⨟ empty ⊢ᵣₚ ⌊R⌋ˢ ⊳ ⌊Q⌋ }}ad.
```

(`decl/def_rules.v`, `algo_decl/def_consis_refine.v`) — and it is what all
eleven consistency-leaf rows take: `d_pat_sub`'s `Infer` / `UnivGhostR` /
`Arrow`-domain, and `ad_pat_sub` / `ad_pat_sub_fuel`'s `Infer` / `Check` /
`UnivGhostR` / `Arrow`-domain. The coupling is therefore **structural**, not a
discipline.

⚙ **WHAT THE MERGE FOUND.** At the SKELETON sort every join insertion is
coupled with a consistency, as hoped. At the TYPE sort there is nothing to
couple: `d_consis` (utyp ∼ btyp) carries **no** refinement datum, because there
are no ghosts at the type sort and refinement there is reflexivity. The single
place a join is *manufactured* out of a bare consistency is therefore the
type-sort bridge `d_consis_join_ty` (`algo_decl/prop_conserv.v` §13), whose
refinement half is `d_consis_refine_ty` — reflexivity, given scope.

⚙ Transport kit for the join (each is its two halves' transports, plus the two
erasure commutations where the substitution moves): `_weakening`,
`_subst_unit`, `_same_tvar` (decl); `_mono`, `_isub`, `_weaken`, `_psi_cong`,
`_subst_mid`, `_subst_flex`, `_subst_flex_def`, `_rename_tvar`,
`_tyequiv_subject`, `_unfold_def_subject`, `_paint_transport` (algo); and the
⇄ bridge `ad_consis_join_to_d` / `d_consis_join_to_ad`. The TY rows'
counterpart is a painting, and `⌊inh B⌋ = B` is a RETRACTION rather than a
conversion, so those rows go through `ad_consis_join_inh` /
`ad_consis_join_inh_intro` / `ad_consis_join_inh_refine`.

⚠️ **Scope: the SKELETON sort only.** Type consistency ranges over types, which
have no ghosts, so the condition is free there — which is why the TY half of the
`d` ⇄ `ad` bridge is closed and the SK half is not.

---

## 3. Guardedness comes from wf, not from a premise

> declarative.tex:1911 — "well-formedness implicitly guarantees that `P` is
> guarded"

~~Here the mechanization took route **(A)**: `*__univ_ghost_keep` carries
`guarded_bskl P` explicitly.~~ **Changed 2026-10-08 — now route (B), as the
paper has it.** `*__univ_ghost_keep` no longer carries a `guarded_*` premise (the
paper's rule has none). Guardedness of a kept ∀◇ body is read off the
well-formedness of the refinement's TARGET (§1's presupposition): the ∀◇ wf
rule demands a guarded body. Lemmas that need it take the target's wf (or, for
the syntactic forms, `lc`) as a hypothesis — e.g. `ad_refine_syn_guarded_r`
(+ `lc_bskl Q'`, `consis/prop_soundness_consis.v`; `ad_refine_syn_guarded_r_all`
for a ∀ target); to rule out a ∀◇ target with no side condition at all,
`ad_refine_*_not_univ_ghost_r` (same file).  (Their `_f` twins went with the `_f`
relations, 2026-10-09.)

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

> algorithmic.tex:89 — the increment is "a finite map κ from flexible variables
> in Θ to **well-formed monotypes in Θ′**" — so the target context Θ′ of any
> solution is **well-formed by construction**.

The mechanized increment `Θ ≤[κ] Θ′` (`a_inc`) does **not** enforce this: its
`a_inc__empty` / `a_suffix` base cases can rest on ill-formed definitions, and
`a_wf_aenv Θ′` is **not** derivable from `Θ ≤[κ] Θ′` alone. So the wf of a
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

## 7. Completeness Δ (P6) — freshness w.r.t. Θ's definition images. **[P6-Cv; via (B)]**

> The `-var` completeness lemmas' precision premise `Δ ⨟ Θ ⊢ᵃᵈ κPi ⊑ᵖ[Ψi] ψa`
> carries a binder context Δ that the paper only ever populates with
> instantiation binders — all introduced AFTER Θ's definitions exist. The
> paper never states this; its rules and lemma statement leave Δ abstract.

**The condition.** `delta_def_fresh Δ Θ`: every `Y ∈ Δ` avoids
`ftvar_in_ptyp τ` for every `binds α (abind_flex_mono_def τ) Θ`
(`algo/prop_look_complete.v`). Carried on the statements (route **B**) of
`a_solve_eq_complete_var` and its helpers (`ad_refine_inh_ghost_ppre`,
`ad_ppre_flexdef_target_unfold`, the chain transports).

**Machine-checked necessity (P6-Cv, Var case).** With `X` a defined flexible
`X := (var Y)→1` in Θ, `Y ∈ Δ` rigid, `Pi = □` (the precision premise holds by
the □-rule at `var X` since `X ∉ Δ`), `P0 = (□→□)` (refinement unfolds X's
definition), every premise of the Δ-free statement holds; the forced solve
output is `Pa = P0`, whose conclusion precision must apply the □-rule at the
definition's paint — and its `Δ ∩ ftv` premise fails on `Y`. The Δ-free
statement is FALSE, not merely hard.

**Why it is the paper's wf.** Δ grows at exactly three points, each of which
supplies the condition for free: ForallInh binders are picked fresh from
`dom Θ ⊇` def-ftvs (`a_wf_aenv_def_ftv_dom`); the ρ-replaced variables carry
it inside the `rsubst_fresh` pack; and the initial Δ of the P6-Cs/Sv callers is
built from the same binder discipline. So the hypothesis is threading, never
a real obligation.

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


## Skeleton wf in the algo layer: `a_wf_pskl` (disciplined) vs `a_scope_pskl` (scoping-only)
   (registered 2026-07-18; renamed same day — the disciplined judgment now owns the `wf` name)

The algo layer has TWO skeleton judgments, both in algo/def_rules.v:

- **`a_wf_pskl` (`Θ ⨟ Δ ⊢ₚₛᵃ P`) — THE paper's skeleton wf** (ex-`ad_wf_pskl`,
  moved up from def_consis_refine.v).  Two contexts: ∀ binds its variable in
  BOTH Θ and Δ (since 2026-10-08; before, in Δ only), the variable rule reads
  only Θ, and a `∀◇`-body must be guarded and well-formed at `Θ∖Δ ⨟ ∅`
  (`aenv_minus`).  This is the ∀◇-discipline behind §1's capture example:
  `∀α.∀◇.(α→α)` is well-formed in NO context.  Whenever the paper writes
  skeleton wf, it means this judgment — the paper has no weak variant.

- **`a_scope_pskl` (algo/def_rules.v:113) — scoping only.**  Single context Θ,
  ∀ binds a plain `abind_tvar` into Θ, `pskl_univ_ghost` merely recurses (no
  guardedness, no Δ-clearing).  `∀α.∀◇.(α→α)` PASSES it.  The reference
  implementation's `is_wf_` takes the same weak reading.

**Where each sits.**

- ForallL's instantiation premise is the DISCIPLINED `(Ξ ++ Θ0) ⨟ ∅ ⊢ₚₛᵃ P1`
  (on `a_sub__forall_l` and both `a_subtag__forall_l_*`; commit a68fc84).
  Rationale: the paper's `Θ0,Ξ ⊢ P1` there IS its disciplined wf; the premise
  is consumed locally by the rule, so the usual transport objection to
  rule-side placement does not apply; and soundness's ForallL case NEEDS it —
  `ad_pat_sub__forall_l`'s scope premise is disciplined, and the
  weak→disciplined conversion is FALSE by the `∀α.∀◇.(α→α)` example.

- Statement-side hypotheses (soundness/completeness motives) all use the
  disciplined `a_wf_pskl` (route B), as prop_sub_sound.v's bundle does.
  Transport kit exists: `a_wf_pskl_isub` / `_weaken` / `_delta_mono` /
  `_mono_subst` / `_msubst_inc` / `_subst_tvar` / `_open`.

- ✅ **DONE 2026-08-09 — `a_wf_aenv__var` now stores the DISCIPLINED
  `Θ ⨟ ∅ ⊢ₚₛᵃ P`.**  `a_scope_pskl` has NO rule site left; it survives only in
  lemma statements.  What the queued-cleanup note above predicted, and what it
  got wrong:
  - The feared "split/guess outputs are disciplined" lemma pack was **already
    there**: `a_split_wf` (typing/prop_soundness_typing.v) yields
    `Θ1 ⨟ ∅ ⊢ₚₛᵃ P` for the split's left output — exactly what `a_pat__abs`
    pushes — and `a_pat__abs_check` pushes `□`, discharged by
    `a_wf_pskl__ghost`.  `ad_pat__abs` already carried the premise on the rule.
    No new pack was needed.
  - ⚙ **The real obstruction was ORDERING, and it was shallow**: `a_wf_pskl`
    was declared AFTER `a_wf_aenv` in algo/def_rules.v, so naming it in the
    constructor was a forward reference.  It depends only on `a_binds_tvar`
    and `guarded_pskl`, so its block moved above `a_wf_aenv` — 28 lines.
  - ⚠️ **The endgame "delete `a_scope_pskl`" is NOT reachable as stated.**  The
    weak judgment is genuinely needed: `ad_pat_consis_target_wf` (a
    consistency JOIN'S target erases to a scoped skeleton) yields
    `a_scope_pskl` and nothing stronger, and `msubst_compose_id_pskl` /
    `a_inc_equiv_msubst_pskl` are applied at exactly that subject.  Demanding
    the disciplined form there was tried and reverted.  Strengthening
    `ad_pat_consis_target_wf` is a real proof obligation (its `∀◇` cases would
    have to establish guardedness and the Δ-reset), not a rename.
  - Migration shape, for the record: consumers convert with
    `a_scope_pskl_of_wf` (prop_swap.v §0), which is also an `#[export] Hint
    Resolve`, so every site that discharged an entry's scope by `eauto` needed
    no edit at all.  `a_wf_pskl_ftv_tvarish` (since 2026-10-09 replaced by
    the stronger `a_wf_pskl_ftv_binds`) and `a_wf_pskl_to_a_scope_pskl`
    moved from the two consistency files to prop_swap.v §0 (the earliest algo
    proof file; algo/prop_basic.v would be the topical home but it IMPORTS
    prop_swap.v).  `a_wf_pskl_scope` — pat/prop_soundness_pat.v's private copy
    of the same conversion — was retired.  ⚠️ prop_swap.v has NO global
    `Set Implicit Arguments` by design, so §0 scopes its own.

**Rule of thumb** (unchanged): a premise consumed locally by its rule (like
ForallL's) may be disciplined at the rule; a condition threaded through the
walk's context surgery must be carried as an external `a_wf_pskl` statement
hypothesis instead — the `strip` lemmas are what kill the rule route (§1).

## `a_tags_sort` is CONTEXT-FREE (registered 2026-07-18; DESIGN-subtyping D3)

The paper's `Θ ⊢^N tags{Ψ}{ψ}` (full-decl-spec.tex:105-118) carries a context
and scope-wf of ψ.  `a_tags_sort` (algo/def_decorated.v:96) drops the context:
purely syntactic (`is_dskl` + `d_tags_skl`, ghost-freeness at TY); the scope
half is restored at each call site ON THE ERASURE (`(Ξ++Θ0) ⨟ ∅ ⊢ₚₛᵃ P1` in
the decorated ForallL; `Θ ⨟ ∅ ⊢ₚₛᵃ ⌊ψ⌋` in `ad_pat_sub`'s ForallL).  This is
the D3 decision of DESIGN-subtyping.md §1.2, now registered: statements
needing the paper's full judgment take `a_tags_sort NM Ψ ψ ∧ (scope premise
of the call site)` as the decomposition.

## Mode discipline on the DECORATION lemmas (registered 2026-07-20)

The L-A decoration lemmas (`a_subtag_decoration_var`, `a_consistag_decoration`,
KEY `a_subtag_decoration`, MAIN `a_sub_decorate` — algo/prop_decorate_sub.v,
prop_soundness_sub.v) all carry the external hypothesis

    NM = SK  ->  mod_comp_sk (pskl_to_bskl_inh P0) M

(`Hmod`).  This is the paper's implicit "the inputs are mode-compatible"
(skmod[SK], algorithmic.tex:239-244) restored in the STATEMENTS, not the
rules: without it the lemmas are FALSE at the ◈-vs-∀X.◇ corner — an SK-mode
∀-target at TC would let a dotted ghost decorate against a universal the
mode discipline forecloses at every real call site (`inh` paints `all_inh`,
`is_sskl` rejects).  It threads through the walk (Flex-Assign transports it
by `pskl_to_bskl_inh_subst_mono` + `mod_comp_sk_subst_mono`), so per §1's
rule of thumb it must live in the statements.

## `pskl_no_ghost P0` on P6-Cv completeness — **REMOVED 2026-07-27** (registered 2026-07-27; historical)

**RESOLVED — the premise no longer exists.**  `a_solve_eq_complete_var` /
`_gen` (algo/prop_look_complete_var.v) are now PREMISE-FAITHFUL to the
paper: the mech-only `pskl_no_ghost P0` side condition was removed by
reworking the Θtv/Θr context split from the LIST equation `Θ = Θtv ++ Θr`
to a binds-level BAG (`aenv_split`: binds-iff + dom-eq + disjointness,
with `a_wf_aenv Θr` carried explicitly).  The premise had been an artifact
of the list representation: the consistency rule PREPENDS the ForallSyn
binder to Θ, so a list split could only place it in Θtv, forcing the
aenv→Δr refinement transport (`ad_refine_syn_aenv_to_delta`) — false for
□-sources whose fill mentions the binder.  With the bag split the binder
joins Θr (`Θr_ih := (X~tvar)++Θr`), the univ_ghost_fill body IS the IH's
refinement premise verbatim, and ghosty `P0` flows through the recursion
to the per-row SolE-VacuousR columns — exactly the paper's per-node
"P0 = Hole" dispatch.  Consequently:

1. **P6-Cs (`a_lookeq_solve_complete`) needs NO `P0 = □ ∨ pskl_no_ghost`
   disjunct** — its statement can mirror the paper's directly, with its
   own `P0 = □` special case via LE-Vacuous as the paper does.  Same for
   P6-Sv/Ss/L.
2. **The accumulated-skeleton invariant below is NO LONGER REQUIRED** for
   the completeness chain.  Its file `algo/prop_accum_no_ghost.v` (Task A)
   was **DELETED 2026-07-27** — with the premise gone nothing consumes it,
   and it was pure supporting kit.  The description below is retained only
   as the historical record of what was proved.

The rest of this entry is kept as the record of the (now-deleted) invariant
proof and of the original analysis.

The invariant *"every accumulated flexible-variable skeleton is `□` or
ghost-free"*:  **INVARIANT PROVED
   (2026-07-27), axiom-free, in the since-deleted `algo/prop_accum_no_ghost.v`.**
   Deep-mixed
   `P0` (□ strictly below a constructor) is NOT reachable.  Four algo-level
   results (`Print Assumptions` = Closed under the global context):
   - **A1 `a_guess_hnh`** — `guess^TY` returns a paint (`ptyp_to_pskl`, no
     □-image ⇒ ghost-free); `guess^SK` is the identity (preserves the
     disjunct).
   - **A2 `a_look_payload_hnh`** — `a_lookeq`/`a_looksub` emit □-or-ghost-free
     constraint payloads whenever the counterpart is (mutual; a □-counterpart
     handled by LE/LS-Var emits the payload `eq(□)`, the left disjunct — it
     need NOT go through the Vacuous rules).
   - **A3 `a_solve_cstr_hnh`** (+ `a_solve_cstr_ghost_start_hnh`, the `□`-start
     form `a_extract` uses) — solving a constraint list from a □-or-ghost-free
     accumulator against □-or-ghost-free payloads stays □-or-ghost-free;
     generalises `a_solve_eq_no_ghost_p0` to the mutual sub/eq/cstr block
     (`a_solve_{sub,eq}_hnh`, `a_solve_sub_no_ghost_q`, the two `_from_subj`
     strict halves).
   - **A4 `a_sub_a_sub_flex_no_ghost_p0`** — `a_sub`/`a_sub_flex` outputs are
     ghost-free when the counterpart `P0` is.  KEY: this is **subject-free** —
     output ghosts come ONLY from the counterpart, so `a_sub__forall_l` merely
     threads `P0` (the ∀-body instantiation `open P P1` is irrelevant to the
     output even when `P1 = □` deep-mixes it), and `Infer`/`UnivGhostR`
     (`P0 = □`) are excluded by `pskl_no_ghost P0`.  (An earlier worry that
     ForallL blocks a subject-carrying induction was an artifact of a
     needless subject premise; the counterpart-only formulation closes
     cleanly.)  Support: `a_consis_out_no_ghost` / `a_consis_out_no_ghost_q`.
   Predicate: `pskl_hnh P := P = pskl_ghost \/ pskl_no_ghost P`.

Historical note: in the premise-carrying closure, ghost-freeness was
derivable from the other premises in some subcases (the Var-case binder
side still derives it locally, via
`ad_refine_inh_deltar_var_rhs_no_ghost`) but not in general — a
guarded-but-ghosty ForallSyn body satisfies every other premise; only the
split rework, not a derivation, could remove it.

## P6-Cs (`a_lookeq_solve_complete`) — the IDEAL GUESS is Θ-scoped

⭐ **NEW 2026-08-05, with the authors' `SolE-FlexR` repair.**  The repaired row
hands the accumulated pattern through `guess^TY` and ASSIGNS the result, so the
solve now emits a block of fresh flexibles whose payloads are read off the
IDEAL GUESS `ψa`.  Those payloads have to be well-formed in the ideal context,
which forces

**`ftvar_in_uskl ψa [<=] dom Θ`**

on `a_lookeq_solve_complete` (and `[<=] dom Θw` on the generalized form).  It
is the paper's prose "all inputs are well-formed" once more — `ψa` is an INPUT
— and it is **not derivable** from the other premises: when α does not occur in
`κR` the subject `(κR)[ψa/α]` does not mention `ψa` at all, so the subject-wf
premise above says nothing about it.

Its generalized companion `Δρ ∩ dom Θw [=] empty` is NOT a wf side condition
but a proof-construction fact about the mech's own ρ-generalization; it is
vacuous at ρ = identity.  See `docs/HANDOFF-solve-flexr-repair.md` §6 Step 1.

## P6-Cs (`a_lookeq_solve_complete`) — the subject-wf premise

Consistency constraint collection and solving
(consistency-proofs.tex:920) needs ONE of the paper's prose
well-formedness conditions restored as a premise, on an INPUT, so it
threads through the induction without touching the rules:

**`Θ ⨟ ∅ ⊢ₚₛᵃ ⌊ (κS)[ψa/α] ⌋ˢ`** — well-formedness of the CONSISTENCY
SUBJECT.  Stated on the erasure so the existing `a_wf_pskl` expresses it
(⌊·⌋ˢ maps the dotted ghosts onto the plain ones); the only content the
proof consumes is the GUARDED ghost body of `a_wf_pskl__univ_ghost`, which
matches the declarative `d_wf_uskl__univ_ghost`.

⚠️ **Without it the lemma is FALSE — machine-checked** in
`fresco/algo/cex/cex_p6cs_subject_wf.v`:
`p6cs_without_subject_wf_is_false` refutes the lemma carrying EVERY premise
except this one (with the conclusion weakened to its three essential
conjuncts, which only strengthens the refutation), and
`p6cs_fires_when_the_subject_is_wf` instantiates the CLOSED theorem on the
same shape with `ψa := ⟨⟩` to show the premise set is satisfiable (the
theorem is not vacuous).  Both are Qed and axiom-free.  Counterexample: `Θ = Θ0 = ·`,
`κ = ·`, `S = ∀◇α` (so `P = ∀◇α`), `ψa = ∀◈⟨⟩`, `P0 = Pi = ∀◇⟨⟩`,
`Q = ∀◇⟨⟩`.  Every other premise holds — consistency by C-UnivGhost2
then C-UnivGhostG, refinement by R-UnivGhostKeep, precision by
P-UnivGhostKeep — but the algorithm is FORCED: LE-UnivGhost is the only
applicable collection rule, so `𝒞 = [α ≐ ⟨⟩]`, and SE-GhostGuarded is
the only solving rule, so `Pa = ⟨⟩`; the resulting precision goal
`⟨⟩ ⊑ᵖ ∀◈⟨⟩` has no rule.  The offending subject is `∀◇(∀◈⟨⟩)` — a
ghost over a ghost — which both `a_wf_pskl__univ_ghost` and
`d_wf_uskl__univ_ghost` forbid.  So this is not a convenience premise: it
is what makes the paper's statement true.

**A wf premise on the SOURCE skeleton P is NOT needed.**  An earlier
closure carried `((α ~ abind_tvar) ++ Θ0) ⨟ ∅ ⊢ₚₛᵃ P` — the paper's
explicit "by well-formedness of P … Q is guarded" in C-UnivGhost2, with
the looked-up rigid α as a context entry because a Δ-reading is
unsatisfiable (`a_wf_pskl__univ_ghost` resets Δ to ∅, so an α under a ghost
could never be justified).  Once the subject-wf premise is in, that one
is dead weight: it was only ever fed back to its own IHs, and every
guardedness fact the proof needs comes from the subject side (the
subject's ghost bodies, not P's, are what the ghost rows inspect).  It
was removed; the proof is unchanged otherwise.

---

## P7b `Sub-Check` — well-formedness of the COUNTERPART in the solution context

**`Θ ⨟ ∅ ⊢ₚₛᵃ ⌊Q⌋`**, i.e. the solution's counterpart is well formed where
the solution lives.  Registered 2026-07-30 with `a_sub_complete_check`
(`fresco/algo/prop_sub_complete_thm.v`), which takes it as a hypothesis; the
P7 bundle will have to carry it on the motive.

**Why it is needed.** The case must move its precision from the solution's `κ`
to the package's `ζ`, and the composition step is `ad_refine_syn_trans`, which
is proved under exactly this external well-formedness — `declarative.tex:1427`
requires it of every refinement judgment anyway.  (This paragraph used to add
"refinement is NOT transitive outright (`cex/cex_refine_not_transitive.v`)";
that refutation was RETRACTED 2026-10-08 — see §1.)

**The two `P0 = □` rows.** At `P0 = □` the motive's own P0-fill premise is a
refinement OUT OF the ghost, and only two rows have a ghost source — `__ghost`
and `__flex_r`, whose target is a defined flexible and so is `a_binds_tvar`.
That was `ad_refine_syn_ghost_l_target_wf`.  ⚠️ Until 2026-10-08 the `__ghost`
row carried the fill's well-formedness on the rule, so these rows got the
counterpart's wf for free; the paper's Ghost rule does not, so the `Δ = ∅` wf of
the target became a hypothesis that the callers supply (from the motive, the
run's output wf, or the declarative derivation), and the lemma, left unused,
was deleted in the 2026-10-09 cleanup.

**Not a well-formedness condition, but registered with it** —
`a_sub_complete_check` also takes `guarded_pskl P0`.  The DECLARATIVE `Check`
row does not pin `P0`'s shape, but the ALGORITHM dispatches on it: a `∀` `P0`
is `ForallR`, not `Check`.  That is the paper's own case split.

## TY ghost-freeness of the SUBJECT (registered 2026-08-03; ⭐ ON THE MOTIVE since the same day)

The P7b motive `sub_complete_concl` (`fresco/algo/prop_sub_complete_thm.v`)
carries

    NM = a_sub_mode_ty  ->  uskl_ghost_free R'

on the JOIN-side subject, as its last premise (`Hgf`); `a_sub_complete`
(the paper-facing corollary, `prop_sub_complete_dispatch.v` §12) states the
same premise, so this is an EXTERNAL side condition of the final theorem — at
the paper's own reflexive instance `R' := κ⌈P⌉ᵘ` it is ghost-freeness of the
input `P`.  It is not decoration: it is the last premise of
`ad_pat_sub_precise_upre_gv`, i.e. P5's precision-substitution transport, and
P5 threads the very same predicate through
`fresco/algo/prop_sub_complete.v` as a hypothesis of every lemma in the pack.
It is what makes the SWAPPED subject `open Rj ⌈κPa⌉ᵘ` ghost-free, given that a
TY guess is a TYPE (`pskl_to_uskl_paint_ghost_free`).

**⚠️ It is NOT derivable from the join, and the near-miss is worth recording.**
All four rules that put a ghost AT THE HEAD of `ad_pat_sub_fuel`'s subject —
`__ghost`, `__ghostg`, `__univ_ghost_l`, `__univ_ghost_lg` — are SK-only, so
ghost-freeness looks like a TY invariant.  It is not: `__arrow`'s DOMAIN is an
arbitrary consistency leaf carrying no sort constraint, and `__infer` accepts
an arbitrary subject, so a ghost can sit *inside* a TY join's subject.  The
condition is genuinely external, in the same family as the `a_wf_pskl`
statement hypotheses of §1.

**Where it went (landed 2026-08-03, same day).** On the P7b motive, guarded by
`NM = a_sub_mode_ty` — which made it an obligation of every row that recurses
into the main half, and every supplier was CHEAP, exactly because the four
ghost-heading join rules are SK-only: Sub-Arrow inverts the arrow's
ghost-freeness for `R2'`; Sub-ForallR passes the same subject through; the two
Sub-ForallL rows DROPPED their own `Hgfj` hypothesis (the motive now supplies
it) and their ghost-free construction is the shared assert `Hgfswap`; the flex
half derives it OUTRIGHT from its own ≡ᵘ-to-a-monotype-painting slack
(`tyequiv_mono_paint_ghost_free`) at Flex-Assign and from the deposited
painting at Flex-Solve; the dispatcher's `__univ_ghost_l/lg` rows discharge it
by `discriminate` and `__flex_mono` by `mono_ptyp_to_uskl_syn_ghost_free`.
The remaining `main_forall n` hypothesis of `a_sub_complete_bundle_holds` now
carries ONLY TASK 0's `sub_shield` component.

**Related:** the ForallL rows' third premise, the WLOG
`guarded_pskl P0 \/ P0 = pskl_ghost`, USED to be part of the same residual and
is now discharged inside the dispatch (`p0_wlog_trichotomy` +
`sub_complete_all_inh_counterpart`, §8b) — it is a case split, not a side condition.

## Skeleton term entries — the payload-wf DISCIPLINE. **RETIRED 2026-08-10**

`a_wf_aenv__var` stores the disciplined `Θ ⨟ ∅ ⊢ₚₛᵃ P` for an `x : P` entry,
so

```coq
forall y Ps, binds y (abind_var_skl Ps) Θ -> Θ ⨟ empty ⊢ₚₛᵃ Ps
```

is a THEOREM of `a_wf_aenv Θ` — `a_wf_aenv_binds_var_skl_wf`
(algo/prop_inc_strengthen.v: the entry's stored wf, weakened past the entry).
It is no longer stated anywhere: not on `a_pat_sound` / `a_typing_sound` /
`a_pat_complete` / `a_typing_complete`, not on their `_gen` lemmas, not on
the step rows, and not inside the rows' induction hypotheses.  A row that
needs it derives it from the `a_wf_aenv` premise it already has.

⚙ Why it was ever needed for the SOLUTION context too, and not just the
question's: the binder rows push a term entry into BOTH contexts before
invoking the IH, so the IH is used at a *changed* target, and the glue
supplies each row's IH at a universally quantified `Θ'` — nothing in scope
could have discharged an omitted condition there.
