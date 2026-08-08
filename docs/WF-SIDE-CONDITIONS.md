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

    □ ⊳ syn(∀◇(□→□))            (Ghost — the fill is well-formed)
    ∀◇(□→□) ⊳ ∀α. ∀◇(α→α)       (GhostForall, then two Ghost fills at α)
    but NOT  □ ⊳ ∀α. ∀◇(α→α)

Refinement is therefore **not transitive** — machine-checked in
`algo/cex/cex_refine_not_transitive.v` (`ad_refine_syn_not_transitive`, Qed,
axiom-free) — which kills `lemma:precision-preserves-refinement`
(full-algo-spec.tex:716) and with it completeness.

The external wf condition is exactly the escape: `∀α. ∀◇(α→α)` is well-formed in
**no** context at all (`Pres_not_wf`) — skeleton wf binds a quantifier's variable
in Δ, while a ∀◇-ghost's body must be well-formed at the EMPTY Δ. So that
derivation was never in the judgment's domain.

**(A) was tried and REJECTED.** Adding the output's wf as a premise of
`*__tophole_fill` works through weakening / strengthening / Δ-monotonicity /
⊴-stability / subst / same_tvar (all five decl+algo files were fixed cleanly),
but it **does not survive `ad_refine_*_f_strip`**: that lemma removes a context
rigid `α` (with `α ∈ F`, `α ∈ Δ`), and a ∀◇-ghost body inside the output may
legitimately mention `α` justified *by that very context binding* — `α ∈ Δ`
cannot rescue it, because ∀◇-ghost bodies are checked at the EMPTY Δ. So the
premise is not transportable and the soundness proof's ∀-cases break.

**(B) is what we do.** Rules verbatim; wf carried in the statements. Mechanized in
`algo/prop_precise.v` (all Qed, axiom-free):

| lemma | content |
|---|---|
| `ad_refine_syn_syn_l` | a syn-headed refinement lands in a syn painting — **shape only**; no wf is derivable and none is needed |
| `a_wf_pskl_delta_shrink` | Δ-variables the skeleton does not mention may be dropped |
| `a_wf_pskl_empty_delta_free` | wf at the empty Δ ⇒ Δ-free (Δ is fresh for Θ) |
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

> The `-var` completeness lemmas' precision premise `Δ ⨟ Θ ⊢ κPi ⊑ᵖ[Ψi] ψa`
> carries a binder context Δ that the paper only ever populates with
> instantiation binders — all introduced AFTER Θ's definitions exist. The
> paper never states this; its rules and lemma statement leave Δ abstract.

**The condition.** `delta_def_fresh Δ Θ`: every `Y ∈ Δ` avoids
`ftvar_in_ptyp τ` for every `binds α (abind_flex_mono_def τ) Θ`
(`algo/prop_look_complete.v`). Carried on the statements (route **B**) of
`a_solve_eq_complete_var` and its helpers (`ad_refine_inh_hole_ppre`,
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
it inside the `rho_fresh` pack; and the initial Δ of the P6-Cs/Sv callers is
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

The algo layer has TWO skeleton judgments, both in algo/def_extra.v:

- **`a_wf_pskl` (`Θ ⨟ Δ ⊢ₚₛᵃ P`) — THE paper's skeleton wf** (ex-`ad_wf_pskl`,
  moved up from def_decl_algo.v).  Two contexts: ∀ binds its variable in Δ,
  and a `∀◇`-body must be guarded and well-formed at the EMPTY Δ.  This is the
  ∀◇-discipline that rescued the refine-non-transitivity counterexample (§1):
  `∀α.∀◇.(α→α)` is well-formed in NO context.  Whenever the paper writes
  skeleton wf, it means this judgment — the paper has no weak variant.

- **`a_scope_pskl` (algo/def_extra.v:113) — scoping only.**  Single context Θ,
  ∀ binds a plain `abind_tvar` into Θ, `pskl_tophole` merely recurses (no
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

- `a_scope_pskl`'s ONLY remaining rule site is `a_wf_aenv__var` (x:P context
  entries).  This is NOT load-bearing discipline — entry wf is only ever
  consumed for scoping facts (ftv ⊆ dom, freshness).  We do not fundamentally
  need the weak judgment: entries never sit under a ∀-binder, so for the
  shapes the algorithm actually stores the two judgments agree, and
  disciplined entry-wf would transport (`a_wf_pskl_isub`, `_msubst_inc`).
  It survives for (a) cost — strengthening `a_wf_aenv__var` reopens every
  a_wf_aenv construction/preservation site (notably the a_pat push sites,
  where "split/guess outputs are disciplined" would become a new lemma pack)
  across the Qed consistency corpus, for zero current benefit; and (b) impl
  parity with `is_wf_`.  QUEUED CLEANUP: strengthen `a_wf_aenv__var` to
  `Θ ⨟ ∅ ⊢ₚₛᵃ P`, prove the split/guess-discipline pack, delete
  `a_scope_pskl`.  Do it when a_pat metatheory is mechanized anyway.

**Rule of thumb** (unchanged): a premise consumed locally by its rule (like
ForallL's) may be disciplined at the rule; a condition threaded through the
walk's context surgery must be carried as an external `a_wf_pskl` statement
hypothesis instead — the `strip` lemmas are what kill the rule route (§1).

## `a_tags_sort` is CONTEXT-FREE (registered 2026-07-18; DESIGN-subtyping D3)

The paper's `Θ ⊢^N tags{Ψ}{ψ}` (full-decl-spec.tex:105-118) carries a context
and scope-wf of ψ.  `a_tags_sort` (algo/def_decorated.v:96) drops the context:
purely syntactic (`is_tskl` + `d_tags_skl`, ghost-freeness at TY); the scope
half is restored at each call site ON THE ERASURE (`(Ξ++Θ0) ⨟ ∅ ⊢ₚₛᵃ P1` in
the decorated ForallL; `Θ ⨟ ∅ ⊢ₚₛᵃ ⌊ψ⌋` in `ad_pat_sub`'s ForallL).  This is
the D3 decision of DESIGN-subtyping.md §1.2, now registered: statements
needing the paper's full judgment take `a_tags_sort NM Ψ ψ ∧ (scope premise
of the call site)` as the decomposition.

## Mode discipline on the DECORATION lemmas (registered 2026-07-20)

The L-A decoration lemmas (`a_subtag_decoration_var`, `a_consistag_decoration`,
KEY `a_subtag_decoration`, MAIN `a_sub_decorate` — algo/prop_decorate_sub.v,
prop_decorate_key.v) all carry the external hypothesis

    NM = SK  ->  mod_comp_sk (pskl_to_bskl_inh P0) M

(`Hmod`).  This is the paper's implicit "the inputs are mode-compatible"
(skmod[SK], algorithmic.tex:239-244) restored in the STATEMENTS, not the
rules: without it the lemmas are FALSE at the ◈-vs-∀X.◇ corner — an SK-mode
∀-target at TC would let a dotted ghost decorate against a universal the
mode discipline forecloses at every real call site (`inh` paints `all_inh`,
`is_sskl` rejects).  It threads through the walk (Flex-Assign transports it
by `pskl_to_bskl_inh_subst_mono` + `mod_comp_sk_subst_mono`), so per §1's
rule of thumb it must live in the statements.

## `pskl_no_hole P0` on P6-Cv completeness — **REMOVED 2026-07-27** (registered 2026-07-27; historical)

**RESOLVED — the premise no longer exists.**  `a_solve_eq_complete_var` /
`_gen` (algo/prop_look_complete_var.v) are now PREMISE-FAITHFUL to the
paper: the mech-only `pskl_no_hole P0` side condition was removed by
reworking the Θtv/Θr context split from the LIST equation `Θ = Θtv ++ Θr`
to a binds-level BAG (`aenv_split`: binds-iff + dom-eq + disjointness,
with `a_wf_aenv Θr` carried explicitly).  The premise had been an artifact
of the list representation: the consistency rule PREPENDS the ForallSyn
binder to Θ, so a list split could only place it in Θtv, forcing the
aenv→Δr refinement transport (`ad_refine_syn_aenv_to_delta`) — false for
□-sources whose fill mentions the binder.  With the bag split the binder
joins Θr (`Θr_ih := (X~tvar)++Θr`), the tophole_fill body IS the IH's
refinement premise verbatim, and holey `P0` flows through the recursion
to the per-row SolE-VacuousR columns — exactly the paper's per-node
"P0 = Hole" dispatch.  Consequently:

1. **P6-Cs (`a_lookeq_solve_complete`) needs NO `P0 = □ ∨ pskl_no_hole`
   disjunct** — its statement can mirror the paper's directly, with its
   own `P0 = □` special case via LE-Vacuous as the paper does.  Same for
   P6-Sv/Ss/L.
2. **The accumulated-skeleton invariant below is NO LONGER REQUIRED** for
   the completeness chain.  Its file `algo/prop_accum_no_hole.v` (Task A)
   was **DELETED 2026-07-27** — with the premise gone nothing consumes it,
   and it was pure supporting kit.  The description below is retained only
   as the historical record of what was proved.

The rest of this entry is kept as the record of the (now-deleted) invariant
proof and of the original analysis.

The invariant *"every accumulated flexible-variable skeleton is `□` or
hole-free"*:  **INVARIANT PROVED
   (2026-07-27), axiom-free, in the since-deleted `algo/prop_accum_no_hole.v`.**
   Deep-mixed
   `P0` (□ strictly below a constructor) is NOT reachable.  Four algo-level
   results (`Print Assumptions` = Closed under the global context):
   - **A1 `a_guess_hnh`** — `guess^TY` returns a paint (`ptyp_to_pskl`, no
     □-image ⇒ hole-free); `guess^SK` is the identity (preserves the
     disjunct).
   - **A2 `a_look_payload_hnh`** — `a_lookeq`/`a_looksub` emit □-or-hole-free
     constraint payloads whenever the counterpart is (mutual; a □-counterpart
     handled by LE/LS-Var emits the payload `eq(□)`, the left disjunct — it
     need NOT go through the Vacuous rules).
   - **A3 `a_solve_cstr_hnh`** (+ `a_solve_cstr_hole_start_hnh`, the `□`-start
     form `a_extract` uses) — solving a constraint list from a □-or-hole-free
     accumulator against □-or-hole-free payloads stays □-or-hole-free;
     generalises `a_solve_eq_no_hole_p0` to the mutual sub/eq/cstr block
     (`a_solve_{sub,eq}_hnh`, `a_solve_sub_no_hole_q`, the two `_from_subj`
     strict halves).
   - **A4 `a_sub_a_sub_flex_no_hole_p0`** — `a_sub`/`a_sub_flex` outputs are
     hole-free when the counterpart `P0` is.  KEY: this is **subject-free** —
     output holes come ONLY from the counterpart, so `a_sub__forall_l` merely
     threads `P0` (the ∀-body instantiation `open P P1` is irrelevant to the
     output even when `P1 = □` deep-mixes it), and `Infer`/`UnivGhostR`
     (`P0 = □`) are excluded by `pskl_no_hole P0`.  (An earlier worry that
     ForallL blocks a subject-carrying induction was an artifact of a
     needless subject premise; the counterpart-only formulation closes
     cleanly.)  Support: `a_consis_out_no_hole` / `a_consis_out_no_hole_q`.
   Predicate: `pskl_hnh P := P = pskl_hole \/ pskl_no_hole P`.

Historical note: in the premise-carrying closure, hole-freeness was
derivable from the other premises in some subcases (the Var-case binder
side still derives it locally, via
`ad_refine_inh_deltar_var_rhs_no_hole`) but not in general — a
guarded-but-holey ForallSyn body satisfies every other premise; only the
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
proof consumes is the GUARDED ghost body of `a_wf_pskl__tophole`, which
matches the declarative `d_wf_uskl__tophole`.

⚠️ **Without it the lemma is FALSE — machine-checked** in
`frost/algo/cex/cex_p6cs_subject_wf.v`:
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
ghost over a ghost — which both `a_wf_pskl__tophole` and
`d_wf_uskl__tophole` forbid.  So this is not a convenience premise: it
is what makes the paper's statement true.

**A wf premise on the SOURCE skeleton P is NOT needed.**  An earlier
closure carried `((α ~ abind_tvar) ++ Θ0) ⨟ ∅ ⊢ₚₛᵃ P` — the paper's
explicit "by well-formedness of P … Q is guarded" in C-UnivGhost2, with
the looked-up rigid α as a context entry because a Δ-reading is
unsatisfiable (`a_wf_pskl__tophole` resets Δ to ∅, so an α under a ghost
could never be justified).  Once the subject-wf premise is in, that one
is dead weight: it was only ever fed back to its own IHs, and every
guardedness fact the proof needs comes from the subject side (the
subject's ghost bodies, not P's, are what the ghost rows inspect).  It
was removed; the proof is unchanged otherwise.

---

## P7b `Sub-Check` — well-formedness of the COUNTERPART in the solution context

**`Θ ⨟ ∅ ⊢ₚₛᵃ ⌊Q⌋`**, i.e. the solution's counterpart is well formed where
the solution lives.  Registered 2026-07-30 with `a_sub_complete_check`
(`frost/algo/prop_sub_complete_thm.v`), which takes it as a hypothesis; the
P7 bundle will have to carry it on the motive.

**Why it is needed.** The case must move its precision from the solution's `κ`
to the package's `ζ`, and the composition step is `ad_refine_syn_trans`.
Refinement is NOT transitive outright (`cex/cex_refine_not_transitive.v`); it
is transitive under exactly this external well-formedness, which
`declarative.tex:1427` requires of every refinement judgment anyway.

**Why the two `P0 = □` rows do not need it.** At `P0 = □` the motive's own
P0-fill premise is a refinement OUT OF the ghost, and only two rows have a
ghost source — `__hole`, which carries the fill's well-formedness on the rule,
and `__flex_r`, whose target is a defined flexible and so is `a_binds_tvar`.
That is `ad_refine_syn_hole_l_target_wf` (same file, Qed).  At `Sub-Check`
the source is guarded and no such reading exists.

**Not a well-formedness condition, but registered with it** —
`a_sub_complete_check` also takes `guarded_pskl P0`.  The DECLARATIVE `Check`
row does not pin `P0`'s shape, but the ALGORITHM dispatches on it: a `∀` `P0`
is `ForallR`, not `Check`.  That is the paper's own case split.

## TY ghost-freeness of the SUBJECT (registered 2026-08-03; ⭐ ON THE MOTIVE since the same day)

The P7b motive `sub_complete_concl` (`frost/algo/prop_sub_complete_thm.v`)
carries

    NM = a_sub_mode_ty  ->  uskl_ghost_free R'

on the JOIN-side subject, as its last premise (`Hgf`); `a_sub_complete_thm`
(the paper-facing corollary, `prop_sub_complete_dispatch.v` §12) states the
same premise, so this is an EXTERNAL side condition of the final theorem — at
the paper's own reflexive instance `R' := κ⌈P⌉ᵘ` it is ghost-freeness of the
input `P`.  It is not decoration: it is the last premise of
`ad_pat_sub_precise_upre_gv`, i.e. P5's precision-substitution transport, and
P5 threads the very same predicate through
`frost/algo/prop_sub_complete.v` as a hypothesis of every lemma in the pack.
It is what makes the SWAPPED subject `open Rj ⌈κPa⌉ᵘ` ghost-free, given that a
TY guess is a TYPE (`pskl_to_uskl_paint_ghost_free`).

**⚠️ It is NOT derivable from the join, and the near-miss is worth recording.**
All four rules that put a ghost AT THE HEAD of `ad_pat_sub_gv`'s subject —
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
`guarded_pskl P0 \/ P0 = pskl_hole`, USED to be part of the same residual and
is now discharged inside the dispatch (`p0_wlog_trichotomy` +
`sub_complete_all_inh_counterpart`, §8b) — it is a case split, not a side condition.

## Skeleton term entries — the payload-wf DISCIPLINE is needed for the TARGET context too, on every completeness row (registered 2026-08-08)

`a_wf_aenv__var` stores only `a_scope_pskl` for an `x : P` entry, while the
subtyping/consistency theorems demand the disciplined `Θ ⨟ ∅ ⊢ₚₛᵃ P`
(see *Skeleton wf in the algo layer* above).  Both soundness theorems
therefore carry

```coq
forall y Ps, binds y (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps
```

for the QUESTION context.  ⭐ The two COMPLETENESS theorems
(`a_pat_complete`, `a_typing_complete`) carry it for the SOLUTION context
`Θ` as well, and every step lemma with an induction hypothesis carries it
INSIDE that hypothesis, for the solution context `Θ'` the hypothesis
quantifies over.

Why the target one is not optional: the binder rows push the term entry into
BOTH contexts (`x : A'` into the question context, `x : A` into the
solution's) before invoking the IH, so the IH is used at a *changed* target.
And the glue supplies each row's IH at a UNIVERSALLY QUANTIFIED `Θ'`, so a
row whose IH premise omits the condition is unusable: nothing in scope can
discharge it.  This is what forced the 2026-08-08 addition of the premise to
`a_typing_complete_anno` and `a_typing_complete_freeze` — the only two rows
that had been provable without it, because they happen to use their IH at an
unchanged target.

⚙ Transport across a run is by `a_wf_pskl_isub` composed with the run's own
`⊴` and its `_tm_ge` stability lemma (`a_split_tm_ge`, `a_consis_tm_ge`, …):
the entry itself is untouched, only the context around it grows.
