# Design note: closing the `forall` (and `abs`/`abs_anno`) cases of `d_pat` safety

Status: open. Records the obstruction and the candidate designs for the safety
witness, so we don't rediscover the dead-ends. Owner decision needed on which
design to build.

## 0. Where this lives

- `frost/decl/prop_safety.v`
  - `gpat m Γ e B` — the per-mode safety property (`Definition`, ~L1840):
    `tc` case = `exists Q, Γ ⊢tc e ⇨ Q /\ FILL(Q,Γ)` where
    `FILL(Q,Γ) := forall Γext Γt A0, ctx_weaken Γ Γext -> ctx_refines Γext Γt ->
       d_wf_denv Γt -> Γt ⊢tc e ⦂ inh A0 -> Γext ⊢ᵣ inh(bskl_to_pskl Q) ⊳ colour(inh(bskl_to_pskl Q)) A0`.
    Note: the `tc` fill **does not mention the type `B`** — it quantifies its own `A0`.
  - `d_pat_total_gen` (~L2005): `Γ ⊢[m] e ⦂ B -> d_wf_denv Γ -> forall Γ',
    ctx_refines Γ' Γ -> gpat m Γ' e B`. Proof by induction on the typing.
    Closed: unit/var/anno/sub/freeze. **Open admits: forall, abs, abs_anno, app.**
  - `d_pat_safety` (the public theorem) — existential; derived from `d_pat_total_gen`.
- Algorithmic references (Phase 3, currently `Admitted`):
  `algo/def_question.v` (`a_pat_solution`, `a_pat_optimal`, `a_fillsyn`),
  `algo/def_extra.v:655` (`a_pat` inference rules), `algo/prop_soundness.v`
  (`a_pat_sound`), `algo/prop_completeness.v` (`a_pat_complete`).

## 1. The obstruction (rigorously established)

The `forall` case: `d_typing__forall` types a **value** `e` at `∀(inh A)` from a
cofinite body premise `forall X∉L, (X::Γ) ⊢tc e ⦂ open(inh A) X`. The IH gives,
per fresh `X`, a gpat over `(X::Γ')` with an existential witness `Q_X`.

A **weak existential witness cannot close it**, by case analysis:

1. Pick one instantiation `X0`; the conclusion's `Q` is fixed at `∃`-intro.
   The fill then receives an **arbitrary** `Γext` (a `ctx_weaken` superset of `Γ'`)
   that **may bind `X0`**. Applying the body's fill needs `d_wf_denv (X0::Γt)`
   (fails if `X0 ∈ dom Γt`) and a strengthen needing `X0 ∉ ftv(colour … A0)`
   (fails if `X0 ∈ ftv A0`, which happens exactly when `X0 ∈ dom Γt`). Since
   `Γext` is universally quantified, **no choice of `X0` dodges all `Γext`**.
2. Re-instantiate the IH per-fill-instance at a fresh `X1` (fresh for `Γext`):
   gives an **independent** witness `Q1`. Inference is **non-deterministic even in
   erasure** (`tophole_remove`/`keep`/`fill` are distinct rules that change the
   skeleton structure, not just colours), so `bskl_to_pskl Q1 ≠ bskl_to_pskl Q`
   in general — the goal (about `Q`) and the produced refinement (about `Q1`)
   don't match. There is no `d_pat` determinism/uniqueness lemma (only
   `d_typing_ti_base_unique` for typing).
3. α-renaming the single witness `X0 → X'` to dodge `Γext`: every route renames
   *some* context to/from `X0`, and that context (`Γext`) already binds `X0` →
   collision. (This is why the rename-infra route — `d_pat/d_typing/d_wf_denv/
   ctx_*_rename_tvar` — does not close it; those lemmas were built then reverted.)

**Conclusion:** the witness must be **canonical** — pinned by the term `e` (and
the term-bindings of `Γ`), independent of the tvar bindings — not *chosen*. The
same canonical construction is what `abs`/`abs_anno` need (their admits are
"needs a principal/canonical body skeleton"); the λ-body's `abs_check` premise
requires a concrete **syn** skeleton `pskl_to_bskl_syn P`, so the trivial
all-holes witness does not type-check. One canonical construction closes
forall + abs + abs_anno together.

## 2. Candidate designs

### A. Declarative `d_look` relation (port of `a_pat`) — *currently favored*

A cofinite, term-syntax-directed *deterministic* inference, one rule per `exp`
form (no `∀` rule), with a "looking" input `P0` and canonical subsumption via
`d_pat_sub`; `aenv`/metasubst dropped vs `a_pat`.

```
d_look : mode → denv → pskl (looking input P0) → exp → bskl (output)
 unit    : canonical (pskl_unit ⊑ P0) ⇒ Q
 var-typ : binds x (typ A); canonical (ptyp_to_pskl A ⊑ P0) ⇒ Q
 var-skl : binds x (skl P);  canonical (P ⊑ P0) ⇒ Q
 anno    : canonical (ptyp_to_pskl A ⊑ P0) ⇒ Q
 freeze  : d_look ti □ e ⇒ Q                      (⊢tc freeze e ⇨ Q)
 abs(m≠tc): split P0 = P→Q0; ∀x, d_look M⁻ Q0 (e^x) ⇒ Q ;  ⇨ arrow P Q
 abs_check: ∀x:□, d_look tc □ (e^x) ⇒ Q ;  ⇨ tophole(□→Q)
 abs_anno / abs_anno_check / app : analogous to a_pat (def_extra.v:655)
```

Bridges: `d_look_sound : d_look m Γ P0 e Q → Γ ⊢[m] e ⇨ Q`; `d_look_fills :
d_look … → FILL(Q,Γ)` (uses the proven engines `d_refine_syn_hole_fills`,
`d_refine_syn_tophole_hole_fills`, `colour_erasure`). `d_pat_total_gen` then
produces the `d_look` witness; forall is X-independent because `d_look` recurses
on the term and ignores tvar bindings.

- **Pros:** mirrors the validated `a_pat`; LN-friendly (cofinite, no `Fixpoint`
  under binders); witness X-independence is structural; closes 3 admits.
- **Cons:** a new ~10-rule inductive + 2 bridge lemmas; "canonical subsumption"
  must be pinned (which `d_pat_sub` derivation is *the* canonical one) — this is
  the subtle part and the place to get the rules right.
- **Risk:** getting the canonical/looking shape exactly faithful to the paper.

### B. Canonical skeleton **function** `look_skel`

`look_skel : mode → denv → pskl → exp → bskl` as a Coq `Fixpoint` on `e`, plus
`look_skel_sound`/`look_skel_fills`. Witness equality across instantiations is
then **definitional** (forall becomes trivial: same function value).

- **Pros:** strongest X-independence (syntactic equality, no reasoning).
- **Cons:** recursing under λ-binders in LN is awkward — the body is `open e x`
  (not structural); bound-var lookups need an indexed skeleton context. Likely
  needs a size/measure or a `_rec` variant. Subsumption/looking still has to be
  encoded functionally (decidable canonical `⊑`).
- **Risk:** LN/Fixpoint friction; total-function encoding of subsumption.

### C. Principality lemma (`≼`-optimal witness)

Strengthen the intermediate to `∃Q, Γ ⊢tc e ⇨ Q ∧ ∀Q', Γ⊢tc e⇨Q' → Q ≼ Q'`
(canonical = `≼`-least), then `principal ⇒ fills-every-type` (optimality ⇒ fills,
à la `a_pat_optimal`). Forall: a principal witness over `(X0::Γ')` strengthens to
a principal one over `Γ'` (any `Γ'`-inference weakens to an `(X0::Γ')`-inference,
so principality transfers down); two principals over the same `Γ'` are
`≼`-equivalent ⇒ equal erasure ⇒ fills match.

- **Pros:** reuses existing `d_pat`; no new inference judgment; matches
  `a_pat_optimal` directly; "strong existential" framing.
- **Cons:** **needs a declarative skeleton-precision `≼`** — none exists in
  `decl/` (only the algo `Θ ⊢ … ≼ …`); must be defined + its theory
  (transitivity, `≼`-equiv ⇒ equal erasure, weakening-monotone). Proving each
  case yields a `≼`-least inference ≈ the algorithmic optimality proof,
  declaratively. Also needs `d_pat_strengthen_tvar` (reverted stub) for the
  down-transfer.
- **Risk:** `≼` theory is itself a subproject; principality proof per case is
  heavy.

### D. Reduce `d_pat_safety` to the algorithmic look (`a_pat`)

Restate safety through `a_pat_solution`/`a_pat_optimal` + `a_pat_sound`/
`a_pat_complete`.

- **Pros:** reuses the algorithm's optimality directly; conceptually clean.
- **Cons:** `a_pat_sound` **and** `a_pat_complete` are **currently `Admitted`**,
  so this **moves** the obstruction into the algo layer rather than closing it;
  pulls the whole Phase-3 metatheory (metasubst, `aenv`, increasing
  substitutions) into the dependency of a declarative theorem. Rejected unless
  the algo layer is closed first.

### E. Reformulate `gpat`'s fill (freshness side-condition on `Γext`)

Add a freshness premise to the `tc` fill so `Γext` cannot bind the witness's
tvar, defeating the obstruction at the cost of a weaker fill.

- **Pros:** smallest change; might let the existing existential route close.
- **Cons:** must re-prove the already-closed cases (unit/var/anno/sub/freeze)
  against the new `gpat`; must check **every consumer** (the recursive `abs`
  uses + `d_pat_safety`) only ever needs the restricted fill. The recursive
  `abs` case genuinely weakens the context, so the generality may be load-bearing
  — needs verification before committing. Changes the public-facing shape.
- **Risk:** the weakened fill may be insufficient downstream.

## 2.5 Findings while validating C (2026-06-28)

- **The `d_pat` inference set is BOUNDED** ⇒ a `≼`-least element exists ⇒
  `d_pat_principal` is *true*. TI mode: only `d_pat_sub__infer` fires (every
  other `d_pat_sub` rule needs `m ≠ ti` or a `hole`/`tophole`/`forall` LHS), so
  TI inference is essentially deterministic (consistency + `is_sskl`). TC/FN:
  ghosts come from `univ_ghost_r`, which adds **exactly one** `tophole` (premise
  is `R ≈ Q`, not recursive on the output). So `tophole_remove/keep`
  non-determinism is bounded.
- **But C's leastness (`∀Q', infer Q' → Q ≼ Q'`) ≈ declarative `a_pat_complete`**
  (heavy): per case it inverts the whole inference set of `e`. The forall case
  does **not** need leastness — it needs the witness to be an inference,
  X-stable, and fill — so "construct the witness + prove fill directly" (A/B
  mechanism) is strictly less work. Decision: go that way; keep `d_precise` only
  for stating stability/monotonicity, drop the `∀Q'` obligation.
- **The fill is NOT purely structural** — `Q` must refine `colour(bskl_to_pskl Q) A0`
  for each *checking* type `A0` (with `e ⦂ inh A0`), so it is entangled with the
  typing; a structural `is_safe_skel ⇒ FILL` lemma is FALSE. The fill stays a
  per-case obligation (the same one `abs`/`app` face).
- **The fill PRIMITIVES are in place:**
  - `gpat_syn_fill` (prop_safety.v): when `bskl_to_pskl Q = ptyp_to_pskl A0`
    (witness erasure matches the type), discharges the refinement.
  - `d_refine_syn_hole_fills` / `d_refine_syn_tophole_hole_fills`
    (prop_skeleton.v): `□` / `⫯.□` fill *any* type (with tvar scoping).
  - **`abs_check_fill` (prop_safety.v, `Qed`)** discharges the λ fill for the
    canonical λ witness `bskl_tophole (bskl_arrow bskl_hole Qb)` — and its OWN
    induction's **forall sub-case peels a `∀`-checking-type** via
    `d_refine_syn__tophole_fill` + `colour_open` + `d_refine_syn_move`,
    introducing the fresh `X` *inside* the fill (cofinitely) with plain context
    constructors (`ctx_weaken_app_front`/`ctxr_cons`/`d_wf_denv__tvar`) — **no
    renaming, no witness-side freshness clash.**
  ⇒ The hard part of the forall fill (∀-prefixed checking types) is ALREADY
  solved. The forall case should connect the value's witness to this machinery
  (the same machinery the `abs` admit needs), rather than via principality.

## 2.6 Finding: tc-syn is FORCED-GHOST (2026-06-29) — the real abs/forall blocker

Investigated "does a concrete syn tc-inference `⊢tc e ⇨ pskl_to_bskl_syn P`
exist?" (the principal-body-skeleton the `abs` admit asks for). **Answer: no,
except for `freeze`.**

- `d_pat_sub` at `m = tc`: a *guarded* LHS (a base term's syn skeleton) matches
  only `univ_ghost_r` → `bskl_tophole _`; a *hole* LHS matches `ghost` → `inh P`.
  No tc rule emits a concrete syn skeleton. Only `d_pat__freeze` does.
- Confirmed by the closed `d_pat_base_safe_tc_gen`: the tc safe witness is
  **`ghost_of P`** (built/inferred/filled by the closed `ghost_of_total` /
  `ghost_of_infer` / `ghost_of_fill_gen`); the kept-var witness is `bskl_hole`.

**Therefore the principal-body-skeleton lemma is FALSE**, and the
ghost(IH)→syn(`abs_check`) bridge is a dead end. The real machinery is
`ghost_of`, but `ghost_of_infer` routes through `d_pat__sub` which needs
`is_base_term`; a λ is not a base term, and `d_pat__abs_check` (the only tc λ
rule) demands a concrete-syn body it can never have.

**OPEN CALCULUS QUESTION (owner):** how does a λ obtain a *safe* (ghost) tc
skeleton, given `d_pat__abs_check`'s `⇨ pskl_to_bskl_syn P` premise is
unsatisfiable for general bodies? Candidates: (a) `d_pat__abs_check`'s body
premise should accept a ghost / `is_sskl` body (what is actually inferable);
(b) a ghost rule for λ. This is the genuine blocker for `abs`/`abs_anno`/
forall-of-λ — not a missing lemma but a rule-shape question.

## 3. Recommendation

Design **A** (`d_look`) is favored: closest to the validated `a_pat`,
LN-friendly, closes forall + abs + abs_anno, and keeps `d_pat_safety`
existential by producing the `d_look` witness and weakening at the end. **B** is
the fallback if a function turns out cleaner than feared; **C** is principled but
gated on building a declarative `≼`; **D** is rejected while the algo layer is
`Admitted`; **E** is a cheap thing to *probe* first (does any consumer need the
unrestricted fill?) before committing to A.

Open design question for A/B: pin the **canonical subsumption / looking** rule
(which `d_pat_sub` step is "the" one) — faithful to the paper's pi-look rules.

## 4. What is already in place (committed, green; 7 flagships axiom-free)

- Rename infrastructure (kept, proven): `d_pat_rename_tvar`,
  `d_typing_rename_tvar` (+ coercion commutes), `d_wf_denv_rename_tvar`, the
  skeleton-layer `_rename_tvar` family, and prop_renaming's type-level renames.
  (Built for the abandoned α-rename route; retained — may serve `app`.)
- Naming convention settled: `_rename_var` (term-var) vs `_rename_tvar` (tvar).
- The gpat-α-rename stubs (`d_pat_strengthen_tvar`, `ctx_weaken_rename_tvar`,
  `ctx_refines_rename_tvar`) were **reverted** (dead-end route).
- Closed safety cases: unit, var, anno, sub (ti/tc/fn), freeze.
- Engines available: `d_refine_syn_hole_fills`, `d_refine_syn_tophole_hole_fills`,
  `colour` + `colour_erasure`, `d_refine_syn_strengthen`, `d_pat_preserves_skel_wf`,
  `gpat_syn_fill`, `d_pat_base_safe_gen`/`_tc_gen`/`_fn_gen`.
