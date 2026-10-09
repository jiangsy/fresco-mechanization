> ## ⛔ STALE — HISTORY ONLY (marked 2026-08-09)
>
> The `d_pat` safety / totality development this note plans **was never
> built in the re-mechanization**: there is no `d_pat_safety`, no
> `safe_fn_skel` and no `d_pat_total` in `fresco/`.  What survives are the
> supporting lemmas in `decl/prop_skeleton.v` (consistency reflexivity, the
> tvar-strengthening cascade), which still cite `d_pat_total` in their
> comments as the motivation they were built for.
>
> Section D reached its four theorems by a different route entirely —
> soundness and completeness of skeleton inference against `ad_pat`, not a
> totality/safety witness.  See `docs/HANDOFF-section-d.md`.
>
> Kept because §2's enumeration of the dead-ends is still the record of why
> the direct route was abandoned.  Do not treat it as an open task.

# Design note: closing the `forall` (and `abs`/`abs_anno`) cases of `d_pat` safety

Status: open. Records the obstruction and the candidate designs for the safety
witness, so we don't rediscover the dead-ends. Owner decision needed on which
design to build.

## 0. Where this lives

- `fresco/decl/prop_safety.v`
  - `gpat m Γ e B` — the per-mode safety property (`Definition`, ~L1840):
    `tc` case = `exists Q, Γ ⊢tc e ⦂ Q /\ FILL(Q,Γ)` where
    `FILL(Q,Γ) := forall Γext Γt A0, ctx_weaken Γ Γext -> ctx_refines Γext Γt ->
       d_wf_denv Γt -> Γt ⊢tc e ⦂ inh A0 -> Γext ⊢ᵣ inh(bskl_to_pskl Q) ⊳ colour(inh(bskl_to_pskl Q)) A0`.
    Note: the `tc` fill **does not mention the type `B`** — it quantifies its own `A0`.
  - `d_pat_total_gen` (~L2005): `Γ ⊢[m] e ⦂ B -> d_wf_denv Γ -> forall Γ',
    ctx_refines Γ' Γ -> gpat m Γ' e B`. Proof by induction on the typing.
    Closed: unit/var/anno/sub/freeze. **Open admits: forall, abs, abs_anno, app.**
  - `d_pat_safety` (the public theorem) — existential; derived from `d_pat_total_gen`.
- Algorithmic references (Phase 3, currently `Admitted`):
  `algo/def_question.v` (`a_pat_solution`, `a_pat_optimal`, `a_fillsyn`),
  `algo/def_rules.v:655` (`a_pat` inference rules), `algo/prop_soundness.v`
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
   erasure** (`univ_ghost_remove`/`keep`/`fill` are distinct rules that change the
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
all-ghosts witness does not type-check. One canonical construction closes
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
 freeze  : d_look ti □ e ⇒ Q                      (⊢tc freeze e ⦂ Q)
 abs(m≠tc): split P0 = P→Q0; ∀x, d_look M⁻ Q0 (e^x) ⇒ Q ;  ⦂ arrow P Q
 abs_check: ∀x:□, d_look tc □ (e^x) ⇒ Q ;  ⦂ univ_ghost(□→Q)
 abs_anno / abs_anno_check / app : analogous to a_pat (def_extra.v:655)
```

Bridges: `d_look_sound : d_look m Γ P0 e Q → Γ ⊢ₛ[m] e ⦂ Q`; `d_look_fills :
d_look … → FILL(Q,Γ)` (uses the proven engines `d_refine_syn_ghost_fills`,
`d_refine_syn_univ_ghost_ghost_fills`, `colour_erasure`). `d_pat_total_gen` then
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

Strengthen the intermediate to `∃Q, Γ ⊢tc e ⦂ Q ∧ ∀Q', Γ⊢tc e⦂Q' → Q ≼ Q'`
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
  other `d_pat_sub` rule needs `m ≠ ti` or a `ghost`/`univ_ghost`/`forall` LHS), so
  TI inference is essentially deterministic (consistency + `is_sskl`). TC/FN:
  ghosts come from `univ_ghost_r`, which adds **exactly one** `univ_ghost` (premise
  is `R ≈ Q`, not recursive on the output). So `univ_ghost_remove/keep`
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
  - `d_refine_syn_ghost_fills` / `d_refine_syn_univ_ghost_ghost_fills`
    (prop_skeleton.v): `□` / `⫯.□` fill *any* type (with tvar scoping).
  - **`abs_check_fill` (prop_safety.v, `Qed`)** discharges the λ fill for the
    canonical λ witness `bskl_univ_ghost (bskl_arrow bskl_ghost Qb)` — and its OWN
    induction's **forall sub-case peels a `∀`-checking-type** via
    `d_refine_syn__univ_ghost_fill` + `colour_open` + `d_refine_syn_move`,
    introducing the fresh `X` *inside* the fill (cofinitely) with plain context
    constructors (`ctx_weaken_app_front`/`ctxr_cons`/`d_wf_denv__tvar`) — **no
    renaming, no witness-side freshness clash.**
  ⇒ The hard part of the forall fill (∀-prefixed checking types) is ALREADY
  solved. The forall case should connect the value's witness to this machinery
  (the same machinery the `abs` admit needs), rather than via principality.

## 2.6 Finding (2026-06-29, CORRECTED): the tc safe witness is `is_sskl` ⇒ bundle it

First (wrong) reading: "tc can't emit a concrete syn skeleton, so the
principal-body-skeleton is FALSE." The *premise* is right but the *conclusion*
was wrong — I conflated "concrete **guarded** syn" with "syn-painted `is_sskl`".

- True: `d_pat_sub` at `m=tc` from a *guarded* LHS forces `bskl_univ_ghost _`
  (`univ_ghost_r`); a *ghost* LHS gives `inh P` (`ghost`). So no **concrete
  guarded** syn tc output (only `freeze`).
- BUT `d_pat__abs_check`'s body premise is `⦂ pskl_to_bskl_syn P` where `P` may
  be a **ghost**. The tc safe witness is `ghost_of P`, whose outputs are
  `bskl_univ_ghost(...)` / `bskl_ghost` (prop_skeleton.v:332) — these **are
  `is_sskl`** (`is_sskl` has `__ghost`,`__univ_ghost`). And
  `is_sskl_syn_roundtrip : is_sskl Q → pskl_to_bskl_syn (bskl_to_pskl Q) = Q`.
  So the ghost body witness **already satisfies** the `⦂ syn P` premise with
  `P := bskl_to_pskl Q`. The principal-body-skeleton is **NOT false**.

**RESOLUTION (tractable):** strengthen `gpat`'s **tc** case to bundle
`is_sskl Q` (mirroring the ti case — and the actual tc witnesses, `ghost_of` and
freeze's, are already `is_sskl`). Re-prove the closed tc cases to carry it
(easy). Then:
- `abs`/`abs_anno`: IH gives `is_sskl Q_body` ⇒ `is_sskl_syn_roundtrip` ⇒
  `Q_body = pskl_to_bskl_syn P` ⇒ `d_pat__abs_check` gives
  `λ ⦂ bskl_univ_ghost(bskl_arrow bskl_ghost Q_body)` (itself `is_sskl`), and
  `abs_check_fill` (Qed) gives the fill from the IH's body fill.
- `forall`: the value's witness is `is_sskl` and X-independent (built from `e`);
  the ∀-checking-types are peeled inside `abs_check_fill`'s machinery.

So plan C's `≼`/principality is **not needed**; the fix is the `is_sskl` bundle
+ roundtrip + the existing `abs_check_fill`. This supersedes §2.5/§2 designs.

## 2.7 Finding (2026-06-29): is_sskl closes the INFERENCE; the FILL wall is gpat's ∀Γext

DONE (committed 42cdb2d): the **abs tc INFERENCE** is closed via the is_sskl route
— body witness `Qb` is `is_sskl` ⇒ `is_sskl_syn_roundtrip` ⇒ `Qb = pskl_to_bskl_syn
(bskl_to_pskl Qb)` ⇒ `d_pat__abs_check`; the per-`x` body inference comes from the
`x0` one by `d_pat_rename_var` + `subst_exp_in_exp_intro`. This confirms the
"principal-body-skeleton" was a red herring (the ghost witness IS syn-paintable).
Also: `is_sskl` is now bundled into `gpat`'s tc case (committed 1aafca3), threaded
through `d_pat_base_safe_tc_gen`/freeze/`d_pat_safety`.

NOT closed — the **FILL** (abs `abs_check_fill` body-hyp, and forall): the obstruction
is **`gpat`'s fill quantifying over arbitrary `Γext`/`Γt`**. The body-hyp must hold for
universally-quantified `Γt''`; discharging it from the single-instantiation witness's
fill `Hfillb` (tied to a fresh `x0`) needs `d_wf_denv ((x0~ghost)++Γt'')`, i.e.
**`x0 ∉ dom Γt''`** — unprovable for arbitrary `Γt''` (no constraint forces `x0` out;
`Γt''` may bind `x0` via the weakening). The asymmetry with the inference: the
inference renames over a FIXED context (`(x0~ghost)++Γ'`, `x0∉dom Γ'` holds), whereas the
fill renames over the fill's ARBITRARY contexts. Term-var context renames just relocate
the obligation onto that freshness; they don't break it. Erasure-determinism (use the IH
at the body-hyp's own `x`) also fails — `d_pat_sub__forall_l` picks `psi`
non-deterministically, so a forall-skeleton'd body can erase two ways.

⇒ Root cause for BOTH abs and forall fills = `gpat`'s `forall Γext, ctx_weaken Γ' Γext
-> ...`. Resolving it is design-E territory: is the `∀Γext` generality actually needed
beyond the contexts it is consumed at (`d_pat_safety` uses `Γext=Γ`; `abs_check_fill`
applies the body fill at `(x~ghost)++Γext0`)? A freshness side-condition on `Γext`, or a
witness that is canonical-by-construction (not instantiation-tied), would break the wall.

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
- Engines available: `d_refine_syn_ghost_fills`, `d_refine_syn_univ_ghost_ghost_fills`,
  `colour` + `colour_erasure`, `d_refine_syn_strengthen`, `d_pat_preserves_skel_wf`,
  `gpat_syn_fill`, `d_pat_base_safe_gen`/`_tc_gen`/`_fn_gen`.
