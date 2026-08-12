# Frost algorithmic system — faithful-definitions sync (design)

**Date:** 2026-06-19
**Branch:** `mech-refine-three-ctx` (algorithmic work; declarative side already synced)
**Author:** brainstorming session (Shengyi + Claude)

## Goal and boundary

Replace every **deferred stub** and **placeholder** in `frost/algo/` with a
faithful transcription of the *current* paper algorithmic rules
(`paper/sections/algorithmic.tex`, `proofs.tex`, `full-alg-spec.tex`).

**In scope:** definitions only. After this work every algorithmic *statement*
(rules + the soundness/completeness/optimality predicates they are stated
against) is paper-faithful. **Out of scope (next push):** discharging the
`Admitted` proofs. They stay admitted; this work makes them
*faithfully stated* so the later proof push is meaningful.

**Strategy decisions (from brainstorming):**
- **Defs-faithful first** — make statements faithful, defer proof-closing.
- **Mechanization as paper-bug finder** — where a rule/definition does not
  transcribe cleanly, treat it as a finding, log it, surface to the authors,
  and (where forced) pick the version that mechanizes cleanly and flag it for
  back-port.

**Verification gate per unit:** `make coq` green (full kernel check, not `vos`),
a dated `PROGRESS.md` note, and a `[mech]` commit. No new `Axiom`; new
`Admitted` only for downstream proofs (never for a *definition*).

## Baseline (2026-06-19)

Build is 🟢 green. `frost/algo/` audit:

**Already faithful (keep):** `a_guess_mono`, `a_refresh`, `a_looksub`,
`a_lookeq`, `a_solve_sub`, `a_solve_eq`, `a_solve_cstr`, `a_extract`,
`a_typing` (9 ctors), `a_pat` (9 ctors), the non-flex rules of `a_consis`,
`a_sub`, and `a_split`; metasubstitution `a_inc`/`a_isub`/`a_inc_equiv`,
projection `aenv_to_denv`, and the solution/optimality predicate *shapes* in
`def_question.v`.

**Deferred stubs (reflexive placeholders) — this work:**
- `a_unify` — `a_unify__refl` only; wrong arity.
- `a_assign` — `a_assign__refl` only.
- `a_broom` — `a_broom__refl` only; missing the `Θ | Ξ` context-suffix slot.
- `a_consis` — flex rules `Flex`/`FlexL`/`FlexR` missing.
- `a_sub` — `ForallL` and `FlexMono` missing.
- `a_split` — flex case missing.
- `a_ty_mode_compat` / `a_sk_mode_compat` — accept-all `__any`.

**Placeholder declarative notions (for faithful solution/optimality
statements) — this work:** `a_precise`, `a_ctx_precise`, `a_morepoly`,
`a_safe_skel`, `a_most_informative` (`prop_lemmas.v`), `a_tyequiv`
(`def_meta.v`), and the duplicate `a_skel_split` vs `a_split`.

## Encoding foundations (shared by Units 1–3)

The flex-variable judgments are paper "move" (`mov`) judgments in
type-inference-in-context style. Three load-bearing encoding facts:

1. **Right-to-left = head-of-list.** Paper writes the examined (rightmost,
   most-recent) entry as `Θ₀, e`. The Coq `aenv = list (atom * abind)` is
   head-most-recent, so `Θ₀, e` is `(a ~ b) ++ Θ₀` — matching the existing
   convention in `a_consis`/`a_sub`. Move rules recurse by peeling the head.

2. **The `Θ | Ξ` split is two `aenv`s.** This is type-inference-IN-CONTEXT,
   NOT a worklist algorithm: `Ξ` in `\mov{\Theta\mid\Xi}{…}{…}` is a local
   context *suffix* of flexible-variable bindings (a second `aenv`), not a
   list of pending judgments. Entries migrate `Θ → Ξ` (`Assign-Depend`) and
   `Ξ` is dumped at commit (`Assign-SolveM`: output `Θ₀, Ξ, β̄, α̂ := τ`).

3. **Substitution-sort decision (key).** Forward substitution `[τ/β̂]` puts a
   **monotype `τ : ptyp`** in for a flex var.
   - In `a_unify` both arguments are `ptyp` (flex vars are monomorphic), so the
     existing `subst_ptyp_in_ptyp` suffices.
   - In `a_assign` the assigned object is a **skeleton `P : pskl`**, so we need
     to substitute a `ptyp` into a `pskl` — and lngen does **not** generate
     `subst_ptyp_in_pskl` (pskl is a parallel AST, not containing ptyp).
   - **Decision:** add a small hand-written
     `psubst_flex : atom → ptyp → pskl → pskl` in `algo/def_rules.v` mapping
     `pskl_var_f β ↦ ptyp_to_pskl τ` and recursing structurally (cofinite under
     binders). Prove only the lemmas the *definitions* need now (lc preservation,
     `notin → identity`); defer substitution-commutes lemmas to the proof push.
   - Reconsider during build: if `subst_pskl_in_pskl (ptyp_to_pskl τ) β P`
     coincides with `psubst_flex` (it should, since `ptyp_to_pskl` is total),
     prefer reusing the lngen function and drop `psubst_flex`. **Settle this in
     Unit 1 step 0** before the rest of the move machinery is built on it.

## Unit 1 — Flex-variable move machinery + `a_consis` flex rules

**Files:** `algo/def_rules.v`.

### 1a. `a_unify` (paper `\boxed{\mov{\Theta}{\unifyvar{\hat\alpha}{\hat\beta}}{\Theta'}}`, alg.tex:1681–1733)

Redesign signature to `aenv → ptyp → ptyp → aenv → Prop`
(`Θ ⊲ α̂ ≈ β̂ ⊣ Θ'`), args `ptyp` to absorb `Flex-Flex-Assign`'s
`α̂[τ/γ̂]`. Rules:
- `Flex-Flex-Id`: `α̂ ∈ dom Θ₀ ⊢ Θ₀ ⊲ α̂ ≈ α̂ ⊣ Θ₀`.
- `Flex-Flex-L`: `α̂ ≠ β̂ ⊢ (Θ₀, α̂) ⊲ α̂ ≈ β̂ ⊣ (Θ₀, α̂ := β̂)`.
- `Flex-Flex-R`: symmetric, defines `β̂ := α̂`.
- `Flex-Flex-Assign`: head `γ̂ := τ`; recurse on
  `unify(α̂[τ/γ̂], β̂[τ/γ̂])`, re-emit `γ̂ := τ`.
- `Flex-Flex-Skip` (two rules, one label): head is an unrelated `γ̂`
  (`α̂≠γ̂`, `β̂≠γ̂`), or head is `e ∈ {γ (rigid) | x:P}`; recurse, re-emit head.

### 1b. `a_assign` (paper `\boxed{\mov{\Theta\mid\Xi}{\assignvar{\hat\alpha}{P}}{\Theta'}}`, alg.tex:1736–1782)

Signature `aenv → aenv → ptyp → pskl → aenv → Prop`
(`Θ | Ξ ⊲ α̂ := P ⊣ Θ'`): `Θ`, `Ξ`, assignee `α̂ : ptyp`, assigned `P : pskl`.
(Current stub had `ptyp` for `P`; fix to `pskl`.) Rules:
- `Assign-SolveM`: head `α̂`, `α̂ ∉ ftv(P)`, `guessMono P = (β̄; τ)` (via
  `a_guess_mono`); output `Θ₀, Ξ, β̄, α̂ := τ`.
- `Assign-Assign`: head `β̂ := τ`; recurse `unify(P[τ/β̂], α̂[τ/β̂])` on
  `Θ₀, Ξ`; re-emit `β̂ := τ`. (Uses `psubst_flex` for `P[τ/β̂]`,
  `subst_ptyp_in_ptyp` for `α̂[τ/β̂]`.)
- `Assign-Depend`: head `β̂`, `α̂≠β̂`, `β̂ ∈ ftv(P)`; move `β̂` into `Ξ`
  (`Θ | β̂,Ξ`), recurse.
- `Assign-Skip`: head `β̂`, `α̂≠β̂`, `β̂ ∉ ftv(P)`; recurse on `Θ₀ | Ξ`,
  re-emit `β̂`.
- `Assign-SkipRigid`: head rigid `β`, `β ∉ ftv(P)`; recurse, re-emit.
- `Assign-SkipTmVar`: head `x:Q`; recurse, re-emit.
  **(Finding F2 — see log; paper writes `\tilde\alpha` here.)**

### 1c. wire flex rules into `a_consis` (alg.tex:1638–1656)

- `Flex`: `Θ₀ ⊲ α̂ ≈ β̂ ⊣ Θ₁` ⟹ `aconsis[β̂] Θ₀ α̂ α̂ Θ₁`
  (inherited `P₀ = β̂`, output join `α̂`).
- `FlexL`: `nonflex P₀`, `Θ₀ | · ⊲ α̂ := P₀ ⊣ Θ₁` ⟹ `aconsis[P₀] Θ₀ α̂ α̂ Θ₁`.
- `FlexR`: `nonflex P`, `Θ₀ | · ⊲ α̂ := P ⊣ Θ₁` ⟹ `aconsis[α̂] Θ₀ P α̂ Θ₁`.

`a_non_flex` already exists (`def_extra.v:98`); confirm it expresses
"not a bare flex var" (a flex var is `pskl_var_f` bound `abind_flex_mono`);
tighten if the current body is the accept-all `a_wf_ptyp` shim.

## Unit 2 — `a_broom` + `a_sub` `ForallL`/`FlexMono`

**Files:** `algo/def_rules.v`. **Depends on:** Unit 1 encoding.

### 2a. `a_broom` (paper second box of fig:alg-subtyping, alg.tex:1091–1139)

Add the `Θ | Ξ` slot. Signature
`a_sub_mode → mode → pskl → aenv → aenv → ptyp → pskl → aenv → Prop`
(`Θ | Ξ ⊢_{N;FN M;P₀} α̂ ◁ A ⊣ Θ'`). Rules `Flex-Solve` (solve
`α̂₀ := α̂→β̂` then recurse on `α̂→β̂`), `Flex-Assign`, `Flex-Depend`,
`Flex-Skip`, `FlexPoly-SkipRigid` — same context-suffix discipline as `a_assign`.

### 2b. `a_sub` two missing rules (alg.tex:1046–1073)

- `FlexMono`: `Θ₀ | · ⊢_{N;FN M;P₀} α̂ ◁ A ⊣ Θ₁` ⟹
  `Θ₀ ⊢_{N;FN M;P₀} α̂ ⊑ A ⊣ Θ₁` (hand off to `a_broom`).
- `ForallL`: `M ≠ TI`, `guarded P₀ ∨ P₀ = □`,
  `looksub[N;M] α P P₀ ⤳ Ξ;P₁` (use `a_extract`/`a_looksub`+`a_solve_cstr`,
  already real), `Θ₀,Ξ ⊢ P₁`, recurse on `Θ₀,Ξ ⊢ P[P₁/α] ⊑ Q ⊣ Θ₁`.
  Forall-`L` opening: cofinite over `α`. Substitution `P[P₁/α]` is
  `subst_pskl_in_pskl P₁ α P`.

## Unit 3 — `a_split` flex case (alg.tex:396–401)

**Files:** `algo/def_rules.v`. **Depends on:** Unit 1 (`a_unify`).

Add `a_split__flex`: introduce fresh `β̂, γ̂`, require
`(Θ₀, β̂, γ̂) ⊲ α̂ ≈ β̂→γ̂ ⊣ Θ₁`, conclude
`split[α̂][β̂→γ̂] : Θ₀ ⤳ Θ₁`. Cofinite freshness for `β̂, γ̂`.

## Unit 4 — Skeleton/mode compatibility `\skmod` (alg.tex:278–300, 578–591)

**Files:** `algo/def_rules.v`. Independent.

Replace `a_ty_mode_compat__any` / `a_sk_mode_compat__any`:
- `skmod[TY]`: `□ / TI`; `A / TC` (any guarded type); `(P→Q)/(FN M) ⇐ Q/M`.
- `skmod[SK]`: `□ / TI`; `□ / TC`; `(P→Q)/(FN M) ⇐ Q/M`.

**Sort note:** `skmod[TY]` ranges over skeletons in its `□`/`(P→Q)` cases but a
type `A` in the `TC` case — current Coq has it over `ptyp`. Confirm whether the
TY judgment should be over `pskl` (with `□` and arrows) and the `TC` case a
guarded skeleton; align the sort with the call sites in `a_typing`/`a_pat`
questions (`def_question.v`). **(Finding F4.)**

## Unit 5 — Real declarative notions for solution/optimality

**Files:** `algo/prop_lemmas.v`, `algo/def_meta.v`, `algo/def_question.v`.
Independent of Units 1–3. Split by whether the paper has a real definition:

**Has a real paper definition → mechanize faithfully:**
- `a_precise` (alg.tex:854–922): syntactic precision with 11 rules incl. the 3
  context rules for flex vars (`Θ ∋ α̂`, `Θ ∋ α̂:=τ ∧ precise τ Q`, sym). Over
  the declarative coloured `bskl` per the existing comment; opening cofinite.
- `a_safe_skel` (declarative.tex:1927–1931): "P safe for M under Γ iff
  ∀A. Γ⊢[TC] M ⦂ inh{A} ⟹ inh{P} fillsyn bid{A}". This is the **D7** shape
  already in `decl/prop_skeleton.v` (`d_pat_safety`); state `a_safe_skel` by
  reference to the declarative refinement/typing judgments, not a fresh stub.
- `guess`/`guessMono`: already mechanized (`a_guess_mono`); just confirm
  `guess[SK] P = (·;P)` is inlined at call sites.

**No clean paper definition → propose faithful working def + flag (Findings):**
- `a_ctx_precise` — paper has **no standalone context-precision relation**; it
  uses metasubstitution/`\inc` instead (alg.tex:133–209). **(Finding F5.)**
  *Proposed:* define `a_ctx_precise Θ' Θ` as: same non-term-var entries, and
  every term var `x:P'` in `Θ'` with `x:P` in `Θ` satisfies
  `Θ' ⊢ precise P' P`. Cross-check against `lemma:context-precision-skeleton`
  (proofs.tex:119–156, itself marked "TODO: check") and surface for back-port.
- `a_morepoly` — paper definition exists but is inside an **`\iffalse` block**
  (alg.tex:694–819), i.e. currently disabled. **(Finding F6.)** *Proposed:*
  transcribe the disabled rules (10 cases incl. flex-context rules), mark the
  Coq def with a comment that the paper section is disabled, and ask whether
  "more information does not harm" (A10) is staying in.
- `a_most_informative` — **not formally defined** in the paper (only used in
  lemma prose). **(Finding F7.)** *Proposed:* define as "safe and `morepoly`-
  maximal among safe skeletons", contingent on `a_morepoly`; flag.
- `a_tyequiv` (`def_meta.v`) — **not formally defined**; paper treats it as
  α-equivalence + solved-flex equality. **(Finding F8.)** *Proposed:* define
  `Θ ⊢ A ≡ᵗ B` as `msubst`-by-solved-flex-then-syntactic-equality (the algos
  produce identity metasubstitutions, so this is adequate and matches the
  current placeholder's intent), with a comment recording it is our reading of
  an under-specified paper notion.
- `a_skel_split` vs `a_split` — duplicate. **Decision:** delete the
  `a_skel_split` placeholder in `prop_lemmas.v`; restate `a_split_refine`
  (`prop_lemmas.v:142`) against the real `a_split` (now with the Unit-3 flex
  case). One splitting relation only.

## Paper-issues log (mech-as-bug-finder deliverable)

Maintained here and surfaced to the authors. Seeded:
- **F1** `Flex-Flex-Skip` has two inference rules sharing one label
  (alg.tex:1715, 1725) — fine, but note for the camera-ready.
- **F2** `Assign-SkipTmVar` (alg.tex:1779) writes the assignee `\tilde\alpha`
  where every sibling uses `\hat\alpha` — likely a typo.
- **F3** Commented-out `FlexMono-Def` (alg.tex:1102–1108) marked "subsumed by
  below" — confirm `Flex-Assign` truly subsumes it before deleting from paper.
- **F4** `skmod[TY]` mixes skeleton (`□`, `P→Q`) and type (`A`) arguments —
  sort needs pinning (Unit 4).
- **F5** Context precision used in proofs but never formally defined (Unit 5).
- **F6** `morepoly` definition is disabled (`\iffalse`) yet "more information
  does not harm" depends on it (Unit 5).
- **F7** "Most-informative skeleton" used in lemma statements, never defined
  (Unit 5).
- **F8** Type equivalence `\tyequiv` used in premises, never defined (Unit 5).
- **F9** alg.tex:407 `\wenhao` TODO: "modified the four Abs rule side
  conditions… should update proofs" — the `a_typing`/`a_pat` Abs rules already
  in Coq may need re-checking against the final side conditions.

## Ordering, checkpoints, out of scope

**Order:** Unit 1 (incl. step-0 substitution decision) → Unit 2 → Unit 3;
Unit 4 and Unit 5 sliced in independently. Each unit is its own green
checkpoint + `[mech]` commit + PROGRESS.md note. Hold one large commit per unit
(not per sub-rule) per the project's commit-hygiene guidance.

**Verification:** `make coq` green after each unit. `grep -c "Admitted" algo/*.v`
must not rise from *definition* work (only the pre-existing proof admits remain).
No new `Axiom`.

**Out of scope (next push, separate spec):** discharging any `Admitted` proof —
the 8 soundness/completeness theorems, the ~16 auxiliary lemmas, and the
declarative-side research-grade admits. Out of scope here: changing the
already-faithful constraint/inference judgments; touching the declarative
system except to *reference* `d_pat_safety`/refinement from `a_safe_skel`.
