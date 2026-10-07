# Re-mechanization: decl ↔ paper sync report (2026-07-10)

Scope: `mechanization/fresco/{def_ott.v, def_extra.v, predicates.v, decl/def_rules.v}`
checked judgment-by-judgment against the **finalized** paper
(`sections/declarative.tex`, `appendices/full-decl-spec.tex`, merge `8dfafca`).
Policy: the paper is never changed; the mechanization is corrected to match.

## A. Genuine inconsistencies (FIXED on `re-mech`)

**A1. `is_tskl` admitted untagged quantifiers.**
Paper decorated skeletons (declarative.tex:1796) are
`ψ ::= 1 | α | ψ→ψ | ∀^ε α.ψ | HoleG | TopHoleG.ψ` — *every* quantifier is
tagged.  The mech's `is_tskl` (fresco/def_shapes.v) had an extra
`is_tskl__all_syn` case accepting the untagged `uskl_all_syn`.  Consequence:
`d_pat_sub`'s ForallL could instantiate with a ψ containing untagged
quantifiers whose tags are never recorded in Ψ′ — i.e. guessing a polytype not
determined by inherited information, contradicting the paper's headline
no-guessing invariant.  **Fix**: removed the `all_syn` case.

**A2. `d_tags_skl` defined beyond ψ's grammar.**
It had cases for `uskl_all_syn`, `uskl_hole`, `uskl_tophole`, which are not in
the ψ grammar (the paper defines `tags{Ψ}{ψ}` only on decorated skeletons).
Mostly latent given A1's gate, but the `all_syn` case (body's tags, no tag for
the quantifier itself) actively co-enabled A1.  **Fix**: restricted to exactly
`1, α, →, ∀^ε, HoleG, TopHoleG`.

**A3. `d_pat` rule structure out of sync with the finalized paper.**
The finalized skeleton-inference rules P-Unit / P-Var / P-Anno
(declarative.tex:1634–1653) embed the skeleton-subtyping premise
`Γ ⊢ₛ[M] · ⊑ Q` directly in each base rule, at *every* mode; there is no
standalone subsumption rule and no "base term" category (it is commented out
of the finalized syntax figure).  The mech instead had exact-skeleton TI rules
plus a `d_pat__sub` rule gated on `is_base_term`.  Extensionally equivalent
(via reflexivity of skeleton consistency), but not the paper's system.
**Fix**: restructured `d_pat__unit/var/anno` to the embedded form; deleted
`d_pat__sub` and `is_base_term`.

## B. Algorithmic system (restart, step 2) — gaps found vs finalized paper

The old `fresco/algo/def_rules.v` (and the newer `mech-algo-props` variant)
were both out of sync with the finalized `appendices/full-algo-spec.tex`:

**B1. `Δ₁ ∣ Δ₂` missing from algorithmic consistency.**  The finalized paper
threads two bound-variable sets through `aconsis` (Δ₁ = binders of the input
`P₀`, Δ₂ = binders of `P`) with side-conditions `Δ₂ ∩ ftv(P₀) = ∅` (Ghost)
and `Δ₁ ∩ ftv(P) = ∅` (GhostR), and extends them in ForallInh (both),
ForallSyn (Δ₂), UnivGhost1 (Δ₁).  Neither branch had these.  **Added.**

**B2. `refresh` does not exist in the finalized paper.**  LS-Var / LE-Var emit
the constraint on `P` directly ("WT: I don't need refresh").  `mech-algo-props`
had re-added an `a_refresh` pass.  **Restart keeps the direct rules.**

**B3. Vacuous rules take `□` on the right.**  LS-Vacuous / LE-Vacuous /
SS-Vacuous are against `Hole` in the finalized paper; the old encoding matched
`TopHole.P'`.  **Fixed.**

**B4. Solve-subtyping ghost rules.**  The finalized figure has
`GhostLF : solvesub(□, FN M, Q₁→Q₂) = ∀◇(P₁'→P₂')` (note the `∀◇` on the
output) and `GhostL : guarded B ⊢ solvesub(□, TC, B) = ∀◇B`.  The old encoding
lacked both; `mech-algo-props` had GhostLF without the `∀◇`.  **Fixed.**

**B5. AT-AbsCheck / AT-AbsAnnoCheck input is `∀ᾱ.A₀`.**  The old rules took
input `□` at TC with an unconstrained bound type — ill-moded (`skmod[TY]` at
TC requires a *type* input) and unsound vs the paper.  **Rewritten** as
`_step`/`_base` pairs: `_step` peels one rigid quantifier off input and
output; `_base` *splits* the input type `A₀` into `A→B` (mech-algo-props'
`_base` still used the `□` input) and, for AbsAnnoCheck, checks
`aconsis{A'}{A}` against the annotation per the paper.

**B6. AT-Freeze input is the checked type `A`.**  The old rule took an
arbitrary input `P₀` unrelated to the consistency premise.  **Fixed**:
input `A`, premises `⊢[TI][□] M ⦂ B` then `aconsis{B}{A}`.

**B7. LS-Check missing `A ≠ α`.**  Present in the finalized figure
(full-algo-spec.tex:1044); added.

**B8. `nonflex` encoded as "not any variable".**  UnivGhost2 / UnivGhostR
in `a_consis` rejected *rigid* variables too (`∀β, P ≠ var β`); the paper's
`nonflex{P}` only excludes flexible variables (a rigid α is guarded and
allowed).  **Fixed** using `a_non_flex` (also covers defined flex vars).

**B9. SS-ForallR / SE binder handling** unified to cofinite quantification
(the old code opened the RHS body with the ad-hoc filler `∀◇□`).

Also: `a_guess` (the paper's `guess[N]`) is now a first-class relation used by
the look judgment (`a_extract`), matching fig:poly-info-extraction; the old
`a_broom` was renamed `a_sub_flex` (paper: flexible-variable subtyping);
`Assign-UnivGhost-Id` (paper `α̂ := ∀◇α̂` corner case) was added; `abind_marker`
and other unused machinery dropped.

## C. Equivalent-encoding deviations (kept, by design)

- **Γ∣Δ split**: the paper adds ∀-bound vars to *both* Γ and Δ and clears via
  `Γ\Δ`; the mech keeps ∀-vars only in Δ (var rules read `Δ ∨ Γ`, `⫯`-rules
  clear Δ).  Equivalent since {Γ, Δ} partition the tvars.
- **Ambient wf side-conditions as premises**: `skmod` (`mod_comp_ty/sk`),
  skeleton well-formedness, and guardedness appear as explicit premises on the
  rules that need them (`d_pat_sub__ghost/ghostg/infer`, `d_pat_consis__hole`,
  `d_refine_syn__tophole_keep`, `d_pat__abs/abs_anno`, `d_refine_syn__var`),
  where the paper states them once as judgment-wide well-formedness conditions.
- **Tag contexts** are Coq `atoms` sets: plain `union` where the paper writes
  `Ψ,Ψ'`; `inter = ∅` sidecars where it writes `⊎` (in `tags{Ψ}{φ/ψ}`).
- **"Ψ′ fresh"** in ForallL is read as `Ψ′ ∩ Ψ = ∅` (weakest sound reading).
- **sd-AbsCheck's `∀ᾱ` prefix** is encoded as `_step`/`_base` recursion
  (declarative and algorithmic alike).
- Term-variable entries: the paper has a single entry `x:P`; the mech keeps
  `abind_var_typ`/`abind_var_skl` (resp. `dbind_typ`/`dbind_skl`) with types
  embedded — a sort-bookkeeping convenience.

## D. Proof-restart plan (step 3, bottom-up per the paper's appendices)

Order (leaf → root), strictly following the paper's own proofs:
1. `consistency-proofs.tex` §B.1–: soundness of decorated consistency,
   decorating algorithmic consistency, consistency decoration; then
   completeness of consistency constraint collection/solving; soundness /
   completeness+optimality of consistency (incl. `unifyvar` / `assignvar`).
2. `subtyping-proofs.tex`: look decoration, decorating constraint solving,
   constraint-solving concatenation, subtyping decoration (variables →
   general), vacuous decoration, stability of collection, look freshness,
   decorating instantiation, flexible-variable soundness → Soundness of
   Subtyping; then the completeness half (complete partial precision,
   stability under more precise substitution, …).
3. `proofs.tex`: suffix moving/erasure, splitting refines, precision extends
   skeleton subtyping, context precision → soundness/completeness+optimality
   of type inference and skeleton inference.
4. `full-decl-proofs.tex`: sd soundness/completeness, CST, subtyping
   transitivity, function subtyping, generalised general subsumption (the
   existing D1/D12 development is re-based onto the synced defs).

Legacy proof files that depended on the pre-sync definitions were moved to
`*.v.legacy` (git-tracked, out of the build) pending their bottom-up redo:
all old `fresco/algo/*.v` except the new `def_extra.v`, plus the decl prop
files that reference the removed `d_pat__sub`/`is_base_term`/`is_tskl__all_syn`.
