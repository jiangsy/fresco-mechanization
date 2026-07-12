# Paper gaps and paper-flagged notes (re-mech)

Canonical registry for everything found while mechanizing that the paper's
authors should see.  Ground rule (CLAUDE.md): paper definitions and lemma
statements are never changed; a broken proof STEP gets a repair here + a
`[paper-gap]` comment at the lemma; a genuinely FALSE statement (with a
counter-example) stops the work and is flagged to the user.

Each entry: status ∈ {GAP (confirmed proof-step problem, repaired),
PROSE-COMPLETION (figure rule completed from the paper's own prose),
WATCH (tension spotted, not yet confirmed to matter), FALSE (statement
refuted — none so far)}.

## PROSE-COMPLETION — `⊑`'s flex-def rule lacks the θ-image side-condition
- Where: fig:information-increase (full-algo-spec.tex:30-35); mech
  `a_inc__flex_def` (algo/def_meta.v).
- The figure's rule for `Θ,α̂:=τ ⊑[θ,τ'/α̂] Θ'` constrains `τ'` only by
  `Θ' ⊢ τ' ≡ θτ`, but the prose (algorithmic.tex:123-126) says θ maps
  flexible variables to *well-formed monotypes in Θ'*.  Without the wf
  side-condition, identity increases may drop defined variables from the
  target, and stability of variable lookups fails.  Mechanized with the
  prose side-condition (`a_wf_ptyp Θ' τ'`, `mono_ptyp τ'`) on the rule.

## PROSE-COMPLETION — identity metasubstitutions preserve entries
- Where: algorithmic.tex:135 ("For an identity metasubstitution, all
  entries of flexible variables in Θ are preserved in Θ'"); mech `a_isub`
  (algo/def_meta.v).
- The figure alone does not pin the target's flexible entries even for ι.
  The identity shorthand `⊴` therefore carries the prose characterization
  as a second component: definitions, once made, are preserved verbatim.
  This is what makes the FlexL/FlexR lookup rules stable under `⊴`
  (algo/prop_stability.v) — without it, a definition could be swapped for
  an ≡-equivalent one and the lookup-shaped rules would not transport.

## RESOLVED (was WATCH) — Assign-SolveM and polymorphic definitions
- Where: fig:alg-consistency `Assign-SolveM` (full-algo-spec.tex:1744).
- Earlier concern: `guess^TY` keeps universal quantifiers, so the rule
  seemed able to define `α̂ := ∀…` against the entry grammar `α̂ := τ`.
- Resolution (user-pointed): the rule binds the result to the SORTED
  monotype metavariable `τ` — under the paper's metavariable convention the
  premise `guess^TY(P) = (β̄; τ)` only matches when the result IS a
  monotype (hence Solve-M).  On a polytype result no assignvar rule
  applies and the algorithm fails, which is correct: a monomorphic `α̂` has
  no polytype solution.  The MECH rule was the unfaithful one (missing the
  mono constraint); fixed by adding `mono_ptyp τ` to `a_assign__solve_m`.
  Consequently every stored definition is a monotype and `Θ ⊢ ctx` is
  preservable across the algorithm.

## PROSE-COMPLETION (in progress) — unifyvar's hatted subjects carry the no-Δ-dependence invariant
- Where: fig:alg-consistency `Flex-Flex-L`/`Flex-Flex-R`
  (full-algo-spec.tex:1683-…); mech `a_unify__flex_l/_flex_r`
  (algo/def_extra.v).  Found while assembling thm:sound-consistency
  part 1 (consistency-proofs.tex, "Soundness of Consistency").
- The augmented solution in the part-1 proof requires that "no flexible
  variables in Θ depend on variables in Δ1 and Δ2", and the proof needs
  this invariant PRESERVED by every unifyvar/assignvar step.  For
  assignvar, `Assign-SkipRigid`'s occurs condition (`β ∉ ftv(P)`) does
  the work.  For unifyvar, preservation rests entirely on the paper's
  METAVARIABLE CONVENTION: the subjects `α̂, β̂` are hatted, i.e.
  flexible variables — `Flex-Flex-Skip'` has no occurs condition, so
  without the convention a rigid variable (skipped earlier, e.g. an
  opened Δ-binder) could flow to a leaf and be captured as a definition
  `β̂ := X` bound ABOVE `β̂` — ill-scoped, and breaking the invariant.
  The mech rules were the unfaithful ones (payload side unconstrained).
- Mech completion (mirrors the Assign-SolveM sorted-τ resolution): add
  flex-boundedness premises for the payload side to
  `a_unify__flex_l/_flex_r`.  Also required for invariant preservation:
  guess^TY's `β̄` freshness (the paper's "fresh"; the mech relation
  carries no freshness — completing `a_assign__solve_m` with the dom-
  freshness side condition), and the positional fact that Δ-binders sit
  above all flexible entries (maintained by the occurs checks).
See [REPORT-remech-decl-sync.md](REPORT-remech-decl-sync.md) — notably the
`is_tskl` untagged-∀ fix (A1), whose downstream effect invalidated the
pre-restart `pskl_to_tskl` decorated witnesses (prop_safety machinery).
