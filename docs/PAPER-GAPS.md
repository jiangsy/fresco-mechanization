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

## WATCH — Assign-SolveM can store a polymorphic definition
- Where: fig:alg-consistency `Assign-SolveM` (full-algo-spec.tex:1744);
  `Θ ⊢ ctx` (full-algo-spec.tex:224) and the entry grammar `α̂ := τ`
  (algorithmic.tex:61-65).
- `guess^TY` (the LaTeX source's `\guessMono`, macro.tex:1505) keeps
  universal quantifiers (`guess^TY(∀α.P) = (β̄; ∀α.P')`),
  so `Assign-SolveM` may define `α̂ := ∀…` even though the entry grammar and
  `Θ ⊢ ctx` say definitions are monotypes `τ`.  Reachable e.g. from
  consistency `FlexL/FlexR` with a `∀`-shaped non-flex side.  Not yet
  confirmed to break any lemma (the mech's `abind_flex_mono_def` stores any
  `ptyp`, and `a_assign` soundness does not conclude `Θ ⊢ ctx`); if a proof
  ever needs `Θ ⊢ ctx` preservation across `assignvar`, this becomes a GAP.

## Resolved definition-sync findings (step 1 of the restart)
See [REPORT-remech-decl-sync.md](REPORT-remech-decl-sync.md) — notably the
`is_tskl` untagged-∀ fix (A1), whose downstream effect invalidated the
pre-restart `pskl_to_tskl` decorated witnesses (prop_safety machinery).
