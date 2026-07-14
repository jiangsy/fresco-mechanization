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

> **See also [WF-SIDE-CONDITIONS.md](WF-SIDE-CONDITIONS.md).**  The paper
> systematically states well-formedness (and sometimes a further judgment) as an
> EXTERNAL requirement in prose — "we require well-formedness of both …", "we
> already required well-formedness separately", "as usual, all inputs are
> well-formed" — and its rules then omit the side conditions well-formedness
> would supply.  A Coq `Inductive` has no such notion, so each of these becomes a
> proof obligation, either as a rule premise or as a hypothesis on every lemma.
> Several judgments looked broken until that condition was restored.  **Check
> that file before concluding a lemma is unprovable.**

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

## MECH-BUG (FIXED 2026-07-14) — `Flex-Flex-Assign` must recurse into CONSISTENCY, not into `unifyvar`
- Where: full-algo-spec.tex:1707 (`Flex-Flex-Assign`), :1754 (`Assign-Assign`),
  :393 / algorithmic.tex:330 (skeleton splitting); mech `a_unify__flex_assign`
  (algo/def_extra.v:487).
- NOTATION — **the paper says this outright**, full-algo-spec.tex:1440-1442:

      "We write  Θ₀ ⊢ P ∼ P₀ ⊣ Θ₁  for  Θ₀ ⊢[P₀] P ∼ Q ⊣ Θ₁
       WHEN THE OUTPUT Q IS NOT USED."

  So the two-slot form `Θ₀ ⊢ A ∼ B ⊣ Θ₁` IS the CONSISTENCY judgment with the
  output dropped: **SUBJECT `A`, INPUT `B`, output existentially quantified**.
  (Consistency "takes two skeletons P and P₀ as input, checks their consistency,
  and calculates their JOIN Q as output" — :1436-1438.  That is why it is a
  4-place relation.)  The macros agree: `\unify{A}{B}` renders `A ∼ B`
  (macro.tex:1234) and `\aconsis`'s relation is `\consis` = `\mathrel{\sim}`
  (macro.tex:1271) — the same symbol.
  It is NOT a separate unification judgment, and it is NOT missing.
  Consistent with the Flex rule, whose premise `unifyvar{α̂}{β̂}` sits under the
  conclusion `aconsis[β̂]{Θ₀}{α̂}{α̂}{Θ₁}` — subject α̂, input β̂.
  And `Δ₁∣Δ₂` are omitted on that premise, which per :1472-1473 means BOTH EMPTY.
- Under that reading all three sites make sense, and only that reading does:
  - Flex-Flex-Assign, when γ̂ IS a subject: substituting turns the subject into
    the monotype τ, and consistency's **FlexR** then assigns `β̂ ≔ τ`.
  - Assign-Assign: subject α̂ against a general SKELETON `P` — only consistency
    takes a skeleton argument at all; **FlexL** assigns `α̂ ≔ P`.
  - Skeleton splitting: subject α̂ against the ARROW `β̂ → γ̂` — **FlexL** again.
    This one cannot be `unifyvar` under any reading.
- THE BUG: mech `a_unify__flex_assign` recurses into `a_unify` (the var-only
  `unifyvar`) where the paper recurses into CONSISTENCY.  So the mechanized
  algorithm gets STUCK the moment a definition is a non-variable monotype —
  machine-checked at the time (`a_unify_stuck_on_arrow_definition`, Qed,
  axiom-free): with `Θ₀ = (α̂ ≔ unit → unit), β̂` it could not unify α̂ with β̂,
  though a solution plainly exists.  That instance is now the SUCCESS
  regression test `frost/algo/test_unify_regression.v`
  (`a_unify_succeeds_on_arrow_definition`).  A definition CAN be an arrow — that is what `Assign-SolveM`
  produces via `guess^TY`.
- NB `a_unify_var_inv` ("every derivable `a_unify` has VARIABLE subjects",
  prop_consis_sound.v) reads like a theorem but is a SYMPTOM of this bug.
- FIX (IMPLEMENTED, algo/def_extra.v).  The premise became, with the output
  existential and both Δs empty (per the shorthand above):

      a_unify__flex_assign : forall Θ0 Θ1 γ τ A B Q,
        a_consis empty empty Θ0
          (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ B))   (* INPUT   = B[τ/γ] *)
          (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ A))   (* SUBJECT = A[τ/γ] *)
          Q Θ1 ->
        ((γ ~ abind_flex_mono_def τ) ++ Θ0) ⊲ A ≈ᵘ B
          ⊣ ((γ ~ abind_flex_mono_def τ) ++ Θ1)

  (plus the used-name set `F` — see the PROSE-COMPLETION entry below: the
  cycle forces `F` through `a_unify` and `a_consis` as well).  So `a_unify`
  and `a_consis` are MUTUALLY inductive — a 2-WAY mutual, not the paper's
  3-way: the mech reads `Assign-Assign` as CONTINUING the assignment (see the
  note at `a_assign` in algo/def_extra.v), so `a_assign` stays BELOW the
  cycle and its lemmas enter the mutual soundness proof as black boxes.
  `a_unify`'s subjects became ATOMS (the paper's hatted `unifyvar{α̂}{β̂}`).
  Also fixed: `a_split__flex` (full-algo-spec.tex:393), whose premise input
  is an ARROW and so could never have been `unifyvar` — forcing it through
  `a_unify` is what made `a_unify` take general monotypes in the first place.
- CONSEQUENCES, all landed (algo/prop_consis_sound.v, prop_mono_bridge.v):
  - `a_unify_consis_sound`: ONE mutual induction (Combined Scheme, 6+14
    cases) proving parts 1+2 of thm:sound-consistency together, exactly how
    the paper organises its own proof (consistency-proofs.tex:1562).  The
    invariant-preservation conjuncts are generalized over the protected Δ
    (Flex-Flex-Assign's consistency premise runs at `Δ₁ = Δ₂ = ∅`).
  - Part 2's conclusion is now a type EQUIVALENCE `Θ₁ ⊢ α̂ ≡ᵗ β̂`.  The
    Flex-Flex-Assign case recovers it from consistency's join + the input's
    refinement via the monotype BRIDGE (`consis_refine_mono_tyequiv`), and
    part 1's Flex case converts it back to declarative consistency via the
    CONVERSE bridge (`tyequiv_mono_consis`) — both in prop_mono_bridge.v.
  - `a_consistag_sound_aux` (decorated, Appendix B) stays a PLAIN induction
    above the bundle: `a_consistag` is not in the recursion cycle (its flex
    rules take `a_unify`/`a_assign` derivations as opaque premises).
  - DELETED as artifacts of the bug: `a_unify_var_inv` (vacuous — subjects
    are atoms), `a_unify_dom` (now FALSE: unification can GROW the context
    via consistency → Assign-SolveM; part-2 soundness only claims an
    information increase), `a_unify_sym` (consistency is subject/input
    asymmetric; symmetry now comes from `a_tyequiv__sym`).
- STATUS: fixed; `make coq` green, zero admits, all flagships axiom-free
  (README.v).  Completeness is unblocked.

## MECH-BUG (fixed) — metasubstitution was a SEQUENTIAL fold, but the paper says "finite map"
- Where: algorithmic.tex:123 — "A metasubstitution `Θ ⊑[θ] Θ'` is a finite **MAP**
  θ from flexible variables in Θ to well-formed monotypes in Θ'."  A finite map is
  a SIMULTANEOUS substitution.  Mech `msubst_ptyp` / `_pskl` / `_btyp` / `_bskl`
  (algo/def_meta.v) instead encoded a SEQUENTIAL fold:
  `msubst ((α,τ)::θ) A = msubst θ (A[τ/α])`.
- These are DIFFERENT functions: the fold lets a LATER entry rewrite inside an
  EARLIER entry's image.  Take the (perfectly legal) `θ = [α ↦ β̂, β̂ ↦ unit]` — the
  fold sends `α ↦ unit`, the map sends `α ↦ β̂`.
- Why it never bit: the two coincide on IDENTITY metasubstitutions (each `α ↦ α`
  substitution is a no-op), and *"our algorithms always give identity
  metasubstitutions"* (algorithmic.tex:140).  Every existing use goes through
  `msubst_ptyp_id` / `msubst_pskl_id`, so nothing depended on the difference.
- Why it matters NOW: completeness/optimality is stated up to `θ ≡ ζ ∘ θ₁`, so it
  needs GENERAL metasubstitutions and their COMPOSITION.  Composition is pointwise
  (`(ζ∘θ)(α) = ζ(θ(α))`), and its action law `msubst (ζ∘θ) A = msubst ζ (msubst θ A)`
  is simply FALSE for the fold — the fold's later-entry interference breaks it.
- Fix (IMPLEMENTED): all four `msubst_*` now recurse on the TYPE and look each free
  variable up in θ (`msubst_lookup`), i.e. they are finite maps, as the paper says.
  Only the two `_id` lemmas needed re-proving; `make coq` green, zero admits.

## GAP — `lemma:precision-preserves-refinement` is stated with NO PROOF, and is FALSE without the external wf condition
- Where: full-algo-spec.tex:716-721.  The lemma is asserted bare — `\begin{lemma}
  … \end{lemma}` followed straight by the next `\begin{definition}`.  There is no
  `\begin{proof}`, here or anywhere else in the appendices.
- It is the key lemma under completeness/optimality of consistency AND of type
  inference, so it carries a lot of weight for something never proved.
- Writing the proof is what exposed the entry below: **the lemma is false unless
  the refinement judgment's external well-formedness condition
  (declarative.tex:1427) is carried**.  Precision is DEFINED as
  `Θ ⊢ inh{P} ⊳ inh{Q}`, so the lemma is an instance of transitivity of
  refinement — and refinement is not transitive on the bare rules
  (`algo/cex_refine_not_transitive.v`).  An unwritten proof hid that.
- MECHANIZED (algo/prop_precise.v, Qed + axiom-free): `ad_refine_syn_trans`
  (general transitivity, given the result is well-formed) and
  `ad_precise_preserves_refine` (the paper's lemma, a direct corollary).
- Proof shape, for the authors: OUTER induction on the second derivation, INNER
  induction on the first to peel the left-hand administrative rules
  (`tophole_remove` / `flex_l`, which shrink the left skeleton while the right
  stands still).  Every case whose left side is a ghost needs the crux: *assuming
  the result is well-formed*, whatever a syn painting refines to is a syn painting
  of a skeleton well-formed at the EMPTY Δ — which is what re-applying the Ghost
  rule requires.
- RELATED, also unproved but TRUE (algorithmic.tex:537): "Since `inh{Q}` is
  inherited, the refinement relation cannot fill Q with more quantifiers, but can
  only fill with monotypes and remove universal ghosts."  This holds because
  `tophole_fill`'s right-hand side is `syn{∀…}` — a SYNTHESISED quantifier — so
  the rule cannot fire against an INHERITED painting.  It is the exact dual of the
  fact our proof turns on (a SYN painting on the LEFT can never fire the `all`
  rule, hence Δ never grows).  The paper could cite it to shorten its own proof;
  our `ad_refine_syn_trans` is strictly stronger (general transitivity) and so has
  to handle `tophole_fill` rather than rule it out.

## RESOLVED (was FALSE) — refinement does not preserve wf; wf is carried by the STATEMENTS
- Where: fig. of refinement, `declarative.tex:1505-1510` (the GhostForall
  rule); the consequence hits `lemma:precision-preserves-refinement`
  (full-algo-spec.tex:716) and hence the whole completeness/optimality
  development, which rests on it.
- Machine-checked artifact: `frost/algo/cex_refine_not_transitive.v` —
  `ad_refine_syn_not_transitive` is Qed and axiom-free.
- The GhostForall rule binds `α` in `Γ` but deliberately KEEPS `Δ`
  (the paper's own inline comment: "It's fine to keep Δ since we already
  required well-formedness separately").  But `Δ` is exactly what the Ghost
  rule tests (`Δ ∩ ftv(syn{Q}) = ∅`).  So a ghost nested UNDER a GhostForall
  may be filled with the very `α` that GhostForall binds — `α` is in `Γ`,
  not in `Δ`, so the side condition does not forbid it.  Witness:

      □ ⊳ syn(⊤.(□→□))              (Ghost; the fill is well-formed)
      ⊤.(□→□) ⊳ ∀α. ⊤.(α→α)         (GhostForall, then two Ghost fills at α)
      but NOT  □ ⊳ ∀α. ⊤.(α→α)

  The last step fails because the Ghost rule may only produce a WELL-FORMED
  skeleton, and `∀α. ⊤.(α→α)` is not one: skeleton well-formedness binds a
  quantifier's variable in `Δ`, while a `⊤`-ghost's body must be well-formed
  at the EMPTY `Δ`.  Hence transitivity — and precision-preserves-refinement
  — fail.
- The MECH rule is FAITHFUL here (`ad_refine_syn__tophole_fill` puts `α` in
  the context and leaves `Δ` alone), so this is a paper-level problem, not an
  encoding slip.  (Unrelated minor discrepancy: mech's `ad_refine_syn__all`
  adds the variable only to `Δ`, where the paper adds it to both `Δ` and `Γ`.)
- LIKELY FIX (needs the authors): make GhostForall extend `Δ` as well as `Γ`
  (`Δ,α ⨟ Γ,α`), exactly as the ∀-rule does.  The Ghost rule's side condition
  then forbids the capture and the second step above becomes underivable.
  This is the same "inherited variables must not fill ghosts" discipline that
  the soundness proof had to carry explicitly as the fill-hygiene set `F`
  (`ad_refine_syn_f`) — evidence the constraint genuinely belongs in the rule.
- RESOLUTION (user-directed, and what the paper's comment actually says): do NOT
  add the premise to the rule.  The declarative rules stay verbatim; instead the
  METATHEORY carries well-formedness — a "solution" is a derivation *whose types
  are well-formed*, so the capturing derivation above is simply not a solution
  (its output is well-formed in NO context, `Pres_not_wf`).  Threading wf into
  the rules was tried and rejected: it does not survive `ad_refine_*_f_strip`
  (a ⊤-ghost body may mention a context rigid α that the strip removes, and
  α ∈ Δ does not rescue it because ⊤-ghost bodies are checked at the EMPTY Δ).
- MECHANIZED (algo/prop_precise.v, all Qed + axiom-free): `ad_refine_syn_syn_l`
  (a syn-headed refinement lands in a syn painting — shape only, no wf),
  `ad_wf_pskl_delta_shrink`, `ad_wf_pskl_empty_delta_free`,
  `ad_refine_syn_syn_delta_free` (a syn-headed refinement never fires the `all`
  rule, so Δ never grows and Δ-freeness propagates), and the crux
  `ad_refine_syn_syn_l_wf`: ASSUMING the result is well-formed, it is a syn
  painting of a skeleton well-formed at the EMPTY Δ — exactly what re-applying
  the Ghost rule needs.
- NEXT: the main induction for lemma:precision-preserves-refinement, then the
  metasubstitution-composition algebra, then completeness.

## MECH-BUG (fixed) — decorated FlexR had an over-general subject
- Where: fig:decorated-alg-consistency (decorated-algosub.tex:237-238); mech
  `a_consistag__flex_r` (algo/def_decorated.v).  Found while closing the
  FlexR case of lemma:sound-decorated-consistency.
- The paper says the flexible-variable rules "are inherited unchanged" from
  fig:alg-consistency, whose FlexR subject is a PLAIN skeleton `P`
  (`a_consis__flex_r`, algo/def_extra.v:630).  Read into the decorated
  system, its subject is therefore the embedding `pskl_to_uskl P` — a
  decorated skeleton with no tags and no dotted ghosts, exactly as
  `a_consis_decorate` produces.  The MECH rule instead took an ARBITRARY
  unresolved skeleton `S` with the premises stated on the erasure
  (`a_non_flex Θ0 ⌊S⌋ˢ`, `Θ0 ⊲[·] α ≔ ⌊S⌋ˢ ⊣ Θ1`) — strictly more
  derivations than the paper's rule.
- The over-general rule makes the soundness lemma FALSE.  Counter-example:
  take `S = ●` (a DOTTED hole, `uskl_holeg`).  Then `⌊S⌋ˢ = □`, which is
  non-flex and assignable (`guess^TY(□)` is a fresh monovar), so the mech
  FlexR fires and yields `Θ0 ⊢ᵗ[…|α̂|·] ● ≈ α̂ ⊣ Θ1`.  Soundness would then
  demand `· ⨟ Θ1 ⊨ ● ≈ α̂`; but the only consistency rule with a dotted hole
  on the left (`GhostG`) forces the right-hand side to be `□` itself, while
  `α̂` is defined to a monotype — unprovable.  The paper's rule never
  produces this, because `●` is not in the image of `pskl_to_uskl`.
- Fix (IMPLEMENTED): `a_consistag__flex_r` now quantifies a plain skeleton
  `P`, keeps the ordinary premises on `P`, and states the subject as
  `pskl_to_uskl P` — mirroring `a_consistag__flex_l` (whose subject
  `uskl_var_f α` is likewise the embedding of the ordinary `pskl_var_f α`).
  `pskl_to_uskl` moved from prop_decorate.v into def_decorated.v so the rule
  can mention it.  The FlexR soundness case then mirrors the ordinary one
  verbatim, and `a_consis_decorate`'s FlexR case gets simpler.

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

## PROSE-COMPLETION — unifyvar's hatted subjects + guess^TY freshness carry the no-Δ-dependence invariant
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
- Mech completion (IMPLEMENTED; mirrors the Assign-SolveM sorted-τ
  resolution): `a_flex_tvar` premises on the payload side of
  `a_unify__flex_l/_flex_r`.  For guess^TY's `β̄` freshness (the paper's
  "fresh" is GLOBAL, but the solve node only sees its local tail —
  and the created names escape into the output context, so they cannot
  be cofinitely quantified the way continuation-passing formulations
  do, cf. worklist `a_wl_red__sub_arrow2`): `a_assign` now carries a
  USED-NAME set `F` accumulated by the entry-walking rules, and
  `Assign-SolveM` requires `uniq β̄` and `dom β̄` fresh from
  `F ∪ {α̂} ∪ dom(Ξ,Θ0)` — which at the solve node covers exactly the
  original context.  The paper-shaped judgments are the `F = ∅` notations.
- EXTENDED to the mutual cycle (2026-07-14): with `Flex-Flex-Assign`
  recursing into consistency, a solve node can fire deep inside a
  consistency premise, BELOW entries that `a_unify`'s skip rules walked
  past — and below the Δ-binders walked past by `Flex-Flex-Skip'`.  Those
  names can only reach the solve node through `F`, so `a_unify` and
  `a_consis` now carry the used-name set too (their skip/assign rules
  accumulate the walked head; all other rules pass `F` through).  Without
  it, `a_guess_mono__hole` may pick a walked head's name and re-attaching
  that head breaks context well-formedness — i.e. wf-preservation (and Δ-
  invariant preservation) would be FALSE for the mutual definitions.
  The invariant-preservation lemmas are now PROVED as conjuncts of the
  mutual soundness bundle `a_unify_consis_sound`
  (algo/prop_consis_sound.v): new names avoid `F`; no-flex-dep +
  flex-above-free + domain bookkeeping are preserved for every protected
  Δ with `Δ ⊆ F ∪ dom Θ₀`, using Assign-SkipRigid's occurs condition and
  the positional fact that Δ-binders sit above all flexible entries.

## Resolved definition-sync findings (step 1 of the restart)
See [REPORT-remech-decl-sync.md](REPORT-remech-decl-sync.md) — notably the
`is_tskl` untagged-∀ fix (A1), whose downstream effect invalidated the
pre-restart `pskl_to_tskl` decorated witnesses (prop_safety machinery).
