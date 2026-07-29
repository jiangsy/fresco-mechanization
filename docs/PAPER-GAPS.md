# Paper gaps and paper-flagged notes (re-mech)

> **Notation.** This file stays in the PAPER's notation.  In the Coq
> development the information-increase metasubstitution the paper writes
> `θ` is spelled **`κ`** (θ is unreadable next to the context Θ), and `ρ`
> is reserved for the paper's rigid-variable substitution.  See the
> metavariable convention in CLAUDE.md.

Canonical registry for everything found while mechanizing that the paper's
authors should see.  Ground rule (CLAUDE.md): paper definitions and lemma
statements are never changed; a broken proof STEP gets a repair here + a
`[paper-gap]` comment at the lemma; a genuinely FALSE statement (with a
counter-example) stops the work and is flagged to the user.

Each entry: status ∈ {GAP (confirmed proof-step problem, repaired),
PROSE-COMPLETION (figure rule completed from the paper's own prose),
WATCH (tension spotted, not yet confirmed to matter), FALSE (statement
refuted by a machine-checked counterexample — see the entries below, most
recently P6-Sv at the end of this file)}.

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

## MECH-BUG (FIXED 2026-07-14) — `Assign-Assign` must recurse into CONSISTENCY too (the OTHER back-edge)

Exactly the same bug as the `Flex-Flex-Assign` entry above, on the other
auxiliary judgment, and missed the first time round.  The paper's two-slot
`∼` is the OUTPUT-SUPPRESSED CONSISTENCY abbreviation
(full-algo-spec.tex:1440-1442), so `Assign-Assign`'s premise
`unify(α̂[τ/β̂])(P[τ/β̂])` over `Θ₀,Ξ` is CONSISTENCY, not a continued
assignment.  The paper expands it exactly so and appeals to "the IH of
consistency" (consistency-proofs.tex:1720-1724).  That is why its soundness
proof is a **3-way** mutual induction, "together with the two auxiliary
judgements of variable unification and assignment" (:1562) — the mech had
`a_assign` outside the cycle entirely.

The reference implementation confirms it: BOTH `U-Flex-Flex-Assign`
(type.ml:316-321) and `U-Assign-Assign` (type.ml:358-363) call `join_sk` —
the consistency/join function — not `join_var`/`assign`.

`a_assign` is now the first motive of the `a_assign`/`a_unify`/`a_consis`
mutual block, and soundness is the 28-case `a_assign_unify_consis_sound`.
Four further encoding bugs fell out of the fix:

* **`β̂ = α̂` IS REACHABLE — do NOT premise `α̂ ≠ β̂`, and substitute BOTH
  slots.**  It is tempting to argue that an assignment's subject must be an
  UNDEFINED flex var, so `α̂ ≠ β̂` by uniqueness, so the subject stays the bare
  variable `α̂`.  That is FALSE.  *Nothing* requires the subject to be
  undefined: neither `a_consis__flex_l` nor the implementation's `U-FlexL`
  (`| p0, MFlex alpha -> assign alpha p0 [] theta`, type.ml:182-185) guards on
  it.  So a DEFINED `α̂` can be the subject, the walk then reaches `α̂`'s OWN
  definition, and the rule must fire with `β̂ = α̂` — whereupon the subject
  `α̂[τ/α̂]` is the MONOTYPE `τ`, not a variable.  With `α̂ ≠ β̂` premised, NO
  rule fires and assignvar is STUCK, exactly as the old `unifyvar` reading was
  stuck on an arrow-valued definition.  The implementation computes precisely
  this (`subst_var (MFlex alpha) tau beta` with `beta = alpha` reduces to
  `tau`).  Machine-checked both ways:
  `a_assign_succeeds_on_own_definition`, algo/test_unify_regression.v.

* **PROSE-COMPLETION: `Assign-Assign` needs a HATTED-SUBJECT premise.**  Before
  the fix, "the subject of an assignment is flexible" was *derivable* — every
  rule either matched `α ~ abind_flex_mono` or inherited it from the `a_assign`
  IH.  With an opaque consistency premise that argument dies, and worse:
  `a_consis__rigid` accepts a var subject for a RIGID `α`, so the rule would
  admit a degenerate "assign a rigid type variable" derivation.  The paper
  excludes this only through the hatted-metavariable convention (`α̂`).  Added
  `a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ0) α` — the same
  prose-completion `Flex-Flex-Assign` already carried, for the same stated
  reason.  It **must** be on the CONCLUSION's context: on `Ξ ++ Θ0` it is FALSE
  in exactly the `β̂ = α̂` case above.

* **`Assign-Depend` REVERSED Ξ.**  The paper's premise suffix is `β̂,Ξ`
  (consistency-proofs.tex:1763) and the implementation does
  `assign alpha p (xi @ [hd]) theta` — both put `β̂` at the `Θ₀`-adjacent end.
  The mech consed at the head.  Inert on its own (every `Ξ` entry is an
  undefined flex var, so their relative order carries no information) but fatal
  for the fix above, whose premise context is literally `Ξ ++ Θ0`.  Now
  tail-appends.

* **`Flex-Flex-Id` was stricter than the paper.**  Paper premise is
  `α̂ ∈ dom(Θ₀)` (implementation: `is_in_dom_`, type.ml:302) — flexible,
  DEFINED or not.  The mech demanded `binds α abind_flex_mono`.  No derivation
  was lost (a defined `α̂` routes through `Flex-Flex-Assign`, whose premise
  degenerates to the consistency `τ ≈ τ`), but the rule was not the paper's.
  Now `a_flex_tvar Θ0 α`.

Gotcha worth recording: `nonflex(P)` is **head-level** — "P is not ITSELF a
flexible variable", NOT "P contains no flexible variables".  The
implementation encodes it as match-arm ORDER.  Read it the other way and
`FlexL` looks inapplicable to `γ̂ → unit`, and the whole "the premise is
consistency" reading looks broken.

## IMPLEMENTATION DISCREPANCY (report to WT) — `U-Flex-Flex-Assign` has its `join_sk` slots SWAPPED

Found while auditing the mech against `paper/artifact/implementation/lib/type.ml`.
**No mech change — we follow the paper.  This is a note about the artifact.**

`join_sk p0 p` takes the INPUT `P₀` first and the SUBJECT `P` second.  This is
pinned three ways: the arm `| Ghost, p -> rule "U-GhostR"` versus
`| p, Ghost -> rule "U-Ghost"` (and `GhostR` is the rule whose *input* is `□`);
the arm `| MFlex alpha, p -> rule "U-FlexR"; assign alpha p [] theta` (and
`FlexR` is the rule whose *input* is `α̂` and which assigns `α̂ := P`, the
subject — the code assigns the second argument); and the `\aconsis` macro
itself (macro.tex:1002 renders `#3 ⊢ #4 ∼ #5 ⊣ #6`, and the abbreviation at
full-algo-spec.tex:1440-1442 writes `\aconsis{Θ₀}{P}{P₀}{Θ₁}`, so LEFT of `∼`
is the subject).

`U-Assign-Assign` respects this — `join_sk (subst_var p tau beta)
(subst_var (MFlex alpha) tau beta)` puts the flex var in the subject slot,
matching the paper.  But `U-Flex-Flex-Assign` (type.ml:319-320) does

```ocaml
join_sk (subst_var (MFlex alpha) tau gamma) (subst_var (MFlex beta) tau gamma) theta
```

i.e. INPUT `α̂[τ/γ̂]`, SUBJECT `β̂[τ/γ̂]` — whereas the paper's
`\unify{α̂[τ/γ̂]}{β̂[τ/γ̂]}` means subject `α̂`, input `β̂`.  **The implementation
is internally inconsistent about its own convention**, which is the strongest
evidence that this is a slip in one of the two sites, and the paper says which.

BENIGN, but for a subtler reason than "both sides are monotypes".  Algorithmic
consistency is **mirror-symmetric** under the swap `(P₀ ↔ P, Δ₁ ↔ Δ₂)`: all 14
rules pair up (`Ghost`↔`GhostR`, `ForallSyn`↔`UnivGhost1`,
`UnivGhost2`↔`UnivGhostR`, `FlexL`↔`FlexR` — which even produce the *same*
output `α̂`; `Unit`/`Rigid`/`Arrow`/`ForallInh`/`UnivGhost`/`Flex` self-mirror),
and the side conditions swap `Δ₁`/`Δ₂` in exactly the right direction.  The one
residue is that `Flex` outputs the *subject's* variable, so `Q` can change.  At
`Flex-Flex-Assign`, however, `Δ₁ = Δ₂ = ∅` and the output `Q` is DISCARDED — so
both caveats vanish precisely there.

Status: **argued, not proved.**  See the DEFERRED entry below.

## DEFERRED — `a_consis_sym` (would turn the above from argued-benign into proved-benign)

Archived at `algo/prop_symmetry.v.deferred` (OUT of the build; the Makefile
globs `*.v`).  **Do not un-archive as-is: the file HANGS** (90s+ of CPU at 98%
without terminating).

Intended statement:

```coq
Theorem a_consis_sym : forall F Δ1 Δ2 Θ0 P0 P Q Θ1,
  Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] P ≈ Q ⊣ Θ1 ->
  exists Q', Θ0 ⊢ₐ[ F ][ Δ2 | Δ1 | P ] P0 ≈ Q' ⊣ Θ1.
```
(mutually with `a_unify_sym`; `a_assign` needs no symmetry and no IH, since
`FlexL` and `FlexR` carry the *same* assign premise and re-use it as a black
box.  `Θ₁` is expected to be preserved; only `Q` may differ, and only at `Flex`.)

TWO REASONS IT STALLED, both worth knowing before anyone retries:

1. **The hang.**  `swap_ptyp_subst` contains
   `repeat match goal with |- context [ if ?t then _ else _ ] => destruct t end`.
   `destruct t` does NOT eliminate that `if`: `subst_ptyp_in_ptyp`'s scrutinee
   elaborates to `@eq_dec ptypvar EqDec_eq_of_X ...`, which a plain `destruct`
   does not abstract, so the `if` survives, the `match` fires again, and
   `repeat` loops forever.  The working form is
   `destruct (@eq_dec ptypvar EqDec_eq_of_X x y)`.  (Same gotcha bites
   `subst_pskl_in_pskl`; recorded in prop_flex.v.)  The file also has ~10
   UNSCOPED `fsetdec` calls, which are minutes-slow in this codebase.

2. **The design, which is the real obstacle.**  The output must be
   EXISTENTIALLY quantified, and that collides with cofinite quantification: in
   `ForallInh` the IH yields some `Q'_α` for each fresh `α ∉ L`, but the
   conclusion needs a SINGLE `Q'` with `open Q' α` for every `α`.  You cannot
   just pick one.  The archived attempt reached for a 960-line atom-swapping /
   equivariance library to get around this.  **That is not how this codebase
   solves it.**  The precedent is `d_consis_compose` (see
   [[frost-compose-tags-witness]]): it dissolved exactly this
   "different witness per fresh variable" blocker by making the output an
   EXPLICIT WITNESS FUNCTION of the inputs — invariant under opening a variable
   — instead of an existential.  Retry that way; it should be a fraction of the
   size and need no equivariance machinery at all.

Priority: LOW.  It changes nothing in our mechanization — our rules already
follow the paper.  It only upgrades our verdict on someone else's code.

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
  (`algo/cex/cex_refine_not_transitive.v`).  An unwritten proof hid that.
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
- Machine-checked artifact: `frost/algo/cex/cex_refine_not_transitive.v` —
  `ad_refine_syn_not_transitive` is Qed and axiom-free.
- The GhostForall rule binds `α` in `Γ` but deliberately KEEPS `Δ`
  (the paper's own inline comment: "It's fine to keep Δ since we already
  required well-formedness separately").  But `Δ` is exactly what the Ghost
  rule tests (`Δ ∩ ftv(syn{Q}) = ∅`).  So a ghost nested UNDER a GhostForall
  may be filled with the very `α` that GhostForall binds — `α` is in `Γ`,
  not in `Δ`, so the side condition does not forbid it.  Witness:

      □ ⊳ syn(∀◇(□→□))              (Ghost; the fill is well-formed)
      ∀◇(□→□) ⊳ ∀α. ∀◇(α→α)         (GhostForall, then two Ghost fills at α)
      but NOT  □ ⊳ ∀α. ∀◇(α→α)

  The last step fails because the Ghost rule may only produce a WELL-FORMED
  skeleton, and `∀α. ∀◇(α→α)` is not one: skeleton well-formedness binds a
  quantifier's variable in `Δ`, while a `∀◇`-ghost's body must be well-formed
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
  (a ∀◇-ghost body may mention a context rigid α that the strip removes, and
  α ∈ Δ does not rescue it because ∀◇-ghost bodies are checked at the EMPTY Δ).
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
  mutual soundness bundle `a_assign_unify_consis_sound`
  (algo/prop_consis_sound.v): new names avoid `F`; no-flex-dep +
  flex-above-free + domain bookkeeping are preserved for every protected
  Δ with `Δ ⊆ F ∪ dom Θ₀`, using Assign-SkipRigid's occurs condition and
  the positional fact that Δ-binders sit above all flexible entries.

## FALSE — `thm:complete-consistency` optimality (parts 2/3): flex migration below term binders defeats the factoring

**Status: FALSE against the paper's rules; MECH HAS ADOPTED THE FIX
(2026-07-15, same day).  The counterexample is machine-checked, axiom-free
(`algo/cex/cex_assign_optimal_syn_middle.v`, now stated against a local copy
`a_inc_syn` of the original rules).  The mechanized `a_inc`/`a_inc_equiv`
(def_meta.v) now use GMM-style SEMANTIC ENTRIES — binder middles up to
`≡ᵗ`/`≡ˢ` (new skeleton equivalence `a_pskl_tyequiv`) — and the same instance
then factors (`cex_zeta_semantic`).  THE PAPER MUST ADOPT THE RULE BELOW
(draft note: sections/appendices/optimality-cex.tex, commented-out \input
after the lemma).**

The OPTIMALITY half of `thm:complete-consistency` part 3 (assignment) is
false as stated; part 2 (unification) inherits the falsity through
`Flex-Flex-Skip'` for contexts with term binders.

Two paper ingredients conspire:

1. **Flex migration.**  `Assign-Depend` moves a payload flexible `X̂` into the
   pending suffix `Ξ`; `Assign-SkipTmVar` threads `Ξ` below walked term
   binders; `Assign-SolveM` deposits it at the subject's position.  The
   migration is FORCED by well-formedness: the deposited definition
   `α̂ ≔ guessᵀᵞ(P)` mentions `X̂`, so `X̂` must end up below it.

2. **Syntactic middles + positional wf in information increase**
   (algorithmic.tex:91-121).  The var rule `Θ,x:P ⊑[θ] Θ',x:θP,Ξ` pins the
   target's binder payload to the SYNTACTIC `θP`, and the flex rule demands
   each image be well-formed in the POSITIONAL remainder of the target.

Instance (5 atoms; `assignvar α̂ ≔ X̂→()`):

    Θ₀ = c : X̂→(), X̂, y : (), α̂
    algorithm:  Θ₁ = c : X̂→(), y : (), α̂ ≔ X̂→(), X̂     (X̂ migrated below y)
    competing:  θ = [δ̂/X̂, ()→()/α̂]  into  Θ = c : δ̂→(), δ̂ ≔ (), y : ()

The competing solution is valid (increment ✓, `a_wf_aenv Θ` ✓, join
`θP ≈ θα̂` ✓ — `δ̂` unfolds to `()`), and `δ̂` is in scope at `X̂`'s ORIGINAL
position (above `y`).  Any factoring `ζ : Θ₁ ⊑ Θ` must reproduce `c`'s payload
`δ̂→()`, forcing `ζX̂ = δ̂` syntactically — but `X̂`'s entry in `Θ₁` is consumed
against the target remainder BELOW `y` (here: empty), where `δ̂` is not
well-formed.  No `ζ` exists.  (Note: GMM, from whom the information-increase
device is borrowed, compare context-entry payloads up to EQUIVALENCE, not
syntax; their minimality theorem does not face this.)

**Provenance (2026-07-15, verified against both sources):** the syntactic rule is
faithful to **Gundry's thesis** (Gundry13, Fig. 2.4: term middles `x : θσ`,
recursion on the stripped remainder, term variables separate localities) — NOT
to the MSFP paper's base relation, whose `≼` is per-entry SEMANTIC
(GundryMM10 §3.1, `Δ ⊩ δ⟦vD⟧`).  The thesis also moves metavariables past term
entries (`inst-depend`/`inst-skip-tm`, Fig. 2.5), so the analogous instance is
constructible in plain HM (`Θ0 = …, γ̂, y:σy, α̂, x:α̂`; solve `γ̂ ≡ α̂→1`), and the
thesis's own generality proof (Lemma 2.6, App. D.1) covers only "some of the
more interesting cases" — the term-walk cases are dispatched by "θ can be
rearranged", a definition-swap that is only valid against the SEMANTIC relation
(it is MSFP Lemma 10's "ψ ≡ θ" step).  So the gap predates this paper; the
repair below applies to the thesis's formulation as well.

**Candidate fix (authors' call, not applied):** make information increase's
binder middles ≡ᵗ-tolerant, GMM-style:

    Θ ⊑[θ] Θ'    Θ' ⊢ P' ≡ θP
    --------------------------------
    Θ,x:P ⊑[θ] Θ',x:P',Ξ

Then `ζ` may use a depth-legal representative of `δ̂`'s ≡ᵗ-class (here `()`)
and the counterexample dissolves; the soundness development only ever uses the
middle up to ≡ᵗ, so it survives.  Affected mech cases (marked FALSE in
`algo/prop_consis_complete.v`): Assign-SkipTmVar (typ/skl) and
Flex-Flex-Skip' (var_typ/var_skl branches).  All other optimality cases are
unaffected (their walks carry no type payload, or none that can migrate).

**UPDATE (2026-07-16): Assign-SkipTmVar(typ) is now CLOSED under the adopted
semantic rule** (`skip_tm_var_case`, Qed, axiom-free, `algo/prop_consis_complete.v`;
optimality bundle admits 13→12).  The factoring is the GMM Lemma 2.6 construction
in full: `a_inc_self_downarrow` + `a_inc_downarrow_prefix` land the competing
increment at `ρ_sub = ⇓ρ = compose(aenv_msubst Θ) ρ` over the sub-target `Θ'`
(below the walked binder); `consis_downarrow_subject` (the join is invariant under
⇓-normalizing the subject when the RHS is monotype) plus the O2 grounding
`join_pskl_downarrow_mono_scoped` transfer the competing join to `Θ'`; the sub-IH
runs; and `a_inc_equiv_mid_insert_var` + `a_inc_equiv_self_downarrow` +
`a_inc_equiv_trans` rebuild the factoring over the original `ρ`.  SkipTmVar(skl)
and SkipRigid are the pskl/tvar mirrors (pending).

**NEW (minor) unstated-invariant gap — `dom Ξ ⊆ ftv P`.**  The optimality induction
needs, at every node, that the pending declarations `Ξ` all occur in the assigned
skeleton `P` (`dom Ξ ⊆ ftvar_in_pskl P`).  It is used to ground each pending decl's
competing image into the sub-target `Θ'` (O2 only reaches decls appearing in `P`);
a decl `Y ∉ ftv P` is unconstrained by the join and its ⇓-image can escape `Θ'`,
i.e. the SAME flex-migration phenomenon (a genuine counterexample, not just a proof
obstacle).  This is NOT a free invariant of the `a_assign` judgment — `Assign-SolveM`
takes `Ξ` as an input.  But it IS an invariant of every REACHABLE derivation: the
top-level `assignvar` starts with `Ξ = nil`; `Ξ` grows only via `Assign-Depend`,
whose premise is literally `β̂ ∈ ftv P` (def_extra.v); the skip/solve rules keep
`Ξ` and `P`.  So a config with a dangling `Y ∈ Ξ, Y ∉ ftv P` is unreachable from
the top.  The mechanization threads `dom Ξ ⊆ ftv P` through `assign_optimal_post`
and `a_assign_optimal_thm`, maintaining it across the closed rules
(UnivGhost-Id/Depend/Skip) and instantiating it vacuously at the corollary's
`Ξ = nil` — so the TOP-LEVEL optimality statement is unchanged and unweakened.  The
paper's assignment optimality, if stated over general `Θ₀ ∣ Ξ` (it is —
consistency-proofs.tex:2420) and inducted without this invariant, has the same
unstated-invariant gap; it should carry `dom Ξ ⊆ ftv P` (or be stated at the
top-level `Ξ = ·`, where it is vacuous).

## GAP — `thm:complete-consistency`: the three induction subjects DO NOT COMBINE

Full analysis, with per-edge verification and the measure that works:
[DESIGN-completeness-measure.md](DESIGN-completeness-measure.md).

The lemma is proved "by mutual induction for the three parts", but each part
declares a DIFFERENT induction subject: §1 (consistency) on the DECLARATIVE
consistency derivation; §2 (unification) on the CONTEXT `Θ₀`; §3 (assignment)
on the PAIR `Θ₀ ∣ Ξ` (consistency-proofs.tex:2257, :2277, :2420).  A
mechanization needs ONE well-founded order, and BOTH obvious candidates are
dead — with witnesses:

* **No context measure can be outermost.**  `Arrow`'s SECOND premise runs at the
  OUTPUT context `Θ₁` of the first, and `Assign-SolveM` can have extended it with
  fresh flexible variables AND made a definition.  Witness: `Θ₀ = (α̂)`, input
  `(◇→unit)→unit`, subject `α̂→unit` ⇒ `Θ₁ = (α̂ ≔ β̂→unit), (β̂)`.  Any weight goes
  up.  (`ForallInh`/`ForallSyn`/`UnivGhost1` break `|Θ₀|` more cheaply, `+1` rigid.)

* **No declarative-derivation measure can be outermost either** — and it does not
  merely fail to shrink, it can GROW.  At `Assign-Assign` the derivation handed to
  the consistency IH is the paper's REFLEXIVITY derivation on `θ(α̂[τ/β̂])`
  (:2510-2515).  Witness: `Θ₀ = (β̂≔unit),(α̂)`, `P = ◇→unit`,
  `θα̂ = (unit→unit)→unit` — caller's derivation is 3 nodes, callee's is 5.  The
  mechanism is `Ghost`: it absorbs an arbitrarily large `Q` in ONE node, so the
  assignment node's derivation is bounded by the GHOST-RIDDEN `P` while the
  spawned consistency node's is bounded by the FULLY-SOLVED `θα̂`.

  **Corollary: §1's "induction on the declarative consistency derivation" is not
  a well-founded induction as written** — `UnivGhostR` (:2570-2572) recurses with
  the LITERALLY IDENTICAL derivation.

The two failures land on DISJOINT edge sets, so no lexicographic combination of
them in either order works.

RESOLUTION (not a paper error, just an unstated measure).  Induct on
`V` = the size of the skeletons **as the SOLUTION sees them** — pushed through the
solution's `θ`, then through the target `Θ`'s own definitions.  `V` strictly
decreases on all 11 consistency-internal edges and is EXACTLY CONSTANT on all 4
cross-edges and both back-edges, which is what lets `|Θ₀|` carry the second
lexicographic component.  The back-edges `X ↦ X[τ/γ̂]` only unfold a definition
THE SOLUTION HAD ALREADY UNFOLDED, so `V` cannot see them; the consistency rules
decompose, so `V` cannot miss those; and the context growth is simply not measured.

PREREQUISITE: `≡ᵗ` is NOT size-preserving (`a_tyequiv__flex_def` gives `α ≡ᵗ τ` for
ANY `τ`), and `≡ᵗ` is exactly what `a_inc_equiv` uses.  So `V` is not even a
well-defined natural number until the skeletons are put in a total-unfolding normal
form.

## GAP — `thm:complete-consistency` §1: the flexible cases are ONE SENTENCE, hiding two obligations

consistency-proofs.tex:2568-2569 — "The cases where `P` or `P₀` is a flexible
variable are handled by the other two parts of the lemma" — is the ENTIRE treatment
of `Flex`, `FlexL`, `FlexR`.  Two things are missing:

* **Constructing the callee's solution.**  A consistency solution gives
  `Θ ⊢ syn θS ≈ bid Q` AND `Δ₁ ⊢ inh θP₀ ⊳ Q`.  The unification/assignment problem
  needs `Θ ⊢ θα̂ ≈ θβ̂` / `Θ ⊢ θP₀ ≈ θα̂` — a DIFFERENT judgment, between the TWO
  INPUTS, with `Q` eliminated.  That needs the BRIDGE (consistency-into-`Q` plus
  refinement-of-`Q` ⟹ a relation between the two inputs) — the same bridge
  soundness already required.  The paper never invokes it here.
* **Recovering PRECISION.**  §1's conclusion demands `Δ₁,Δ₂ ⊢ θ₁P₁ ⊑ Q`, and for
  these three rules the algorithmic output is `P₁ = α̂`.  The §2/§3 IHs produce NO
  precision statement at all (:2266-2270, :2412-2416).  So `Θ ⊢ θ₁α̂ ⊑ Q` must be
  proved separately — it is NOT "handled by the other two parts".

## GAP — `thm:complete-consistency` §3 never proves the assignment walk is not STUCK

§3's skip cases are dismissed as "Our goal follows from IH and context weakening"
(:2557-2558).  But `Assign-Skip`/`Assign-SkipRigid` carry `β̂ ∉ ftv(P)`, and there
is NO RULE AT ALL for a RIGID head `β ∈ ftv(P)`.  Completeness must therefore PROVE
the walk never reaches such a head — the escape/scope check, the classic hard step
in DK-style completeness.  It is true and provable (`a_inc` peels the rigid `β`
before it reaches `α̂`, so `θα̂` is well-formed BELOW `β`; whereas `β ∈ ftv(P)` forces
`β ∈ ftv(θP)` since `θ` cannot erase a rigid variable, and consistency against the
MONOTYPE `θα̂` then forces `β ∈ ftv(θα̂)` — contradiction).  The paper does not do it.

*Status (2026-07-17, 47bcc36):* the stuck-check is MACHINE-CHECKED in
`algo/prop_consis_complete.v` (`assign_complete_step`, rigid-head case,
`γ ∈ ftv(P)` sub-path).  Ingredient (i) is `a_inc_strip_decls_prefix` +
`a_inc_tvar_inv` (the competing increment peels `γ`, so `θα̂` is wf in the
truncated target); ingredient (ii) is the new scoped join ftv-survival
`ad_pat_consis_rigid_ftv_rev_scoped` (the definition side condition holds only
for definitions reachable from the truncated target's scope — the blanket
version is false, definitions above `γ` may mention it).

Likewise `Assign-SolveM` (:2430-2461) silently assumes BOTH of its premises: the
occurs check `α̂ ∉ ftv(P)`, and that `guess^TY(P)` succeeds AND returns a MONOTYPE
(`a_guess_mono` has no `all` case; `a_assign__solve_m` additionally premises
`mono_ptyp τ`).  Both follow from the solution; neither is proved.

## GAP — the SOLUTION notions: the active 2-condition definitions admit binder-capturing fills

*(2026-07-18, found while mapping the subtyping proofs; DESIGN-subtyping.md §3.1.)*

The completeness proof for consistency AUGMENTS the definition of a solution
to THREE conditions — join, `P0`-fill at Δ₁, and the subject-side refinement
`skctx[Δ2]{Θ} θ⌊S⌋ ⋈ Q` (consistency-proofs.tex:2230-2242) — and the
standalone 2-condition Definition of consistency solutions is commented out
in algorithmic.tex.  The third condition is NOT derivable from the other
two: on `(P0 = ∀X.X, P = ∀X.◇, Q = ∀X.X)` the join and the fill hold (the
capturing `X` sits at a concrete position of `P0`, so the fill premise never
inspects it; the join's hole rule checks the fill's well-formedness over the
binder-EXTENDED context), the subject refinement fails, and the algorithm is
stuck (its Ghost rule carries `Δ2 ∩ ftv(fill) = ∅`, and the ∀-step puts the
binder in both Δs — by design, so that soundness outputs refine both
inputs).  So completeness against the 2-condition notion is false; the
mechanization states it against the paper's own augmented (3-condition)
notion.

The subtyping-solution Definition (algorithmic.tex:1423-1437) is ACTIVE and
2-condition, and the same capture transplants: at `TI`,
`(P0 = ◇, P = ∀X.◇, Q = syn ∀X.X)` passes the `typsub`-Infer premise and the
`P0`-fill, yet the optimality conclusion demands `θ(∀X.◇) ⊑ ∀X.X`, which the
precision rules forbid (the hole rule's `Δ ∩ ftv ψ = ∅`).  The subtyping
proofs' appeals to thm:complete-consistency ("(θ;Q) is a solution to the
consistency problem") silently assume the augmented notion.  SUGGESTED FIX:
add the subject-side refinement `Θ ⊢ θ⌊S⌋ ⋈ Q` to the definitions of
solutions (both consistency and subtyping); soundness already establishes it
for every algorithmic output, so the theorems still characterize the
algorithm exactly.  The mechanization proceeds with the augmented notion;
no machine-checked counterexample was made (the mech never diverges from the
paper's PROOF-level statements here — unlike the optimality-cex case).

## Resolved definition-sync findings (step 1 of the restart)
See [REPORT-remech-decl-sync.md](REPORT-remech-decl-sync.md) — notably the
`is_tskl` untagged-∀ fix (A1), whose downstream effect invalidated the
pre-restart `pskl_to_tskl` decorated witnesses (prop_safety machinery).


## Soundness ForallR: the strengthening step is TRUE but needs the substitution generalization (2026-07-18)

`subtyping-proofs.tex` (lemma:sound-decorated-subtyping, ForallR case,
~:1293-1314) discards the trailing suffix Ξ with "Since Ξ is fresh for S and
B, by context strengthening for unused variables in Ξ".  The strengthening
STATEMENT is true — but it is not provable by direct induction on the
derivation: a ForallL instantiation witness may mention a Ξ-variable the
conclusion (S, B) does not expose, so the conclusion-only freshness motive
does not propagate to the premises.  The decl layer hit the same for
`d_sub` (decl/prop_syntax_directed.v NOTE — its "is FALSE" refers to the
induction motive, not the theorem).

Mech route (decl-style): the inductive generalization is SUBSTITUTION —
substitute the stripped variables away, rewriting
witnesses too — unit for an undefined flex entry, its own definition
painting for a defined one, iterating head-first over Ξ (defs scope to
tails, so the head entry is never mentioned elsewhere).  Foundations in
algo/prop_pat_sub.v §4 (`guarded_pskl_subst`, `a_wf_pskl_subst_ctx`,
`uskl_to_pskl_subst_unit`); the `ad_pat_consis`/`ad_pat_sub` strip
inductions and the suffix driver are the remaining pieces (the decl cribs
are `d_pat_consis_subst_unit` / `d_pat_sub_subst_unit`,
decl/prop_skeleton.v:268/313).

Paper note: the step is correct; a footnote that the strengthening lemma is
proved via witness-rewriting substitution (not direct induction) would make
the appendix self-contained.


## Decorated ForallL: the ∃-decoration is a cofinite tag FAMILY (prose-completion, 2026-07-19)

`subtyping-proofs.tex`'s decorated ForallL (and lemma:subtyping-decoration's
use of it) picks ONE decoration ψ of the guessed instantiation P1 ("let ψ be
a decorated skeleton with ⌊ψ⌋ = P1 ...") and treats its choice as
WLOG-irrelevant.  The mech's `a_subtag__forall_l_{tagged,untagged}`
(algo/def_decorated.v) instead quantifies the premise over EVERY sorted
decoration whose tag names avoid the rule's cofinite set L:

    forall Ψg ψg, inter Ψg L [=] empty -> a_tags_sort NM Ψg ψg ->
      ⌊ψg⌋ˢ = P1 -> subderivation @ (Ψ ∪ Ψg)

— the tag analog of cofinite binder quantification.  Consumers pick a
witness via `pskl_decorate_exists` / `a_tags_sort_decorate_exists`
(algo/prop_pat_sub.v §7).  This is an ENCODING device, not a semantic
strengthening: with a decoration-renaming lemma the single-witness rule is
equivalent (renaming lets any consumer move to fresh tag names); the family
form just avoids proving that renaming.  Paper needs no change beyond
reading "let ψ be" as "for any fresh ψ".

## PROSE-COMPLETION — `lemma:precision-substitution`'s `fresh Ψ'` must mean GLOBAL tag freshness (2026-07-24)

`lemma:precision-substitution` (subtyping-proofs.tex:1664) carries the
side condition `fresh{Ψ'}` on the instantiation's tags.  The weakest
faithful reading of ForallL's own freshness — the instantiation's tags
are disjoint from the current *tag context* — makes the lemma **false**:
the tag context splits at Arrow (`Ψ = Ψ₁, Ψ₂`), so a tag `ε` of `ψa` can
leave the context on one branch while `ψa`-copies still carry it
syntactically on the other; a ForallL deeper in that branch may then
legally reuse `ε` in its own instantiation `ψ''`, and one can build a
derivation in which `ε` is consumed at a `ψa`-node while the `ψ''`-node
faces an `all_syn` target (which records nothing).  After substituting
`Pa` for `ψa`, the `ψ''`-ForallL still re-introduces `ε`, no remaining
node can consume it, and every leaf forces the tag context to `∅` — the
transported judgment is underivable.

So `fresh{Ψ'}` must be read as Barendregt-style *global* freshness: fresh
from the context AND from every tag in the subject (in particular from
the tags of previously substituted instantiations).  The mechanization
renders this as a tag-HYGIENIC mirror of the fuel-indexed judgment
(`ad_pat_sub_g`, def_decl_algo_sub_hyg.v: ForallL additionally requires
`inter Ψ' (ftag_in_uskl subject) = ∅`), over which precision-substitution
is proved (`ad_pat_sub_precise_upre`, prop_sub_complete.v, Qed); an
arbitrary derivation is converted once, at the completeness theorem's
entry point, by a tag-renaming freshening lemma.  Nothing is wrong with
the paper's statement under the intended reading — but the proof depends
on the global reading in an essential, non-obvious way, and a reader
formalizing the local reading gets a false lemma.

## GAP (proof-step) — `lemma:precision-substitution`'s "straightforward induction" does not go through as stated; the motive must be generalized (2026-07-24)

The paper proves `lemma:precision-substitution` by "a straightforward
induction on the subtyping derivation …, observing that … replacing
ψa with Pa would not result in any type mismatch"
(subtyping-proofs.tex:1668-1673).  Two steps of that induction are not
straightforward and required genuine repairs (both machine-checked,
prop_consis_precise.v / prop_sub_complete.v, all Qed axiom-free):

1. **The substitution motive is too weak for its own ForallL case.**
   When the subject is (an occurrence of) `ψa` itself and the last rule
   is ForallL on `ψa`'s own quantifier, the premise's subject is
   `ψa-body[ψ''/α']` and the reconstruction needs
   `Pa-body[ψ''/α']` — the changing part is the *whole* skeleton
   surrounding `ψ''`, not the positions of the substituted variable, so
   the `S[ψa/α] → S[Pa/α]` induction hypothesis does not apply (and
   re-instantiating with the stripped `⌊ψ''⌋` is not a legal ForallL
   instantiation, since decorated skeletons have no untagged
   quantifier).  REPAIR: generalize the motive from single-variable
   substitution to a *decorated subject-precision relation* ⊑ᵤ
   (`uskl_precise`) — congruences + refinement-mirroring ghostier-side
   rules + reflexivity — which is closed under instantiation
   (`uskl_precise_subst`) and embeds plain precision against a decorated
   target (`uskl_precise_of_precise`).  The subst-form is the special
   case `S[Pa/α] ⊑ᵤ S[ψa/α]`.

2. **Fuel/height preservation needs a rule-granularity accounting.**
   The main completeness induction applies its IH to the substituted
   premise, so precision-substitution must not increase the derivation
   height — but the more-precise subject may carry `∀◇`-wrappers or
   fold flexible definitions that the original derivation lacks, forcing
   extra UnivGhostL / FlexMono steps.  REPAIR: in the measure-carrying
   mirror, leaves take any fuel and UnivGhostL/UnivGhostLG/FlexMono are
   non-incrementing (only Arrow/ForallR/ForallL increment); the main
   theorem's measure is then lex(fuel, derivation structure), which its
   non-incrementing cases support because they recurse structurally.

Also elided by "no type mismatch": the transported subject's tag
context must drop *exactly* by the substituted instantiation's consumed
tags — the mechanization threads the invariant "tag context ⊆ the
subject's syntactic tags" (`ad_pat_consis_ftag_sub`,
`ad_pat_sub_g_ftag_sub`) to pin the residual context, and threads the
solution target's well-formedness (external-wf reading) for the
ghost-introduction cases.

## RESOLVED (isolated statement FALSE, but NOT a completeness problem) — the -var completeness lemmas: a flexible counterpart `P0` refutes the ISOLATED statement (machine-checked, 2026-07-24; resolved 2026-07-25)

> **Resolution (2026-07-25):** the isolated `-var` statement is false as
> written, but the refuting configuration is UNREACHABLE, so it is not a
> completeness problem and needs no P0-side premise.  See the "### Resolution"
> subsection at the end of this entry.  The earlier "Suggested repair"
> (a P0-side positional condition) is SUPERSEDED and was reverted from the
> mechanization.

`lemma:complete-consistency-constraint-collection-solving-var`
(consistency-proofs.tex:1181) and its subtyping twin
`lemma:complete-constraint-collection-solving-var`
(subtyping-proofs.tex:1696) are FALSE as stated.  Machine-checked
counterexample: `algo/cex/cex_p6_flex_counterpart.v` (Qed, axiom-free,
refuting the conclusion for EVERY `P_a`, EVERY `θ_a` with
`inc[θ≡θ_a]{Θ0}{Θ}`, and every Δ/tag-set in the conclusion's precision).

The configuration: `Θ0 = X, α̂`; `Θ = X`; `θ = [α̂ ↦ unit→unit]`;
`ψ_a = X → unit`; `ρ = [X ↦ unit]` (so `ρ(ψ_a) = unit → unit`);
`P_i = X → unit`; `P_0 = α̂`; `Q = unit → unit`.  Every premise holds —
including the positional side condition ("P_i has the same rigid
variable in the same position") and the freshness facts it stands for.
The only applicable solve rule is FlexR, forcing `P_a = α̂`; the
conclusion `precise[Ψi,Ψa]{θ_a P_a}{ψ_a}` then demands
`(unit→unit) ⊑ (X → unit)` (θ ≡ θ_a pins `θ_a α̂` up to ≡, which is
syntactic at the definition-free Θ), whose argument obligation
`unit ⊑ X` has no derivation — X is rigid.

Root cause: every case analysis in the five completeness lemmas of the
cluster recovers `P_0`'s shape by inversion on the refinement premise
`Θ ⊢ inh{θP_0} ⊳ Q`, silently assuming the subject exposes a matching
constructor (or ∀◇/□).  But the inversion also admits `P_0` = flexible
variable, whose θ-IMAGE supplies the constructor.  The algorithm's own
rule for flexible counterparts — LE-FlexR (fig:poly-info-extraction),
which replaces the payload by a fresh `γ̂ ∈ Ξ_c` — is never invoked in
either completeness appendix.  At the non-var lemmas the fresh-`γ̂`
mechanism can repair the flexible subcase (θ_a extends to Ξ_c and may
map `γ̂` to a ψ_a-refining monotype when ψ_a is mono-paintable; when it
is not, the premises are vacuous — but BOTH facts need proof).  At the
-var lemmas there is no Ξ_c and θ_a is pinned on all of Θ0, so the
flexible subcase is not repairable in place: the statement itself needs
a premise excluding it (e.g. `P_0` is not a flexible variable, with the
flexible case handled at the caller via LE-FlexR before descending), or
a rephrased conclusion.  Blocked pending the authors' intended reading.

A related mech-side infidelity was found and FIXED in the same pass
(independent of this refutation, which uses an UNDEFINED flexible):
`a_solve_eq__flex_r` was encoded for undefined flexibles only
(`binds α abind_flex_mono Θ`), while the paper's context-free FlexR
(full-algo-spec.tex:1374) fires on any hatted variable.  A DEFINED
flexible nested inside a structural counterpart (e.g. `P0 = unit → β̂`,
`β̂ := unit`) made the mech solve stuck where the paper succeeds — a
second, mech-side falsifier of the completeness statements that would
have survived any repair of the paper-level gap.  The rule now takes
`a_flex_tvar Θ α` (hattedness); the soundness stack is unaffected
(restriction → relaxation; the decorated twin SEq-FlexR was already
context-free).

### Addendum (2026-07-25): the `nonflex{P0}` repair is INSUFFICIENT — refuted at depth

Trying the proposed repair in the mechanization before adopting it
falsified it: `cex_p6_var_nonflex_insufficient` (same cex file, Qed,
axiom-free) reruns the refutation with `ψa = 1 → (X→1)`, `Pi = 1 → (X→1)`,
`P0 = 1 → β̂` — the counterpart is an arrow, so `nonflex{P0}` HOLDS, but
the -var lemma's Arrow case recurses on P0's PIECES and the right piece is
the old flexible β̂ opposite the ρ-leaf position: solving is forced through
SE-Arrow then SE-FlexR to `Pa = 1 → β̂`, and the conclusion precision fails
one constructor down.  A head-shape premise cannot survive the structural
recursion.

Two further facts locate the real repair:
* At the TOP of the call chain (ρ = identity, the P = α crux), the bad
  configuration is UNSATISFIABLE: the subject there is ψa itself, and the
  consistency/subtyping premise at the leaf position (rigid X vs the
  flexible's unit-image) has no derivation.  The falsity is an artifact of
  the ρ-GENERALIZATION being too coarse: it forgets that in premise sets
  arising from actual runs, a flexible counterpart piece cannot sit at or
  above a ρ-substituted position.
* The implementation's `solve_eq` (type.ml) confirms the context-free
  FlexR reading (any flexible target wins, keeping the flexible), so the
  solve side cannot be tightened; the invariant must exclude the
  configuration.

### Resolution (2026-07-25): the configuration is UNREACHABLE — no P0-side premise needed

The "Suggested repair" above (a P0-side positional condition) is SUPERSEDED.
It patched an isolated statement that does not need patching, and its ForallL
maintenance turned out not to be derivable from the local solve (SolE-Check
bridges the subtyping solve into SolE-FlexR). The whole `pskl_dominates_rho`
experiment was REVERTED from the mechanization.

Three facts settle it (all machine-checked; new file
`algo/cex/cex_p6_flex_freshened.v`, Qed axiom-free):

1. **Only the Arrow case can even have a flexible `P0`.** θ maps flexibles to
   MONOTYPES (unit / mono-or-rigid var / arrow). Refinement `inh{θP0} ⊳ Q`
   into a ∀ or ∀◇ requires a ∀/∀◇/defined-flex source (inversion on
   `ad_refine_syn` into `bskl_all_inh`), which a monotype never is. So
   ForallInh/ForallSyn/ghost provably have non-flex `P0`; leaves are handled
   directly (SolE-Flex / the SolE-Var ρ-var special case).
2. **No flex-SPLIT rule exists in constraint solving, and none is needed.**
   SolE-Arrow needs both sides arrows; SolE-FlexR solves the flexible
   counterpart directly to `β̂`. `split[α̂][β̂→γ̂]` lives only in the
   inference/`⤳ᵐ` layer.
3. **The cex's θ is FORCED BY ρ; the configuration is not producible.** ρ
   substitutes the rigid `c` away, so `ρ(ψa)=unit→unit ∼ Q` and
   `inh{θβ̂} ⊳ Q` (same Q) pin `θβ̂ = unit→unit` — c is stripped from
   everything θ sees, while ψa (used only for the final precision) keeps it.
   A run never emits a raw Θ0-flex payload at a compound subject: LE-FlexR
   FRESHENS a flexible counterpart there to a fresh `γ ∈ Ξ`
   (`a_lookeq_arrow_subject_flex_target_freshened`; and
   `a_lookeq_flex_target_raw_subject_not_arrow`: a raw flex payload's subject
   is never an arrow). The fresh `γ` is the NON-var lemma's job (θ extends
   over Ξ and can assign `γ` the rigid `c`, so precision holds).

**P6-Cv/Sv plan:** ∀/∀◇/ghost cases prove non-flex `P0` from the
monotype→refinement fact (no premise); leaf cases as the paper does; the
Arrow case handles a flexible `P0` via SolE-FlexR like the leaf case, relying
on the freshening so a raw Θ0-flex opposite a ρ-rigid-var cannot occur.

## GAP (REPAIRED 2026-07-27 — proof-step gap; statement TRUE) — `complete-consistency-cc-solving-var` ForallInh/ForallSyn Subcases `Pi=□` and `Pi=∀◇.Pi'`: the Δ-bookkeeping of the IH output is broken

> **Resolution.** Repair candidate (1) below was implemented, as the
> generalized theorem `a_solve_eq_complete_var_gen`
> (algo/prop_look_complete_var.v): the refinement premise is carried at
> `(Θr, Δr)` with `Δr [=] dom Θtv` (the ForallInh descent binders), which
> keeps □-fills wf away from those binders; the precision conclusion is
> strengthened to a fresh-extension family `∀S` so the ∀-rows can fold
> their bodies.  The split is a binds-level BAG (`aenv_split`) — an
> earlier LIST-equation form (`Θ = Θtv ++ Θr`) forced the ForallSyn
> binder into Θtv and with it a mech-only `pskl_no_hole P0` premise; the
> bag form (2026-07-27) removed that premise, so the statement is
> premise-faithful to the paper (see WF-SIDE-CONDITIONS.md, historical
> entry).  The one genuinely-implicit paper step made explicit is the
> aenv-tvar precision rename `ad_partial_precise_rename_tvar` (the
> paper's silent "removing β as necessary").  `a_solve_eq_complete_var`
> is Qed, axiom-free.

- Where: consistency-proofs.tex, Lemma
  `lemma:complete-consistency-constraint-collection-solving-var`
  (:1181), cases ForallInh/ForallSyn, Subcases `P_i = □` and
  `P_i = ∀◇.P_i'`; mech `a_solve_eq_complete_var` (dev scratch
  `algo/cex/p6cv_dev_tmp.v`, cases forall_inh_tagged /
  forall_syn_tagged).  Status 2026-07-25: the mech is at 13/15 cases
  (all others Qed-threaded); these two rows are the only blockers.
- The paper's subcases invoke the IH at the ∀-body and conclude with the
  ∀-precision rule, whose body obligation lives at `Δ,β | Θ,β`.  But the
  IH's PRECISION PREMISE for `P_i = □` can only be built by the □-rule,
  whose side condition `Δ ∩ ftv(ψ') = ∅` FAILS at `Δ,β` whenever the
  target body `ψ'` uses its binder — so the IH can only be invoked at
  `Δ`, and its output precision is at `Δ`, not the `Δ,β` the ∀-rule
  needs.  The □-rule's side condition is not Δ-monotone, so the step
  "goal follows from GhostL" silently uses an inadmissible Δ-weakening.
  The `∀◇` subcase (precision inverted through the fill rule, concluded
  by SolE-GhostForall) has the same mismatch: its body precision sits at
  `Δ | Θ,β` and must be moved to `Δ,β | Θ`.
- The STATEMENT survives: the configurations that would break the
  weakening are premise-unreachable.  A refinement □-fill is wf in
  `Θ` at empty Δ (the refinement's own □-rule), hence β-free; the
  consistency and ρ transfer that β-freeness to the □-opposite TARGET
  subtrees.  Concretely, with `ψ' = β→1` and `P_0' = □→1` the □-fill's
  synthesised-paint would have to be `β` itself, whose wf premise fails —
  so a □ of `P_0` never sits opposite a β-containing subtree.  But no
  premise of the lemma EXPOSES this fact, so the proof step needs a
  repair, not just a rewording.
- Repair candidates (DESIGN-completeness-subtyping.md §6(l); decision
  pending): (1) generalize the lemma's refinement premise to a Δr that
  carries the descent binders (keeps fills β-free by the refinement's
  own wf discipline; touches the case-lemma kit that pins `Δr = ∅`);
  (2) a standalone `P_i = □`-column lemma by its own consistency
  induction with a Δr-indexed refinement premise + ftv-bound lemmas for
  consistency (`ftv S ⊆ ftv Q ∪ dom Θ`) and ρ (`ftv ψa ⊆ ftv ψsub ∪ Δρ`);
  (3) a positional hole-apartness premise (flex_apart-style) — 
  dispreferred, since call sites cannot derive it across the binder
  descent from cleanliness alone.

## FALSE (machine-checked, 2026-07-28) — `lemma:complete-constraint-collection-solving-var` (P6-Sv) is FALSE: its own ForallL case MANUFACTURES the configuration that the 2026-07-25 "unreachable" resolution excludes

- Where: subtyping-proofs.tex:1696 (`lemma:complete-constraint-collection-
  solving-var`, the SUBTYPING twin of the consistency lemma at
  consistency-proofs.tex:1181).  Mech: the counterexample is
  `frost/algo/cex/cex_p6sv_forall_flex.v`
  (`p6sv_with_p6cv_premises_is_false`, Qed, axiom-free).
- **Status: FALSE as an isolated statement, and — unlike the 2026-07-25
  entry above — the standing reachability argument does NOT cover it.**
  The statement still needs a decision by the paper's authors.
- **RESOLVED IN THE MECHANIZATION (2026-07-29), statement-side.**  The
  algorithm is UNCHANGED; the lemma carries one extra premise,
  `flex_shield Θ₀ Ψ' Δρ P₀ ψa` (a positional invariant: at every position
  where a raw Θ₀-flexible faces the guess, the guess is both Δρ-clean and
  Ψ'-tag-free — with an explicit row keeping it from being too strong, see
  `fsh_rho_var`), plus `flex_apart_walk` (P6-Cv's own premise at every state
  the descents can reach).  `a_solve_sub_complete_var` is now **Qed and
  axiom-free** in `frost/algo/prop_look_complete_sub_var.v`, and
  `flex_shield_excludes_cex` is the machine-checked regression test that the
  premise rules out the witness below.  What the authors must decide is
  whether the PAPER adopts this side condition (or an equivalent one) —
  the write-up as it stands claims a statement that is false.

### The witness (ρ is the IDENTITY — this is not a ρ-encoding artefact)

```
Θ₀ = α̂            Θ = α̂ := ⟨⟩→⟨⟩        θ = [α̂ ↦ ⟨⟩→⟨⟩]
N = TY  M = TC    Pi = ∀β. β→β          P₀ = α̂
ψa = ψsub = ∀^ε β. β→β                  Q  = inh{⟨⟩→⟨⟩}
Ψ' = Ψi = {ε}     Ψa = Ψsub = Ψρ = ∅    Δ = Δρ = ∅
```

Every premise of the paper's statement holds — and so does every premise of
the mech's CLOSED consistency twin `a_solve_eq_complete_var`, including the
mech-only `flex_apart` freshening invariant (vacuous at `Δρ = ∅`), the
subject well-formedness premise that made P6-Cs true, and the subtyping-side
tag EQUATION `Ψi , Ψa = Ψ'`.  The subtyping premise is `Sub-ForallL`
instantiating `β := ⟨⟩`, then `Sub-Check`; the refinement is a mono paint
refining itself; the precision is `P-Forall` over the identity.

The algorithm is then FORCED: a `∀` is not `guarded`, so the only solve rule
with a `∀` input skeleton is `SolS-ForallL`; its body `β→β ≼[TC] α̂` can only
go `SolS-Check` + `SolE-FlexR`, giving `P_a = ∀β. α̂`.  The precision
obligation `θ_a(∀β.α̂) ⊑ᵖ ∀^ε β.(β→β)` reduces to `⟨⟩ ⊑ᵖ β` — no rule.  The
refutation holds for **every** output metasubstitution `θ_a : Θ₀ ⊑ Θ` (the
file proves the general fact `mono_paint_ppre_target_ftv`: a mono-paint
subject is never precise to a target mentioning a variable outside Θ), so it
is not an artefact of the mech's `θ_a := θ` strengthening.

### Why the 2026-07-25 resolution does not apply

That resolution (entry above) rules the bad configuration — a raw Θ₀-flexible
payload facing a ρ-substituted part of `ψa` — UNREACHABLE, because `LE-FlexR`
freshens a flexible counterpart at a compound subject.  Two independent gaps
at the subtyping level:

1. **ρ is created by the lemma's own induction, not by constraint
   collection.**  The paper's ForallL case sets `ρ_b = ρ ∘ [ψ_b/β]` starting
   from `ρ = id`; so the recursive call sees `ψa = β→β` with `β` ρ-substituted
   — i.e. the induction manufactures the "unreachable" premise set out of
   innocent inputs.  Any `flex_apart`-style invariant stated at the CURRENT
   `ψa` is destroyed by that descent (`Δρ := Δρ ∪ {β}` while `P₀` is not
   decomposed), so it cannot be maintained.
2. **The raw flexible payload does not come through `LE-FlexR` at all.**  It
   comes from `LS-Var` — and `a_looksub` (fig:constraint-collection) has NO
   FlexR rule, so nothing freshens `α̂` on the subtyping route.
3. The paper's own side condition ("for every rigid variable in `ψa`
   substituted by ρ, `P_i` has the same rigid variable in the same position",
   :1730) is SATISFIED all the way down: at the recursive call `ψa = β→β`,
   `ρ_b` substitutes `β`, and `P_i = β→β` does have `β` in exactly those
   positions.

### What a repair has to do (for the authors)

The failing configuration is "the accumulated input skeleton is a `∀` while
the constraint payload is a raw flexible whose θ-image is fixed before the
`∀`'s binder exists".  Either

- (a) exclude it by an invariant that is stable under the ForallL descent —
  it must forbid a raw Θ₀-flexible payload facing ANY tagged `ψa` (not just a
  Δρ-dirty one), since a tagged `ψa` will become Δρ-dirty one ForallL step
  later — together with a reachability argument covering the `LS-Var` route;
  or
- (b) accept that the ALGORITHM is incomplete here and change it (e.g. freshen
  the flexible payload when solving under a `∀` binder, mirroring what
  `LE-FlexR` does at arrow nodes); or
- (c) restrict the declarative guesses `ψa` that the completeness statement
  quantifies over.

Nothing in the mechanization is retracted by this entry: P5, P6-Cv and P6-Cs
are unaffected (they have no ForallL, so ρ never grows there).

### Addendum (2026-07-28, after re-reading paper + implementation): root cause is `SolE-FlexR`; proposed fix = keep the non-flexible side

Verified against all three witnesses:

* **Paper** (fig:constraint-solving, full-algo-spec.tex:1371): `SolE-FlexR`
  is `nonflex{P} ⊢ solveeq{P}{α̂}{α̂}` — context-free, keeps the flexible,
  discards `P`.  The consistency -var proof's Arrow case says "*We assume
  P₀ = P₀,₁→P₀,₂*" (consistency-proofs.tex:1421) — the flexible-P₀ subcase
  is silently absent, and the leaf cases dispatch it with one sentence
  ("use SolEqFlexL or SolEqFlexR", :1272) with no precision argument.  The
  missing subcase is exactly where the subtyping ForallL descent lands.
* **Implementation** (type.ml): `solve_eq`'s `| _, (MFlex _ as alpha) ->
  end_rule alpha` and `solve_sub`'s ForallL/Check chain reproduce the mech
  behaviour line-for-line; `Pa = ∀β.α̂` on the witness.  The `(β,γ)` pairs
  LE-FlexR puts into ξ are consumed by `look` only to propagate the KIND
  (`BMFlex (γ, None, k)`) — no link constraint — so the mech's unlinked
  fresh flexible is a faithful encoding.  `LS-Var` passes the raw payload;
  the sub route has no freshening anywhere.
* **Mech**: `cex_p6sv_forall_flex.v` (Qed).

**Why the failure is forced.**  `SolE-FlexR` is the ONLY solve rule in
which the payload REPLACES a structured subject (`SolE-Var`/`FlexL`/
`VacuousR` all keep the subject; every other rule is a congruence or a
ghost step).  Under a `SolS-ForallL` descent the subject's body mentions
the locally-opened rigid `β`; replacing it by `α̂` commits the skeleton to
"whatever monotype α̂ becomes", and no future solution of `α̂` can mention
`β` (it is bound outside `α̂`'s scope) — the accumulated information
`β→β`, which an earlier eq-constraint had established and which the
declarative `ψa` retains, is unrecoverable.  Freshening the payload (the
LE-FlexR treatment) does NOT help: a fresh `γ̂ ∈ Ξ` is equally bound
outside the binder.  The eq route never hits this because CONSISTENCY (no
ForallL) pins `ψa` mono against a flexible counterpart; only the sub
route, where the declarative side may instantiate a `∀` down to the
flexible's mono image, exposes it.

**Proposed fix (one rule): flip `SolE-FlexR`'s output —**

```
nonflex{P}  ⊢  solveeq{P}{α̂}  ⤳  P        (was: ⤳ α̂)
```

(and correspondingly `end_rule p` in type.ml's `solve_eq`.)  Arguments:

1. *Completeness*: in every flex-payload case of the -var lemmas the
   refinement premise pins `θα̂` mono ⇒ `Q` mono-ish ⇒ no tag of `ψa` is
   solved by this constraint (`Ψa = ∅`), so the required conclusion
   `θ Pa ⊑ᵖ[Ψi ∪ Ψa] ψa` with `Pa := Pi` IS the precision premise.  On
   the counterexample the fixed algorithm yields `Pa = ∀β.β→β` and the
   needed precision is literally the cex's own `Hpre`.
2. *Soundness*: keep-subject-discard-payload is the existing `SolE-Var`
   pattern; the discarded `α̂`-constraint is re-established by the main
   subtyping run on the committed skeleton (unchanged discipline).  On
   the witness the recheck goes `∀β.β→β ⩽ α̂` → flex split
   `α̂ := β̂₁→β̂₂` → instantiate `β := β̂₁` — accepts, matching the
   declarative run.
3. *Old behaviour never load-bearing*: the two mech sites that USED
   keep-`α̂` (P6-Cv's flexible-P₀ chain, P6-Cs's LE-FlexR row) both have
   `ψa` pinned mono there, and close via the premise under keep-`P` as
   well — more simply.  In particular the mech-only `flex_apart` premise
   of P6-Cv (and the whole 2026-07-25 "unreachable-configuration"
   resolution, incl. `cex_p6_flex_counterpart`'s isolated falsity) exists
   ONLY to protect keep-`α̂`; under the flip it can be dropped, making
   P6-Cv premise-faithful to the paper.
4. *No alternative*: a statement-side premise cannot exclude the
   configuration (the top-level instance is reachable and declaratively
   solvable — e.g. `(fun x y -> y x) (id0 ids) useMono` puts a raw
   λ-bound flexible opposite `id0`'s result while `ids` forces the
   ∀-instantiation); restricting the declarative side would reject
   standard impredicative programs; freshening fails on scope as above.

Mech impact if adopted: rule flip in algo/def_extra.v (full algo
rebuild); ~13 construction sites (all in prop_look_complete*.v, get
SIMPLER); one changed case in each induction over `a_solve_eq`
(prop_solve_sub, prop_decorate_sub/key, prop_sub_sound,
prop_look_complete utility lemmas, test_unify_regression); plus a small
new "mono-ish target solves no tags" lemma for `ad_pat_sub_g`.

### Correction (2026-07-28, after TESTING the implementation): the source-level reachability claims above were WRONG; the composed pipeline shields the SolE-FlexR site; statement-side fix is back on the table; NEW independent impl crash found

Ran the built artifact (`met.exe`) on the constructed programs.  Three
results, two of which refute my own earlier end-to-end claims:

1. `(fun x y -> y x) (id0 ids) useMono` — **ACCEPTED** (rc=0).  The
   claim above that this exhibits the failure is WRONG on two counts:
   (i) `I-App` pre-shapes an applied λ's binder by
   `guess_mono(skeleton-of-argument)` — the expected type is an arrow of
   fresh flexibles, never a bare flexible; (ii) the skeleton pass
   (`PI-*`) ERASES top-level ∀s of argument skeletons to `∀◇(□→□)`
   (SI-ForallL + SI-UnivGhostR), so the eq-payload never carries the
   rigid `∀β.β→β` and a MONO instantiation suffices — which is exactly
   what the run does.
2. `h id0 3` with `h : ∀c.((∀b.b→b)→c)→c` — rejected, but CORRECTLY:
   checking against a guarded type is `LS-Check` = pure CONSISTENCY
   (shallow subtyping — no covariant descent under arrows in TC mode),
   so it is declaratively rejected too.  My "FN-mode arrow" reading of
   that shape was wrong.
3. **NEW BUG** — `k : ∀a. list a → a`, `args : list (∀b.b→b)`,
   `let g = fun f -> f (k args)` (f unannotated): the implementation
   **CRASHES** with `Failure("broom_flex_poly: should not happen")`
   (type.ml:1048 — `sub_flex` pops a `Marker`/`Lock` while brooming the
   bare flexible `f` against a Fun-mode whose argument skeleton carries
   the manifest rigid `∀b.b→b`, kept by the eq-solve under the `list`
   constructor, which skeleton erasure does NOT strip).  The annotated
   twin `fun (f : (int→int)→int) -> f (k args)` is ACCEPTED.  Whether
   the unannotated program is declaratively typeable turns on whether
   the declarative skeleton judgment may return a lazy/ghosted skeleton
   for `k args` (if yes — which the ghost rules suggest — this is a real
   completeness failure of the composed algorithm, through the
   flex-broom/mono-assign wall, NOT through SolE-FlexR).  Either way the
   assertion failure is an artifact bug to report.

CONSEQUENCE FOR THE FIX.  The pipeline appears to maintain exactly the
invariants that keep the SolE-FlexR configuration out of real runs:
FN-mode eq-payloads are skeletons with ghost-erased top-level ∀s;
TC-mode collapses to consistency (where a flexible payload pins
everything mono — the closed P6-Cv/P6-Cs territory); bare-flexible
expected types arise only from inference-mode λs, and routes combining
them with manifest-∀ payloads hit the flex-mono wall earlier (finding
3).  So the -Sv LEMMA as stated remains FALSE (the mech counterexample
stands), but the repair should likely be STATEMENT-SIDE after all:
strengthen P6-Sv's premises with the reachability invariant — a
candidate formulation: "every tag in Ψi was solved by a GHOST (∀◇/fill)
step of the precision derivation, not by a rigid quantifier of Pi,
whenever some constraint payload is a raw flexible" — equivalently,
rigid top-level ∀-spines in Pi and raw-flexible payloads for the same
look are mutually exclusive.  The exact form must be read off P6-Ss's
call sites and proved supplied by the pipeline (P7).  The SolE-FlexR
flip remains sound and uniformizing but is no longer forced; it would
not fix finding 3 (different wall).  Decision deferred to the authors.

## IMPLEMENTATION BUG (report to WT) — `broom_flex_poly: should not happen` assertion failure on a 5-line program (2026-07-28)

- Where: `paper/artifact/implementation/lib/type.ml:1048` (`sub_flex`, the
  flexible-variable broom walk: `| Marker | Lock _ -> failwith
  "broom_flex_poly: should not happen"`).
- Witness (benchmark vocabulary; crashes with
  `Fatal error: exception Failure("broom_flex_poly: should not happen")`):

  ```text
  type list a = Nil | Cons of a, list a

  val k    : forall a . list a -> a
  val args : list (forall b . b -> b)

  let g = fun f -> f (k args)
  ```

  The annotated twin `let g2 = fun (f : (int -> int) -> int) -> f (k args)`
  is ACCEPTED (rc=0).
- Mechanism: the skeleton pass keeps the manifest `∀b.b→b` when it sits
  UNDER a constructor (`list`) — ghost erasure strips only top-level ∀s of
  the argument type — so `k`'s eq-solve yields `a := ∀b.b→b` and the
  skeleton of `k args` has a rigid top-level ∀.  `f` is an inference-mode
  λ-binder, i.e. a BARE flexible; inferring `f` against the Fun-mode whose
  payload is that poly skeleton enters `sub_flex` (SI-FlexMono), whose
  context walk pops a `Marker`/`Lock` before resolving — a state the code
  asserts unreachable.
- Status — **ROBUSTNESS BUG ONLY (author decision 2026-07-28: the program
  should be REJECTED; the impl must reject cleanly instead of crashing).**
  The lazy-skeleton worry raised earlier is unfounded — the declarative
  side rejects it too, and the mech rules show why: the skeleton of `args`
  is derived from its type by SK-checking against □, whose Check case is
  CONSISTENCY against the fill — and consistency has NO rule for a
  ∀-subject against a hole or ∀◇ TARGET (only `ad_pat_consis__hole` with
  the hole as SUBJECT), so the inner `∀b.b→b` survives into every
  derivable skeleton; `k`'s instantiation must be consistent with it, so
  `k args`'s skeleton is forced poly; and the declarative app rule's
  domain premise is consistency `τ_dom ∼ skel(arg)`, mono vs ∀ — no rule.
  Hence rejection is forced declaratively; no completeness gap here, and
  the flex-mono wall is the intended design.


## GAP (proof-step; statement TRUE) — `complete-constraint-collection-solving-var`'s UnivGhostLG case omits the `P_i = □` subcase (2026-07-28)

- Where: subtyping-proofs.tex:2196, case `UnivGhostLG` of
  `lemma:complete-constraint-collection-solving-var`.  Mech: the `□` row of
  the `univ_ghost_lg` case in `frost/algo/prop_look_complete_sub_var.v`
  (now proved).
- The paper writes "We know that `P_i` must have a top-level `∀◇`", reading
  the precision premise `Δ|Θ ⊢ precise[Ψi]{θP_i}{∀◈ψ'}` as if only
  `P-UnivGhostKeep` — whose subject is `∀◇P` — could target a `∀◈`.  But
  **`P-Ghost` is target-agnostic**: `□ ⊑ᵖ[·] ψ` holds for ANY `ψ` (given its
  Δ-disjointness side condition), so a hole input skeleton is precise to a
  `∀◈` as well, and the subcase is real.
- Not a statement problem: the row goes through.  Nothing is decomposed (a
  `□` input stays `□`), so the induction hypothesis's own solve is the one
  needed; only its precision must be lifted back under the ghost.  In the
  mech that lift is `ad_ppre_lift_topholeg`, which needs (i) the shape of a
  `□`-input solve output (`a_solve_sub_hole_output`: `□` or `∀◇B`), (ii)
  stripping a `∀◇` from the subject against a guarded guess
  (`ad_ppre_tophole_strip`, whose FILL/KEEP rows die on guardedness and
  whose flexible-target row recurses through the definition), and (iii)
  guardedness of the guess's erasure, transported along ρ by
  `uskl_rho_guarded_erase`.
- **Corroboration (checked 2026-07-28, and it is decisive): the same
  authors handle `P_i = □` FIRST in the IDENTICAL situation on the
  consistency side.**  `complete-consistency-cc-solving-var`'s case
  `UnivGhostG` (consistency-proofs.tex:1477-1516) has exactly this shape —
  `ψ_a = ∀◈ψ'`, a dotted universal ghost on the guess — and its subcase
  list is:
    1. `P_i = □` — "IH on refa and refb with input `□` … our goal follows
       from SolEq-GhostL and choosing `P_a = ∀◇P_0'`", i.e. precisely the
       row the mech proves (nothing decomposed, the IH's own solve reused);
    2. `P_i = ∀◇P_i'`;
    3. "the remaining non-flexible shapes are impossible by inversion on
       the precision premise; the flexible case follows from SolEq-FlexL".
  Were there an invariant forcing a `∀◇` input skeleton opposite a dotted
  ghost, subcase 1 would be dead and would have been listed as impossible
  (as the same proof does list `Ghost`, `UnivGhost`, `UnivGhost1` and
  `UnivGhost2`).  It is not; so the subtyping side's compressed write-up
  ("Similar to the previous case of ForallL … It is simpler …") simply
  dropped it.
- To be fair to the paper's phrasing, its claim is ALMOST right: precision
  does force the input skeleton to be GHOSTLY at a `∀◈` guess — the only
  live shapes are `□` and `∀◇P_i'` (unit / var / arrow / ∀ are refuted, in
  the mech by `ad_ppre_guarded_topholeg_absurd`).  It named one of the two
  ghost shapes.
- Side note on the same case: the paper also provides for a FLEXIBLE `P_i`
  ("the flexible case follows from SolEq-FlexL").  In the mech that case is
  VACUOUS — `θP_i` is then a monotype painting, and
  `ad_ppre_mono_paint_topholeg_absurd` (already needed by P6-Cv) shows no
  painting is precise to a dotted ghost.  Harmless over-provision, recorded
  only so the discrepancy is not re-investigated.

## ~~GAP~~ RESOLVED BY THE AUTHORS (2026-07-29) — `lemma:complete-constraint-collection-solving` (P6-Ss), ForallR case: \lslab{ForallR} does NOT need `β ∉ ftv 𝒞`; scope is checked SEPARATELY at the use site.  Reclassified to a MECH-ENCODING question

- Where: subtyping-proofs.tex:2412 (the ForallR case of P6-Ss); the rule is
  full-algo-spec.tex:1049.
- **The rule lets `𝒞` escape the binder's scope.**  \lslab{ForallR} reads

  ```
        looksub[TC] α A B 𝒞 [Ξ]
    ────────────────────────────────
      looksub[TC] α A (∀β.B) 𝒞 [Ξ]
  ```

  Under the Barendregt convention the premise's `B` has β free, so the
  premise's `𝒞` may mention β — while β is BOUND in the conclusion's
  `∀β.B`.  For the rule to be well-scoped it needs `β ∉ ftv 𝒞` (and
  `β ∉ dom Ξ`).  A locally-nameless encoding makes this explicit: the
  mechanized `a_looksub__forall_r` is cofinite in β with the SAME `Ξ ⨾ 𝒞`,
  which IS that side condition.
- **The proof does not supply it.**  The ForallR case applies
  \lslab{ForallR} to a single IH instance ("By \lslab{ForallR} on \refc")
  and then establishes β-freshness only for `P_a` — "by \refh, we have
  β∉ftv(θ_a P_a), and thus β∉ftv(P_a)" — never for `𝒞` or `Ξ_c`.
- **The gap is real, not vacuous.**  With `A = ⟨⟩→α` and `B = ⟨⟩→β`,
  \lslab{Arrow} then \lslab{Var} collect `𝒞 = [ ≼ β ]`, and \lslab{ForallR}
  cannot fire.  Completeness therefore has to SHOW that configuration
  unreachable.  On the consistency side that is exactly what the invariant
  `ftv 𝒞 ⊆ ftv ψ_a ∪ dom Ξ_c ∪ dom θ ∪ def_ftv Θ` does (ψ_a is Θ-scoped,
  hence β-free); the mechanized P6-Cs carries it as a conclusion.
- Note the consistency route does NOT transport verbatim: it comes from the
  target-ftv bound for consistency, whose ForallInh opens with a fresh
  VARIABLE, whereas Sub-ForallL instantiates with a GUESS whose only bound
  is `ftv ψ_b ⊆ dom Θ`.  The subtyping proof needs the bound tied to `ψ_a`
  through the PRECISION and REFINEMENT premises instead.
- **\lslab{ForallL} is NOT affected — the two rules bind on opposite sides.**
  Constraints carry TARGET subterms (`ftv 𝒞 ⊆ ftv P' ∪ dom Ξ`,
  `a_looksub_ftv`).  \lslab{ForallL} binds β in the SUBJECT and leaves the
  target `P'` untouched, so β cannot reach `𝒞` at all and the side
  condition is discharged structurally, with no completeness argument;
  likewise for `Ξ`, whose entries are freshly generated by \lslab{FlexR}.
  \lslab{ForallR} binds β in the TARGET, and the premise's target is
  `B[β]`, so the same bound ADMITS β.  The obligation is ForallR-only.
- **RESOLUTION (WT, 2026-07-29).**  *"look 不管 scoping — look 完另一个单独的
  wellformedness 检查了"*: constraint collection is deliberately
  scoping-AGNOSTIC.  The scope check is the SEPARATE premise at the use
  site — the extract rule's `\Theta_0,\Xi \vdash P_1` (full-algo-spec, the
  `[P_0] \vdash^n_m \forall\alpha.P \leqslant Q \dashv \Theta_1` rule) — which
  rejects an instantiation candidate that escaped its binder.  So
  \lslab{ForallR} carries NO `β ∉ ftv 𝒞` obligation and the completeness
  proof owes nothing: this is NOT a paper gap.  The entry stays for the
  record and because it leaves a MECH question behind.
- **What remains is a MECHANIZATION-ENCODING question — and it is settled:
  KEEP the cofinite rule.**  The locally nameless `a_looksub__forall_r` is
  cofinite in β with one `Ξ ⨾ 𝒞`, which *is* the side condition, so the mech
  rule is strictly narrower than the paper's.  That is not a defect:
  completeness of a NARROWER algorithm is a STRONGER theorem, and soundness
  is unaffected.  The only real question is whether the completeness proof
  can still discharge `β ∉ ftv 𝒞` — and it can, by re-acquiring the
  ψa-RELATIVE bound P6-Cs already carries as a conclusion,
  `ftv 𝒞 ⊆ ftv ψ_a ∪ dom Ξ_c ∪ dom θ ∪ def_ftv Θ` (β is fresh for all four).
  P6-Ss's statement dropped that conjunct; the ForallR row must put it back.
- **Why that route is available NOW but was not before.**  The bullet three
  up says P6-Cs's bound "does not transport, because \sublab{ForallL}
  instantiates with a GUESS bounded only by `ftv ψ_b ⊆ dom Θ`".  The
  ρ-generalized induction (next entry) DISSOLVES that objection: under ρ the
  lookup side never sees a guess at all — every \sublab{ForallL} opens with
  a fresh RIGID and the guess rides in ρ — so the collected constraints stay
  bounded by ψ_a exactly as on the consistency side.  ρ's own binders live
  in Δρ, and ForallR's β is a genuine context rigid, never a Δρ entry, so
  the bound still excludes it.  ⇒ ForallL and ForallR are fixed by the SAME
  change.
- ⚠️ **For the record: the two rule ENCODINGS are NOT literally equivalent**
  (checked, not assumed).  `SS-Var` is `Θ ⊢ₛ α̂ ≼[m] Q ⤳ α̂` — it DISCARDS
  the target — so a `𝒞` that mentions β can solve to a `P_1` that does not,
  and `\Theta_0,\Xi \vdash P_1` then lets it through.  The lax rule therefore
  admits derivations the cofinite one refuses.  This costs nothing here
  (narrower algorithm ⇒ stronger completeness claim), but it means "the wf
  check catches it anyway" is not by itself a proof of equivalence, and the
  exists-fresh relaxation should NOT be adopted on that basis.
- Mech status: P6-Ss is stated and its machinery is in
  `frost/algo/prop_look_complete_sub_cstr.v`; 8 of the 12 induction cases
  are closed.  The ForallR row is the one this entry concerns; P6-Ss's
  ForallL row is blocked on something else entirely (see the next entry).

## GAP (proof-step, 2026-07-29) — `lemma:complete-constraint-collection-solving` (P6-Ss), ForallL case: the IH instance needs `θψ_b = ψ_b`, which fails even for legitimate θ; no side condition on θ repairs the step — the statement is believed TRUE via a ρ-generalized induction

- Where: subtyping-proofs.tex:2600–2643 (the \sublab{ForallL} case of P6-Ss).
  Machine-checked evidence: `frost/algo/cex/cex_p6ss_inc_compat.v`.
- **The step.**  The rule's premise is
  `⊢ ((θ S')[ψ_a/α])[ψ_b/β] ⩽ Q`, and the proof rewrites it (\refe) as
  `⊢ ((θ S')[ψ_b/β])[ψ_a/α] ⩽ Q`, then applies the IH with
  `S := S'[ψ_b/β]` and `P := P'[⌊ψ_b⌋/β]` (\reff).  For the IH's subject —
  which by the lemma's own statement is `(θ S)[ψ_a/α]` — to BE \refe, one
  needs

  ```
      θ (S'[ψ_b/β])  =  (θ S')[ψ_b/β] ,     i.e.     θ ψ_b = ψ_b .
  ```

  The paper justifies \refe by "capture-avoiding substitution and freshness
  conditions", which covers the α/β commutation but NOT the θ/ψ_b one.
  Nothing gives `θψ_b = ψ_b`: `ψ_b`'s only constraint is `Θ ⊢ ⌊ψ_b⌋`, so
  `ftv ψ_b ⊆ dom Θ`, and a Θ-scoped guess may mention `dom θ` variables.
  Nor can `ψ_b` be re-based below θ: θ's images are MONOTYPES while `ψ_b`
  is a general tagged skeleton (impredicative instantiation is the point of
  the rule), so `ψ_b` has no θ-pre-image in general.
- **No side condition on θ rescues the step** (this bullet went through two
  corrections, both machine-checked, before converging):
  1. Barendregt disjointness `dom θ ∩ dom Θ = ∅` is UNSATISFIABLE at
     identity metasubstitutions — their flexible entries are all PRESERVED
     in the target (algorithmic.tex:135–140, "our algorithms always give
     identity metasubstitutions"), so `dom ι ⊆ dom Θ`
     (`id_inc_dom_overlap`).
  2. Syntactic compatibility `∀ α̂ ∈ dom θ ∩ dom Θ, θα̂ = α̂` EXCLUDES a
     legitimate θ: at `Θ = [α̂ := ⟨⟩]` the θ with `θα̂ = ⟨⟩` substitutes a
     DEFINED survivor's definition — exactly what "preserved … but possibly
     with more monomorphic information (e.g., from α̂ to α̂ := ⟨⟩)"
     licenses — and it is inc-EQUIVALENT to ι
     (`def_subst_theta_is_legit`).
  3. The strongest defensible invariant is therefore SEMANTIC:
     `α̂ ∈ dom Θ ⟹ Θ ⊢ θα̂ ≡ α̂` (for an UNDEFINED survivor ≡ collapses to
     `θα̂ = α̂`; for a defined one it licenses the definition).  It still
     does NOT give the syntactic `θψ_b = ψ_b` the IH needs — the
     definition-substituting θ of point 2 satisfies it and still moves a
     `ψ_b` that mentions α̂.  The written step holds essentially only at
     ι-like θ, while the lemma quantifies over general θ.
- **Mech repair (decided; keeps the paper's statement UNCHANGED).**
  Restructure the induction as P6-Sv's already is: generalize the motive
  over an accumulated rigid substitution ρ.  Each ForallL opens with a
  FRESH RIGID β and absorbs its guess into ρ (`ρ ∘ [ψ_b/β]`,
  `uskl_rho_subst`), so the subject is `ρ((θS)[ψ_a/α])` with β ∉ dom θ and
  θ's images β-free — the θ/ψ_b commutation never arises, for ANY θ.  The
  theorem is the ρ = identity instance.  The `P = α` leaf then calls
  `lemma:…-var` (P6-Sv) at the ACCUMULATED ρ — its general-ρ interface,
  which the paper's own "with the identity substitution" leaf never
  exercises.  The paper could adopt the same restructuring; alternatively
  its authors may prefer to note the lemma is only ever instantiated at
  ι-like θ (where the written step is sound) — but then the ForallL
  recursion must be checked to preserve ι-likeness, which is the same
  obligation in different clothes.
- **Independent definitional observation** (for the authors; surfaced by
  the same review).  The figure's flex rule for `inc[θ]{Θ,α̂}{Θ'}`
  constrains the image by nothing but `Θ' ⊢ τ`, so it formally admits a θ
  that "solves" α̂ to ⟨⟩ while Θ' keeps the SAME α̂ UNDEFINED —
  `[(α̂,⟨⟩)] ∷ [α̂] ⊑ [α̂]` is derivable (`inc_moves_survivor`) — junk
  under the information-increase reading (the target does not refine such
  a θ's claim).  The invariant of point 3 above
  (`α̂ ∈ dom Θ' ⟹ Θ' ⊢ θα̂ ≡ α̂`) is the side condition that excludes it
  while keeping the legitimate definition-substituting θ.  The mech keeps
  `a_inc` faithful to the figure (the ρ-repair needs no such condition);
  whether the paper's definition should carry it is the authors' call.
- **Scope of the ρ-repair, measured (2026-07-29).**  The Check row of P6-Ss
  hands its WHOLE subject to P6-Cs (`a_lookeq_solve_complete`), and a
  ForallL can sit above a Check — so **P6-Cs must be ρ-generalized too**.
  That is threading, not new theory: P6-Cv
  (`a_solve_eq_complete_var_gen`, prop_look_complete_var.v:505) ALREADY
  takes `uskl_rho NM Θ Δρ Ψρ ψsub ψa` and the whole `uskl_rho_*_l_inv`
  inversion kit exists, so P6-Cs's rows invert ρ per subject shape exactly
  as P6-Cv's do, its measure (`size R' + size P0`, on the ρ-FREE ideal
  subject) is unaffected, and its leaf passes the real ρ down instead of
  `urho__refl`.  P6-Cs's own ∀ rows open with fresh VARIABLES, so ρ never
  grows inside it.
- **Bookkeeping done en route** (2026-07-29, committed):
  - The scope premise `ftv S ⊆ {α} ∪ dom Θ0` was relaxed to
    `ftv S ⊆ {α} ∪ dom Θ0 ∪ dom Θ` with the dual conclusion
    `α0 ∈ dom θ_c ⇒ α0 ∉ {α} ∪ dom Θ0 ∪ dom Θ` strengthened to match, in
    both `prop_look_complete_cstr.v` (P6-Cs, re-`Qed`ed) and
    `prop_look_complete_sub_cstr.v`.  Kept: harmless, and the Arrow row
    wants the strengthened conclusion.
  - The reverse direction of
    `lemma:constraint-collection-stable-substitution` is mechanized as
    `a_looksub_subst_stable_rev` (prop_looksub.v §4b, `Qed`, axiom-free).
    The ρ-route does not need it (the looksub side stays on var-opened
    subjects), but it is the lemma the PAPER's own proof route ends with,
    and it is true and kept.
  - `sub_shield` now carries Δρ (the current statement instantiates it at
    `empty`, so nothing else moved), with `sub_shield_add_fresh` /
    `_weaken_tvar` — Sub-ForallL grows Δρ by a fresh β while ψa does NOT
    move, so neither `fastep_all_r` nor `fsh_all_r` applies and the Δρ
    quantifier is built into the definition instead (as the `ss_walk` one
    already is).
  - `ad_partial_precise_delta_shrink_fresh` (`Qed`) — the mirror of
    `ad_partial_precise_delta_weaken_fresh`: Sub-ForallL hands the IH the
    precision premise at `add β Δ` (β joins Δρ, and `Δρ ⊆ Δ`) and must
    return the conclusion at plain Δ.
