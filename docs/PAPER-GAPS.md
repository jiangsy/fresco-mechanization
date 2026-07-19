# Paper gaps and paper-flagged notes (re-mech)

Canonical registry for everything found while mechanizing that the paper's
authors should see.  Ground rule (CLAUDE.md): paper definitions and lemma
statements are never changed; a broken proof STEP gets a repair here + a
`[paper-gap]` comment at the lemma; a genuinely FALSE statement (with a
counter-example) stops the work and is flagged to the user.

Each entry: status ∈ {GAP (confirmed proof-step problem, repaired),
PROSE-COMPLETION (figure rule completed from the paper's own prose),
WATCH (tension spotted, not yet confirmed to matter), FALSE (statement
refuted — one so far, see below)}.

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
