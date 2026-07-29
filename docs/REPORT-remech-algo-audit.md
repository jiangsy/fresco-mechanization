# Audit: algorithmic-system mech encoding vs paper vs reference implementation

*2026-07-18, branch `re-mech` (HEAD 24fd17d).  Read-only audit — no mech file was
changed.  Three witnesses compared judgment-by-judgment:*

- **Mech**: `frost/algo/def_extra.v`, `def_meta.v`, `def_decorated.v`,
  `def_decl_algo.v`, `def_decl_algo_sub.v` (+ shared AST in `def_ott.v`).
- **Paper**: `sections/algorithmic.tex`, `sections/appendices/full-algo-spec.tex`
  (+ `decorated-algosub.tex`, `consistency-proofs.tex`, `subtyping-proofs.tex`,
  `full-decl-spec.tex`), macros resolved via `macro.tex`
  (`\aconsis`: subject left of `∼`; two-slot form = output-suppressed per
  full-algo-spec.tex:1440-1442).
- **Impl**: `paper/artifact/implementation/lib/type.ml` (+ `syntax.ml`,
  `context.ml`).  Third witness, **not an oracle** (known bugs recorded below).

Classification: findings already in `PAPER-GAPS.md` / `WF-SIDE-CONDITIONS.md` /
`DESIGN-subtyping.md` are cited as KNOWN; wf premises the paper states in prose
are DOCUMENTED-COMPLETIONS, not discrepancies; cofinite/LN encoding is never
flagged.

---

## Executive summary

**The mech is faithful to the paper across the overwhelming majority of the
algorithm.**  All 27 rules of the 3-way consistency/unifyvar/assignvar block
(including all five 2026-07-14 bug-fixes), all 8+11 look rules, all 9+12 solve
rules, all of splitting/pattern-typing/typing (a_split/a_pat/a_typing,
rule-for-rule including the suffix-kept-vs-dropped distinctions and the consis
subject/input orientations), the metasubstitution/increment layer (modulo the
documented semantic-middle deviation), and the decorated systems + `ad_*`
devices line up with the paper, with every previously documented
prose-completion confirmed in place and correctly registered.

**Five NEW mech-side findings (F1–F5)** surfaced, all in the *subtyping-adjacent*
judgments — exactly the greenfield area the subtyping milestone
(`DESIGN-subtyping.md`) is about to build on.  F1 is a probable
completeness-breaker; F2 is a proof-plumbing hazard for the decoration lemma;
F3–F5 are latent/registration items.  **Per the audit mandate, none was fixed.**

Also produced: five **new implementation-side divergences** (report-to-WT
grade, §4) and two **paper/doc hygiene notes** (§5).

---

## 1. New mech findings (not previously registered anywhere)

### F1 — `a_sub_flex__assign` loses the defined-subject (β̂ = α̂) case  ⚠ highest priority

`def_extra.v:840-846` (plain) and `def_decorated.v` `a_subtag_flex__assign`
(same shape).  The paper's Flex-Assign (full-algo-spec.tex:888-894) merges
`Θ₀,Ξ` and **re-enters the MAIN judgment with the substituted subject
`α̂[τ/β̂]`**; the impl does exactly that
(`add_bindings xi >> sub … (subst_var (MFlex alpha0) tau beta)`,
type.ml:1021-1027); and the paper's own soundness proof has an explicit
**α̂ = β̂ subcase** (subtyping-proofs.tex:1212-1221) — the walk reaching the
subject's own definition, whereupon the subject becomes the monotype τ (the
commented-out FlexMono-Def, full-algo-spec.tex:881-887, is "subsumed by below"
only under this reading).

The mech instead **continues the aux walk with the subject fixed at `α`**,
substituting only the input `P0`.  The in-file rationale (def_extra.v:824-828)
assumes `α̂ ≠ β̂` — an assumption **the rule does not premise**, and the exact
assumption already refuted once for `a_assign` (PAPER-GAPS "β̂ = α̂ IS
REACHABLE", regression `a_assign_succeeds_on_own_definition`).  Reachability
here: `a_sub__flex_mono` (:797-799) places **no undefinedness condition** on
the subject, so a *defined* flex subject enters the walk (e.g. `x : α̂` with
`α̂` already solved, FN mode; or Arrow's first consis premise defining a flex
var that is the second premise's subject).  When the walk pops the subject's
own definition via `__assign` with β = α, every context below is α-free, and
since **`Flex-Solve` is the walk's only terminal rule** and requires
`(α₀ ~ abind_flex_mono) ++ Θ₀` at the head, no derivation can complete —
**the mech relation is stuck where paper + impl succeed.**

Soundness is unaffected (strictly fewer derivations); completeness of flex
subtyping (DESIGN-subtyping P7, and anything P3 hardens around the current
rule shape) will hit this.  Candidate repairs: (a) follow the paper/impl —
merge `Ξ ++ Θ₀` and re-enter `a_sub` with the substituted subject (the stated
re-fire-FlexMono worry is answered by the impl: the defined entry is consumed,
so re-entry terminates); or (b) keep the aux walk but substitute the subject
slot too, adding a monotype-subject terminal rule — i.e. transplant the
`a_assign` fix.  Statement changes cascade into `a_subtag_flex` and the P3
soundness bundle, so decide **before** more of the flagship hardens.

### F2 — Check rule: plain and decorated twins encode the paper differently

Paper pins the consistency premise's **output** to `B` in *both* figures
(`\aconsis[B]{Θ₀}{A}{B}{Θ₁}`, full-algo-spec.tex:807;
`\aconsistag[B][Ψ]{Θ₀}{T}{B}{Θ₁}`, decorated-algosub.tex:57).  The decorated
mech follows the paper (`… T ≈ B ⊣ Θ1`, def_decorated.v:237); the plain mech
relaxed it to the output-suppressed `a_consis_chk Θ0 A B Θ1` = ∃Q
(def_extra.v:783-786) — an **unregistered deviation**, and the two twins now
disagree with each other.  The decoration lemma (paper
lemma:decorating-algorithmic-subtyping, phase P4) connects exactly these two
rules; at Check it must turn "some Q" into "Q = B".

Nuance: under the paper's external N-sort convention (full-decl-spec.tex:29-31
— at N = TY the metavariables range over *types*), `B` is an embedded `ptyp`,
hence ghost/hole-free, and the join output on a ghost-free input should equal
the input — so within the convention's domain the two readings coincide **via a
lemma that does not yet exist** ("consis output with ghost-free input is the
input").  Resolution options: harmonize the twins (pin both, or ∃Q both), or
bank that lemma before P4.  Either way, register the plain rule's ∃Q reading
in PAPER-GAPS.

### F3 — `a_lookeq__flex_r` fires on rigid-variable right-hand sides

`def_extra.v:309-313`.  Paper's LE-FlexR (full-algo-spec.tex:1112-1118)
restricts the RHS to the hatted `β̂`; the impl matches `MFlex` syntactically
(type.ml:561-566).  The mech RHS is `pskl_var_f β` — *any* variable — and the
look judgment is **context-free, so flexibility cannot even be stated**
(unlike `a_solve_eq`, which was given a Θ slot precisely for its FlexR check,
header comment def_extra.v:346-351).  Consequence: on a rigid-var RHS with
`α ∈ ftv P`, `P ≠ α`, the mech *additionally* derives a fabricated fresh
`eq(γ̂)` constraint — derivations paper + impl do not have.  Since the look
judgments currently have **zero lemmas** over them (DESIGN-subtyping §3), this
is the cheap moment to decide: thread Θ (as solve_eq did), or carry the
restriction as an external side condition on the look metatheory — and
register the choice.

### F4 — Three reversed suffix-block orders (inert today, same class as the fixed Assign-Depend reversal)

All three put a suffix block in the mirror order of paper + impl.  Every entry
involved is an undefined payload-free flex var, so the reversals are
semantically inert *until* a lemma consumes the block positionally (which is
exactly how the original `a_assign__depend` reversal became fatal —
PAPER-GAPS: "inert on its own but fatal for (1), whose premise context is
literally `Ξ ++ Θ0`"):

| site | mech | paper / impl |
| --- | --- | --- |
| `a_sub_flex__depend` def_extra.v:847-851 (and `a_subtag_flex__depend`) | head-cons `(β ~ flex) ++ Ξ` | suffix `β̂,Ξ` — β̂ at the Θ₀-adjacent end (full-algo-spec.tex:896-902); impl `xi @ [bind]` (type.ml:1031-1035); mech's own `a_assign__depend` tail-appends |
| `a_extract__solve` def_extra.v:468 | `Ξ ++ Ξ'` (look-vars newest) | `[Ξ,Ξ']` — guess-vars newest (full-algo-spec.tex:1002); impl conses onto xi (type.ml:96,717) |
| `a_guess_mono__arrow` def_extra.v:235 | `Ξ1 ++ Ξ2` (domain's vars newest) | `(β̄₁,β̄₂)` — codomain's newest (full-algo-spec.tex:488); impl accumulator agrees with paper |

Note `a_sub_flex__solve`'s premise context is literally `Ξ ++ …` (def_extra.v:836),
so the Depend reversal sits one lemma away from mattering.  Cheap to normalize
now; costly after the subtyping bundles quantify over these blocks.

### F5 — `a_wf_pskl` at explicit rule premises: an UNVALIDATED interpretive deviation (not a route-B item)

*(Reclassified after review — the initial audit framed this as a
registration gap under the external-wf discipline; that framing was wrong.
Route B licenses omitting the paper's PROSE wf conditions from rules.  It
does not license substituting a different judgment into an EXPLICIT
in-figure premise.)*

The paper's ForallL premise `Θ₀,Ξ ⊢ P₁` (full-algo-spec.tex:845) and the
ctx-wf entry premise `Θ ⊢ P` (:249-254) are in the figures, and the paper
states which judgment they denote: "All declarative judgements, **including
well-formedness**, … are naturally extended to algorithmic contexts"
(algorithmic.tex:155-160); "We omit well-formedness rules, where we simply
look up the definition of a flexible variable and check the well-formedness
of its definition" (full-algo-spec.tex:128-129).  I.e. the transplanted
declarative skeleton wf — with the Δ slot, ⊤-ghost guardedness, and empty-Δ
body discipline — which the mech has as `ad_wf_pskl` (def_decl_algo.v:51-71).

The mech instead uses the **scoping-only** `a_wf_pskl` (def_extra.v:113-131:
no Δ, ∀-vars into Θ, no ghost discipline — `∀α.⊤.(α→α)` passes) at both
premises (`a_wf_aenv__var`; `a_sub__forall_l` :814).  A different judgment at
a stated premise, under the follow-paper-proofs rule, needs validation or a
flag — currently it has neither.  What leans weak: the paper's own inline
comment on the premise ("% Needed because of rigid vars",
algorithmic.tex:946 — scoping intent) and the impl's `is_wf_`
(type.ml:50-63, scoping-only).  What leans strong: the paper's quoted text.
Open question either way: whether solve/extract outputs can legitimately be
strong-wf-violating (solve's GhostForall/ForallGhost rules move ⊤-ghosts
under quantifiers) — if yes, the STRONG premise would wrongly reject
reachable ForallL instances (a paper gap); if no, the weak and strong rule
versions coincide on reachable derivations.

**Resolution options**: (a) prove the bridging lemma "extract outputs on
strongly-wf inputs are strongly wf" and keep the weak premise with that
lemma as the recorded justification; or (b) switch the two premises to
`ad_wf_pskl` at Δ=∅ per the paper's literal text and check nothing
reachable breaks.  Confirm the intended reading with WT; register the
outcome in WF-SIDE-CONDITIONS.md.

Related registrations still pending (these ARE ordinary route-B items):
**`a_tags_sort` context-free** (def_decorated.v:96) — a legitimate factoring
(syntactic sort/tags + scope restored at call sites), but its scope half
goes through the weak `a_wf_pskl`, so it inherits the question above;
DESIGN-subtyping D3 prescribed its WF-SIDE-CONDITIONS entry, still unwritten.
And the un-encoded N-sort syntax convention on `ad_pat_sub`
(full-decl-spec.tex:29-31), which F2 shows is now proof-relevant.

---

## 2. Confirmed faithful (mech ↔ paper), by cluster

- **Syntax / contexts / wf / guessing**: grammar, `abind`/`aenv` (the
  `x:A`-vs-`x:P` two-constructor split is a documented AST encoding), `a_suffix`,
  `a_binds_tvar`, `a_wf_ptyp`, `a_wf_aenv` (Barendregt freshness + `mono_ptyp`
  completions documented in-file), skmod[TY]/skmod[SK] (including the SK/TC □
  *replacement*), `nonflex` head-level in all three witnesses, `a_flex_tvar` =
  dom-membership-as-flexible (the deliberate post-fix Flex-Flex-Id reading),
  `guess^TY` keeping ∀ with monotype-ness enforced downstream (the resolved
  Assign-SolveM convention), `guess^SK` identity.
- **Consistency / unifyvar / assignvar** (14+6+7(+1 split) constructors): all
  MATCH.  **All five 2026-07-14 fixes verified present**: (i) Assign-Assign
  consis premise over `Ξ ++ Θ0` (:567); (ii) no `α̂ ≠ β̂`, both slots
  substituted; (iii) Depend tail-append; (iv) hatted-subject `a_flex_tvar`
  premises on the conclusion contexts; (v) Flex-Flex-Id via `a_flex_tvar Θ0 α`.
  F-set threading, `mono_ptyp τ`, global β̄-freshness = the registered
  prose-completions.  `a_consis_chk` = the paper's output-suppressed
  abbreviation.
- **Look / solve / extract / subtyping**: all `a_looksub` (8) and remaining
  `a_lookeq` (10 of 11, cf. F3) rules MATCH; `a_solve_sub` (9 = paper's 10 via
  the Var/Flex merge, forced by the one-atom-sort AST) and `a_solve_eq` (12,
  FlexR's Θ-threading documented in-header) MATCH; `a_solve_cstr`,
  `a_extract`'s fused look∘solve∘guess structure MATCH; `a_sub`'s
  Infer/ForallR/UnivGhostR/FlexMono/Arrow/ForallL/Ghost/UnivGhostL MATCH with
  the expected documented completions (`uniq (Ξ ++ Θ0)` at ForallL = the
  commit-3729d25 freshness prose-completion; `a_suffix Ξ` at ForallR;
  Barendregt `β ∉ dom Θ1` on the walk's re-attachments);
  `a_sub_flex` Solve/Skip/SkipRigid MATCH (Assign and Depend: F1, F4).
  `a_split__flex`'s consistency reading of the paper's `unify{α̂}{β̂→γ̂}` = KNOWN
  ([paper-gap] in-file; forced — the input is an arrow).
- **Split / pattern / typing**: every constructor of
  `a_split`/`a_pat`/`a_typing` matches rule-for-rule, including: suffix Ξ
  *kept* in Abs/AbsAnno (both judgments) but *dropped* by the AbsCheck family
  (all three witnesses agree); the deliberate consis-orientation asymmetry
  (AbsAnno subject = annotation; AbsAnnoCheck subject = split domain); App's
  three-premise plumbing with the re-check output `A'` discarded; AbsCheck's
  ∀ᾱ prefix folded as `_step`/`_base` (documented encoding, mirrors
  `d_sd_typing`; net context effect identical); Anno not recursing into the
  term (paper prose point (2)).  **No `refresh` anywhere** — mech and impl both
  match the finalized paper.
- **Metasubstitution / increment**: `msubst_*` is the paper's simultaneous
  finite map (post-fix; PAPER-GAPS entry); compose direction correct for the
  paper's `κ ≡ ζ∘κ₁` convention; `a_inc__flex_def`'s wf/mono side-condition and
  `a_isub`'s entry-preservation conjunct = the two registered
  prose-completions; **the sole semantic deviation is exactly the documented
  one** — `a_inc__var`/`__var_skl` (and the `a_inc_equiv` mirrors) use
  `≡ᵗ`/`≡ˢ` middles, machine-checked both ways in
  `cex/cex_assign_optimal_syn_middle.v` against a verbatim copy of the paper
  rule.  `a_tyequiv` explicitizes a prose-only relation
  (full-algo-spec.tex:100-112 — the paper never gives rules);
  `a_pskl_tyequiv` is mech-only, acknowledged in optimality-cex.tex.
- **Decorated + `ad_*`**: `a_consistag` (incl. the repaired FlexR — the
  dotted-hole counterexample rule is gone; subject is `pskl_to_uskl P`),
  `a_subtag` (modulo F1/F2), all of tag solving, `ad_pat_consis`,
  `ad_refine_syn/_pskl`, `ad_pat_sub`, `ad_partial_precise` — MATCH or
  documented (context-free `a_tags_sort`; `uskl_ghost_free` stronger than
  dotted-ghost-free, equal on decorated ψ; Δ-only ∀-rules with the var rule's
  `Δ ∨ binds` disjunction; `ad_partial_precise__var`'s visibility completion).
  **Erasure check**: every decorated rule erases to its plain twin — the single
  exception is Check (F2).  `a_subtag_flex` as a separate mutual walk correctly
  resolves the paper's inherited-rules/decorated-proof presentation split (the
  DESIGN-subtyping WLOG hazard), and erases exactly to `a_sub_flex`.
- **Standing [WATCH] unchanged**: the external refinement presupposition on
  skeleton consistency (declarative.tex:2074) remains uncarried by
  `d_pat_consis`/`ad_pat_consis` — still unbitten; first suspect if a
  consistency lemma looks unprovable.

---

## 3. Implementation-only extensions (not divergences)

Effects (`TMod`, U-ModInh/UnivGhost3/ModSyn, Lock, `across`), datatypes
(`TCon`, U-Con, match/handle/do rules), kinds (`k' <<< k` guards), Marker
entries, let/seq, error paths, elaboration outputs.  All outside the
paper-core language; none affects the audit verdicts.

## 4. Implementation divergences (artifact notes — report to WT)

1. **KNOWN, still present**: `U-Flex-Flex-Assign` (type.ml:319-320) has its
   `join_sk` subject/input slots swapped vs the paper; `U-Assign-Assign`
   (:361-362) uses the correct order — internally inconsistent.  Argued-benign
   (mirror symmetry at Δ=∅ with discarded output); `a_consis_sym` still
   deferred.  (PAPER-GAPS has the full entry.)
2. **NEW — missing premise**: `sk_infer`'s PI-AbsAnno (type.ml:1217-1228)
   *discards the split domain* (`let* _, q = split_fun …`) and **omits the
   paper's `\aconsis{Θ1}{A}{P}{Θ2}` check entirely** — the annotation is never
   reconciled with the input skeleton's domain (contra
   full-algo-spec.tex:658-665 and prose point (3) at :700-701).  `finfer`'s
   I-AbsAnno does perform the join, so this is specific to skeleton inference.
3. **NEW — more slot swaps of the same family as (1)**: I-Freeze
   (`join_sk b a`: subject = checked A vs paper's subject = inferred B),
   I-AbsAnnoCheck (`join_sk a' a`: subject = annotation vs paper's subject =
   split domain — and inconsistent with the impl's own I-AbsAnno), and
   `split_fun`'s flex case (α̂ passed in the input slot; paper/mech put it in
   the subject slot).  Each is plausibly benign by the same mirror-symmetry
   argument, which remains argued-not-proved.
4. **NEW — checking a λ against a bare flex var errors**: `split_fun_check`
   (type.ml:1068-1079) has no `MFlex` case (`function_non_arr`), whereas the
   paper's AbsCheck split premise and mech's `a_split__flex` solve
   `α̂ := β̂→γ̂`.  Impl strictly more restrictive in checking mode.
5. **NEW — λ-variable bound to the join output**: in I-AbsAnno and
   I-AbsAnnoCheck the impl binds `x` to `join_sk`'s result rather than the
   annotation `A` (paper/mech: `x:A`, output suppressed).  Likely-benign
   precision improvement, but a rule-shape divergence.
6. Minor: `is_in_dom_` (context.ml:252-256) also accepts rigid `BType` entries
   where paper/mech require flexibility — unreachable at current call sites.
7. Consistent with the mech's optimality diagnosis: the impl performs the
   flex-migration-below-binders walk (U-Assign-Depend + U-Assign-SkipTmVar)
   that generates the counterexample; the ⊑ repair is spec-side only, impl
   untouched.

## 5. Paper / documentation hygiene

- **optimality-cex.tex**: accurate on the ⊑ repair (instance, ζ-witness, and
  provenance all match the mech's cex file), but (i) its `\input` at
  full-algo-spec.tex:1571 is **still commented out** — the compiled appendix
  states the refuted syntactic rules with only a LaTeX-comment warning; and
  (ii) it omits that `a_inc_equiv`'s var rules were repaired in tandem
  (PAPER-GAPS does record this).
- **PAPER-GAPS.md staleness**: the first Flex-Flex-Assign entry (:96-99) still
  describes the interim "2-way mutual, `a_assign` below the cycle" design; the
  current mech is the 3-way block (correctly described by the second entry).
  One-line touch-up.
- Paper typo (no action): Flex-SkipRigid's mode annotation `[\N][\M]` should be
  `FN M` like its siblings (full-algo-spec.tex:912); mech is uniform and right.

---

## 6. Recommended order of follow-ups (none performed — audit only)

1. **F1** — decide the Flex-Assign reading (merge-and-re-enter vs
   subject-substituting walk) *before* P3/P7 harden; transplant the
   `a_assign` β̂=α̂ regression test to `a_sub_flex`.
2. **F2** — harmonize the Check twins (or bank the "ghost-free input pins the
   join" lemma) before the P4 decoration lemma; register in PAPER-GAPS.
3. **F3** — pick the LE-FlexR flexibility mechanism (Θ-threading vs external
   condition) while the look metatheory is still empty.
4. **F4** — normalize the three suffix orders in one mechanical pass.
5. **F5** — write the two pending WF-SIDE-CONDITIONS entries (+ N-sort
   convention note).
6. §4 items — one consolidated note to WT (impl); §5 items — paper/doc
   touch-ups.
