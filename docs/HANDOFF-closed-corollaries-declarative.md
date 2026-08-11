Handover — Frost mechanization: state the CLOSED-PROGRAM COROLLARIES against
the PURELY DECLARATIVE system (`d_sd_typing` / `d_typing`), in BOTH
directions.

## STATE (2026-08-11, third pass)

⭐ **SOUNDNESS IS DONE.**  `a_typing_sound_infer` / `a_typing_sound_check`
(`frost/algo/typing/prop_closed.v`) now read the paper's own §declarative
system on the declarative side — `· ⊢ˢ[M] e ⦂ B` AND `· ⊢[M] e ⦂ B` — over a
declarative context.  `make coq` exit 0, admit-free, axiom-free, README.v
24/24 `Print Assumptions` closed.

⛔ **COMPLETENESS IS NOT DONE**, but it is now blocked by ONE thing, not two.

- **(B) tag hygiene — ✅ RESOLVED 2026-08-11.**  All four subtyping judgements
  (`d_sub`, `d_pat_sub`, `ad_pat_sub` and the fuel mirrors) read the paper's
  `fresh Ψ'` the same, GLOBAL way.  §(B) below records the repair, and its
  shape — collect the tags, then move them wholesale — is worth reusing.
- **(A) the leaf-valid datum — still open**, and independent of (B).

⚠️ What is left of (B)'s neighbourhood is now purely a FUEL question: the
`ad_pat_sub → ad_pat_sub_g` direction still has to be built, but the two
judgements no longer differ in hygiene.

## WHAT LANDED

**`frost/algo/typing/prop_conserv.v`** (new, ~1300 lines) — the conservativity
bridge the paper asserts and never states (`app:decl-in-algo-context`: *"it is
easy to extend them to algorithmic contexts Θ"*).  Registered in
`docs/PAPER-GAPS.md`.

| § | what |
|---|---|
| 0 | `denv_to_aenv` — a declarative context IS a flexible-free algorithmic one; `denv_to_aenv_no_flex_def` is what makes every FlexL/FlexR/FlexMono row vacuous |
| 0b | Δ is `atoms` on the `ad` side, `list atom` on the `d` side: related by membership (`delta_agree`), not converted |
| 1 | `a_tyequiv_denv_eq` — the appendix's four `Θ ⊢ A ≡ B` premises collapse to `=` |
| 2 | `a_wf_ptyp` / `a_wf_pskl` ⇄ `d_wf_ptyp` / `d_wf_pskl` |
| 3–4 | `ad_pat_consis` ⇄ `d_pat_consis` (SK) and ⇄ `d_consis` (TY) |
| 5 | `ad_refine_syn` ⇄ `d_refine_syn` |
| 6 | the ForallL instantiation across the sorts (`d_wf_uskl_of_a_wf_pskl`, the ghost-free retraction `uskl_to_utyp`, `d_tags_uskl_to_utyp`, `d_wf_utyp_of_d_wf_uskl`) |
| 7–8 | `ad_pat_sub` ⇄ `d_pat_sub` (SK) and → `d_sub` (TY) |
| 9–10 | `ad_pat` → `d_pat`, `ad_sd_typing` → `d_sd_typing` |
| 11 | ⭐ CLOSING the run's output context: `ad_sd_typing_close_suffix` |
| 12 | the completeness direction: how far it reaches and where it stops |

Two conversions were added to `frost/coercions.v` (`utyp_to_uskl` — the sort
inclusion — and its retraction `uskl_to_utyp`), with their facts in
`frost/prop_coercions.v`.  The `msubst_btyp` facts §11 needs are in
prop_conserv.v: `msubst_btyp` was DEFINED in `algo/def_meta.v` and used by no
proof anywhere, so that section is its only home.

**The closing (§11) is the step the paper does not mention.**  Soundness
delivers its declarative derivation at the run's OUTPUT context Θ₁, which
normally still holds flexibles (`fun x -> x` at `·` gives `Θ₁ = α̂` and answer
`α̂ → α̂`), and the bridge needs a flexible-FREE context.  Since the run starts
at `·`, Θ₁ is a pure suffix, so every entry is solvable into its own tail
(`solves_flex_of_wf_head`); peeling it with `ad_sd_typing_subst_mid` and
accumulating the solutions BUILDS a `ζ ∷ Θ₁ ⊑ ·` together with the derivation
at `·`.  Building it (rather than quantifying over one) is what keeps the
corollary non-vacuous.

The corollaries also lost their existential `Bt`: at `TI` the answer's
colouring is forced to `syn{A}` and at `TC` to `inh{A}`, so the statement now
names the type directly.

## WHAT BLOCKS COMPLETENESS

Completeness needs the OTHER direction, `d_sd_typing · e B → ad_sd_typing · e B`.

### (A) The leaf-valid datum — ⭕ R0 IS NOW SETTLED, and the answer is "no"

`ad_pat` / `ad_sd_typing` embed `ad_pat_sub_v`, whose consistency leaves carry
`Θ ⨟ ∅ ⊢ᵣₚᵃᵈ ⌊R⌋ˢ ⊳ ⌊Q⌋`; `d_pat` / `d_sd_typing` embed the plain join.
`cex/cex_ad_pat_join_not_leaf_valid.v` machine-checks that the datum is not
recoverable at the capture configuration (subject `∀X.◇`, counterpart `∀ˢX.X`).

⭐ **The open half is now proved** — `d_pat_consis_subject_refine_ghost_free`
(prop_conserv.v §12): **at a ghost-free subject the leaf datum IS derivable
from consistency alone.**  The ∀ rows line up (consistency pushes the bound
rigid into Γ, refinement into Δ — the `tvars_denv Δd ++ Γ0` split in the
statement is exactly that correspondence) and every rule that could fill a
ghost with a binder-bound variable is excluded by the subject.

So the previous session's question — *"is the capture configuration reachable
for `ad_sd_typing` at a closed program?"* — resolves as follows:

- **`ad_sd_typing`'s OWN base rows can never be the problem.**  They join
  `ptyp_to_uskl_syn A` for a `ptyp` `A`, which has no ghosts.
- **`ad_pat`'s P-Var can.**  Its subject is `syn{P}` for a `P` read out of the
  context, and `ad_pat__abs` may push `x : P` for ANY well-formed `P`,
  including `∀ˢ.◇`.  `d_sd_typing`'s App rule has a `d_pat` premise, so
  skeleton inference is reachable from typing; inside it, `d_pat__abs`
  requires `M ≠ TC` and is reached from the App premise's `TC` through
  `d_pat__app`'s function premise (`mode_fn M`) or `d_pat__freeze` (`TI`).

⚠️ Note what this does NOT establish: a *reachable configuration* is not yet a
*counterexample to the bridge*.  Refuting `d_sd_typing · e B → ad_sd_typing ·
e B` needs a closed `e`, `B` with the `ad` side FALSE — i.e. ruling out every
`ad` derivation, not just the one the `d` derivation mirrors.  The App rule
existentially quantifies its skeleton `P`, so a refutation has to close over
all choices of `P`.  That is the remaining piece of work on (A).

### (B) Tag hygiene — ✅ **RESOLVED 2026-08-11.  All four subtyping judgements now read `fresh Ψ'` the same (GLOBAL) way**

`ad_pat_sub_gv`'s two ForallL rows carry, beyond the paper's `Ψ' ∩ Ψ = ∅`,

```coq
Ψ' ∩ (ftag_in_uskl (uskl_all_etag ε R)) [=] empty
```

— the instantiation's tags fresh from the SUBJECT's syntactic tags.  That is
the mech's rendering of the paper's prose `fresh Ψ'` as GLOBAL freshness, and
it is load-bearing: `lemma:precision-substitution` is FALSE without it
(`docs/DESIGN-completeness-subtyping.md` §5.2).  `d_sub` / `d_pat_sub` /
`ad_pat_sub` used to render the same prose as freshness from the TAG CONTEXT
only; the two agree along a ForallL chain but come apart at **Arrow**, where
the tag context splits into `Ψ₁ ∪ Ψ₂` and the subject keeps all its tags.

**The premise is now ON all six ForallL rows** (`d_sub` ×2, `d_pat_sub` ×2,
`ad_pat_sub` ×2), so this obstruction is gone at BOTH sorts.  It cost:

- **~35 of ~38 build sites: mechanical.**  Every transport either keeps the
  subject, takes `Ψ' := ∅`, or substitutes a type variable — and a substitution
  by a TAG-FREE term cannot change a tag.  Stated once, in its strongest form,
  as `ftag_in_utyp_subst_tagfree` / `ftag_in_uskl_subst_tagfree`
  (`frost/prop_etag.v` §0).
- **One place that was not: `d_consis_sub_trans_mid`** (CST, paper B.3,
  `decl/prop_general_subsumption.v`), whose ForallL case transports along
  `utyp_tag_refines`, where the subject **GAINS** tags.  Repaired by the
  tags-bound twin below.
- **One more that was not, and is smaller: `d_sub_prefix_spine_perm`**
  (`decl/prop_stability.v`), which PERMUTES a spine.  Repaired by two lines of
  syntax — ε tags are order-blind on a spine and blind to a ∀-prefix
  (`ftag_spine_utyp_perm`, `ftag_utyp_all_syn_n`) — plus exposing the hygiene
  premise from `d_sub_fn_all_syn_inv` / `_fnn_`, which are inversion lemmas and
  should have reported it anyway.

### ⭐ HOW CST WAS REPAIRED — the general shape, worth reusing

`frost/prop_etag.v` + `frost/decl/prop_etag_swap.v` (~1000 lines, green):

1. **§1–§2 EQUIVARIANCE, with no freshness side condition**, for `d_tags`,
   `d_tags_skl`, `d_wf_utyp`, `d_wf_uskl`, `d_consis`, `d_pat_consis`, `d_sub`
   and `d_pat_sub`.  ⭐ The primitive is a TRANSPOSITION, not a one-way rename:
   a rename needs ε₂ fresh for the WHOLE derivation, and "the tags of a
   derivation" is not collectable from a `Prop`; a swap is a bijection, so it
   is an automorphism outright.  (Same reason `algo/prop_swap.v` takes
   equivariance as the renaming primitive for type variables.)
2. **§3 `d_sub_freshen_forall_l`** — ONE ForallL node's instantiation moves out
   of any finite set, one transposition per offending tag.  ⚠️ **This is not
   enough**, and the reason is the lesson: rewriting a WHOLE derivation node by
   node needs the freshened premise fed back to an induction hypothesis, and a
   structural induction cannot — at a ForallL node the IH is tied to the
   ORIGINAL instantiation `ph`, while freshening yields a derivation of a
   DIFFERENT statement.  Nor can the swap be applied to the IH's OUTPUT: there
   the instantiation's tags and the refined subject's tags sit in the SAME term
   `T0[ph]`.
3. **§4 the tags-BOUND twin `d_sub_tagsin U`** — `d_sub` with `Ψ' [<=] U` on
   the two ForallL rows.  `d_sub_to_tagsin` COLLECTS the bound by a plain
   induction, with no freshening anywhere; `d_sub_tagsin_of` forgets it.
   ⚙ Its ForallR is EXISTS-FRESH where `d_sub`'s is cofinite: the collection
   must produce ONE `U` for the whole rule, and a cofinite premise would demand
   a bound uniform in infinitely many `α`.  The forgetful direction pays for
   that with the tree's existing `d_sub_rename_tvar`.
4. **§5 WHOLESALE freshening `d_sub_freshen`** — with every tag inside one `U`,
   a single chain of transpositions moves `U` off any finite set, provided that
   set avoids what the CONCLUSION mentions.  One swap now rewrites the whole
   derivation, so there is no changed statement to feed back.
5. **CST restated** (`decl/prop_general_subsumption.v`): the induction runs on
   `d_sub_tagsin U` against a tag-BOUNDED refinement `utyp_tag_refines_in V`
   (the added tags confined to `V`), with one global `U ∩ V [=] ∅`.  Its
   ForallL case then closes from the node's own hygiene plus `Ψ' ⊆ U`.
   ⚙ The bound must be an indexed RELATION, not the set inclusion
   `ftag C' ⊆ ftag Cmid ∪ V` it implies: the inclusion does not survive
   descending into a ∀'s body, because `ftag (∀^ε T0)` has already absorbed ε.
6. **The two call sites** — `decl/prop_stability.v` and `d_sub_trans_spine`'s
   infer case — discharge `U ∩ ftag C' = ∅` by (4), legitimate exactly there
   because the transported derivation runs at the EMPTY tag context with a
   PAINTED (hence tag-free) subject.

**What the paper's own statements lost: nothing.**  `d_consis_sub_trans` (the
paper's CST) gains `Δb [=] empty`, which is the paper's own statement at `·`;
the general-context form was a mech-internal inductive generalisation and
survives as `d_consis_sub_trans_mid_tagsin`.  `d_sd_typing` / `d_typing` are
untouched.

## ROUTES, RE-SCORED

⚠️ Every score below is now about (A) ALONE — the prerequisite all four routes
shared, (B), is closed.

- **R1 (restricted bridge)** — needs (A)'s reachability question closed in the
  *negative sense* described above.  The (A) half now has its positive lemma;
  the missing invariant would have to say that the ghosty skeleton entries
  `d_pat__abs` may introduce never reach a capture at a closed program, over
  ALL choices of the App rule's existential `P`.
- **R2 (leaf-validity as a side condition)** — still the cheapest way to keep
  the paper's system untouched, but the side condition is a property of the
  DERIVATION, not of the conclusion, so it does not state well.
- **R3 (a leaf-valid declarative twin)** — a twin carrying the leaf data.  ⚠️ It
  was scored the most promising route only because it also dodged (B); with (B)
  closed that advantage is gone, and it still buys a judgement whose relation to
  `d_sd_typing` becomes the open question.  Re-score it against R1/R2 before
  building anything.
- **R4 (strengthen the paper's declarative system)** — unchanged: it forces
  the standalone `Sub` rule too and re-opens Phase 2 plus the paper's
  §declarative figure.  Author-facing decision; ASK first.
- **✅ THE SHARED PREREQUISITE IS DONE**: the ε-tag freshening for `d_sub` /
  `d_pat_sub`.  Both halves — the equivariance primitive AND the induction that
  applies it (the tags-bound twin + wholesale freshening) — are proved, and the
  rule change they were for has landed.  The choice between "change the rules"
  and "freshen in the bridge" is now a matter of taste, not of provability; the
  tree took the first.

## ACCEPTANCE — where it stands

- ✅ `a_typing_sound_infer` / `a_typing_sound_check` read `⊢ˢ` and `⊢` on the
  declarative side
- ⛔ `a_typing_complete_infer` / `a_typing_complete_check` still read `⊢ᵃᵈ`
- ✅ all four subtyping judgements carry the GLOBAL reading of `fresh Ψ'`
- ✅ `make coq` exit 0, every `Print Assumptions` "Closed under the global
  context", zero Axioms/Parameters/Variables/Admitted
- ✅ README.v's `Check`s updated for the two soundness corollaries
- ✅ the bridge is registered in `docs/PAPER-GAPS.md` as the prose-completion
  of `app:decl-in-algo-context`'s "it is easy to extend"
- ⚠️ no route was taken that requires changing `d_sd_typing` / `d_typing` —
  that decision is still the user's
