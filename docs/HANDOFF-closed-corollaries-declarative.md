Handover — Frost mechanization: state the CLOSED-PROGRAM COROLLARIES against
the PURELY DECLARATIVE system (`d_sd_typing` / `d_typing`), in BOTH
directions.

## STATE (2026-08-11, third pass)

⭐ **SOUNDNESS IS DONE.**  `a_typing_sound_infer` / `a_typing_sound_check`
(`frost/algo/typing/prop_closed.v`) now read the paper's own §declarative
system on the declarative side — `· ⊢ˢ[M] e ⦂ B` AND `· ⊢[M] e ⦂ B` — over a
declarative context.  `make coq` exit 0, admit-free, axiom-free, README.v
24/24 `Print Assumptions` closed.

⭐ **COMPLETENESS IS DONE TOO (2026-08-11, fourth pass).**
`a_typing_complete_sd_infer` / `_sd_check` / `_decl_infer` / `_decl_check`
(`algo/typing/prop_closed.v`) read the paper's own declarative judgements —
`· ⊢ˢ[M] e ⦂ B` AND `· ⊢[M] e ⦂ B` — so soundness and completeness now meet on
the same judgement. `make coq` exit 0, admit-free, axiom-free, README.v **28/28**
`Print Assumptions` closed.

⚠️ Both halves take `a_wf_exp nil e`, and it is a real premise, not bookkeeping:
on the `ad` side it was free (`ad_sd_typing_wf_exp`), on the declarative side it
is not, because `d_sd_typing__anno` states no well-formedness for its annotation
(the sd-Anno gap).

**How it closed** — see §(A) and "THE REPAIR" below. In one line: the
mechanisation stopped deferring two presuppositions the paper states in prose,
and with them on the rules the bridge is a rule-for-rule induction.

- **(B) tag hygiene — ✅ RESOLVED 2026-08-11.**  All four subtyping judgements
  (`d_sub`, `d_pat_sub`, `ad_pat_sub` and the fuel mirrors) read the paper's
  `fresh Ψ'` the same, GLOBAL way.  §(B) below records the repair, and its
  shape — collect the tags, then move them wholesale — is worth reusing.
- **(A) the leaf-valid datum — ✅ DIAGNOSED AND REPAIRED 2026-08-11.**
  It is the paper's own presupposition on skeleton consistency
  (`declarative.tex:2074`), deferred on the `d_` side; it is machine-checked NOT
  derivable from the consistency rules, and both candidate bridge hypotheses are
  machine-checked FALSE.  ⚠️ That makes the committed `d_sd_typing_to_ad`
  VACUOUS.  §(A) and "THE REPAIR" below; author-facing note in
  `docs/ghost-capture.tex`.

⚠️ What is left of (B)'s neighbourhood is now purely a FUEL question: the
`ad_pat_sub → ad_pat_sub_g` direction still has to be built, but the two
judgements no longer differ in hygiene.

## WHAT LANDED

**`frost/decorated_algo/prop_conserv.v`** (new, ~1300 lines) — the conservativity
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

### (A) The leaf-valid datum — ⭐ **DIAGNOSED 2026-08-11. It is the paper's own presupposition, which the mech deferred on the `d_` side; it is NOT derivable, and both candidate bridges are machine-checked FALSE**

`ad_pat` / `ad_sd_typing` embed `ad_pat_sub_v`, whose consistency leaves carry
`Θ ⨟ ∅ ⊢ᵣₚᵃᵈ ⌊R⌋ˢ ⊳ ⌊Q⌋`; `d_pat` / `d_sd_typing` embed the plain join.

⭐ **THE DIAGNOSIS.** That datum is not a mech invention and not a
strengthening. `declarative.tex:2073-2075` states it:

> "Skeleton consistency `Ψ ⨟ Γ ⊢ syn{S} ∼ bid{P}` requires well-formedness of
> `syn{S}` and `bid{P}` under Γ **as well as the refinement judgement
> `Γ ⊢ ⌊S⌋ ⊳ P`**."

It is a PRESUPPOSITION in the paper's usual external-side-condition style, and
`docs/WF-SIDE-CONDITIONS.md` §2 had registered the deferral as `[WATCH] — it has
not bitten yet`. It has now bitten. The mechanism is a scoping asymmetry between
two judgements that the paper's own prose says must agree:

| | where a ∀-bound `α` goes | may a ghost's fill use it? |
|---|---|---|
| consistency, `C-ForallSyn` | Γ | yes — `C-Ghost` has no condition |
| refinement, `R-Forall` | Δ | no — `R-Ghost` requires `Δ ∩ ftv = ∅` |

⚠️ The universal ghost `∀◇` goes the OTHER way (`R-TopHoleFill` extends Γ, not
Δ) — a universal ghost IS allowed to capture, that is what generalisation means.
Any repair must keep that; only `∀` (both colours) creates the conflict.

**What is machine-checked** (all Qed, axiom-free):

| statement | witness |
|---|---|
| `∅ ⨟ Γ ⊢ᵃᵈ ∀α.◇ ∼ ∀ˢα.α` is derivable | `cap_consis` |
| `Θ ⨟ ∅ ⊢ᵣₚᵃᵈ ∀α.◇ ⊳ ∀ˢα.α` is NOT | `cap_no_refine` |
| ⟹ the presupposition is **not derivable from the consistency rules** | the two above |
| `x : ∀α.◇ ⊢ₛ[TI] x ⦂ ∀ˢα.α` is derivable declaratively | `cap_d_pat` |
| …and refuted once the presupposition is carried | `cap_not_reachable` |
| ⟹ **the pointwise bridge `d_pat → ad_pat` is FALSE** | `d_pat_bridges_false` |
| ⟹ …and App's EXISTENTIAL skeleton does not repair it | `d_pat_app_package_false` |

The last two are in the new `cex/cex_d_pat_bridges_false.v`; the first four in
`cex/cex_ad_pat_join_not_leaf_valid.v`.

⚠️⚠️ **`d_pat_bridges` being false makes `d_sd_typing_to_ad` VACUOUS, not merely
conditional.** It must not be built on. It is still in the tree at
`prop_conserv.v` §15 and comes out with the repair.

⚠️ Neither refutation lifts to the bridge as literally stated, and the reason
matters: both use a `dbind_skl` entry whose skeleton has a ghost under a ∀, and
`d_sd_typing`'s App has a SECOND premise on the same `e₂` — it TYPES it — while
typing reads only `dbind_typ` entries, whose skeleton view `ptyp_to_pskl A` is
ghost-free. So a refutation of the bridge itself is still open, and there is a
positive-looking argument the other way (a ghost under a ∀ can only be REFINED
INTO a skeleton, never created by one, so it should be unreachable at a typeable
subject). **That argument is moot if the repair lands** — do not spend time on it
first.

**Author-facing note, in the paper's own notation:** `docs/ghost-capture.tex`
(`make -f Makefile.ghost-capture`). It recaps the four paper statements it
needs, gives the configuration and the facts above, and costs both renderings of
the repair.

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

## THE REPAIR — the four-route scoring is RETIRED

⚠️ The old "ROUTES, RE-SCORED" list (R1 restricted bridge / R2 leaf-validity as a
side condition / R3 leaf-valid declarative twin / R4 strengthen the declarative
system) is **deleted, not re-scored**. It was written when the datum looked like
a mech-invented strengthening, so every route was a way of *choosing* how much to
strengthen. It is not a choice: the paper states the condition, so the only
question is where to render it.

**(R-a) carry it as a premise.** Put `Γ ⨟ ∅ ⊢ᵣₚ ⌊S⌋ ⊳ P` on the consistency-bearing
rows of `d_pat_sub` (Infer / UnivGhostR / the Arrow domain), mirroring what
`ad_pat_sub_gv` already does. A transcription of the paper's sentence — it cannot
exclude anything the paper does not already exclude. Cost: a premise per row, and
one new obligation wherever a `d_pat_consis` derivation is BUILT.

**(R-b) make it derivable, by giving consistency the Δ that refinement has.**
Index `d_pat_consis` / `ad_pat_consis` by Δ; the four ∀ rows push `α` into Δ, not
Γ; `C-Var` reads `Γ,Δ ∋ α`; `C-Ghost`'s fill is well-formed with Δ CLEARED;
⚠️ `C-UnivGhost1` keeps extending Γ (see the ∀◇ caveat above). Then the datum is a
THEOREM at arbitrary subjects — `d_pat_consis_subject_refine_ghost_free` drops its
`uskl_ghost_free R` hypothesis — and `ad_pat_sub_gv`'s leaf premises can be
DELETED rather than mirrored.

**Recommendation: (R-b) for the mech, (R-a) for the paper.** (R-b) removes a
premise instead of adding one and makes the two scoping disciplines visibly the
same. They should agree, but ⚠️ that must be CHECKED — one known divergence: the
mech's `*__tophole_keep` carries an explicit `guarded_bskl P` that the paper's
rule has commented out (`declarative.tex:1508`, WF-SIDE-CONDITIONS.md §3), so
(R-b)'s derivation of the datum at `C-UnivGhostG` / `C-UnivGhost` needs that
premise or the paper's version of the rule.

**What the repair buys:** `cap_d_pat` stops being derivable, so
`d_pat_bridges_false` and `d_pat_app_package_false` RETRACT (that is their job —
same pattern as `docs/refutations.tex` and the SolE-FlexR repair); `d_pat` and
`ad_pat` coincide; `d_sd_typing_to_ad` closes with no hypothesis, and the
completeness corollaries can be stated over the paper's own declarative system.

**What it costs, expressiveness-wise:** exactly the derivations `cap_no_refine`
rejects — a ghost filled with a variable bound by a quantifier of its own
skeleton. No algorithmic run produces such a fill, so nothing the implementation
accepts is lost.

## ACCEPTANCE — where it stands

- ✅ `a_typing_sound_infer` / `a_typing_sound_check` read `⊢ˢ` and `⊢` on the
  declarative side
- ✅ `a_typing_complete_sd_infer` / `_sd_check` / `_decl_infer` / `_decl_check`
  read `⊢ˢ` and `⊢` too — **the hand-off's goal is met in both directions**
- ✅ all four subtyping judgements carry the GLOBAL reading of `fresh Ψ'`
- ✅ `make coq` exit 0, every `Print Assumptions` "Closed under the global
  context", zero Axioms/Parameters/Variables/Admitted
- ✅ README.v's `Check`s updated for the two soundness corollaries
- ✅ the bridge is registered in `docs/PAPER-GAPS.md` as the prose-completion
  of `app:decl-in-algo-context`'s "it is easy to extend"
- ✅ `d_sd_typing` / `d_typing` are UNCHANGED.  What changed is `d_pat_sub`
  (three rows) and `d_pat` (three rows), each gaining a premise the paper
  states in prose — no published statement was weakened or altered.
