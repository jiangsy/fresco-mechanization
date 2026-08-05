Handover — Frost mechanization: what still stands between the tree and an
UNCONDITIONAL thm:complete-subtyping.  ONE obligation, and it is a P6-TOWER
CAMPAIGN, not an assembly step: the FOURTH re-indexing of `sub_shield`.

READ FIRST: mechanization/CLAUDE.md; memories `remech-p7c-scoped` (start
here), `remech-shield-over-strong`; PROGRESS.md Part 2's top TWO entries
(both 2026-08-03: the assembly, then the Step A closure + the
double-occurrence refutation); docs/DESIGN-completeness-subtyping.md §14.5 →
§14.6 (§14.6 is the new finding) and §12.4's residual note;
cex/cex_p7_shield_double_occ.v END TO END — it is the ground truth this
hand-off is about.

STATE.  Branch `freshness-campaign-cluster3-wip`; `make coq` green,
admit-free, axiom-free; every flagship `Print Assumptions`-clean.  P5 done;
P6 complete; P7a/P7b all rows Qed; P7c assembled
(`a_sub_complete_bundle_holds` + `a_sub_complete_thm`,
frost/algo/prop_sub_complete_dispatch.v §12) under ONE hypothesis
`forall n, main_forall n`.

WHAT JUST HAPPENED (2026-08-03, this session):

⭐ STEP A of the previous hand-off is DONE — the TY ghost-freeness is ON THE
MOTIVE.  `sub_complete_concl` (prop_sub_complete_thm.v) carries
`NM = a_sub_mode_ty -> uskl_ghost_free R'` (JOIN-side subject) as its LAST
premise; `a_sub_complete_thm` states it as the paper-facing EXTERNAL side
condition (WF-SIDE-CONDITIONS.md, last section).  The ForallL rows' own
`Hgfj` hypothesis is DELETED; their construction is the shared `Hgfswap`
assert, consumed by both the `ad_pat_sub_precise_upre_gv` swap and the IH.
Suppliers: Sub-Arrow inverts; Sub-ForallR passes through; Flex-Assign uses
the new helper `tyequiv_mono_paint_ghost_free` (thm.v, after the leaf
plumbing) on its own ≡ᵘ slack; Flex-Solve uses
`mono_ptyp_to_uskl_syn_ghost_free` on the deposited painting; dispatch's
`__univ_ghost_l/lg` are SK-only (discriminate) and `__flex_mono` is a
painting.  Landed in TWO files only, both first try.

⚠️⚠️ STEP B is SETTLED IN THE NEGATIVE — the residual `main_forall n` CANNOT
be discharged through `a_sub_complete_forall_l_tagged` as stated, because the
POSITIONAL `sub_shield` is refuted AT A REACHABLE ForallL NODE.
`cex/cex_p7_shield_double_occ.v` (all Qed, axiom-free):

  Θ0 = α̂    P0 = (∀γ.γ→γ) → α̂    ψa = ∀^e β.β→β  (tagged, compound body)
  R  = ∀^t.(□₀ → □₀)             ⭐ the marker occurs TWICE
  κ  = α̂ ↦ unit→unit             Q = (∀ᵢ.β→β) → (unit→unit)

  · `p7_sub_shield_positional_over_strong` — every hypothesis of the ForallL
    row EXCEPT the shield is inhabited (join, fill, inc, wf's, modes, WLOG,
    ghost-freeness, tag-sort).  The tag `e` is discharged at the arrow's
    DOMAIN (`consis_d`, matched against the inherited ∀), while the CODOMAIN
    copy of the guess is ForallL-INSTANTIATED with `unit` against the raw
    flexible's mono-ish counterpart at NO tag cost (`join_cod_d`).
  · `join_at_Rd_is_forall_l` — no other join rule applies at the node.
  · `p7_sub_shield_double_fails` — the shield premise, in exactly the row's
    form, is FALSE for EVERY marker α: subject `open (□₀→□₀) α = α → α`, one
    `sss_arrow_r` step reaches `(α̂, α)`, the guard `α ∈ ftv α` is MET, and
    the leaf is cex_p7_shield_forall_flex.v's stuck shape (raw flexible vs
    the whole tagged guess).

  ⭐ THE LESSON: the positional guard localises WHERE the guess lands but
  cannot see WHAT THE DERIVATION DOES there.  With two occurrences the two
  guess copies are treated DIFFERENTLY — one MATCHED (tag solved), one
  INSTANTIATED (no tag solved) — and `flex_shield` demands whole-guess
  protection at every guarded position.

================================================================
THE ONE REMAINING TASK — the FOURTH re-indexing of `sub_shield`
================================================================
The repair direction the witness dictates (DESIGN §14.6): distinguish guarded
positions by MATCH vs INSTANTIATE, and the FILL is the handle that pins which
is which — at a raw Θ0-flexible of `P0` the counterpart is the refinement of
a monotype painting, hence `bskl_inh_free`
(`ad_refine_mono_paint_rhs_monoish` / `ad_refine_syn_inh_free`,
prop_sub_shield_supply.v §7), and an inh-free counterpart solves NO tags
(`ad_pat_sub_g_inh_free_tag_free`).  So exactly where `flex_shield`'s stuck
leaf bites, the guess copy is provably instantiated.

OPEN QUESTIONS, in the order to settle them:
 1. WHAT DOES P6-Sv's LS-Var LEAF NEED at an INSTANTIATED position?  Read
    `a_looksub_solve_complete`'s LS-Var case (prop_look_complete_sub_cstr.v)
    and find what `flex_shield` buys there; the current
    `fsh_clean`/`fsh_flexfree` dichotomy is what must be relaxed.  The solve
    at an instantiated position goes through SolE-FlexR (fresh-flexible
    arrows) — the conjecture is that this is ⊑-fine precisely because the
    declarative ALSO instantiated there, so the lost ∀-identity was never
    needed.  Make that precise.
 2. HOW DOES THE COUNTERPART REACH THE PREDICATE?  `flex_shield` is consumed
    by P6-Sv, whose statement has NO fill in scope.  Options: (a) thread an
    inh-free BIT per position (a second uskl-indexed predicate); (b) index
    `sub_shield`'s guarded conjunct by the walk position's counterpart and
    make P6-Ss/P6-L relay it (they DO have the fill); (c) split the guard
    into "α occurs AND the position's κP0-part is not a mono paint".
    Estimate the blast radius of each on P6-Sv → P6-Ss → P6-L → the two
    P7b ForallL rows BEFORE writing code; the 3rd re-indexing
    (remech-shield-over-strong) is the cost precedent (one session,
    P6-Ss compiled first try after the design was right).
 3. Re-run prop_swap.v §13b/§13c's "rule shape loses nothing" check if any
    RULE changes (it should not — this is a premise-only repair).

DO NOT weaken `sub_shield`'s consumers to dodge the question, and DO NOT
restate the bundle's residual as a repaired-shield-supply hypothesis until
the supply is PROVED — `main_forall n` is KNOWN-TRUE and stays the honest
hypothesis; both §12 flagships stay OUT of README.v until unconditional.

WHEN THE SUPPLY LANDS — the old Step C, unchanged: prove `main_forall n` by
inverting the join at a ∀-headed subject (case list is SHORT: only `__infer`,
`__forall_r` and the two `__forall_l` rows can conclude there; `__check` /
`__univ_ghost_r` demand a guarded subject and every other row's subject has a
different head; get R' ∀-headed from R via `a_uskl_tyequiv_sym` +
`a_uskl_tyequiv_all_{syn,etag}_l_inv`, dispatch.v §2).  Then drop the
hypothesis from both §12 theorems, add `a_sub_complete_thm` to README.v,
`Print Assumptions` on the flagships, docs.

================================================================
HAZARDS (all paid for already)
================================================================
⚙ Develop new leaf lemmas in a SCRATCH .v OUTSIDE the tree Requiring the
  compiled modules; copy the import list VERBATIM (Import is not transitive).
  15 s per iteration instead of 96 s.
⚙ Rebuild costs: prop_sub_complete_thm.v 96 s, dispatch.v 12 s,
  prop_look_complete.v 24 s, P6-Ss 16 s, P6-L 41 s; a touch of
  algo/def_extra.v ≈ 10 min for the algo tree (`make NJOBS=8 coq`).
⚠️ `Set Implicit Arguments` — on "term X has type T, expected U", write
  `@lemma` with the full argument list; do NOT trust rules of thumb about
  which args stay explicit.
⚠️ `apply H` does not unfold a Definition-shaped HYPOTHESIS (`sub_complete_ctx_lt`,
  `main_forall`, `sub_shield`) — apply it to its explicit arguments.  A row
  lemma whose conclusion is `sub_complete_concl …` CAN be `exact`ed against
  the intro'd goal.
⚠️ In an `eapply …; [ … | … ]` premise list use `eassumption`, not
  `assumption`.  Never `eapply <lemma>; fsetdec` with unresolved evars — PIN
  witnesses with named `assert`s (an evar-`fsetdec` diverges).
⚠️ `repeat split` closes a reflexive equality goal and silently shifts every
  bullet after it.  Use explicit `split`s.
⚠️ A double quote inside a Coq comment opens a STRING; use `*…*` not `*"…"*`.
⚠️ `Require Import` is NOT transitive for NOTATIONS.
⚠️ An empty coqc output is NOT success — `coqc … > /tmp/x 2>&1; echo EXIT=$?`.
⚙ NEVER hand a big union to fsetdec; scope every call with `clear - …`.
⚠️ The vsrocq MCP hangs — do not use it.

================================================================
REJECTED / CORRECTED — do not retry
================================================================
- Supplying the CURRENT shield for a ∀-below-head P0 from any combination of
  P0 / ψa / the guard: refuted, cex_p7_shield_double_occ.v.  (The previous
  entries stand: the unguarded `forall R` form, guarding all three conjuncts,
  trimming `ss_walk`, lex(fuel,|Θ0|), `R = var α ->` escapes, walkability.)
- Deriving TY ghost-freeness from the join (`__arrow`'s domain leaf and
  `__infer` take arbitrary subjects) — it is a MOTIVE premise now; done.
- Reporting the ForallL overlap or the shield refutations as paper defects:
  `sub_shield` / `fa_walk` / `ss_walk` are MECH-INVENTED; findings go to
  DESIGN, not PAPER-GAPS.

STANDING RULES.  Never weaken a paper statement; check
docs/WF-SIDE-CONDITIONS.md before calling one false; genuine falsehoods get
`cex/*.v` + a docs/PAPER-GAPS.md entry — mech-invented predicates' refutations
go to DESIGN.  Never commit a known-false proof; the tree is admit-free —
prefer an honest explicit hypothesis over an admit.  ⚠️ in .v comments is for
counterexamples only.  Commit tag `[mech]`.  `make coq` before committing;
re-check `Print Assumptions` on the flagships.
