⛔ SUPERSEDED by docs/HANDOFF-close-subtyping-completeness.md (2026-08-03).
Kept for the TASK 1 record and the producer facts; the tasks below are
restated there with the reachability question sharpened.

⚠️ STATUS (2026-08-03, end).  **TASK 1 is DONE** — the probe is
machine-checked (`probe_no_run`, `probe_motive_instance_false`,
`probe_main_forall_false`, all Qed + axiom-free; docs updated; committed).
**TASKS 2–3 are still OPEN and the plan below stands**, with ONE correction
and ONE sharpening:

⚠️⚠️ CORRECTION.  A same-day TASK 2 verdict — "the failing payload class is
TYPING-REACHABLE, the algorithm is incomplete on programs, TASK 3 is
invalid" — is RETRACTED (co-author caught it).  The witness program
`pipe (fun g -> g arg)` is rejected DECLARATIVELY too: a polytype
instantiation must be PAID FOR by an inherited ∀ in the counterpart
(`d_sub__forall_l_untagged` runs at `Ψ ∪ Ψ'` with `d_tags Ψ' ph`; only
`d_consis__forall_inh_tagged` puts a tag into Ψ, against a `btyp_all_inh`;
`d_sub__infer` demands `Ψ = ∅`) — the paper's "never guess polymorphism out
of thin air" — and the skeleton `⫯(◇ → ◇)` supplies no ∀.  That program is
the paper's own §2.9 limitations 2 and 3 ("ghosts are nameless"; "only
flowing back and forth once").  ⚠️ Do NOT re-derive a separation without
first enumerating ALL declarative side conditions (the TAG obligation, not
just the monotype one) and checking §2.9.

⭐ SHARPENING for TASK 2.  The refuting configuration needs BOTH
  (1) a raw `Θ0`-flexible at the payload's codomain — the algorithm has NO
      inherited information there — and
  (2) a concrete counterpart at that codomain, with the guess's tag paid at
      the DOMAIN by an inherited ∀ — the declarative side HAS information.
These pull in OPPOSITE directions (the flexible arises exactly where
inherited information is absent), so the conjunction is plausibly
UNREACHABLE.  The retracted program is the instructive near-miss: it gets
(1) and loses (2), and the declarative side then rejects with the
algorithm.  Proving the conjunction unreachable IS the payload invariant
TASK 2 asks for — and it would make the theorem merely over-quantified,
with TASK 3's motive side condition as the repair.

The producer facts found while looking (accurate, reusable): the spine
collection ghosts only HEAD quantifiers (`a_sub__univ_ghost_r` keeps a
guarded argument type verbatim under ⫯, so a ∀ below the head survives
raw), and an undetermined result position becomes a fresh flexible.

⭐⭐ TASK 2, STATE OF PLAY (2026-08-03, end) — the tension is IDENTIFIED and
every probe so far confirms UNREACHABILITY.  Work from here.

1. **A naive invariant is FALSE — `freeze` is the loophole.**  "Payload
   arrow domains are never ∀-headed" holds for every ordinary argument
   (collected at TC, where a head ∀ is ForallL-instantiated away and a
   guarded type is kept under ⫯), **but `{| e |}` collects at TI**
   (`a_pat__freeze`), where `a_sub__infer` returns the subject VERBATIM —
   so a frozen polymorphic argument DOES put a bare ∀ at a payload domain.
   Do not try to prove the naive form.
2. **That loophole is exactly what makes the tag payable** — a bare ∀ in
   the payload domain is painted INHERITED by the fill, which is what pays
   a polytype guess's tag (the cex's `consis_d`).  The earlier
   `_reject_pipe.mle` probe failed *because* its domain was `⫯(◇→◇)`, with
   no inherited ∀ to pay with.
3. ⚠️ **But freeze also BLOCKS the other half.**  `a_typing__freeze` checks
   by CONSISTENCY, which matches ∀s and never instantiates, so a frozen
   `{| idc |}` forces the guess `b := ∀c.c→c` — a polytype — and with the
   double-occurrence subject `∀b.b→b` the RESULT is that same polytype.
   The cex instead needs the codomain's resolution to be a MONOTYPE
   (`κ f̂ = 1→1`, so no tag is owed there; `join_cod_d` instantiates the
   codomain copy down).  Getting that mono resolution requires
   instantiating the argument down — which freeze forbids.
4. ⟹ **THE TENSION, precisely**: the cex needs a POLYTYPE guess paid at the
   domain (only freeze supplies the ∀) AND a MONOTYPE resolution at the
   codomain (freeze forbids it).  Without freeze, no payment; with freeze,
   no mono codomain.  ⭐ Turning this into the payload invariant — and thus
   into `main_forall` restricted to reachable payloads — is TASK 2's
   remaining work.
5. Probes run, all consistent with unreachability (both systems reject the
   near-misses): `docs/repros/thm_complete_subtyping_reachable_*` —
   `_reject_pipe` (no ∀ in the domain ⟹ tag unpayable),
   `_probe_frozen_arg` (∀ in the domain, tag payable, but the codomain
   resolution is then a polytype ⟹ unpayable at a ghost) plus its control.
   ⭐ `_probe_frozen_arg`'s met error prints `∀ c . [] ˆx1` — the probe's
   vacuous-binder collapse, reproduced in a real run.

The text below is the ORIGINAL plan, still current apart from the above.

Handover — Frost mechanization: REPAIR thm:complete-subtyping's payload
over-quantification and CLOSE subtyping completeness.  Supersedes
HANDOFF-p7c-finish.md (its Step A landed; its Step B resolved into the
finding below).  THREE tasks, in strict order.

READ FIRST: mechanization/CLAUDE.md; memory `remech-flex-shield-dead`
(the whole arc of 2026-08-03, INCLUDING its retraction sections — the
wrong turns are documented so you do not repeat them);
frost/algo/cex/probe_double_occ_run.v HEADER (the resolved trace — THE
central document); cex/cex_p7_shield_double_occ.v; docs/PAPER-GAPS.md's
retraction note; DESIGN-completeness-subtyping.md §14.5–§14.6.

STATE.  Branch `freshness-campaign-cluster3-wip` @ 79ea940; `make coq`
green, admit-free, axiom-free.  This session's landings: TY ghost-freeness
ON the P7b motive (bdb9d31); flex_shield proved DEAD and deleted from
P6-Sv (d53334e); sub_shield's flex_shield conjunct dropped tree-wide
(dd242e2); the double-occ cex (1581aba); a WRONG thm-refutation claim
(09b10a7) and its RETRACTION (e0ff87b); the probe, scaffolded (d53c173)
and RESOLVED at the rule level (79ea940).

================================================================
THE FINDING (rule-level; Coq construction is TASK 1)
================================================================
At the machine-checked configuration of cex_p7_shield_double_occ.v —

    Θ0 = f̂ ~ flex    P0 = (∀γ.γ→γ) → f̂    subject P = ∀.(□₀→□₀)
    NM = TY, M = fn tc;  join_d + fill_d Qed (the declarative solution:
    guess ∀^e β.β→β, κ = f̂ ↦ unit→unit)

— NO a_sub run exists.  The forced trace (probe_double_occ_run.v):
looksub is deterministic (LS-Arrow = LE-Var + LS-Var ⟹
[eq (∀γ.γ→γ); sub tc f̂]); the solve THREADS the accumulated pattern, so
the eq's yield ∀γ.γ→γ is fed into the sub-constraint, where SS-ForallL is
forced, then SS-Check → SE-FlexR — whose output IS the flexible
(a_solve_eq__flex_r : P ∼ α̂ ⤳ α̂) — so the guess collapses to ∀_.f̂
(vacuous binder); the continuation's domain consistency then needs
f̂ ∼ γ″→γ″ at a FRESHER rigid γ″ and every route is scope-refused (assign:
γ″ newer; solve-deposit: fresh flexibles sit below γ″; SkipRigid: γ″ ∈
ftv).  Meanwhile met.exe ACCEPTS the corresponding SOURCE program
(docs/repros/thm_complete_subtyping_fn_tc_passes.mle) because the TYPING
builds a different payload (ghosts, not the ∀).

⟹ **thm:complete-subtyping OVER-QUANTIFIES P0**: it claims completeness
at payloads the typing never produces, and there the algorithm fails.
⭐⭐⭐ The failing payload shape is EXACTLY the shield saga's residual — a
P0 with a ∀ below its head at a consis-feeding position.
prop_sub_shield_supply.v's covered shapes (∀-free / atomic /
mono-counterpart / inh-free-counterpart / flex-free) are the REACHABLE
ones.  The mech-invented sub_shield was groping toward the typing's
payload invariant all along.

================================================================
TASK 1 — machine-check the refutation (bounded, cex-style)
================================================================
In probe_double_occ_run.v (imports already compile):
 (a) CONSTRUCT steps 1–3: the looksub derivation (LS-Arrow over LE-Var +
     LS-Var), the solve (a_solve_cstr__eq with SE-GhostL, then
     a_solve_cstr__sub with SS-ForallL / SS-Check / SE-FlexR — for
     SE-FlexR you need `a_flex_tvar Θ0d f` and `a_non_flex` of the opened
     arrow; CHECK a_non_flex's definition first), and the guess
     (a_guess__ty via a_guess_mono on ∀_.f̂ — read a_guess_mono's rules
     before assuming its output).
 (b) PROVE the ¬∃: `forall P1 Θ1, ~ a_sub a_sub_mode_ty (mode_fn mode_tc)
     (P0d f) (Θ0d f) (pskl_all_syn (pskl_arrow (pskl_var_b 0)
     (pskl_var_b 0))) P1 Θ1`.  Inversion route: at a ∀ subject with an
     arrow P0 only a_sub__forall_l applies; the extract is deterministic
     up to fresh names (write concrete inversion lemmas on looksub/solve
     at these literal shapes — each has ONE applicable rule); the
     continuation's stuckness must be proved UNIFORMLY in the fresh names
     (γ″ ∈ ftv blocks SkipRigid for ANY γ″; the scope refusals are
     name-generic).  ⚙ Develop in a scratch .v against compiled .vos;
     the cex files compile in seconds.
 (c) Wire the headline: every completeness-motive premise (already in
     p7_sub_shield_positional_over_strong) + the ¬∃ ⟹ the motive instance
     is FALSE ⟹ main_forall is FALSE as stated.  ⚠️ Only THEN update the
     "main_forall is believed-true" language in dispatch.v §10 /
     CLAUDE.md / DESIGN — with the finding, not before.

================================================================
TASK 2 — find the typing's ACTUAL payload invariant
================================================================
The repair hinges on the right side condition.  Do NOT guess it — read it
off the producers:
 (a) grep a_typing / a_pat (frost/algo/def_extra.v) for every a_sub call
     site; characterize the P0 each rule passes (paints of source types?
     holes? spine-collected skeletons with ghosts?).
 (b) Cross-check against the implementation's spine collection
     (benchmark/Fresco/lib/type.ml; also
     paper/artifact/implementation/lib/type.ml) — the 👻 in the probe's
     first error shows the impl builds payloads with HOLES where my cex
     put the ∀.
 (c) Candidate predicate family: "every consis-feeding position of P0
     reachable by the walk is ∀-free" — compare pskl_all_free and the
     supply file's routes; the right form is the WEAKEST one the typing
     maintains AND the supply routes cover.  Validate BOTH directions:
     the typing maintains it (check each a_sub call site) and
     sub_shield's supply is total under it (prop_sub_shield_supply.v —
     ideally sub_shield then DIES: its remaining walk conjuncts become
     derivable, and P6-Ss/P6-L lose the premise).
 ⚠️ The invariant must survive the RECURSIONS: Sub-Arrow's codomain keeps
 P0's codomain; ForallL substitutes into P0? (check a_sub__forall_l — P0
 is FIXED there); P7a's rows substitute monotypes into P0 (mono
 substitution preserves ∀-freeness — msubst_pskl_all_free exists).

================================================================
TASK 3 — the repaired theorem + the endgame
================================================================
 (a) Add the payload condition to the P7b motive exactly as Step A added
     ghost-freeness (bdb9d31 is the recipe: premise at the END of
     sub_complete_concl, suppliers at each recursing row, wrappers
     threaded; both files compiled first try that way).  The flex motive
     needs its own copy iff the walk rows disturb it (they substitute
     monotypes — likely free).
 (b) With the supply total, discharge main_forall: the old Step C —
     invert the join at a ∀-headed subject; the case list is SHORT
     (__infer, __forall_r, the two __forall_l rows; __check /
     __univ_ghost_r demand a guarded subject; all other rows
     discriminate on the head; get R' ∀-headed from R via
     a_uskl_tyequiv_sym + a_uskl_tyequiv_all_{syn,etag}_l_inv,
     dispatch.v §2).  Drop the hypothesis from both §12 theorems, add
     a_sub_complete to README.v, Print Assumptions on the flagships.
 (c) PAPER-GAPS: rewrite the retraction note into the REAL entry —
     thm:complete-subtyping needs the payload side condition; the
     algorithm is fine on programs; witness = TASK 1's machine-checked
     package.  Then the author report.
 (d) Vestigial cleanup (any time): sub_shield's dead Ψ' index; the
     flex_shield Inductive + kit (~500 lines of prop_look_complete_sub_var
     
     .v) once sub_shield stops referencing it.

================================================================
HAZARDS (all paid for)
================================================================
⚠️ MODE FIRST: before ANY "decl accepts / algo rejects" claim, pin the
  mode the configuration invokes.  At TC the decl side is MUCH weaker
  (Sub-Arrow concludes only at fn M; Check drops to consistency where ∀s
  only MATCH).  Both wrong turns of 2026-08-03 were mode confusions.
⚠️ The solve THREADS its accumulated pattern through the constraint list
  — order matters; SE-FlexR's output IS the flexible.
⚠️ met probes: the surface language CANNOT force an arbitrary P0 — a met
  run never settles a rule-level claim about a specific payload.  And
  eta-expand around modality boxing (naive forms fail on [] mismatches).
⚠️ Section-local Definitions discharge to FUNCTIONS of the section
  variables (Θ0d f, P0d f) — Check before writing instances.
⚙ Scratch-file discipline: develop against compiled .vos; copy imports
  VERBATIM.  Rebuilds: thm.v 96 s, dispatch.v 12 s, sub_var ~60 s,
  sub_cstr 16 s; `make NJOBS=8 coq` for the bar.
⚠️ `Set Implicit Arguments`: on arity errors use @lemma with all args.
⚠️ eassumption not assumption in eapply premise lists; explicit splits
  (repeat split silently closes reflexive equalities); scope fsetdec
  with `clear -`; empty coqc output is NOT success — check exit code.
⚠️ The vsrocq MCP hangs — do not use it.

================================================================
REJECTED / CORRECTED — do not retry
================================================================
- "The solve opens the pattern-∀ rigidly and fails at γ ∼ unit": WRONG —
  SolS keeps vars (a_solve_sub__var takes ANY payload); the failure is
  the THREADING + FlexR overwrite (probe file).
- "thm:complete-subtyping refuted by a closed pair at TC": WRONG — decl
  rejects at TC too (retraction, e0ff87b).  met's TC rejections are
  CORRECT behaviour; do not report them.
- The Ψi-indexed premise replacement: DEAD as stated — at the flexible
  leaf both cex_p6sv's and double-occ's local Ψi are ∅ (the tag is
  consumed higher up); the distinction is the PATTERN-side dirt.
- Resurrecting flex_shield: it is DEAD (deleted from P6-Sv, d53334e);
  every use was a relay.
- Guessing the payload invariant instead of reading it off a_typing +
  type.ml: the whole 2026-08-03 arc is the cost of assuming.

STANDING RULES.  Never weaken a paper statement silently — the payload
side condition is a REGISTERED repair (PAPER-GAPS + WF-SIDE-CONDITIONS
family), stated and documented, never quietly assumed.  Genuine
falsehoods get cex/*.v + PAPER-GAPS; mech-invented predicates' findings
go to DESIGN.  Never commit a known-false proof; the tree is admit-free.
⚠️ in .v comments is for counterexamples only.  Commit tag `[mech]`.
`make coq` before committing; Print Assumptions on the flagships.
