Handover — Frost mechanization: CLOSE subtyping completeness.  Supersedes
HANDOFF-completeness-repair.md (its TASK 1 landed; its TASK 2 verdict was
retracted; its TASK 3 is still the endgame).  FOUR tasks, in strict order.

READ FIRST: mechanization/CLAUDE.md; memory `remech-reachable-incompleteness`
(this is the current front — read its RETRACTION and LESSON sections, they
are the two wrong turns already paid for); `frost/algo/cex/probe_double_occ_run.v`
HEADER + `p6l_look_completeness_fails` (the central document);
docs/PAPER-GAPS.md's two 2026-08-03 entries (the `lemma:complete-look`
falsity, and the retraction below it); DESIGN-completeness-subtyping.md
§14.7–§14.9.  THE PAPER: subtyping-proofs.tex:2730 (`lemma:complete-look`)
and :3371 (thm:complete-subtyping's ForallL case) — read BOTH before
touching the mech; overview.tex:1005 (§2.9 limitations).

STATE.  Branch `freshness-campaign-cluster3-wip` @ 4273b36; `make coq`
green, admit-free, axiom-free.  Machine-checked (all Qed, axiom-free):
 · `probe_no_run` — NO `a_sub` run exists at the double-occ configuration
   (`cex_p7_shield_double_occ.v`), while its join+fill are Qed-inhabited.
   The look/solve/guess are DETERMINISTIC there (`probe_*_det`), uniform in
   every fresh name (the collapsed binder is vacuous and swallows them).
 · `probe_main_forall_false : ~ main_forall 3` — the completeness
   assembly's ONE hypothesis is FALSE, so `a_sub_complete_bundle_holds` and
   `a_sub_complete_thm` are VACUOUS as stated (they stay out of README.v).
 · `p6l_look_completeness_fails` — the PAPER's `lemma:complete-look` is
   FALSE as stated at that configuration: every premise holds and the
   precision conclusion fails for the forced output.

================================================================
THE PICTURE (co-author's; confirmed against the rules — trust it)
================================================================
A polytype instantiation must be PAID FOR by an INHERITED ∀ in the
counterpart — the paper's "never guess polymorphism out of thin air":
`d_sub__forall_l_untagged` runs its premise at `Ψ ∪ Ψ'` with
`d_tags Ψ' ph`; the ONLY `d_consis` rule that puts a tag into Ψ is
`d_consis__forall_inh_tagged`, whose counterpart must be `btyp_all_inh`;
and `d_sub__infer` demands `Ψ [=] empty`.  The counterpart is what the
SKELETON supplies, so where the skeleton has a ghost, no polytype
instantiation is licensed.  ⭐ THE TAG INDEX IS THE REAL POSITIONAL
HANDLE — the paper's P6-Ss conclusion carries `precise[Ψi,Ψa]`, and the
mech's P6-Ss already has it (`⊑ᵖ[ Ψi ]` + `Ψi ∪ Ψa [=] Ψ'`), with
`sub_shield` bolted on TOP as the mech's own repair.

================================================================
WHAT THE PAPER GIVES, AND WHERE IT IS BROKEN
================================================================
USE AS GUIDANCE, DO NOT COPY BLINDLY.  The ForallL case (:3371) is a
faithful map of the case structure: invoke `lemma:complete-look`, then
`lemma:precision-substitution` on its precision output, then the IH, then
algorithmic ForallL.  The mech mirrors it row-for-row.  ⚠️ But the chain
has REGISTERED FALSITIES (docs/PAPER-GAPS.md): `lemma:complete-look`
itself (NEW, this session), P6-Sv (`cex/cex_p6sv_forall_flex.v`), P6-Ss's
Sub-ForallR (needed a mode-guarded ftv-𝒞 disjunction), the 2-condition
`thm:complete-consistency`, and the `:3243` TODO property.  So expect to
REPAIR + DOCUMENT (CLAUDE.md's rule), not to transcribe.

================================================================
TASK A — DECIDE REACHABILITY.  This gates everything else.
================================================================
The refuting configuration needs BOTH
  (1) a raw `Θ0`-flexible at the payload's CODOMAIN — the algorithm has NO
      inherited information there; and
  (2) a CONCRETE counterpart at that codomain, with the guess's tag paid at
      the DOMAIN by an inherited ∀ — the declarative side HAS information.
These pull in OPPOSITE directions.  Settle it:
 (a) The producers are already mapped.  Every `a_sub` payload is the
     ambient `a_typing`/`a_pat` payload; the grammar is
     `P0 ::= ◇ | ⌈A⌉ | P_arg → P0 | (a_split output)`, where `P_arg` is the
     argument's skeleton collected at TC/◇ and `a_split__flex` is what
     introduces a RAW FLEXIBLE payload.
 (b) ⚠️ `freeze` is the loophole for (1)'s dual: ordinary arguments are
     collected at TC (a head ∀ is ForallL-instantiated away; a guarded type
     is kept under ⫯), but `{| e |}` collects at TI (`a_pat__freeze`) where
     `a_sub__infer` returns the subject VERBATIM — so a frozen polymorphic
     argument DOES put a bare ∀ at a payload domain, and the fill paints it
     INHERITED, which PAYS a guess's tag.  Do not try to prove "domains are
     never ∀-headed"; it is false.
 (c) ⭐ THE TENSION TO EXPLOIT: `a_typing__freeze` checks by CONSISTENCY,
     which MATCHES ∀s and never instantiates.  So freeze forces the guess to
     be a POLYTYPE, and with a double-occurrence subject the codomain
     resolution is then that same polytype — whereas the cex needs a
     MONOTYPE there (`κ f̂ = 1→1`; `join_cod_d` instantiates the codomain
     copy down).  Without freeze there is no ∀ to pay the tag at all.
     Probes so far (`docs/repros/thm_complete_subtyping_reachable_*`) all
     land on one horn or the other and are rejected by BOTH systems.
 OUTCOME, either:
   · a REACHABLE witness ⟹ the theorem is false on programs: cex + a
     PAPER-GAPS entry + the author report.  ⚠️ Before claiming it, verify
     the declarative side pays EVERY tag (the hazard below).
   · unreachable ⟹ TASK B's predicate, and the theorem is OVER-QUANTIFIED.

================================================================
TASK B — STATE AND PROVE THE PAYLOAD INVARIANT
================================================================
Define a `reachable_payload`-style predicate in Coq capturing TASK A's
answer, and prove `a_typing`/`a_pat` maintain it at EVERY `a_sub` call site
(`a_pat__{unit,var,var_skl,anno,app}`, `a_typing__{unit,var,anno,app}`, and
the `a_split` outputs; the freeze route is the one that bites).  ⚠️ It must
survive the RECURSIONS: Sub-Arrow keeps P0's codomain; ForallL FIXES P0;
P7a's rows substitute MONOTYPES into P0 (`msubst_pskl_all_free` is the
precedent).  Validate BOTH directions before building on it.

================================================================
TASK C — MAKE THE SUPPLY TOTAL (or kill sub_shield outright)
================================================================
`prop_sub_shield_supply.v` already discharges `sub_shield` for a flex-free
P0, a ∀-free P0, an atomic P0, a mono-ish counterpart and an INH-FREE
counterpart (§8 is the weakest: inh-free counterpart ⟹ `Ψa = ∅` ⟹ shield).
Under TASK B's invariant, make the routes cover everything.  ⭐ PREFER the
paper's route: derive what P6-L needs from the TAG-INDEXED precision
`⊑ᵖ[Ψi]` it already carries, so `sub_shield` DIES (then P6-Ss/P6-L lose the
premise and ~500 lines of `flex_shield` kit + the dead `Ψ'` index go).

================================================================
TASK D — THE ENDGAME
================================================================
Put the condition on the P7b motive exactly as the ghost-freeness premise
was landed (commit bdb9d31 is the recipe: premise at the END of
`sub_complete_concl`, cheap suppliers per row, wrappers threaded; both files
compiled first try).  Then discharge `main_forall` (short join inversion —
only `__infer`/`__forall_r`/`__forall_l`×2 conclude at a ∀-headed subject;
get `R'` ∀-headed from `R` via `a_uskl_tyequiv_sym` +
`a_uskl_tyequiv_all_{syn,etag}_l_inv`, dispatch.v §2), drop the hypothesis
from both §12 theorems, add `a_sub_complete_thm` to README.v, `Print
Assumptions` on the flagships, and write the PAPER-GAPS repair + author
report.

================================================================
HAZARDS — all paid for; the first two are the retracted claims
================================================================
⚠️ MODE FIRST: pin the mode a configuration invokes before ANY
  "decl accepts / algo rejects" claim.  At TC the decl side is MUCH weaker
  than at FN(TC).
⚠️ TAGS SECOND: enumerate ALL the declarative side conditions, not the
  first plausible one.  `d_sub__forall_l_untagged` has NO `mono_ptyp`
  restriction — reading that as "instantiation is free" is what produced a
  FALSE author-facing claim.  The gate is the TAG obligation.  ⭐ And check
  paper §2.9's limitation list: it is the authoritative catalogue of what
  the declarative system DELIBERATELY rejects ("ghosts are nameless";
  "only flowing back and forth once" — that one IS the retracted witness).
⚠️ A met.exe run NEVER settles a rule-level claim about a specific payload:
  the surface language cannot force an arbitrary P0.  Use met for
  reachability only, and eta-expand around modality boxing.
⚠️ Section-local Definitions discharge to FUNCTIONS of the section
  variables (`Θ0d f`, `P0d f`, `ψd e`) — `Check` before writing instances.
⚙ Scratch-file discipline: develop in a scratch .v against compiled .vos,
  copy imports VERBATIM; cex files compile in seconds, thm.v is 96 s,
  dispatch.v 12 s, sub_var ~60 s, sub_cstr 16 s; `make NJOBS=8 coq` for the
  bar.  ⚠️ `coqc | tail` hides the exit code — check `${PIPESTATUS[0]}`.
⚠️ `Set Implicit Arguments`: on arity errors use `@lemma` with all args.
  `eassumption` not `assumption` in eapply premise lists; explicit splits;
  scope `fsetdec` with `clear -`; the vsrocq MCP hangs — do not use it.
⚙ PROOF RECIPE that worked first try in the probe: pure inversion chains;
  the only refuters needed are (i) `α ∉ ftv` freshness clashes → `simpl` +
  `fsetdec`, (ii) `x ≠ x` → `eq_refl`, (iii) `guarded_pskl (pskl_all_syn _)`
  → empty inversion; close computations via local `close_*_var_f_neq`
  lemmas.  Match hypotheses by NOTATION (`_ ⨟ _ ⊢ᵣᵃ _ ⊳ _`), not by the
  inductive's name.
✍️ In chat output write the unit type as `1` and NEVER show the modality
  boxes `[]` (the .mle artifacts keep both).

STANDING RULES.  Never weaken a paper statement silently — repairs are
REGISTERED (PAPER-GAPS + WF-SIDE-CONDITIONS).  Genuine falsehoods get a
cex/*.v + PAPER-GAPS; mech-invented predicates' findings go to DESIGN.
Never commit a known-false proof or claim; the tree is admit-free.  ⚠️ in
.v comments is for counterexamples only.  Commit tag `[mech]`.  `make coq`
before committing; `Print Assumptions` on the flagships.
