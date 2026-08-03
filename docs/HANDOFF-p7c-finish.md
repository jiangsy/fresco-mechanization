Handover — Frost mechanization: the LAST obligations of subtyping completeness.
ONE task, TWO independent obligations inside it (one of them a MOTIVE
decision).  Everything else in P5/P6/P7 is closed.

READ FIRST: mechanization/CLAUDE.md; memories `remech-p7c-scoped` (start here),
`remech-shield-over-strong`, `remech-p7a-started`; PROGRESS.md Part 2's top
entry (2026-08-03, "SUBTYPING COMPLETENESS IS ASSEMBLED");
docs/DESIGN-completeness-subtyping.md §12.1 → §12.4 (§12.4 is what landed);
docs/PAPER-GAPS.md's last two entries.

STATE.  Branch `freshness-campaign-cluster3-wip`; `make coq` green, admit-free,
axiom-free.  P5 done; P6 complete; P7a's SEVEN walk rows and P7b's seven join
rows all Qed; P7c's five layers all Qed in the leaf
`frost/algo/prop_sub_complete_dispatch.v` (§1–§12, ~1290 lines, 12 s):

  §3/§4  the shape transfer completed + the RIGID-subject refutation
  §5     `sub_flex_rigid_head_absurd`  — the STUCK-CHECK
  §7     `flex_step`                   — the flex half           (layer b)
  §8     `check_row_guarded_p0`        — the Check row's obligation
  §8b    `ad_pat_sub_gv_fuel_weaken`, `sub_gv_all_inh_forall_r_family`,
         `main_all_inh_counterpart`, `p0_wlog_trichotomy`
                                       — the JOIN PERMUTATION (former A2),
                                         DISCHARGED inside §9's ForallL rows
  §9     `main_join`                   — the 12-row join dispatch (layer c)
         `main_arrow_holds`            — the arrow-subject half  (layer a)
  §12    `a_sub_complete_bundle_holds` — the assembly
         `a_sub_complete_thm`          — the Ψ:=∅, R:=⌈P⌉ᵘ corollary

`prop_sub_complete_thm.v` is 7455 lines / 96 s — put new work in the leaf
unless the task says otherwise.

================================================================
THE ONE TASK — `main_forall n`: a MOTIVE change, then TASK 0's `sub_shield`
================================================================
`a_sub_complete_bundle_holds` and `a_sub_complete_thm` both take
`(forall n, main_forall n)` as a hypothesis.  `main_forall n`
(prop_sub_complete_dispatch.v, just above `main_join`) is the main half at a
∀-headed subject with the WLOG `guarded_pskl P0 \/ P0 = pskl_hole` as a
HYPOTHESIS (§8b discharges that case inside the dispatch).  It is the only
thing `main_join` does not discharge, and it owes exactly TWO things.

⭕ **(2) FIRST, the cheaper one, and it is NOT the shield.**  The ForallL rows
also demand `NM = a_sub_mode_ty -> uskl_ghost_free (uskl_all_etag ε Rj)`.  It
is the last premise of `ad_pat_sub_precise_upre_gv` (P5's
precision-substitution transport; prop_sub_complete.v threads the same
predicate through every lemma of the pack).  ⚠️ It is NOT derivable from the
join, and the near-miss is the trap: all four rules that put a ghost AT THE
HEAD of the subject (`__ghost`, `__ghostg`, `__univ_ghost_l`,
`__univ_ghost_lg`) are SK-only, so ghost-freeness LOOKS like a TY invariant —
but `__arrow`'s DOMAIN is an arbitrary consistency leaf with no sort
constraint, and `__infer` accepts an arbitrary subject.  It is an EXTERNAL side
condition (docs/WF-SIDE-CONDITIONS.md, last section).  **The fix is to put it
ON THE P7b MOTIVE guarded by `NM = a_sub_mode_ty`**, after which every row that
recurses into the main half owes it for its recursive subject: Sub-Arrow at
`R2`, Sub-ForallR, both Sub-ForallL rows, and P7a's Flex-Assign / Flex-Solve.
That is a MOTIVE change touching ~6 proofs plus every wrapper
(`main_all`, `main_below`, `main_arrow`, `flex_here`, `main_join`,
`flex_step`, `a_sub_complete_bundle`) — decide it deliberately, and expect the
transports to be: arrow-decomposition (trivial), and "if `open Rj ψa` is
ghost-free then so is `open Rj (var α)`" (an induction, ~15 lines).

⭕ **(1) THEN the shield.**  The premise the two ForallL row lemmas demand
(`a_sub_complete_forall_l_tagged` :2450 / `_untagged` :2753 in
prop_sub_complete_thm.v) is

    forall α, sub_shield Θ0 Ψa empty α P0 (open_uskl_wrt_uskl Rb (uskl_var_f α)) ψa

(definition at prop_look_complete_sub_cstr.v:197, POSITIONALLY indexed since
2026-08-03).  `prop_sub_shield_supply.v` discharges it for a flex-free /
atomic / mono-counterpart / inh-free-counterpart / ∀-free `P0`; open is a `P0`
carrying a ∀ BELOW its head.

⚠️ THE BOUNDARY IS MACHINE-CHECKED — `sub_shield_forall_flex_p0_fails`
(cex/cex_p7_shield_forall_flex.v): at `P0 = (∀γ.γ) → α̂`, `ψa = ∀^ε β.β→β`,
subject `unit → α`, the shield is FALSE.  So a general supply CANNOT come from
`P0`/`ψa` alone; it MUST use the positional guard, i.e. relate the walk
position's `R'` to `P0'`.  The two move in lockstep only at `sss_arrow_r`; the
other handles are the FILL (ties `κP0` to `Q`) and the JOIN (ties `R` to `Q`),
and the ForallL row has both on hand.  ⭐ Read `p7_sub_shield_repaired_holds`
(cex/cex_p7_shield_realizable.v) — the worked instance — before designing the
general statement.

⚠️⚠️ DO NOT restate the residual as a "shield supply" hypothesis.  It is
tempting: the missing thing IS the shield.  But the side conditions under
which it holds are precisely the open question, and the unguarded form is
FALSE (above) — a wrong guess makes the conditional bundle VACUOUSLY TRUE and
worthless.  `main_forall n` is KNOWN-TRUE (an instance of the theorem being
proved), so the hypothesis as it stands is honest.  Keep it until the supply
is actually proved.

DO NOT weaken `sub_shield` to make it go through.

WHEN BOTH CLOSE: discharge `main_forall n` and drop the hypothesis from both
theorems in §12, add `a_sub_complete_thm` to README.v, and re-run
`Print Assumptions` on the flagships.  ⭐ Proving `main_forall n` needs a join
inversion at a ∀-headed subject, and the case list is SHORT — only `__infer`
(row lemma `a_sub_complete_infer`, unconditional), `__forall_r` (row lemma +
fuel IH) and the two `__forall_l` rows can conclude there.  `__check` and
`__univ_ghost_r` both demand a GUARDED subject and a ∀ is not
`guarded_uskl`; every other row's subject has a different head, so they
`discriminate`.  Get `R'` ∀-headed from `R` ∀-headed via `a_uskl_tyequiv_sym`
+ `a_uskl_tyequiv_all_{syn,etag}_l_inv` (both already in dispatch.v §2).

================================================================
HAZARDS (all paid for already)
================================================================
⚠️ `Set Implicit Arguments` — DO NOT trust a rule of thumb about which
   arguments stay explicit.  Empirically: `flex_step`'s `NM M Θ0 Ξ …` and
   `sub_gv_all_inh_forall_r_family`'s `B` are all IMPLICIT even though they
   appear only inside a `Definition` application.  When an application fails
   with "the term X has type T while it is expected to have type U", write
   `@lemma` with the full argument list.
⚠️ `apply H` does NOT unfold a Definition-shaped HYPOTHESIS (`main_below`,
   `main_forall`) — apply it to its explicit arguments.  Conversely a row
   lemma whose conclusion is `sub_complete_concl …` CAN be `exact`ed against
   the intro'd (unfolded) goal: the Definition is transparent.
⚠️ `repeat split` CLOSES a reflexive equality goal and silently shifts every
   bullet after it.  Use explicit `split`s (this bit twice).
⚠️ `eapply <lemma>; … auto` / `… fsetdec` HANGS when implicit arguments are
   still evars.  Build premises as named `assert`s, close with an evar-free
   `exact`.  And in a `[ … | … ]` premise list, use `eassumption`, not
   `assumption`: `assumption` will not instantiate an evar left by `eapply`.
⚠️ A double quote inside a Coq comment opens a STRING — `*"…"*` markdown
   emphasis makes coqc warn that `*)` is not a terminator.  Use `*…*`.
⚠️ dispatch.v did not `Require` `prop_precise` / `prop_decorate`; `Require
   Import` is NOT transitive for notations, so `⊢ₚᵣᵃ … ⊑ …` failed to parse
   until both were added.
⚠️ An empty `coqc` output is NOT success — `coqc … > /tmp/x 2>&1; echo EXIT=$?`.
⚙ NEVER hand a big union to `fsetdec`; scope every call with `clear - …`.
⚙ Develop new leaf lemmas in a SCRATCH .v outside the tree that
   `Require`s the compiled `prop_sub_complete_thm` / `_dispatch` — the edit
   loop is 15 s instead of 96 s.  Copy the imports verbatim from the target
   file (Import is not transitive).
⚙ Rebuild costs: prop_sub_complete_thm.v 96 s, dispatch.v 12 s, a touch of
   algo/def_extra.v ≈ 10 min for the whole algo tree (`make NJOBS=8 coq`).
⚠️ The vsrocq MCP hangs — do not use it.

================================================================
REJECTED / CORRECTED — do not retry
================================================================
- lex(fuel, |Θ0|) for the bundle (DESIGN §12).  Refuted; §12.1 is the fix, and
  §12.4's assembly is lex(fuel, CONTEXT LENGTH) with the length induction
  INSIDE the fuel one.
- "`__flex_mono` ⇒ P7a" (§12's table).  WRONG: the join's `__flex_mono` is a
  PEEL of a Θ-definition; P7a is entered from `__arrow` when the MOTIVE's
  subject `R` is a variable — and only there.
- Phrasing `main_join`'s escape as `R = uskl_var_f α -> …`.  It does not
  survive the induction: `__univ_ghost_l`/`_lg` STRIP the subject and can
  EXPOSE a variable the conclusion hid.  The abstract `ESC` predicate with its
  three closure conditions is what makes ONE dispatch serve both layers.
- Carrying `a_sub_flex_walkable` to the final bundle instead of writing P7a's
  two term-variable rows.  The row lemmas' fuel IH is the UNRESTRICTED motive,
  so the restriction would have to move INTO `sub_complete_concl` and every
  row would then owe walkability of the contexts it recurses at.  (Moot now —
  the rows are written and the predicate is deleted.)
- Reporting the ForallL overlap as a paper defect.  The paper handles it
  (subtyping-proofs.tex:3385); the mechanization owed the permutation and §11
  now pays it.
- Guarding all three `sub_shield` conjuncts (DESIGN §14.2).  `flex_apart_p0`
  must stay UNGUARDED.
- The `forall R` form of P7b's ForallL shield premise: over-strong at the
  witness.
- Restating the bundle's residual as a shield-supply hypothesis (see above).

STANDING RULES.  Never weaken a paper statement; check
docs/WF-SIDE-CONDITIONS.md before calling one false; genuine falsehoods get
`cex/*.v` + a docs/PAPER-GAPS.md entry + a report — but `sub_shield`, `ss_walk`,
`fa_walk` and the two motives are MECH-INVENTED, so their refutations go to
DESIGN, not PAPER-GAPS.  Never commit a known-false proof.  `Admitted` is
allowed ONLY on individual cases of a large incremental bundle that are TRUE and
merely unfinished, each marked `Admitted. (* TODO[..]: <case>; true; blocked on
<reason> *)` and in its OWN lemma so the glue stays `Qed` — the tree is
currently admit-free, so prefer an honest explicit hypothesis (as
`main_forall` is) over an admit.  ⚠️ in .v comments is for
counterexamples only.  Commit tag `[mech]`.  `make coq` before committing, and
re-check `Print Assumptions` on the flagships.
