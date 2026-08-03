Handover — Frost mechanization: FINISH subtyping completeness (`a_sub_complete_bundle`).
Three tasks, in dependency order.  Everything else in P5/P6/P7 is closed.

READ FIRST: mechanization/CLAUDE.md; memories `remech-p7c-scoped` (start here),
`remech-shield-over-strong`, `remech-p7a-started`; PROGRESS.md Part 2's top TWO
entries (both 2026-08-03); docs/DESIGN-completeness-subtyping.md §12.1 → §12.3
(§12.3 is the recipe for TASK 1); docs/PAPER-GAPS.md's last two entries.

STATE.  Branch `freshness-campaign-cluster3-wip` @ `23d30d2`; `make coq` green,
admit-free, axiom-free.  P5 done; P6 complete; P7a's five walk rows and P7b's
seven join rows all Qed; **P7c's three layers all Qed** in the leaf
`frost/algo/prop_sub_complete_dispatch.v` (1099 lines, 5.5 s):

  §3/§4  the shape transfer completed + the RIGID-subject refutation
  §5     `sub_flex_rigid_head_absurd`  — the STUCK-CHECK
  §7     `flex_step`                   — the flex half           (layer b)
  §8     `check_row_guarded_p0`        — the Check row's obligation
  §9     `main_join`                   — the 12-row join dispatch (layer c)
         `main_arrow_holds`            — the arrow-subject half  (layer a)

`prop_sub_complete_thm.v` is 6599 lines / 68 s — put new work in the leaf
unless the task says otherwise.  Row-lemma interfaces there: ghost :367,
ghostg :432, infer :1158, univ_ghost_r :1290, check :1380, arrow :1541,
forall_r :2077, forall_l_tagged :2450, forall_l_untagged :2753; P7a depend
:3381, skip :3447, assign :3765, solve :4410, skip_rigid :6241.  Motives:
`sub_complete_concl` :139, `sub_flex_complete_concl` :191,
`a_sub_complete_bundle` :249 (stated + `Check`ed, UNPROVED — that is the goal).

⭐ THE LAYERING (DESIGN §12.1, all three layers already built).  §12's
lex(fuel,|Θ0|) is REFUTED — the halves call each other at the SAME fuel and
Flex-Solve re-enters with a context TWO ENTRIES LARGER.  What breaks the cycle
is the SUBJECT: Flex-Solve re-enters at an ARROW, and an arrow-subject main
call can never come back into P7a.  Hence `main_arrow_holds` from the fuel IH
alone, then `flex_step` from it plus the main half at SHORTER contexts, then
`main_join`.  Five row-lemma hypotheses in prop_sub_complete_thm.v were
weakened to match (walk IH `length Ξ' <= S (length Ξ)` ×3, assign's cross-half
IH `length Θ0' <= length Ξ + length Θ0`, **solve's cross-half IH restricted to
an ARROW subject**).  Do not undo these.

================================================================
TASK 1 — the two P7a TERM-VARIABLE completeness rows
================================================================
⭐ The rules already EXIST: `a_sub_flex__skip_tm_var` / `__skip_tm_skl`
(algo/def_extra.v, after `__skip_rigid`), decorated mirrors on `a_subtag_flex`,
and all three mutual inductions over the `a_sub`/`a_sub_flex` pair carry their
two cases (prop_sub_sound.v, prop_decorate_key.v, prop_swap.v).  They were
added 2026-08-03 because `fig:alg-subtyping`'s printed five-rule box makes
`thm:complete-subtyping` FALSE — machine-checked in
`cex/cex_p7_flex_walk_tm_var.v`, and the reference implementation CRASHES on
`let f = fun x -> x 1` (docs/PAPER-GAPS.md).

WHAT TO WRITE, in prop_sub_complete_thm.v next to `a_sub_flex_complete_skip_rigid`:

    Lemma a_sub_flex_complete_skip_tm_var :
      forall n NM M Θ0 Ξ α β Qv P0 R' Ψ Θ κ Q,
      (forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
         length Ξ' <= S (length Ξ) ->
         sub_flex_complete_concl n NM M Θ0 Ξ' α' P0' R'' Ψ' Θ'' κ' Q') ->
      sub_flex_complete_concl n NM M ((β ~ abind_var_typ Qv) ++ Θ0) Ξ α P0
        R' Ψ Θ κ Q.
    (* and the [abind_var_skl] twin *)

⭐ NOTE: NO `α <> β` and NO `β ∉ ftv P0` premises — both are DERIVED (a term
entry is never `a_binds_tvar`, so under `uniq` neither `α` nor any free
variable of a well-formed `P0` can be it; 4 lines each, via
`a_wf_pskl_ftv_tvarish` + `binds_unique`).  That is deliberate and matches the
twin walk's `Assign-SkipTmVar`, which carries no such premise either — do NOT
add them to the rules.

HOW.  `a_inc__var` / `a_inc__var_skl` shrink the `a_inc` TARGET exactly as
`a_inc__tvar` does, so each row is `a_sub_flex_complete_skip_rigid`
(:6241-6606, ~365 lines) transcribed with this table:

  | SkipRigid                     | SkipTmVar                                  |
  |---|---|
  | `a_inc_tvar_inv`              | `a_inc_var_inv`   (one more output, `A'`)  |
  | `a_inc__tvar`                 | `a_inc__var`      (one more premise)       |
  | `a_inc_tvar_mid_strip_id`     | `a_inc_var_mid_strip_id`                   |
  | `a_inc_equiv_mid_insert_tvar` | `a_inc_equiv_mid_insert_var` (+1 premise)  |
  | `a_wf_aenv__tvar`             | `a_wf_aenv__var_typ`         (+1 premise)  |
  | `a_sub_flex__skip_rigid`      | `a_sub_flex__skip_tm_var`                  |

⚠️ WATCH THE TWO SIDES OF `(β ~ abind_tvar)` when transcribing: occurrences
inside `Ξv ++ …` are the a_inc TARGET and become `(β ~ abind_var_typ A')`;
every other occurrence is the SOURCE and becomes `(β ~ abind_var_typ Qv)`.

⭕ THE ONE GENUINELY NEW OBLIGATION is the **SEMANTIC MIDDLE** — a rigid entry
has no payload, a term entry does, and both `a_inc__var` and
`a_inc_equiv_mid_insert_var` demand `Θ' ⊢ A' ≡ᵗ κ A`.  The consistency twin's
`Assign-SkipTmVar` case proves EXACTLY it: prop_consis_complete.v:5595-5690
(`Hmiddle` and the `a_inc__var` bullet just above it), through
`a_inc_equiv_msubst_ptyp` + `msubst_compose_id_ptyp` + `msubst_ptyp_agree` +
`msubst_compose_downarrow_tyequiv`.  Crib it.

⚙ ONE STEP BEYOND THE TWIN.  Subtyping re-attaches through the JUNK SWAP
(`a_sub_flex_swap_junk`, prop_swap.v:1361 — the subtyping motive has no
generated-names conjunct, so the rule's `x ∉ dom Θ1` premise is bought that
way), so the increase's witness is `kswap_msubst β β1 ζ`, not
`msubst_compose ζ κf`.  Close the gap with `msubst_ptyp_kswap`
(prop_swap.v:1983) — its hypotheses are free because `β`/`β1` are fresh for the
payload, which is scoped in `Θ0`.

THEN: delete `a_sub_flex_walkable` and its two lemmas from
prop_sub_complete_dispatch.v §6, drop the premise from `flex_step` (:680), and
turn its two `exfalso` branches into delegations to the new rows.

================================================================
TASK 2 — `main_forall n`: the two ForallL rows
================================================================
`main_join` (:860) is complete except for ONE hypothesis, `main_forall n`
(:855) — the main half at a ∀-headed subject.  It bundles two independent
problems; do 2a first, it is the smaller one.

⭕ 2a — THE FORALL-L / FORALL-R OVERLAP.  Both row lemmas demand
`(guarded_pskl P0 \/ P0 = pskl_hole)`, and at `NM = TY` with `M = TC` that is
NOT derivable: `a_ty_mode_compat mode_tc P0` admits a ∀-headed `P0`, and §8's
refutation does not transfer (it consumes the CHECK row's guarded counterpart;
ForallL's counterpart is arbitrary).  So the join's last rule does not
determine the algorithm's rule: ForallL fires on a ∀ SUBJECT, ForallR on a ∀
INPUT, and a ∀-headed `P0` blocks ForallL by its own premise.

⭐ THE PAPER HANDLES THIS — subtyping-proofs.tex:3385: *"Since declarative
subtyping is congruent, we assume WLOG that guarded(P0) ∨ P0 = □; otherwise we
apply ForallR first."*  It is a compressed proof step, NOT a defect; do not
re-report it as one.  What it costs is a **JOIN-PERMUTATION lemma**: from a
ForallL-rooted join with a `bskl_all_inh` target, extract the cofinite ForallR
family that `a_sub_complete_forall_r` (:2077) consumes, i.e.

    ad_pat_sub_gv (S n) TY TC Ψ Θ (∀^ε.R) (bskl_all_inh B)
    ⟹ ∀ α ∉ L, ad_pat_sub_gv n' TY TC Ψ ((α ~ abind_tvar) ++ Θ) (∀^ε.R) (open B α)

Induct on the join: the ForallL chain must bottom out in `__forall_r`; then
re-apply the ForallL instantiations under the binder.  ⚠️ Mind the fuel — `n'`
is whatever the extraction yields, and `a_sub_complete_forall_r` wants `n` with
a conclusion at `S n`; if the arithmetic does not line up, weaken the join's
fuel first (look for an existing `ad_pat_sub_gv` fuel-monotonicity lemma; if
none exists it is a 10-line induction).
The fill half is already available: a `bskl_all_inh` SOURCE refines only to a
`bskl_all_inh` TARGET — `ad_refine_syn_f_all_inh_l_shape`, dispatch.v §8 :784.

⭕ 2b — TASK 0's `sub_shield` at both ForallL rows.  The premise is
`forall α, sub_shield Θ0 Ψa empty α P0 (open_uskl_wrt_uskl Rb (uskl_var_f α)) ψa`
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
IF 2b CANNOT BE CLOSED: say so, and leave `main_forall` as a hypothesis of the
final theorem with a corollary discharged for `pskl_all_free P0` via
`sub_shield_supply_all_free_p0`.  That is a legitimate delivery.  Do NOT weaken
`sub_shield` to make it go through.

================================================================
TASK 3 — assemble `a_sub_complete_bundle` (prop_sub_complete_thm.v:249)
================================================================
Once TASK 1 and TASK 2 are in, this is short.  In dispatch.v:

    Theorem a_sub_complete_bundle_holds : a_sub_complete_bundle.
    (* strong induction on the fuel n (lt_wf_ind);
       inside, strong induction on |Θ0|:
         main_arrow_holds  (fuel IH)
       → flex_step         (main_arrow + main at contexts of length < |Θ0|)
       → main_join         (fuel IH + flex_step at Ξ = ·, via `flex_here`) *)

`main_join`'s ESC argument: instantiate with `fun _ => True`-style constants —
the three closure conditions become trivial and the third hands back
`flex_here n Θ0`, which is `flex_step` at `Ξ = nil` (`length nil + length Θ0 =
length Θ0`).  Then re-derive `a_sub_complete_thm` (algorithmic.tex:1446) as the
`Δ = ∅` corollary and add it to README.v.  Finish with `Print Assumptions` on
the flagships and a PROGRESS.md entry.

================================================================
HAZARDS (all paid for already)
================================================================
⚠️ `Set Implicit Arguments` makes an argument implicit only when STRICT.
   Everything appearing solely inside a `Definition` application — i.e. EVERY
   argument of `sub_complete_concl` — stays EXPLICIT, so row-lemma
   applications need `@` with the full argument list in declaration order.
⚠️ `apply H` does NOT unfold a Definition-shaped HYPOTHESIS (`main_below`,
   `a_sub_flex_walkable`, `main_forall`) — apply it to its explicit arguments.
   Conversely a row lemma whose conclusion is `sub_complete_concl …` CAN be
   `exact`ed against the intro'd (unfolded) goal: the Definition is transparent.
⚠️ `repeat split` CLOSES a reflexive equality goal and silently shifts every
   bullet after it.  Use explicit `split`s (this bit twice).
⚠️ `eapply <lemma>; … auto` / `… fsetdec` HANGS when implicit arguments are
   still evars.  Build premises as named `assert`s, close with an evar-free
   `exact`.
⚠️ An empty `coqc` output is NOT success — `coqc … > /tmp/x 2>&1; echo EXIT=$?`.
⚙ NEVER hand a big union to `fsetdec`; scope every call with `clear - …`.
⚙ Rebuild costs: prop_sub_complete_thm.v 68 s, dispatch.v 5.5 s, a touch of
   algo/def_extra.v ≈ 10 min for the whole algo tree (`make NJOBS=8 coq`).
⚠️ The vsrocq MCP hangs — do not use it.

================================================================
REJECTED / CORRECTED — do not retry
================================================================
- lex(fuel, |Θ0|) for the bundle (DESIGN §12).  Refuted; §12.1 is the fix.
- "`__flex_mono` ⇒ P7a" (§12's table).  WRONG: the join's `__flex_mono` is a
  PEEL of a Θ-definition; P7a is entered from `__arrow` when the MOTIVE's
  subject `R` is a variable — and only there.
- Phrasing `main_join`'s escape as `R = uskl_var_f α -> …`.  It does not
  survive the induction: `__univ_ghost_l`/`_lg` STRIP the subject and can
  EXPOSE a variable the conclusion hid.  The abstract `ESC` predicate with its
  three closure conditions is what makes ONE dispatch serve both layers.
- Carrying `a_sub_flex_walkable` to the final bundle instead of TASK 1.  The
  row lemmas' fuel IH is the UNRESTRICTED motive, so the restriction would have
  to move INTO `sub_complete_concl` and every row would then owe walkability of
  the contexts it recurses at.
- Reporting the ForallL overlap as a paper defect.  The paper handles it
  (subtyping-proofs.tex:3385); only the mechanization owes the permutation.
- Guarding all three `sub_shield` conjuncts (DESIGN §14.2).  `flex_apart_p0`
  must stay UNGUARDED.
- The `forall R` form of P7b's ForallL shield premise: over-strong at the
  witness.

STANDING RULES.  Never weaken a paper statement; check
docs/WF-SIDE-CONDITIONS.md before calling one false; genuine falsehoods get
`cex/*.v` + a docs/PAPER-GAPS.md entry + a report — but `sub_shield`, `ss_walk`,
`fa_walk` and the two motives are MECH-INVENTED, so their refutations go to
DESIGN, not PAPER-GAPS.  Never commit a known-false proof.  `Admitted` is
allowed ONLY on individual cases of a large incremental bundle that are TRUE and
merely unfinished, each marked `Admitted. (* TODO[..]: <case>; true; blocked on
<reason> *)` and in its OWN lemma so the glue stays `Qed` — the tree is
currently admit-free, so prefer an honest explicit hypothesis (as
`a_sub_flex_walkable` is) over an admit.  ⚠️ in .v comments is for
counterexamples only.  Commit tag `[mech]`.  `make coq` before committing, and
re-check `Print Assumptions` on the flagships.
