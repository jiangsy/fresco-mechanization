(** ⚠️⚠️⚠️ RETRACTED (2026-08-04) — THIS PROBE NO LONGER HOLDS, BECAUSE THE
    RULE IT ANALYSED HAS BEEN REPAIRED.  Kept as history; the paper's
    docs/refutations.tex cites its lemma names.

    ─────────────────────────────────────────────────────────────────────
    WHAT IT USED TO SHOW, AND UNDER WHICH RULE
    ─────────────────────────────────────────────────────────────────────

    Under the PUBLISHED [SolE-FlexR] (full-algo-spec.tex:1371),

        SolE-FlexR   nonflex(P)  ⟹  solveeq P α̂ ⤳ α̂

    this file traced the algorithm step by step at the DOUBLE-OCCURRENCE
    configuration of cex/cex_p7_shield_double_occ.v —

        Θ0 = f̂ ~ flex        P0 = (∀γ.γ→γ) → f̂       NM = TY, M = FN(TC)
        subject ∀β.β→β       declarative solution κ = f̂ ↦ 1→1,
                             guess ψa = ∀^ε β.β→β  ([join_d], [fill_d] Qed)

    and machine-checked, Qed and axiom-free, that EVERY STEP IS FORCED and
    the run then DIES:

      [probe_looksub] / [probe_look_det]   the collection is deterministic:
          the marker occurs TWICE, so it yields [eq(∀γ.γ→γ); sub_tc(f̂)]
      [probe_solve]   / [probe_solve_det]  SE-GhostL threads the eq's yield
          into the sub-constraint, SS-ForallL opens β, SS-Check hands
          [β→β ∼ f̂] to SE-FlexR — whose output IS the flexible — and the
          close re-binds a VACUOUS binder [∀_.f̂]
      [probe_guess]   / [probe_guess_det]  the TY guess passes [∀_.f̂] on
      [probe_extract] / [probe_extract_det]  hence the extract is FORCED to
          the vacuous [∀_.f̂]
      [probe_continuation_stuck]  and with that instantiation the domain
          consistency [∀_.f̂ ∼ ∀γ.γ→γ] pushes a fresh rigid, leaving the bare
          [f̂] against [γ→γ], where the assignment walk meets [γ] with [γ]
          occurring — scope-stuck
      [probe_no_run]  ⟹ NO [a_sub] run exists at all

    and the consequences that flowed from it:
      [p6l_look_completeness_fails]   Lemma E.17 ([lemma:complete-look],
          subtyping-proofs.tex:2730) is FALSE
      [probe_motive_instance_false] / [probe_main_forall_false] /
      [probe_main_forall_hyp_false]  the mech's completeness motive
          [main_forall] is FALSE, so [a_sub_complete_bundle_holds] and
          [a_sub_complete_thm] were VACUOUS as stated

    ─────────────────────────────────────────────────────────────────────
    WHY IT IS RETRACTED
    ─────────────────────────────────────────────────────────────────────

    The authors accepted the refutation and replaced the row: the solve now
    KEEPS the accumulated pattern, normalized by [guess^TY], and emits the
    fresh flexible block [Ξ] it invents —

        nonflex(P)   nonghost(P)   guess^TY(P) = (Ξ; P')
        ─────────────────────────────────────────────────
                     solveeq P α̂ ⤳ Ξ ⨾ P'

    Retraced at the SAME configuration, the two decisive steps go the other
    way: [guess^TY(β→β) = (·; β→β)] has no ghosts, so nothing is invented
    and nothing is lost; the close re-binds a REAL occurrence; the solve
    yields [∀γ.γ→γ]; the extract returns it; and the continuation — the one
    that used to be scope-stuck — runs to an assignment.

    ⭐ THE REPLACEMENT IS [cex/probe_flexr_repair.v]:
        [new_solve]       the solve yields [∀γ.γ→γ], not [∀_.f̂]
                              — negates [probe_solve_det]
        [new_extract]     the extract returns [∀γ.γ→γ] with an empty suffix
                              — negates [probe_extract_det]
        [new_run_exists]  a full [a_sub] run EXISTS
                              — negates [probe_no_run]
    all Qed and axiom-free.  Soundness of subtyping survives the repair with
    its statement unchanged ([a_sub_sound_thm], prop_decorate_key.v).

    ⚙️ NOTE ON WHAT IS *NOT* RETRACTED.  The three stuck-ness sub-lemmas
    ([a_assign_rigid_head_occurs_stuck],
    [a_consis_var_vs_head_rigid_arrow_stuck],
    [a_consis_forall_arrow_vs_vacuous_var_stuck]) are statements about the
    CONSISTENCY and ASSIGNMENT judgments, which the repair does not touch —
    they remain true.  They are dropped here only because their sole
    consumer was [probe_continuation_stuck]; restore them from git if a use
    reappears.  Likewise cex/cex_p7_shield_double_occ.v — the declarative
    join and fill — is untouched and still holds: it is the DECLARATIVE side
    of the configuration, and nothing declarative moved.

    The Coq text is preserved in git at commit [d5f9169] (the last commit
    under the published rule).  It is not carried forward here: the tree's
    standing rule is that no KNOWN-FALSE proof is committed (CLAUDE.md).

    ⭕ ONE OPEN ITEM MOVES WITH IT.  [main_forall] was refuted BY this probe;
    with the probe retracted, the hypothesis of [a_sub_complete_bundle_holds]
    is no longer known-false — it is OPEN again, and re-deciding it is the
    pay-off the repair campaign is aiming at (docs/HANDOFF-solve-flexr-repair.md
    Step 5: re-prove P6-L and see whether [sub_shield] can be weakened or
    dropped, since [sub_shield] was invented as the mech's repair of exactly
    the lemma this configuration refuted).

    See docs/PAPER-GAPS.md and docs/refutations.tex §"Status". *)
