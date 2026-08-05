(** ⚠️⚠️⚠️ RETRACTED (2026-08-04) — THIS REFUTATION NO LONGER HOLDS, BECAUSE
    THE RULE IT REFUTED HAS BEEN REPAIRED.  Kept as history; the paper's
    docs/refutations.tex cites its theorem names.

    ─────────────────────────────────────────────────────────────────────
    WHAT IT USED TO SHOW, AND UNDER WHICH RULE
    ─────────────────────────────────────────────────────────────────────

    Under the PUBLISHED [SolE-FlexR] (full-algo-spec.tex:1371),

        SolE-FlexR   nonflex(P)  ⟹  solveeq P α̂ ⤳ α̂

    this file machine-checked, Qed and axiom-free, that THEOREM 4.6
    ([thm:complete-subtyping], "Completeness and optimality of subtyping",
    algorithmic.tex:1447) is FALSE, by one self-contained instance:

        Θ0 = f̂            N = TY            M = FN(TC)
        P0 = (∀γ.γ→γ) → f̂                   P  = ∀β.β→β

    which IS a subtyping problem, HAS the declarative solution
    [κ = f̂ ↦ 1→1], [Q = inh(∀β.β→β) → (1→1)] ([solution_d], with the
    guess's tag ε paid by ForallInh-TAGGED against the INHERITED ∀ of the
    counterpart), and YET admitted NO algorithmic run ([probe_no_run],
    probe_double_occ_run.v — also retracted).

    The mechanism: algorithmic ForallL opens the subject at a fresh MARKER
    α, and α occurs TWICE in [α→α].  The domain occurrence faces
    [∀γ.γ→γ] at a CONSISTENCY position and emits [eq(∀γ.γ→γ)]; the codomain
    occurrence faces [f̂] at a SUBTYPING position and emits [sub_tc(f̂)].
    One marker, two constraints — so the solve had to COMBINE them, and
    [SolE-FlexR] destroyed the combination: SS-ForallL opened β, SS-Check
    handed [β→β ∼ f̂] to SE-FlexR, whose output WAS the flexible, and the
    close re-bound a VACUOUS binder [∀_.f̂].  With a single occurrence there
    would have been one constraint and nothing to lose.

    Companion refutation, one lemma lower and by the same instance: LEMMA
    E.17 ([lemma:complete-look], subtyping-proofs.tex:2730), which was
    [p6l_look_completeness_fails] in probe_double_occ_run.v.

    ─────────────────────────────────────────────────────────────────────
    WHY IT IS RETRACTED
    ─────────────────────────────────────────────────────────────────────

    The authors accepted the refutation and replaced the row: the solve now
    KEEPS the accumulated pattern, normalized by [guess^TY], and emits the
    fresh flexible block [Ξ] it invents —

        nonflex(P)   nonghost(P)   guess^TY(P) = (Ξ; P')
        ─────────────────────────────────────────────────
                     solveeq P α̂ ⤳ Ξ ⨾ P'

    At the very configuration above, [guess^TY(β→β) = (·; β→β)] — no ghosts,
    so nothing is invented and nothing is lost — the close re-binds a REAL
    occurrence, the solve yields [∀γ.γ→γ], and A FULL RUN EXISTS.

    ⭐ THE REPLACEMENT IS [cex/probe_flexr_repair.v] ([new_extract],
    [new_run_exists]; Qed, axiom-free), which is the direct NEGATION of what
    this file rested on.  Soundness of subtyping survives the repair with
    its statement unchanged ([a_sub_sound_thm], prop_decorate_key.v).

    ⚙️ The Coq text that carried [thm_complete_subtyping_false],
    [solution_d], [look_premise_d] and [join_untagged_gv] is preserved in
    git at commit [d5f9169] (the last commit under the published rule).  It
    is not carried forward here: the tree's standing rule is that no
    KNOWN-FALSE proof is committed (CLAUDE.md).

    See docs/PAPER-GAPS.md and docs/refutations.tex §"Status". *)
