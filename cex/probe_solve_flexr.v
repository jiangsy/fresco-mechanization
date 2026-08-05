(** ⚙️ SUPERSEDED (2026-08-04) — folded into cex/probe_flexr_repair.v.

    ─────────────────────────────────────────────────────────────────────
    WHAT IT SHOWED
    ─────────────────────────────────────────────────────────────────────

    Under the PUBLISHED [SolE-FlexR] ([solveeq P α̂ ⤳ α̂]) this file localized
    the failure of the two refutations to that ONE row, by showing the
    failure was NOT structural: hand the algorithm the RIGHT instantiation —
    [P1 = ∀β.β→β], i.e. exactly the declarative guess [⌊ψa⌋ˢ] with its tag
    erased — and the continuation SUCCEEDS,

        [run_exists_at_correct_instantiation] :
          ∃ Q Θ1,  Θ0 ⊢ₐ[TY | FN(TC) | P0]  (∀β.β→β) → (∀β.β→β)  ⩽ Q ⊣ Θ1

    with the expected run: the domain by ForallInh at a fresh rigid then
    Arrow of two Rigids; the codomain [∀β.β→β ⩽[TC] f̂] by ForallL, whose
    collection takes LS-Check and then LE-FlexR (inventing a fresh [α̂1]);
    and the continuation [α̂1→α̂1 ⩽[TC] f̂] by Check / FlexR / Assign, setting
    [f̂ ≔ α̂1 → α̂1] — a solution MORE GENERAL than the declarative one, which
    factors through it by [α̂1 ↦ 1].  So every rule the run needed already
    existed and already worked; what the algorithm could not do was CHOOSE
    [∀β.β→β].

    ─────────────────────────────────────────────────────────────────────
    WHY IT IS SUPERSEDED
    ─────────────────────────────────────────────────────────────────────

    The authors' repair makes the algorithm choose it.  Under

        nonflex(P)   nonghost(P)   guess^TY(P) = (Ξ; P')
        ─────────────────────────────────────────────────
                     solveeq P α̂ ⤳ Ξ ⨾ P'

    the extract COMPUTES [∀β.β→β] ([new_extract]), so the hypothetical
    "if it were handed the right instantiation" becomes an actual run from
    the top: [new_run_exists] applies ForallL at that very instantiation and
    then continues with exactly the derivation this file built.  The whole
    content of [run_exists_at_correct_instantiation] is therefore the TAIL of
    [new_run_exists] in cex/probe_flexr_repair.v — which additionally rests
    on nothing but [algo/def_extra.v], where this file sat behind
    cex_p7_shield_double_occ.v and hence behind the completeness cluster.

    ⚙️ The Coq text is preserved in git at commit [d5f9169].
    See docs/refutations.tex §"Status". *)
