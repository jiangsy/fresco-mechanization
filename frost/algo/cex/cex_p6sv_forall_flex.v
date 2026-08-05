(** ⚠️⚠️ RETRACTED (2026-08-05) — THE AUTHORS' `SolE-FlexR` REPAIR
    NEUTRALISES THIS COUNTEREXAMPLE.

    What this file used to claim: that the paper's P6-Sv
    ([lemma:complete-constraint-collection-solving-var],
    subtyping-proofs.tex:1696) is FALSE at

      Pi = ∀β. β → β      P0 = f̂ (a flexible of Θ0)      guess = ∀^ε β. β → β

    because the only solve derivation was SS-ForallL over SS-Check over the
    OLD `SolE-FlexR` — which read `P ∼ α̂ ⤳ α̂` and so DISCARDED the
    accumulated pattern, forcing the body answer to be the bare flexible `f̂`.
    The enclosing `close` then re-bound a VACUOUS binder `∀_.f̂`, and no
    instantiation of `f̂` (declared OUTSIDE the ∀) could ever mention the
    bound variable, so the required precision was underivable.

    ⭐ WHY IT IS RETRACTED.  That forcing step is exactly the defect the
    authors' repaired row removes: `SolE-FlexR` now returns `guess^TY(P)`,
    and at this configuration `P = β → β` is GHOST-FREE, so `guess^TY`
    invents nothing and the body answer IS `β → β`.  The close then re-binds
    a REAL occurrence and the run yields `∀β. β → β` — the very shape the
    paper's statement asks for.  MACHINE-CHECKED in
    `cex/probe_flexr_neutralises_p6.v`
    (`p6sv_body_returns_the_pattern`, `p6sv_forall_returns_the_pattern`,
    `p6sv_close_is_the_real_binder`; all Qed, axiom-free).

    ⛔ WHAT THIS DOES **NOT** SETTLE.  The mech's `sub_shield` premise was
    invented as the repair of this lemma, and it is still carried by P6-Sv,
    P6-Ss and P6-L.  One dead witness does not license dropping it — that
    has to be decided by RE-PROVING the statements without the premise
    (Step 3 of `docs/HANDOFF-solve-flexr-repair.md`).  Until then, every
    comment in the tree that cites this file as the reason for `sub_shield`
    should be read as "cited a witness that the repair has since killed".

    The Coq text of the refutation is recoverable at the pre-repair commit
    `d5f9169`.  It is deleted rather than updated because its central lemma
    — `cex_body_solve_forced`, "the body solve is forced to `f̂`" — is now
    FALSE, and a known-false proof must not stay in the tree
    (CLAUDE.md, "Never commit a KNOWN-FALSE proof").

    RESTART NOTE.  If a P6-Sv counterexample is wanted again under the
    repaired rule, it must defeat `guess^TY` rather than the old discard:
    the payload has to carry a GHOST that `guess^TY` freshens into a
    flexible the enclosing binder cannot reach.  `cex_p7_shield_double_occ.v`
    is the nearest surviving shape. *)
