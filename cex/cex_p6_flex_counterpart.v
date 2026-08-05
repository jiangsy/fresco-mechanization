(** ⚠️⚠️ RETRACTED (2026-08-05) — THE AUTHORS' `SolE-FlexR` REPAIR
    NEUTRALISES THIS COUNTEREXAMPLE.

    What this file used to claim: that the `-var` completeness lemmas of the
    constraint cluster
    ([lemma:complete-consistency-constraint-collection-solving-var],
    consistency-proofs.tex:1181, and its subtyping twin
    subtyping-proofs.tex:1696) are FALSE when the solve counterpart `P0` is
    a FLEXIBLE VARIABLE of `Θ0` whose κ-image collides with a ρ-substituted
    position of the guess.  The configuration was

      Θ0 = c~tvar, β̂~flex     Θ = c~tvar     κ = [β̂ ↦ ⟨⟩→⟨⟩]
      ψa = c → ⟨⟩              ρ = [c ↦ ⟨⟩]
      P_i = c → ⟨⟩             P_0 = β̂

    and the refutation was: the OLD `SolE-FlexR` forced `P_a = β̂`, so the
    conclusion demanded `κ β̂ ⊑ᵖ ψa`, i.e. `(⟨⟩→⟨⟩) ⊑ᵖ (c → ⟨⟩)`, whose
    argument obligation `⟨⟩ ⊑ᵖ c` has no rule at a RIGID `c`.

    ⭐ WHY IT IS RETRACTED.  The repaired row returns `guess^TY(P_i)` instead
    of the flexible, and `P_i = c → ⟨⟩` is GHOST-FREE, so the answer is
    `c → ⟨⟩` and the obligation becomes `(c → ⟨⟩) ⊑ᵖ (c → ⟨⟩)` — derivable,
    with the rigid `c` matched by the precision var rule.  MACHINE-CHECKED in
    `cex/probe_flexr_neutralises_p6.v`
    (`flexctp_solve_returns_the_pattern`, `flexctp_precision_now_holds`;
    Qed, axiom-free).

    ⚙️ WHAT SURVIVES.  The file's OTHER content was a resolution, not a
    refutation: that the configuration is UNREACHABLE because `LE-FlexR`
    freshens a flexible target facing a COMPOUND subject
    (`cex_p6_flex_freshened.v`, still green).  That reasoning is unaffected
    — it is now simply redundant for this configuration, since the repaired
    solve handles it directly.  The `a_flex_tvar` WIDENING that this file
    motivated (`algo/def_extra.v`, `SolE-FlexR`'s comment) also stands: it
    is about which counterparts the rule accepts, not about what it returns.

    The Coq text is recoverable at the pre-repair commit `d5f9169`.  It is
    deleted rather than updated because its central lemma —
    `cex_solve_forces_flex`, "the only solve derivation forces `P_a = β̂`" —
    is now FALSE (CLAUDE.md, "Never commit a KNOWN-FALSE proof"). *)
