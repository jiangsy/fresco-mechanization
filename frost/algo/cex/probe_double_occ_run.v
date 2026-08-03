(** ⭕ PROBE (open work, 2026-08-03): does the MECH's [a_sub] SUCCEED at the
    double-occurrence configuration of cex_p7_shield_double_occ.v?

    THE RETHINK THAT MOTIVATES THIS FILE (user-directed).  The mode episode
    (docs/PAPER-GAPS.md, retraction note) exposed two blind spots in the
    completeness analysis:

    (1) THE MODE DISCIPLINE IS THE MATCH/INSTANTIATE MAP.  Arrow DOMAINS
        drop into consistency, where quantifiers can only MATCH (and where
        guess-tags are solved); only the fn-spine CODOMAINS remain in the
        SUB judgment where ForallL instantiation exists.  [ss_walk]
        descending only codomains ([sss_arrow_r]) is the same fact stated
        on the shield's side.  Any repaired premise must be derived from
        this map, not bolted on.

    (2) SOURCE PROBES CANNOT REACH THIS PAYLOAD.  met.exe accepts
        [id2 idc] at FN(TC) (docs/repros/..fn_tc_passes.mle), but the
        spine-collection there builds ITS OWN payload (with ghosts); the
        surface language cannot force [P0 = (∀γ.γ→γ) → α̂] directly.  So
        the implementation run does NOT settle whether the ALGORITHMIC
        RULES succeed at the machine-checked join/fill configuration —
        only this file can.

    THE CONFIGURATION (all from cex_p7_shield_double_occ.v, Section
    [DoubleOccurrence] with atoms f e t, e <> t):

      Θ0 = f̂ ~ flex        P0 = (∀γ.γ→γ) → f̂       NM = TY, M = fn tc
      subject P = ∀.(□₀→□₀)   (so the opened body at the marker α is α→α)
      declarative solution: κ = f̂ ↦ unit→unit, guess ψ = ∀^e β.β→β,
      join [join_d] + fill [fill_d] Qed.

    WHAT TO DECIDE — exactly one of:

    (A) exhibit P1 Θ1 with
          [a_sub a_sub_mode_ty (mode_fn mode_tc) P0d Θ0d (∀.(□₀→□₀)) P1 Θ1]
        i.e. build the run: a_sub__forall_l needs
          [Θ0 ⊢ α→α ⊳[TY,α,fn tc] P0 ⤳ Ξ ↪ P1]
        which unfolds to  looksub (LS-Arrow: domain constraint from
        (α, ∀γ.γ→γ) on the CONSIS side, codomain from (α, f̂) on the SUB
        side)  →  solve 𝒞 ⨾ pskl_hole  →  a_guess; then the continuation
        [a_sub … P0 (Ξ++Θ0) ((open □₀→□₀) P1) Q Θ1].
        ⚙ The candidate that mirrors the declarative: P1 = ∀γ.γ→γ — the
        solve's eq-constraint pins it, and the sub-constraint
        [∀γ.γ→γ ≼[tc] f̂] must NOT destroy it (this is where SolE-FlexR's
        output shape decides everything; read the actual [a_solve_cstr]
        threading rather than assuming).
        The continuation then runs (∀γ.γ→γ)→(∀γ.γ→γ) vs (∀γ.γ→γ)→f̂:
        domain consis matches; codomain a_sub (∀γ.γ→γ) ⩽[tc] f̂ goes
        through the FLEX half (subject ∀ vs flexible payload? — check
        which rule fires: P0 = f̂ at tc with a ∀ subject is ForallL again,
        at payload f̂).

    (B) refute: [forall P1 Θ1, ~ a_sub … ] — then [main_forall] is FALSE
        and the completeness theorem itself is refuted AT THE RULE LEVEL
        (a mech/impl divergence or a genuine paper gap: the theorem
        quantifies over payloads the typing never produces).

    Either outcome reshapes the sub_shield repair:
      (A) ⟹ the run's shape IS the dichotomy supply to mirror;
      (B) ⟹ the residual moves from the premise to the THEOREM's
            quantification over P0 (a wf/reachability side condition on
            payloads — WF-SIDE-CONDITIONS.md family).

    ⭐⭐ STATUS (2026-08-03, end of session): the trace is RESOLVED to (B) at
    the rule level, every step read off the definitions — the Coq
    construction is what remains.

      1. looksub: LS-Arrow = LE-Var + LS-Var ⟹ [nil ⨾ [eq (∀γ.γ→γ);
         sub tc f̂]] — deterministic.
      2. solve: the eq runs on the HOLE (SE-GhostL) ⟹ P'' = ∀γ.γ→γ; the
         sub then runs ON P'': SS-ForallL is FORCED (a ∀ is not guarded,
         no other SS rule matches a var payload), opening γ' fresh;
         [γ'→γ' ≼[tc] f̂] goes SS-Check → SE-FlexR, whose output IS the
         flexible ([a_solve_eq__flex_r] : P ∼ α̂ ⤳ α̂), so the close
         re-binds a VACUOUS binder:  Q_solved = ∀_.f̂.  ⭐ The domain's
         ∀γ.γ→γ is DESTROYED by the threading — the eq-constraint's yield
         is overwritten because the sub-constraint solves on the
         accumulated pattern.
      3. guess (TY): P1 = paint(∀_.f̂) — forced up to names.
      4. continuation: subject (∀_.f̂) → (∀_.f̂) vs (∀γ.γ→γ) → f̂: the
         domain CONSISTENCY opens both ∀s at a common fresh γ'' and needs
         [f̂ ∼ γ''→γ''] — every route is scope-refused (assign: γ'' is
         newer than f̂; solve-deposit: the fresh flexibles sit below γ'';
         SkipRigid: γ'' ∈ ftv).  STUCK.  No alternative choice point
         exists upstream (ForallL is the only a_sub entry at a ∀ subject
         with an arrow P0).

    ⟹ NO [a_sub] run exists at this configuration, while the join + fill
    are Qed-inhabited and met.exe ACCEPTS the corresponding SOURCE program
    (whose typing builds a DIFFERENT payload).  I.e. thm:complete-subtyping
    is refuted AT THE RULE LEVEL by a payload the TYPING NEVER PRODUCES —
    the theorem's quantification over P0 is broader than the reachable
    payloads.  ⭐⭐⭐ And the failing payload shape is EXACTLY the shield
    saga's residual: a P0 with a ∀ below its head (at a consis-feeding
    position).  prop_sub_shield_supply.v's covered shapes (∀-free /
    mono-counterpart / inh-free / flex-free) are the REACHABLE ones.

    THE REPAIR THIS POINTS TO: a PAYLOAD side condition on the theorem
    (the typing's actual P0-invariant — ∀-freeness of consis-feeding
    payload positions, or whatever the typing maintains), under which the
    existing supply routes become TOTAL and [main_forall] discharges.
    TO DO IN COQ: build steps 1–3 as derivations, prove step 4's ¬∃ by
    inversion (bounded, cex-style), then state the reachability repair and
    take it to PAPER-GAPS + the authors. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.prop_basic.
Require Import src.frost.algo.cex.cex_p7_shield_forall_flex.
Require Import src.frost.algo.cex.cex_p7_shield_double_occ.

Set Implicit Arguments.

(* The two decision goals, stated so the next session only has to prove ONE
   of them.  [Θ0d]/[P0d] are Section-discharged functions of the atom [f] —
   Check them before writing instances. *)

(* Check (fun f => Θ0d f). *)
(* Check (fun f => P0d f). *)
