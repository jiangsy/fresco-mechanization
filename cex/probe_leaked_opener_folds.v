(** PROBE (2026-08-23): ⛔⛔ **"A LEAKED OPENER MAKES THE FOLD STUCK" IS FALSE**,
    and with it the no-leak-into-[𝒞] design and every simplification costed on
    it (docs/REPORT-proof-path-audit.md §4c tiers 1–4).

    ⚠️ THE HYPOTHESIS UNDER TEST.  The collection's five ∀ rows leak their
    opener into [𝒞].  `cex/probe_extract_conflated_opener.v` §2b observes that
    at a UNIT accumulator a genuinely-rigid opener leaves the fold stuck —
    [1 ∼ δ] matches no [a_solve_eq] row — which suggested that a leaked opener
    never contributes to a SUCCESSFUL run, hence that the collection could
    simply REJECT at emission (the standard skolem-escape check) and lose
    nothing.  That would delete the [ρx] column, make [rel_fun] global, and
    collapse the relational currency to a functional one.

    ⛔ IT IS FALSE, AND THE COUNTEREXAMPLE IS ONE RULE.  [SE-GhostL]
    ([a_solve_eq__ghost_l], algo/def_rules.v) is

        {{ Θ ⊢ₑ pskl_ghost ∼ Q ⤳ nil ⨾ Q }}a

    with NO side condition on [Q] whatsoever.  At a GHOST accumulator the fold
    accepts an arbitrary target and RETURNS IT.  So a constraint carrying an
    opener bound nowhere in the fold's context is not stuck — it succeeds, and
    the opener propagates into the fold's RESULT.  §2b's stuckness was an
    artefact of its UNIT accumulator, not a property of leaked openers.

    ⇒ THE LEAK IS LOAD-BEARING.  Rejecting at emission would reject runs that
    today succeed and are filtered — correctly and later — by the wf side
    condition [a_sub__forall_l]'s [{{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a], exactly as
    algo/def_rules.v's [a_solve_sub__forall_r] header already says: "the leak is
    BY DESIGN; ill-scoped results are filtered downstream by wf side
    conditions, NOT by narrowing this rule."

    ⇒ [ρx] STAYS, [rel_fun] STAYS LOCAL, AND THE RELATIONAL ρ IS NOT AN
    ACCIDENT OF LAZY DESIGN.  It is forced. *)

From Coq Require Import Lists.List.
From Metalib Require Import Metatheory.

From src Require Import fresco.notations.
From src Require Import fresco.def_shapes.
From src Require Import fresco.algo.def_rules.

Open Scope fresco_a_scope.

(** §1  The one rule that does it: [SE-GhostL] accepts ANY target. *)
Lemma se_ghostl_accepts_anything : forall Θ Q,
  {{ Θ ⊢ₑ pskl_ghost ∼ Q ⤳ nil ⨾ Q }}a.
Proof. intros. apply a_solve_eq__ghost_l. Qed.

(** §2  ⛔ THE REFUTATION.  A constraint whose target is an atom the fold's
    context does NOT bind — a leaked opener, in the exact sense
    prop_solve_rel.v §9 means it ("bound NOWHERE — not in [Θ0], not in [Ξ]") —
    folds SUCCESSFULLY against a ghost accumulator, and the result IS that
    atom.  Note [β] is universally quantified and constrained only by
    [β ∉ dom Θ]: the fold never looks. *)
Lemma leaked_opener_folds : forall Θ (β : atom),
  β `notin` dom Θ ->
  {{ Θ ⊩ (a_cstr_eq (pskl_var_f β) :: nil) ⨾ pskl_ghost
       ⤳ nil ⨾ (pskl_var_f β) }}a.
Proof.
  intros Θ β _.
  change (@nil (atom * abind)) with ((@nil (atom * abind)) ++ (@nil (atom * abind))).
  eapply a_solve_cstr__eq.
  - apply a_solve_eq__ghost_l.
  - simpl. apply a_solve_cstr__empty.
Qed.

(** §3  …and the leaked atom is genuinely in the OUTPUT, so it is not merely
    tolerated in an intermediate: it reaches [a_extract]'s result. *)
Lemma leaked_opener_reaches_the_result : forall Θ (β : atom),
  β `notin` dom Θ ->
  exists Ξ Pa,
    {{ Θ ⊩ (a_cstr_eq (pskl_var_f β) :: nil) ⨾ pskl_ghost ⤳ Ξ ⨾ Pa }}a
    /\ β `in` ftvar_in_pskl Pa.
Proof.
  intros Θ β Hβ. exists nil, (pskl_var_f β).
  split; [ apply leaked_opener_folds; exact Hβ | simpl; fsetdec ].
Qed.
