(** PROBE (2026-08-17): [a_inc] is BLIND TO THE HEAD, so a motive that
    quantifies the derivation over an arbitrary [⊑]-larger context cannot
    line the two ASSIGNMENT WALKS up step for step.
    (docs/HANDOFF-extractable-algo-encoding.md §8c.12c.)

    ⭐ WHY THIS MATTERS FOR (c).  §8c.12a settled the motive's shape as
    "the derivation runs at some [Θd] with [κ ∷ Θ ⊑ Θd]", and showed the
    [U-Arrow] case closes with that reading.  What it did not check is the
    ASSIGN component, and the assign judgement dispatches on the CONTEXT'S
    HEAD: [Assign-SolveM] fires when the head IS the flexible target,
    [Assign-Assign] when the head is some other DEFINED flexible,
    [Assign-Skip] / [Assign-Depend] / [Assign-SkipRigid] when it is
    something else.

    ⚠️ [a_inc] constrains none of that.  Below, the target context is the
    source with an ENTIRELY NEW defined flexible pushed on top — and the
    increase still holds, at the IDENTITY metasubstitution.  So from
    [κ ∷ Θ ⊑ Θd] one may NOT conclude that the two walks take the same
    rule, nor even that they take the same NUMBER of steps: the runner at
    [Θ] fires [Assign-SolveM] immediately, while the derivation at [Θd]
    must first step past [β̂ ≔ 1] by [Assign-Assign].

    ⇒ A runner-sided induction consumes ONE runner step per case, so the
    derivation's extra steps have nowhere to go.  Closing (c) therefore
    needs one of:

      (1) a STRUCTURAL context refinement (entries matched positionally,
          with solved-in-place and fresh-insertion as the only moves) in
          place of bare [a_inc], plus inversion lemmas that absorb the
          derivation's extra pass-through steps; or
      (2) a runner-MONOTONICITY induction — the runner's answer at [Θ] is
          [⊑]-below its answer at any [⊑]-larger [Θd] — which keeps the
          motive same-context and puts all the rule-switching in one place.

    ⚙ Note this does NOT touch §8c.12's landed results: the increase, its
    [e_] face and the ghost-row inversions are all statements at a SINGLE
    context. *)

From Coq Require Import Lists.List.
From Metalib Require Import Metatheory.

From src Require Import frost.notations.
From src Require Import frost.def_shapes.
From src Require Import frost.algo.def_rules.
From src Require Import frost.algo.def_meta.

Open Scope frost_a_scope.

(** The runner's context, and a [⊑]-larger one whose HEAD is new. *)
Definition head_src (α : atom) : aenv := (α ~ abind_flex_mono) ++ nil.
Definition head_tgt (α β : atom) : aenv :=
  (β ~ abind_flex_mono_def ptyp_unit) ++ (α ~ abind_flex_mono) ++ nil.

(** ⛔ The increase holds, at the identity — yet the two contexts disagree
    about which rule an assignment walk for [α̂] fires first. *)
Lemma probe_inc_head_blind : forall α β,
  ((α, ptyp_var_f α) :: nil) ∷ (head_src α) ⊑ (head_tgt α β).
Proof.
  intros α β. unfold head_src, head_tgt.
  apply a_inc__flex.
  - apply a_inc__empty.
    apply a_suffix__cons; [ | apply a_suffix_binding__flex_mono_def ].
    apply a_suffix__cons; [ | apply a_suffix_binding__flex_mono ].
    apply a_suffix__nil.
  - apply a_wf_ptyp__var. right; left.
    unfold binds; right; left; reflexivity.
  - apply mono_ptyp__var.
Qed.

(** And the heads really are different constructors, which is what the
    assign judgement branches on. *)
Lemma probe_head_differs : forall α β,
  (exists Θ, head_src α = (α ~ abind_flex_mono) ++ Θ)
  /\ (exists Θ, head_tgt α β = (β ~ abind_flex_mono_def ptyp_unit) ++ Θ).
Proof.
  intros α β. split; [ exists nil | exists ((α ~ abind_flex_mono) ++ nil) ];
    reflexivity.
Qed.
