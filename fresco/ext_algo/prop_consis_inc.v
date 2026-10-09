(** THE GHOST-ROW INVERSIONS of the threaded consistency trio — the cells
    where a hole meets a pattern or a subject, as prop_consis_complete.v
    consumes them.

    At a hole SUBJECT only [U-Ghost] can fire unless the pattern is a
    variable, and at a hole PATTERN only [U-GhostR] can unless the subject
    is.  ⚙ [U-UnivGhostR] is excluded everywhere here because it demands a
    GUARDED subject and [◇] is not guarded ([guarded_pskl] is
    [1 | α | A → B] and nothing else).  The two variable cells are mirror
    images; since the [<> ◇] dispatch guards landed on [U-FlexL]/[U-FlexR]
    each of them admits exactly one rule as well. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.prop_basic.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.prop_consis.
Require Import src.fresco.ext_algo.prop_termination.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(** ⚙ The surviving goals are the rule's own premises plus, at the [(◇,◇)]
    overlap, a disjointness against [ftvar_in_pskl ◇ = ∅]. *)
Local Ltac ghost_close :=
  repeat split;
  first [ assumption | reflexivity | (simpl in *; fsetdec) ].

(** A hole SUBJECT against a non-variable pattern: only [U-Ghost]. *)
Lemma e_consis_inv_hole_subject : forall Δ1 Δ2 S0 Θ0 P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] pskl_hole ∼ Q ⊣ Θ1 }}e ->
  (forall β, P0 <> pskl_var_f β) ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = P0 /\ Δ2 ∩ ftvar_in_pskl P0 [=] empty.
Proof.
  intros * Hd Hnv. inversion Hd; subst;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | match goal with
                | H : guarded_pskl pskl_hole |- _ => inversion H
                end ].
  all: ghost_close.
Qed.

(** A hole PATTERN against a non-variable subject: only [U-GhostR].
    ⚙ The subject may itself be [◇]: there [U-Ghost] fires too, but it
    returns the SAME triple, so the cell needs no uniqueness argument —
    the level-5 analogue of [U-Rigid] versus [U-Flex], which [e_unify_refl]
    settled the same way. *)
Lemma e_consis_inv_hole_pattern : forall Δ1 Δ2 S0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_hole ] P ∼ Q ⊣ Θ1 }}e ->
  (forall β, P <> pskl_var_f β) ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = P /\ Δ1 ∩ ftvar_in_pskl P [=] empty.
Proof.
  intros * Hd Hnv. inversion Hd; subst;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | match goal with
                | H : guarded_pskl pskl_hole |- _ => inversion H
                end ].
  all: ghost_close.
Qed.

(** ⭐ FORMERLY DIVERGENT CELL 1 — a hole subject against a FLEXIBLE
    pattern.  [U-Ghost] leaves the context alone; [U-FlexR] would have
    assigned, and the runner takes the first
    (def_consis_impl.v:807-813).  Since the [<> ◇] dispatch guards landed
    on [U-FlexL]/[U-FlexR] (algo/def_rules.v) the second route is BARRED,
    so this cell now admits exactly ONE rule and the inversion is no
    longer a disjunction — which is what retires the two-context problem
    docs/HANDOFF-close-consis-unrestricted.md was written about. *)
Lemma e_consis_inv_hole_flex_pattern : forall Δ1 Δ2 S0 Θ0 β Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ] pskl_hole ∼ Q ⊣ Θ1 }}e ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = pskl_var_f β
    /\ Δ2 ∩ ftvar_in_pskl (pskl_var_f β) [=] empty.
Proof.
  intros * Hd. inversion Hd; subst;
    try solve [ congruence
              | match goal with
                | H : guarded_pskl pskl_hole |- _ => inversion H
                end ].
  ghost_close.
Qed.

(** ⭐ FORMERLY DIVERGENT CELL 2 — the mirror: a FLEXIBLE subject against
    a hole pattern.  [U-GhostR] versus [U-FlexL], the runner takes GhostR
    (def_consis_impl.v:759-763, whose hole-pattern arm is unconditional in
    the subject), and the [<> ◇] guard now bars [U-FlexL] here, so this
    cell too admits exactly one rule. *)
Lemma e_consis_inv_flex_subject_hole : forall Δ1 Δ2 S0 Θ0 α Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_hole ] (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = pskl_var_f α
    /\ Δ1 ∩ ftvar_in_pskl (pskl_var_f α) [=] empty.
Proof.
  intros * Hd. inversion Hd; subst;
    try solve [ congruence
              | match goal with
                | H : guarded_pskl pskl_hole |- _ => inversion H
                end ].
  ghost_close.
Qed.
