(** THE THREADED TRIO ONLY ADDS INFORMATION — the [e_] face of
    `algo/consis/prop_consis_inc.v`.

    ⭐ WHAT IT IS FOR.  §8c.12 of
    docs/HANDOFF-extractable-algo-encoding.md lifts the consistency
    runner's completeness off its hole-free restriction.  §8c.12a scoped
    that to TWO divergent cells — (pattern [β̂] flexible, subject [◇]) and
    its mirror (pattern [◇], subject [α̂] flexible) — at both of which the
    RUNNER answers with its input context UNCHANGED while the derivation
    may run an assignment walk.  So the level's whole [⊑] obligation is
    that the walk only ADDED information, which is [e_assign_isub] below.

    ⚙ NOTHING NEW IS PROVED HERE.  The content is the [a_] lemma; this file
    is the bridge composition, and it is cheap precisely because
    prop_consis.v §4 relates [e_] to [a_] over the SAME contexts.  ⭐ Its
    two hypotheses ([uniq], coverage) are the ones
    prop_consis_complete.v's motive ALREADY carries
    ([consis_call_uniq] / [consis_call_cover]), so they cost the consumer
    nothing.

    ⚠️ [lc_aenv] IS A GENUINELY NEW SIDE CONDITION and the level's motive
    will have to carry it.  It is not derivable from what is already
    there: [consis_call_lc] constrains the SKELETONS, not the context, and
    coverage is a statement about names.  It is also not avoidable —
    reflexivity of [⊴] needs it, because [a_inc]'s term-variable rows
    demand [Θ' ⊢ A' ≡ᵗ κA] and the equational theory's base rule demands
    local closure.  It IS the minimal such hypothesis: every well-formed
    context satisfies it ([a_wf_aenv_lc_aenv], algo/prop_basic.v).

    ⭐ [aenv_defs_lc], by contrast, is FREE at every call site: it follows
    from [aenv_defs_mono], which is already an INPUT of every runner call
    ([consis_call_defs_mono], ext_algo/def_consis_impl.v). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.prop_coercions.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.def_meta.
Require Import src.frost.prop_basic.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.consis.prop_consis_inc.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.prop_consis.
Require Import src.frost.ext_algo.prop_termination.

Set Implicit Arguments.

Open Scope frost_a_scope.
Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  the runner's own context discipline supplies the definition half  *)
(* ===================================================================== *)

Lemma aenv_defs_mono_defs_lc : forall Θ, aenv_defs_mono Θ -> aenv_defs_lc Θ.
Proof.
  intros Θ H α τ Hb.
  apply mono_ptyp_lc.
  exact (proj1 (Forall_forall _ Θ) H (α, abind_flex_mono_def τ) Hb).
Qed.

(* ===================================================================== *)
(*  §2  the three increases, threaded                                     *)
(* ===================================================================== *)

Lemma e_assign_isub : forall S0 Θ0 Ξ α P S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  uniq (Ξ ++ Θ0) ->
  ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S0 ->
  a_suffix Ξ ->
  lc_aenv (Ξ ++ Θ0) ->
  aenv_defs_mono (Ξ ++ Θ0) ->
  Θ0 ⊴ Θ1.
Proof.
  intros * Hd Huq Hcov Hsuf Hlc Hdm.
  pose proof (proj1 e_assign_unify_consis_sound _ _ _ _ _ _ _ Hd Huq Hcov)
    as [Ha _].
  exact (proj1 a_assign_unify_consis_isub _ _ _ _ _ Ha Hsuf Hlc
           (aenv_defs_mono_defs_lc Hdm)).
Qed.

Lemma e_unify_isub : forall S0 Θ0 α β S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 [<=] S0 ->
  lc_aenv Θ0 ->
  aenv_defs_mono Θ0 ->
  Θ0 ⊴ Θ1.
Proof.
  intros * Hd Huq Hcov Hlc Hdm.
  pose proof (proj1 (proj2 e_assign_unify_consis_sound)
                _ _ _ _ _ _ Hd Huq Hcov) as [Ha _].
  exact (proj1 (proj2 a_assign_unify_consis_isub) _ _ _ _ Ha Hlc
           (aenv_defs_mono_defs_lc Hdm)).
Qed.

Lemma e_consis_isub : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P ∪ Δ1 ∪ Δ2 [<=] S0 ->
  lc_aenv Θ0 ->
  aenv_defs_mono Θ0 ->
  Θ0 ⊴ Θ1.
Proof.
  intros * Hd Huq Hcov Hlc Hdm.
  pose proof (proj2 (proj2 e_assign_unify_consis_sound)
                _ _ _ _ _ _ _ _ _ Hd Huq Hcov) as [Ha _].
  exact (proj2 (proj2 a_assign_unify_consis_isub) _ _ _ _ _ _ _ Ha Hlc
           (aenv_defs_mono_defs_lc Hdm)).
Qed.

(** ⭐ THE ONE THE TWO DIVERGENT CELLS CONSUME.  Both [U-FlexL] and
    [U-FlexR] call the walk with an EMPTY pending block, and the runner
    answers those cells with [Θ] untouched — so this is exactly "the
    runner's answer is ⊴-below the derivation's". *)
Corollary e_assign_nil_isub : forall S0 Θ0 α P S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ P ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P [<=] S0 ->
  lc_aenv Θ0 ->
  aenv_defs_mono Θ0 ->
  Θ0 ⊴ Θ1.
Proof.
  intros * Hd Huq Hcov Hlc Hdm.
  eapply e_assign_isub; simpl_env; eauto. apply a_suffix__nil.
Qed.

(* ===================================================================== *)
(*  §3  THE GHOST-ROW INVERSIONS                                          *)
(*                                                                        *)
(*  The six cells prop_consis_complete.v currently kills with             *)
(*  [pskl_no_hole] (§8c.12a's table).  ⭐ FOUR of them admit exactly ONE   *)
(*  rule and so need no [⊑] at all: at a hole SUBJECT only [U-Ghost] can  *)
(*  fire unless the pattern is a variable, and at a hole PATTERN only     *)
(*  [U-GhostR] can unless the subject is.  ⚙ [U-UnivGhostR] is excluded   *)
(*  everywhere here because it demands a GUARDED subject and [◇] is not   *)
(*  guarded ([guarded_pskl] is [1 | α | A → B] and nothing else).         *)
(*                                                                        *)
(*  The two that remain are mirror images, and each comes out as a        *)
(*  DISJUNCTION whose second branch is an assignment walk — which is      *)
(*  exactly what §2's increase measures.                                  *)
(* ===================================================================== *)

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
