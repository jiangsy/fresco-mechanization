Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.consistency.prop_precision_recovery.
Require Import src.fresco.algo.consistency.prop_consis_rename.

Set Implicit Arguments.

Require Export src.fresco.algo.consistency.prop_consis_solution.
Require Export src.fresco.algo.consistency.prop_completeness_unify.
Require Export src.fresco.algo.consistency.prop_completeness_assign.
Require Export src.fresco.algo.consistency.prop_completeness_consis_step.

Theorem complete_mu : forall m, complete_at m.
Proof.
  intro m; induction (mu_lt_wf m) as [m _ IH].
  repeat split;
    [ apply consis_complete_step
    | apply unify_complete_step
    | apply assign_complete_step ]; exact IH.
Qed.

Lemma consis_complete : forall Ψ Θ R Qb,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qb }}ad ->
  forall Δ1 Δ2 Θ0 P0 P κ,
    {{ ⊢ Θ0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
    (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    κ ∷ Θ0 ⊑ Θ ->
    {{ ⊢ Θ }}a ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    R = pskl_to_uskl (msubst_pskl κ P) ->
    {{ Θ ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Qb }}ad ->
    {{ Θ ⨟ Δ2 ⊢ᵣₚ (msubst_pskl κ P) ⊳ (bskl_to_pskl Qb) }}ad ->
    {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Qb) }}a ->
    exists P1 Θ1,
      a_consis Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           {{ Θ ⨟ (Δ1 `union` Δ2) ⊢ₚᵣ (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb) }}ad).
Proof.
  intros Ψ Θ R Qb Hj Δ1 Δ2 Θ0 P0 P κ
    Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ HeqS Hrs Hrp HwfQb.
  subst R.
  destruct (complete_mu (mu_consis Θ κ P0 P Θ0)) as [Hc _].

  destruct (Hc empty Δ1 Δ2 Θ0 P0 P κ Θ Ψ Qb eq_refl Hwf0 HwfP0 HwfP Hrig
              Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs Hrp HwfQb)
    as [P1 [Θ1 [Hcons [_ Hopt]]]].
  exists P1, Θ1. split; [ exact Hcons | exact Hopt ].
Qed.

Lemma a_consis_complete : forall Θ0 P0 P,
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  forall κ Θ Qb,
    κ ∷ Θ0 ⊑ Θ ->
    {{ ⊢ Θ }}a ->
    {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P)) ∼ Qb }}ad ->
    {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Qb }}ad ->
    {{ Θ ⨟ empty ⊢ᵣₚ (msubst_pskl κ P) ⊳ (bskl_to_pskl Qb) }}ad ->
    {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Qb) }}a ->
    exists P1 Θ1,
      a_consis empty empty Θ0 P0 P P1 Θ1 /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           {{ Θ ⨟ empty ⊢ₚᵣ
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb) }}ad).
Proof.
  intros Θ0 P0 P Hwf0 HwfP0 HwfP κ Θ Qb Hinc Hwfth Hjoin Hrs Hrp HwfQb.

  assert (Hcc : exists P1 Θ1,
      a_consis empty empty Θ0 P0 P P1 Θ1 /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           {{ Θ ⨟ (empty `union` empty) ⊢ₚᵣ (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb) }}ad)).
  { eapply consis_complete with (Δ1 := empty) (Δ2 := empty).
    all: try (first [ eassumption | reflexivity ]).
    all: try (intros α Hα; exfalso; clear - Hα; fsetdec).
    all: repeat intro; fsetdec. }
  destruct Hcc as [P1 [Θ1 [Hc Hopt]]].
  exists P1, Θ1. split; [ exact Hc | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
  exists ζ. repeat split; try assumption.

  eapply ad_refine_syn_delta_mono; [ exact Hprec | clear; fsetdec ].
Qed.
