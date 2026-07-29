(** Stability of the declarative-over-Θ judgments under information
    increase (the paper's "stability" remark, proofs.tex:19-26): if
    [Θ ⊢ J] and [Θ ⊴ Θ'], then [Θ' ⊢ J].

    The judgments only consult the context through (i) tvar-ish variable
    lookups, (ii) flexible-definition lookups (FlexL/FlexR), and (iii)
    rigid-tvar extensions for binders — all transported by the [prop_inc]
    kit and the definition-preservation component of [⊴]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.

Set Implicit Arguments.

(* ===================================================================== *)
(*  ⊴ transport wrappers                                                  *)
(* ===================================================================== *)

Lemma a_isub_binds_tvarish : forall Θ Θ' α,
  Θ ⊴ Θ' ->
  a_binds_tvar α Θ ->
  a_binds_tvar α Θ'.
Proof.
  intros * [[κ [Hid Hinc]] _] Hb. eauto using a_inc_binds_tvarish.
Qed.

Lemma a_isub_binds_flex_def : forall Θ Θ' α τ,
  Θ ⊴ Θ' ->
  binds α (abind_flex_mono_def τ) Θ ->
  binds α (abind_flex_mono_def τ) Θ'.
Proof. intros * [_ Hd] Hb. auto. Qed.

(** ⊴ is preserved by pushing a rigid tvar on both sides. *)
Lemma a_isub_cons_tvar : forall Θ Θ' α',
  Θ ⊴ Θ' ->
  ((α' ~ abind_tvar) ++ Θ) ⊴ ((α' ~ abind_tvar) ++ Θ').
Proof.
  intros * [[κ [Hid Hinc]] Hd]. split.
  - exists κ. split; auto.
    apply (a_inc__tvar (Ξ := nil)); auto. constructor.
  - intros α τ Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    unfold binds; apply in_or_app; right. apply Hd; auto.
Qed.

(* ===================================================================== *)
(*  Stability of the Θ-level declarative judgments                        *)
(* ===================================================================== *)

Lemma a_wf_pskl_isub : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall Θ', Θ ⊴ Θ' ->
  Θ' ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H; induction H; intros Θ' Hle;
    eauto using a_wf_pskl.
  - (* var *)
    apply a_wf_pskl__var.
    destruct H as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
Qed.

Lemma ad_pat_consis_isub : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  forall Θ', Θ ⊴ Θ' ->
  Ψ ⨟ Θ' ⊢ₛᵃ R ∼ Q.
Proof.
  intros Ψ Θ R Q H; induction H; intros Θ' Hle.
  - apply ad_pat_consis__unit; auto.
  - apply ad_pat_consis__var; eauto using a_isub_binds_tvarish.
  - eapply ad_pat_consis__arrow; eauto.
  - eapply ad_pat_consis__forall_inh_tagged with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - eapply ad_pat_consis__forall_inh_untagged with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - eapply ad_pat_consis__forall_syn_tagged with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - eapply ad_pat_consis__forall_syn with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_pat_consis__ghostg; auto.
  - apply ad_pat_consis__topholeg; auto.
  - apply ad_pat_consis__hole; eauto using a_wf_pskl_isub.
  - apply ad_pat_consis__tophole; auto.
  - eapply ad_pat_consis__tophole_inh with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_pat_consis__tophole_drop; auto.
  - eapply ad_pat_consis__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_pat_consis__flex_r; eauto using a_isub_binds_flex_def.
Qed.

Lemma ad_refine_syn_isub : forall Θ Δ Q Q',
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ Q' ->
  forall Θ', Θ ⊴ Θ' ->
  Θ' ⨟ Δ ⊢ᵣᵃ Q ⊳ Q'.
Proof.
  intros Θ Δ Q Q' H; induction H; intros Θ' Hle.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
    destruct H as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
  - apply ad_refine_syn__arrow; auto.
  - eapply ad_refine_syn__all with (L := L); eauto.
  - apply ad_refine_syn__hole; eauto using a_wf_pskl_isub.
  - apply ad_refine_syn__tophole_remove; auto.
  - eapply ad_refine_syn__tophole_fill with (L := L).
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_refine_syn__tophole_keep; auto.
  - eapply ad_refine_syn__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_refine_syn__flex_r; eauto using a_isub_binds_flex_def.
Qed.

Lemma ad_refine_pskl_isub : forall Θ Δ P P',
  Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ P' ->
  forall Θ', Θ ⊴ Θ' ->
  Θ' ⨟ Δ ⊢ᵣₚᵃ P ⊳ P'.
Proof.
  intros Θ Δ P P' H; induction H; intros Θ' Hle.
  - apply ad_refine_pskl__unit.
  - apply ad_refine_pskl__var.
    destruct H as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
  - apply ad_refine_pskl__arrow; auto.
  - eapply ad_refine_pskl__all with (L := L); eauto.
  - apply ad_refine_pskl__hole; eauto using a_wf_pskl_isub.
  - apply ad_refine_pskl__tophole_remove; auto.
  - eapply ad_refine_pskl__tophole_fill with (L := L).
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_refine_pskl__tophole_keep; auto.
  - eapply ad_refine_pskl__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_refine_pskl__flex_r; eauto using a_isub_binds_flex_def.
Qed.
