(** STRUCTURAL KIT for [ad_pat_sub] and [ad_partial_precise]
    (docs/DESIGN-subtyping.md P2).

    The tag-context congruences and the [⊴]-stability lemmas — the exact
    mirrors of [ad_pat_consis_psi_cong] (prop_consis_sound.v) and of the
    [prop_stability.v] family: every declarative-over-Θ judgment is stable
    under information increase, because its only context-sensitive rules are
    variable visibility ([a_isub_binds_tvarish]), definition lookups
    ([a_isub_binds_flex_def]), rigid-binder extension ([a_isub_cons_tvar]),
    and skeleton well-formedness ([ad_wf_pskl_isub]). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_consis_sound.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Tag-context congruence                                            *)
(* ===================================================================== *)

Lemma ad_pat_sub_psi_cong : forall NM M Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⊑ Q ->
  forall Ψc, Ψ [=] Ψc ->
  Ψc ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⊑ Q.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros Ψc Heq.
  - (* Infer *) apply ad_pat_sub__infer; auto. fsetdec.
  - (* Check keeps the SAME Ψ on its consistency premise: transport it. *)
    apply ad_pat_sub__check; auto.
    eapply ad_pat_consis_psi_cong; eauto.
  - (* ForallR : the same Ψ threads through the binder premise *)
    eapply ad_pat_sub__forall_r with (L := L).
    intros α Hα. apply H0; auto.
  - (* UnivGhostR *) apply ad_pat_sub__univ_ghost_r; auto. fsetdec.
  - (* Arrow : sub-premise keeps its own Ψ2 *)
    eapply ad_pat_sub__arrow; eauto. fsetdec.
  - (* ForallL tagged : rec at Ψc ∪ Ψ' *)
    eapply ad_pat_sub__forall_l_tagged; eauto;
      first [ apply IHad_pat_sub; fsetdec | fsetdec ].
  - (* ForallL untagged *)
    eapply ad_pat_sub__forall_l_untagged; eauto;
      first [ apply IHad_pat_sub; fsetdec | fsetdec ].
  - (* Ghost *) apply ad_pat_sub__ghost; auto. fsetdec.
  - (* GhostG *) apply ad_pat_sub__ghostg; auto. fsetdec.
  - (* UnivGhostL *)
    apply ad_pat_sub__univ_ghost_l; [ auto | apply IHad_pat_sub; exact Heq ].
  - (* UnivGhostLG *)
    apply ad_pat_sub__univ_ghost_lg; [ auto | apply IHad_pat_sub; exact Heq ].
  - (* FlexMono *)
    eapply ad_pat_sub__flex_mono; [ eauto | apply IHad_pat_sub; exact Heq ].
Qed.

Lemma ad_partial_precise_psi_cong : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Ψc, Ψ [=] Ψc ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψc ] ψ.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Ψc Heq;
    econstructor; eauto; fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  Stability under information increase [⊴]                          *)
(* ===================================================================== *)

Lemma ad_pat_sub_isub : forall NM M Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⊑ Q ->
  forall Θ', Θ ⊴ Θ' ->
  Ψ ⨟ Θ' ⊢ₛᵃ[ NM | M ] R ⊑ Q.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros Θ' Hle.
  - apply ad_pat_sub__infer; eauto using ad_pat_consis_isub.
  - apply ad_pat_sub__check; eauto using ad_pat_consis_isub.
  - eapply ad_pat_sub__forall_r with (L := L); eauto.
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_pat_sub__univ_ghost_r; eauto using ad_pat_consis_isub.
  - eapply ad_pat_sub__arrow; eauto using ad_pat_consis_isub.
  - eapply ad_pat_sub__forall_l_tagged; eauto using ad_wf_pskl_isub.
  - eapply ad_pat_sub__forall_l_untagged; eauto using ad_wf_pskl_isub.
  - apply ad_pat_sub__ghost; eauto using ad_wf_pskl_isub.
  - apply ad_pat_sub__ghostg; auto.
  - apply ad_pat_sub__univ_ghost_l; auto.
  - apply ad_pat_sub__univ_ghost_lg; auto.
  - eapply ad_pat_sub__flex_mono; eauto using a_isub_binds_flex_def.
Qed.

Lemma ad_partial_precise_isub : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Θ', Θ ⊴ Θ' ->
  Θ' ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Θ' Hle.
  - apply ad_ppre__unit; auto.
  - apply ad_ppre__var; auto.
    destruct H0 as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
  - eapply ad_ppre__arrow; eauto.
  - eapply ad_ppre__forall with (L := L); eauto.
  - apply ad_ppre__hole; auto.
  - apply ad_ppre__tophole_remove; auto.
  - eapply ad_ppre__tophole_fill with (L := L).
    intros X HX. eauto using a_isub_cons_tvar.
  - apply ad_ppre__tophole_keep; auto.
  - eapply ad_ppre__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_ppre__flex_r; eauto using a_isub_binds_flex_def.
Qed.
