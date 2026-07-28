(** Refinement metatheory over Θ: weakening, Δ-monotonicity, and the
    reflexivity lemmas feeding the appendix-B soundness induction
    (consistency-proofs.tex): inherited paintings refine themselves, and an
    unresolved skeleton is consistent with the synthesised painting of its
    own erasure (the paper's GhostR subsidiary induction). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_flex.

Set Implicit Arguments.

(** Erasure commutes with opening (converse direction of
    [pskl_to_uskl_open_rec] in prop_decorate.v). *)
Lemma uskl_to_pskl_open_rec : forall R0 R' k,
  uskl_to_pskl (open_uskl_wrt_uskl_rec k R' R0)
  = open_pskl_wrt_pskl_rec k (uskl_to_pskl R') (uskl_to_pskl R0).
Proof.
  induction R0; intros; simpl; f_equal; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

(* ===================================================================== *)
(*  Δ-monotonicity and painting transport                                 *)
(* ===================================================================== *)

(** Δ-monotonicity: enlarging the ∀-scope set preserves well-formedness
    (occurrences only ever TEST membership positively). *)
Lemma a_wf_pskl_delta_mono : forall Θ Δ0 P,
  Θ ⨟ Δ0 ⊢ₚₛᵃ P ->
  forall Δ, Δ0 [<=] Δ ->
  Θ ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ0 P H; induction H; intros Δ' Hsub; eauto using a_wf_pskl.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Htv]; [ left; fsetdec | auto ].
  - apply a_wf_pskl__all with (L := L).
    intros X HX. apply H0; auto. fsetdec.
Qed.

Lemma lc_pskl_to_bskl_inh : forall P,
  lc_pskl P -> lc_bskl (pskl_to_bskl_inh P).
Proof.
  intros P H; induction H; simpl; auto.
  apply lc_bskl_all_inh. intros X.
  rewrite <- pskl_to_bskl_inh_open; auto.
Qed.

Lemma guarded_pskl_to_bskl_inh : forall P,
  guarded_pskl P -> guarded_bskl (pskl_to_bskl_inh P).
Proof.
  intros P H; inversion H; subst; simpl; constructor;
    auto using lc_pskl_to_bskl_inh.
Qed.

(* ===================================================================== *)
(*  Binds-monotone weakening of the refinement judgments                   *)
(* ===================================================================== *)

Lemma ad_refine_syn_weaken : forall Θ Δ Q Q',
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ Q' ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Θ' ⨟ Δ ⊢ᵣᵃ Q ⊳ Q'.
Proof.
  intros Θ Δ Q Q' H; induction H; intros Θ' Hmon.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
    destruct H as [HΔ | [Hb | [Hb | [τ Hb]]]];
      [ left | right; left | right; right; left
      | right; right; right; exists τ ]; auto.
  - apply ad_refine_syn__arrow; auto.
  - eapply ad_refine_syn__all with (L := L); eauto.
  - apply ad_refine_syn__hole.
    eapply a_wf_pskl_weaken; eauto.
  - apply ad_refine_syn__tophole_remove; auto.
  - eapply ad_refine_syn__tophole_fill with (L := L).
    intros X HX. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_refine_syn__tophole_keep; auto.
  - eapply ad_refine_syn__flex_l; eauto.
  - eapply ad_refine_syn__flex_r; eauto.
Qed.

Lemma ad_refine_pskl_weaken : forall Θ Δ P P',
  Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ P' ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Θ' ⨟ Δ ⊢ᵣₚᵃ P ⊳ P'.
Proof.
  intros Θ Δ P P' H; induction H; intros Θ' Hmon.
  - apply ad_refine_pskl__unit.
  - apply ad_refine_pskl__var.
    destruct H as [HΔ | [Hb | [Hb | [τ Hb]]]];
      [ left | right; left | right; right; left
      | right; right; right; exists τ ]; auto.
  - apply ad_refine_pskl__arrow; auto.
  - eapply ad_refine_pskl__all with (L := L); eauto.
  - apply ad_refine_pskl__hole.
    eapply a_wf_pskl_weaken; eauto.
  - apply ad_refine_pskl__tophole_remove; auto.
  - eapply ad_refine_pskl__tophole_fill with (L := L).
    intros X HX. apply H0; auto.
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? ?] | Hb']; subst;
      [ unfold binds; left; reflexivity
      | unfold binds; right; apply Hmon; auto ].
  - apply ad_refine_pskl__tophole_keep; auto.
  - eapply ad_refine_pskl__flex_l; eauto.
  - eapply ad_refine_pskl__flex_r; eauto.
Qed.

(* ===================================================================== *)
(*  Reflexivity of refinement                                             *)
(* ===================================================================== *)

(** Helper: refinement from an empty Δ holds at any Δ (occurrences only
    test Δ-membership positively). *)
Lemma ad_refine_syn_delta_mono : forall Θ Δ0 Q Q',
  Θ ⨟ Δ0 ⊢ᵣᵃ Q ⊳ Q' ->
  forall Δ, Δ0 [<=] Δ ->
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ Q'.
Proof.
  intros Θ Δ0 Q Q' H; induction H; intros Δ' Hsub;
    eauto using ad_refine_syn.
  - apply ad_refine_syn__var.
    destruct H as [HΔ | Htv]; [ left; fsetdec | auto ].
  - apply ad_refine_syn__all with (L := L).
    intros X HX. apply H0; auto. fsetdec.
Qed.

Lemma ad_refine_pskl_delta_mono : forall Θ Δ0 P P',
  Θ ⨟ Δ0 ⊢ᵣₚᵃ P ⊳ P' ->
  forall Δ, Δ0 [<=] Δ ->
  Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ P'.
Proof.
  intros Θ Δ0 P P' H; induction H; intros Δ' Hsub;
    eauto using ad_refine_pskl.
  - apply ad_refine_pskl__var.
    destruct H as [HΔ | Htv]; [ left; fsetdec | auto ].
  - apply ad_refine_pskl__all with (L := L).
    intros X HX. apply H0; auto. fsetdec.
Qed.

Lemma ad_refine_syn_refl_inh : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  Θ ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh P).
Proof.
  intros Θ Δ P H; induction H; simpl.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var; auto.
  - apply ad_refine_syn__arrow; auto.
  - apply ad_refine_syn__all with (L := L).
    intros X HX.
    repeat rewrite <- pskl_to_bskl_inh_open. auto.
  - replace (pskl_to_bskl_inh pskl_hole)
      with (pskl_to_bskl_syn pskl_hole) at 2 by reflexivity.
    apply ad_refine_syn__hole. apply a_wf_pskl__hole.
  - apply ad_refine_syn__tophole_keep;
      auto using guarded_pskl_to_bskl_inh.
    eapply ad_refine_syn_delta_mono; eauto. fsetdec.
Qed.

Lemma ad_refine_pskl_refl : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ P.
Proof.
  intros Θ Δ P H; induction H; simpl.
  - apply ad_refine_pskl__unit.
  - apply ad_refine_pskl__var; auto.
  - apply ad_refine_pskl__arrow; auto.
  - apply ad_refine_pskl__all with (L := L). auto.
  - apply ad_refine_pskl__hole. apply a_wf_pskl__hole.
  - apply ad_refine_pskl__tophole_keep; auto.
    eapply ad_refine_pskl_delta_mono; eauto. fsetdec.
Qed.

(* ===================================================================== *)
(*  Consistency reflexivity along the erasure (the GhostR subsidiary       *)
(*  induction of the paper's soundness proof): an unresolved skeleton is   *)
(*  consistent, with no solved tags, with the synthesised painting of its  *)
(*  own erasure.                                                          *)
(* ===================================================================== *)

Lemma ad_pat_consis_refl_erase : forall R' Θ,
  lc_uskl R' ->
  (forall X, X `in` ftvar_in_uskl R' -> a_binds_tvar X Θ) ->
  ad_pat_consis empty Θ R' (pskl_to_bskl_syn ⌊ R' ⌋ˢ).
Proof.
  intros R' Θ Hlc; revert Θ; induction Hlc; intros Θ Hvis; simpl.
  - apply ad_pat_consis__unit. fsetdec.
  - apply ad_pat_consis__var; [ fsetdec | ].
    apply Hvis. simpl. fsetdec.
  - apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHlc1 | apply IHHlc2 | fsetdec ];
      intros X HX; apply Hvis; simpl; fsetdec.
  - (* all_syn ↦ ∀ syn *)
    apply ad_pat_consis__forall_syn with (L := dom Θ).
    intros X HX.
    rewrite <- pskl_to_bskl_syn_open.
    replace (open_pskl_wrt_pskl ⌊ R ⌋ˢ (pskl_var_f X))
      with (⌊ open_uskl_wrt_uskl R (uskl_var_f X) ⌋ˢ)
      by (unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl;
          apply uskl_to_pskl_open_rec).
    apply H0.
    intros Y HY.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                  R (uskl_var_f X)) as Hup.
    simpl in Hup.
    assert (HY' : Y `in` (singleton X `union` ftvar_in_uskl R))
      by (clear - HY Hup; fsetdec).
    destruct (union_1 HY') as [HYX | HYR].
    + apply singleton_1 in HYX; subst.
      left. unfold binds; left; reflexivity.
    + apply a_binds_tvar_weaken_cons; auto.
  - (* all_etag ↦ ∀ syn (ForallSyn on a tagged head, tag unsolved) *)
    apply ad_pat_consis__forall_syn_tagged with (L := dom Θ).
    intros X HX.
    rewrite <- pskl_to_bskl_syn_open.
    replace (open_pskl_wrt_pskl ⌊ R ⌋ˢ (pskl_var_f X))
      with (⌊ open_uskl_wrt_uskl R (uskl_var_f X) ⌋ˢ)
      by (unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl;
          apply uskl_to_pskl_open_rec).
    apply H0.
    intros Y HY.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                  R (uskl_var_f X)) as Hup.
    simpl in Hup.
    assert (HY' : Y `in` (singleton X `union` ftvar_in_uskl R))
      by (clear - HY Hup; fsetdec).
    destruct (union_1 HY') as [HYX | HYR].
    + apply singleton_1 in HYX; subst.
      left. unfold binds; left; reflexivity.
    + apply a_binds_tvar_weaken_cons; auto.
  - (* hole ↦ □ : the RHS is the inherited painting of □ *)
    replace bskl_hole with (pskl_to_bskl_inh pskl_hole) by reflexivity.
    apply ad_pat_consis__hole; [ fsetdec | apply a_wf_pskl__hole ].
  - (* tophole ↦ ⊤ *)
    apply ad_pat_consis__tophole. auto.
  - (* holeg ↦ □ *)
    apply ad_pat_consis__ghostg. fsetdec.
  - (* topholeg ↦ ⊤ *)
    apply ad_pat_consis__topholeg. auto.
Qed.
