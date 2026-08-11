(** COMPLETENESS + OPTIMALITY OF ALGORITHMIC SUBTYPING.

    Paper: [thm:complete-subtyping] (algorithmic.tex:1446); proofs
    subtyping-proofs.tex:1526-3536.  Plan: docs/DESIGN-completeness-subtyping.md.

    This file builds bottom-up, starting at P5b.  ⚙ It used to open with a
    P5a block — the non-hygienic fuel measure [ad_pat_sub_n] and its five
    bridges — which was deleted 2026-08-11 with the judgment it served; see
    the RESTART NOTE below and in algo_decl/def_decl_algo_sub.v. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo_decl.def_decl_algo.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_decl_algo_sub.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.sub.prop_soundness_sub.  (* ad_pat_sub_gv_psi_cong *)
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.consis.prop_consis_precise.

Set Implicit Arguments.

(* ⚙ RESTART NOTE (2026-08-10) — P5a's fuel-measure block ([ad_pat_sub_of_n],
   [ad_pat_sub_n_succ], [ad_pat_sub_n_mono], [ad_pat_sub_n_rename_tvar],
   [ad_pat_sub_to_n]) was DELETED with the [ad_pat_sub_n] judgment it served
   (algo_decl/def_decl_algo_sub.v — see the note there).  Nothing outside
   the block ever used it: the completeness track settled on the tag-hygienic
   fuel [ad_pat_sub_g], whose own bridges are [ad_pat_sub_g_of] /
   [ad_pat_sub_gv_forget] / [ad_pat_sub_gv_fuel_weaken]
   (def_decl_algo_sub.v). *)

(* ===================================================================== *)
(*  P5b — partial-precision-complete + precision-substitution.            *)
(*  See docs/DESIGN-completeness-subtyping.md §5.1 for the case-plan.     *)
(* ===================================================================== *)

(** The solved tag context of partial precision is contained in [ψ]'s tags —
    the invariant that makes the [tophole_fill] case of partial-precision-
    complete vacuous. *)
Lemma ad_partial_precise_tags_sub : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall Ψt, d_tags_skl Ψt ψ -> Ψ [<=] Ψt.
Proof.
  intros Θ Δ Ψ P ψ Hwf H. induction H; intros Ψt Hdt.
  - apply d_tags_skl_unit_inv in Hdt. fsetdec.
  - apply d_tags_skl_var_inv in Hdt. fsetdec.
  - apply d_tags_skl_arrow_inv in Hdt as [Ψt1 [Ψt2 [Hd1 [Hd2 [_ Heqt]]]]].
    specialize (IHad_partial_precise1 Hwf _ Hd1).
    specialize (IHad_partial_precise2 Hwf _ Hd2).
    fsetdec.
  - apply d_tags_skl_all_tag_inv in Hdt as [L0 [Ψt0 [Hd0 [Hεt Heqt]]]].
    pick fresh α for (L `union` L0).
    specialize (H0 α ltac:(solve_notin_auto) Hwf _ (Hd0 α ltac:(solve_notin_auto))).
    fsetdec.
  - fsetdec.
  - eapply IHad_partial_precise; eauto.
  - (* tophole_fill: the recursive premise keeps Ψ but drops the ε tag;
       here the sub-derivation extends Θ with the rigid α *)
    apply d_tags_skl_all_tag_inv in Hdt as [L0 [Ψt0 [Hd0 [Hεt Heqt]]]].
    pick fresh α for (L `union` L0 `union` dom Θ).
    assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    specialize (H0 α ltac:(solve_notin_auto) Hwf' _ (Hd0 α ltac:(solve_notin_auto))).
    fsetdec.
  - apply d_tags_skl_topholeg_inv in Hdt. eapply IHad_partial_precise; eauto.
  - eapply IHad_partial_precise; eauto.
  - (* flex_r: ψ = var α ⇒ Ψt = ∅, and the def body is a tag-free monotype *)
    apply d_tags_skl_var_inv in Hdt.
    assert (Hmono : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Ψ [<=] empty).
    { eapply IHad_partial_precise; [ exact Hwf | ].
      apply mono_ptyp_to_uskl_syn_tags; [ exact Hmono | reflexivity ]. }
    fsetdec.
Qed.

(** [lemma:partial-precision-complete] (subtyping-proofs.tex:1639).  Under
    wf of [ψ] and the tag-sort premise, partial precision at the FULL tag set
    [Ψ] upgrades to plain (coloured) precision against [⌊ψ⌋].  See §5.1. *)
Lemma ad_partial_precise_complete : forall NM Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  a_tags_sort NM Ψ ψ ->
  {{ Θ ⨟ Δ ⊢ₚₛ ⌊ ψ ⌋ˢ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  {{ Θ ⨟ Δ ⊢ₚᵣ P ⊑ ⌊ ψ ⌋ˢ }}ad.
Proof.
  intros NM Θ Δ Ψ P ψ Hwf Htags Hwfp H.
  revert Hwf Htags Hwfp. induction H; intros Hwf Htags Hwfp;
    unfold ad_precise in *; simpl in *.
  - (* unit *) apply ad_refine_syn__unit.
  - (* var *) apply ad_refine_syn__var. assumption.
  - (* arrow *)
    apply a_tags_sort_arrow_inv in Htags as [Ψa [Ψb [Hta [Htb [Hdisj Hun]]]]].
    inversion Hwfp; subst.
    assert (Hs1 : Ψ1 [<=] Ψa) by
      (eapply (ad_partial_precise_tags_sub Hwf H); exact (a_tags_sort_d_tags Hta)).
    assert (Hs2 : Ψ2 [<=] Ψb) by
      (eapply (ad_partial_precise_tags_sub Hwf H0); exact (a_tags_sort_d_tags Htb)).
    apply ad_refine_syn__arrow.
    + apply IHad_partial_precise1;
        [ exact Hwf
        | eapply a_tags_sort_psi_cong; [ exact Hta | clear - H1 Hun Hdisj Hs1 Hs2; fsetdec ]
        | assumption ].
    + apply IHad_partial_precise2;
        [ exact Hwf
        | eapply a_tags_sort_psi_cong; [ exact Htb | clear - H1 Hun Hdisj Hs1 Hs2; fsetdec ]
        | assumption ].
  - (* forall: ψ = all_tag ε ψ0, P = all_syn P0 *)
    apply a_tags_sort_all_tag_inv in Htags as [Lt [Ψt [Hta [Hεt Hun]]]].
    apply a_wf_pskl_all_inv in Hwfp as [Lw Hwbody].
    apply ad_refine_syn__all with (L := L `union` Lt `union` Lw `union` dom Θ
       `union` ftvar_in_pskl P `union` ftvar_in_uskl ψ).
    intros α0 Hα0.
    assert (Hs0 : Ψ0 [<=] Ψt) by
      (eapply (ad_partial_precise_tags_sub Hwf (H α0 ltac:(solve_notin_auto)));
        exact (a_tags_sort_d_tags (Hta α0 ltac:(solve_notin_auto)))).
    assert (Heq0 : Ψ0 [=] Ψt) by (clear - H1 Hun Hεt Hs0; fsetdec).
    rewrite <- pskl_to_bskl_inh_open.
    rewrite <- pskl_to_bskl_inh_open.
    rewrite <- (uskl_to_pskl_open ψ).
    apply H0; [ fsetdec | exact Hwf | | ].
    + eapply a_tags_sort_psi_cong; [ apply Hta; fsetdec | clear - Heq0; fsetdec ].
    + rewrite uskl_to_pskl_open. apply Hwbody. fsetdec.
  - (* hole: ψ ∀-free (empty tags) ⇒ inh = syn, wf-strip supplies the fill *)
    assert (Hnf : pskl_no_forall (uskl_to_pskl ψ)) by
      (eapply d_tags_empty_no_forall;
        [ exact (a_tags_sort_d_tags Htags) | assumption ]).
    rewrite (pskl_no_forall_inh_eq_syn _ Hnf).
    apply ad_refine_syn__hole.
    eapply a_wf_pskl_delta_strip; [ exact Hwfp | ].
    rewrite ftvar_in_pskl_uskl_to_pskl. assumption.
  - (* tophole_remove *)
    apply ad_refine_syn__tophole_remove.
    apply IHad_partial_precise; [ exact Hwf | exact Htags | exact Hwfp ].
  - (* tophole_fill: VACUOUS via tags_sub — ε is solved but the premise drops it *)
    exfalso.
    apply a_tags_sort_all_tag_inv in Htags as [Lt [Ψt [Hta [Hεt Hun]]]].
    pick fresh α for (L `union` Lt `union` dom Θ).
    assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (Hsub : Ψ [<=] Ψt) by
      (eapply (ad_partial_precise_tags_sub Hwf' (H α ltac:(solve_notin_auto)));
        exact (a_tags_sort_d_tags (Hta α ltac:(solve_notin_auto)))).
    clear - Hun Hεt Hsub. fsetdec.
  - (* tophole_keep: ψ = topholeg ψ0 (SK-only; TY gf excludes it) *)
    apply a_wf_pskl_tophole_inv in Hwfp as [Hg Hw0].
    apply ad_refine_syn__tophole_keep.
    + apply guarded_pskl_to_bskl_inh. exact Hg.
    + apply IHad_partial_precise; [ exact Hwf | | ].
      * inversion Htags; subst;
          match goal with Hit : is_tskl (uskl_topholeg _) |- _ =>
            inversion Hit; subst end.
        -- match goal with Hd : d_tags_skl _ (uskl_topholeg _) |- _ =>
             apply d_tags_skl_topholeg_inv in Hd end.
           apply a_tags_sort__sk; auto.
        -- match goal with Hg0 : uskl_ghost_free (uskl_topholeg _) |- _ =>
             inversion Hg0 end.
      * eapply a_wf_pskl_delta_mono; [ exact Hw0 | clear; fsetdec ].
  - (* flex_l: subject α unfolds to its mono def; ψ unchanged *)
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    eapply ad_refine_syn__flex_l; [ exact H | ].
    rewrite <- (ptyp_to_bskl_inh_syn_eq Hmono).
    apply IHad_partial_precise; [ exact Hwf | exact Htags | exact Hwfp ].
  - (* flex_r: target α unfolds to its mono def (tag-free, wf since flex-free) *)
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact H ]).
    assert (HΨ : Ψ [=] empty)
      by exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags)).
    eapply ad_refine_syn__flex_r; [ exact H | ].
    rewrite <- (ptyp_to_bskl_inh_syn_eq Hmono).
    replace (ptyp_to_pskl τ) with (uskl_to_pskl (ptyp_to_uskl_syn τ))
      by (apply uskl_to_pskl_ptyp_to_uskl_syn).
    apply IHad_partial_precise.
    + exact Hwf.
    + (* build at concrete [empty] FIRST (no evar), then re-tag to Ψ [=] empty
         — psi_cong with an evar source would make [fsetdec] hang. *)
      assert (Htagpaint : a_tags_sort NM empty (ptyp_to_uskl_syn τ)).
      { destruct NM.
        - apply a_tags_sort__ty.
          + exact (mono_ptyp_to_uskl_syn_is_tskl Hmono).
          + apply (mono_ptyp_to_uskl_syn_tags Hmono). reflexivity.
          + exact (mono_ptyp_to_uskl_syn_ghost_free Hmono).
        - apply a_tags_sort__sk.
          + exact (mono_ptyp_to_uskl_syn_is_tskl Hmono).
          + apply (mono_ptyp_to_uskl_syn_tags Hmono). reflexivity. }
      eapply a_tags_sort_psi_cong; [ exact Htagpaint | clear - HΨ; fsetdec ].
    + rewrite uskl_to_pskl_ptyp_to_uskl_syn.
      apply a_scope_pskl_of_ptyp_vis.
      * eapply a_wf_ptyp_lc; exact Hwfτ.
      * intros α0 Hα0. right.
        eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfτ | exact Hα0 ].
Qed.

(* ===================================================================== *)
(*  P5b-ii — precision-substitution.                                       *)
(*  The consistency-level metatheory (crux (1a)/(1b)/(1) and the general   *)
(*  subject substitution, step (2)) lives in prop_consis_precise.v.        *)
(*  Step (3), the ad_pat_sub-level [ad_pat_sub_precise_subst], needs the   *)
(*  TAG-HYGIENIC fuel mirror (the paper's ForallL [fresh Ψ'] is GLOBAL     *)
(*  freshness) — see docs/DESIGN-completeness-subtyping.md §5.4.           *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  P5b-ii step (3) — infrastructure over the TAG-HYGIENIC fuel mirror     *)
(*  [ad_pat_sub_g] (def_decl_algo_sub.v; DESIGN §5.4).                 *)
(* ===================================================================== *)

(** Re-tag under set equality. *)
Lemma ad_pat_sub_g_psi_cong : forall n NM M Ψ Θ R Q,
  ad_pat_sub_g n NM M Ψ Θ R Q ->
  forall Ψc, Ψ [=] Ψc ->
  ad_pat_sub_g n NM M Ψc Θ R Q.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; intros Ψc Heq.
  - apply ad_pat_sub_g__infer;
      [ clear - H Heq; fsetdec | assumption | assumption ].
  - apply ad_pat_sub_g__check; [ assumption | assumption | ].
    eapply ad_pat_consis_psi_cong; [ eassumption | exact Heq ].
  - eapply ad_pat_sub_g__forall_r with (L := L).
    intros α Hα. apply (H0 α Hα _ Heq).
  - apply ad_pat_sub_g__univ_ghost_r; try assumption.
    clear - H Heq; fsetdec.
  - eapply ad_pat_sub_g__arrow;
      [ eassumption | eassumption | clear - H1 Heq; fsetdec ].
  - eapply ad_pat_sub_g__forall_l_tagged with (Ψ' := Ψ') (ψ := ψ);
      [ assumption | clear - H0 Heq; fsetdec | assumption | assumption
      | assumption | ].
    apply IHad_pat_sub_g. clear - Heq; fsetdec.
  - eapply ad_pat_sub_g__forall_l_untagged with (Ψ' := Ψ') (ψ := ψ);
      [ assumption | clear - H0 Heq; fsetdec | assumption | assumption
      | assumption | ].
    apply IHad_pat_sub_g. clear - Heq; fsetdec.
  - apply ad_pat_sub_g__ghost;
      [ clear - H Heq; fsetdec | assumption | assumption ].
  - apply ad_pat_sub_g__ghostg;
      [ clear - H Heq; fsetdec | assumption ].
  - apply ad_pat_sub_g__univ_ghost_l; [ assumption | ].
    apply IHad_pat_sub_g; exact Heq.
  - apply ad_pat_sub_g__univ_ghost_lg; [ assumption | ].
    apply IHad_pat_sub_g; exact Heq.
  - eapply ad_pat_sub_g__flex_mono; [ eassumption | ].
    apply IHad_pat_sub_g; exact Heq.
Qed.

(** The tag context is contained in the subject's syntactic tags. *)
Lemma ad_pat_sub_g_ftag_sub : forall n NM M Ψ Θ R' Q,
  ad_pat_sub_g n NM M Ψ Θ R' Q ->
  Ψ [<=] ftag_in_uskl R'.
Proof.
  intros n NM M Ψ Θ R' Q H; induction H; simpl.
  - (* infer *) clear - H; fsetdec.
  - (* check *)
    pose proof (ad_pat_consis_ftag_sub H1) as Hcf.
    clear - Hcf; fsetdec.
  - (* forall_r *)
    pick fresh α for L.
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto)) as Hα.
    clear - Hα; fsetdec.
  - (* univ_ghost_r *) clear - H; fsetdec.
  - (* arrow *)
    pose proof (ad_pat_consis_ftag_sub H) as Hcf.
    clear - Hcf H1 IHad_pat_sub_g; fsetdec.
  - (* forall_l_tagged *)
    pose proof (ftag_in_uskl_open_upper R ψ) as Hou.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags H2)) as Htg.
    simpl in IHad_pat_sub_g.
    clear - H0 Hou Htg IHad_pat_sub_g; fsetdec.
  - (* forall_l_untagged *)
    pose proof (ftag_in_uskl_open_upper R ψ) as Hou.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags H2)) as Htg.
    simpl in IHad_pat_sub_g.
    clear - H0 Hou Htg IHad_pat_sub_g; fsetdec.
  - (* ghost *) clear - H; fsetdec.
  - (* ghostg *) clear - H; fsetdec.
  - (* univ_ghost_l *) clear - IHad_pat_sub_g; fsetdec.
  - (* univ_ghost_lg *) clear - IHad_pat_sub_g; fsetdec.
  - (* flex_mono *)
    pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt.
    clear - Hpt IHad_pat_sub_g; fsetdec.
Qed.

(** Wrap a ∀◇ over an SK subject at the SAME fuel — [UnivGhostL] is
    non-incrementing; at TI, re-route through the [Infer] consistency
    premise ([tophole_drop]). *)
Lemma ad_pat_sub_g_wrap_tophole : forall n M Ψ Θ R Q,
  ad_pat_sub_g n a_sub_mode_sk M Ψ Θ R Q ->
  ad_pat_sub_g n a_sub_mode_sk M Ψ Θ (uskl_tophole R) Q.
Proof.
  intros n M Ψ Θ R Q H.
  destruct M.
  - (* ti *)
    inversion H; subst; try congruence.
    + apply ad_pat_sub_g__infer; [ assumption | | assumption ].
      apply ad_pat_consis__tophole_drop; assumption.
    + (* ghost: subject hole, target inh P *)
      apply ad_pat_sub_g__infer; [ assumption | | ].
      * apply ad_pat_consis__tophole_drop.
        apply ad_pat_consis__hole; [ clear; fsetdec | assumption ].
      * match goal with Hmc : mod_comp_sk _ mode_ti |- _ =>
          inversion Hmc; subst; assumption end.
    + (* ghostg *)
      apply ad_pat_sub_g__infer; [ assumption | | ].
      * apply ad_pat_consis__tophole_drop.
        apply ad_pat_consis__ghostg; clear; fsetdec.
      * match goal with Hmc : mod_comp_sk _ mode_ti |- _ =>
          inversion Hmc; subst; assumption end.
  - (* tc *)
    apply ad_pat_sub_g__univ_ghost_l; [ discriminate | assumption ].
  - (* fn *)
    apply ad_pat_sub_g__univ_ghost_l; [ discriminate | assumption ].
Qed.

(** Fold a flexible definition back into its variable on the subject side,
    at the SAME fuel ([FlexMono] is non-incrementing; non-fn modes re-route
    through their consistency premises with [flex_l]). *)
Lemma ad_pat_sub_g_fold_flex : forall n NM M Ψ Θ Rτ Q,
  ad_pat_sub_g n NM M Ψ Θ Rτ Q ->
  forall α τ,
  Rτ = ptyp_to_uskl_syn τ ->
  binds α (abind_flex_mono_def τ) Θ ->
  {{ ⊢ Θ }}a ->
  ad_pat_sub_g n NM M Ψ Θ (uskl_var_f α) Q.
Proof.
  intros n NM M Ψ Θ Rτ Q HD; induction HD; intros α0 τ0 HeqS Hb Hwf.
  - (* infer *)
    apply ad_pat_sub_g__infer; [ assumption | | assumption ].
    eapply ad_pat_consis__flex_l; [ exact Hb | ].
    rewrite <- HeqS; assumption.
  - (* check *)
    apply ad_pat_sub_g__check;
      [ apply guarded_uskl__var | assumption | ].
    eapply ad_pat_consis__flex_l; [ exact Hb | ].
    rewrite <- HeqS; assumption.
  - (* forall_r *)
    eapply ad_pat_sub_g__forall_r with (L := L `union` dom Θ).
    intros β Hβ.
    eapply (H0 β ltac:(clear - Hβ; solve_notin_auto) α0 τ0 HeqS);
      [ unfold binds; simpl; right; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hβ; fsetdec | exact Hwf ] ].
  - (* univ_ghost_r *)
    apply ad_pat_sub_g__univ_ghost_r; try assumption.
    + apply guarded_uskl__var.
    + eapply ad_pat_consis__flex_l; [ exact Hb | ].
      rewrite <- HeqS; assumption.
  - (* arrow *)
    eapply ad_pat_sub_g__flex_mono with (τ := τ0); [ exact Hb | ].
    rewrite <- HeqS.
    eapply ad_pat_sub_g__arrow; eassumption.
  - (* forall_l_tagged — a painted monotype has no quantifier *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* forall_l_untagged *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* ghost *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* ghostg *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* univ_ghost_l *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* univ_ghost_lg *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* flex_mono *)
    eapply ad_pat_sub_g__flex_mono with (τ := τ0); [ exact Hb | ].
    rewrite <- HeqS.
    eapply ad_pat_sub_g__flex_mono; [ exact H | exact HD ].
Qed.

(** For a ∀-free-erasure SK subject, the target is an inh-painting of its
    own erasure, the tag context is empty, and the target is
    mode-compatible — the data the [Ghost] reconstruction needs. *)
Lemma ad_pat_sub_g_concrete_target : forall n NM M Ψ Θ R' Q,
  ad_pat_sub_g n NM M Ψ Θ R' Q ->
  NM = a_sub_mode_sk ->
  {{ ⊢ Θ }}a ->
  pskl_no_forall (uskl_to_pskl R') ->
  Ψ [=] empty /\ pskl_to_bskl_inh (bskl_to_pskl Q) = Q /\ mod_comp_sk Q M.
Proof.
  intros n NM M Ψ Θ R' Q HD; induction HD; intros HNM Hwf Hnf;
    try discriminate HNM.
  - (* infer *)
    pose proof (ad_pat_consis_strip_tags H0) as Hstr.
    destruct (consis_concrete_target_inh Hstr Hwf (uskl_to_pskl R) eq_refl Hnf)
      as [_ Heq].
    split; [ exact H | split; [ exact Heq | apply mod_comp_sk__ti; assumption ] ].
  - (* univ_ghost_r *)
    pose proof (ad_pat_consis_strip_tags H3) as Hstr.
    destruct (consis_concrete_target_inh Hstr Hwf (uskl_to_pskl R) eq_refl Hnf)
      as [_ Heq].
    split; [ exact H | split ].
    + simpl. rewrite Heq. reflexivity.
    + apply mod_comp_sk__tc. apply is_sskl__tophole. assumption.
  - (* arrow *)
    simpl in Hnf. destruct Hnf as [Hnf1 Hnf2].
    pose proof (ad_pat_consis_strip_tags H) as Hstr1.
    destruct (consis_concrete_target_inh Hstr1 Hwf (uskl_to_pskl R1)
                eq_refl Hnf1) as [HΨ1 Heq1].
    destruct (IHHD HNM Hwf Hnf2) as [HΨ2 [Heq2 Hmc2]].
    pose proof (ad_pat_consis_ftag_sub H) as Hf1.
    pose proof (no_forall_uskl_ftag _ Hnf1) as He1.
    split; [ clear - H0 Hf1 He1 HΨ2; fsetdec | split ].
    + simpl. rewrite Heq1. rewrite Heq2. reflexivity.
    + apply mod_comp_sk__fn. exact Hmc2.
  - (* forall_l_tagged *)
    simpl in Hnf. contradiction.
  - (* forall_l_untagged *)
    simpl in Hnf. contradiction.
  - (* ghost *)
    split;
      [ exact H
      | split; [ rewrite bskl_to_pskl_pskl_to_bskl_inh; reflexivity
               | assumption ] ].
  - (* ghostg *)
    split; [ exact H | split; [ reflexivity | assumption ] ].
  - (* univ_ghost_l *)
    simpl in Hnf.
    destruct (IHHD HNM Hwf Hnf) as [HΨ [Heq Hmc]].
    split; [ assumption | split; assumption ].
  - (* univ_ghost_lg *)
    simpl in Hnf.
    destruct (IHHD HNM Hwf Hnf) as [HΨ [Heq Hmc]].
    split; [ assumption | split; assumption ].
  - (* flex_mono *)
    apply IHHD; [ exact HNM | exact Hwf | ].
    rewrite uskl_to_pskl_ptyp_to_uskl_syn.
    apply mono_ptyp_pskl_no_forall.
    eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ].
Qed.

(** Uniform refl-transport: shrink the tag context of a derivation whose
    subject's tags are Ψsup-free (the ⊑ᵤ-refl case of every rule). *)
Lemma ad_pat_sub_g_refl_transport : forall n NM M Ψfull Θ' R Q,
  ad_pat_sub_g n NM M Ψfull Θ' R Q ->
  forall Ψsup Ψn Ψna,
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ ftag_in_uskl R [=] empty ->
  ad_pat_sub_g n NM M Ψn Θ' R Q.
Proof.
  intros n NM M Ψfull Θ' R Q HD Ψsup Ψn Ψna HΨf HΨa Hftag.
  pose proof (ad_pat_sub_g_ftag_sub HD) as Hfs.
  eapply ad_pat_sub_g_psi_cong;
    [ exact HD | clear - HΨf HΨa Hftag Hfs; fsetdec ].
Qed.

(** Uniform hole-introduction: replace a ∀-free-erasure SK subject by [□]
    at ANY fuel (the ⊑ᵤ-hole case of every rule), via [Ghost]. *)
Lemma ad_pat_sub_g_hole_intro : forall n n' NM M Ψfull Θ' R Q,
  ad_pat_sub_g n NM M Ψfull Θ' R Q ->
  NM = a_sub_mode_sk ->
  {{ ⊢ Θ' }}a ->
  pskl_no_forall (uskl_to_pskl R) ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  forall Ψn, Ψn [<=] Ψfull ->
  ad_pat_sub_g n' NM M Ψn Θ' uskl_hole Q.
Proof.
  intros n n' NM M Ψfull Θ' R Q HD HNM Hwf Hnf Hwfq Ψn HΨn.
  destruct (ad_pat_sub_g_concrete_target HD HNM Hwf Hnf)
    as [HΨe [Heq Hmc]].
  rewrite <- Heq. subst NM.
  apply ad_pat_sub_g__ghost.
  - clear - HΨn HΨe; fsetdec.
  - exact Hwfq.
  - rewrite Heq. exact Hmc.
Qed.

(* ⚙ [uskl_ghost_free_subst] MOVED 2026-08-11 to algo/prop_pat_sub.v, where
   its two instances ([_subst_unit], [_subst_mono]) already lived and where
   [uskl_ghost_free_open_gen] needs it. *)

(** A painted monotype is a guarded subject. *)
Lemma mono_paint_guarded : forall τ,
  mono_ptyp τ ->
  lc_uskl (ptyp_to_uskl_syn τ) ->
  guarded_uskl (ptyp_to_uskl_syn τ).
Proof.
  intros τ Hm Hlc; destruct Hm; unfold ptyp_to_uskl_syn in *; simpl in *.
  - apply guarded_uskl__unit.
  - apply guarded_uskl__var.
  - inversion Hlc; subst. apply guarded_uskl__arrow; assumption.
Qed.

(** ⊑ᵤ preserves guardedness of the subject (used by the Check /
    UnivGhostR reconstructions; the ghostier side must not grow a ∀◇ or
    hole head, which [uskl_ghost_free]—TY—or the case analysis—SK refl /
    congruence roots—supplies). *)
Lemma uskl_precise_guarded : forall Θb Ψrep R' R,
  uskl_precise Θb Ψrep R' R ->
  {{ ⊢ Θb }}a ->
  guarded_uskl R ->
  uskl_ghost_free R' ->
  guarded_uskl R'.
Proof.
  intros Θb Ψrep R' R Hup; induction Hup; intros Hwfb Hg Hgf.
  - exact Hg.
  - apply guarded_uskl__arrow;
      [ eapply uskl_precise_lc_l; exact Hup1
      | eapply uskl_precise_lc_l; exact Hup2 ].
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hgf.
  - inversion Hgf.
  - apply guarded_uskl__var.
  - apply IHHup; [ exact Hwfb | | exact Hgf ].
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfb | exact H ]).
    apply mono_paint_guarded; [ exact Hm | ].
    assert (Hwfτ : a_wf_ptyp Θb τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwfb | exact H ]).
    rewrite <- pskl_to_uskl_ptyp.
    apply pskl_to_uskl_lc.
    apply a_wf_pskl_lc with (Θ := Θb) (Δ := empty).
    apply a_wf_pskl_mono_ptyp; [ exact Hm | exact Hwfτ ].
Qed.

(* ===================================================================== *)
(*  Step (3) per-rule ⊑ᵤ-transports.  Each runs the inner induction on ⊑ᵤ  *)
(*  with the rule's data as named arguments (the ∀◇/flex peels recurse on  *)
(*  the smaller ⊑ᵤ; congruence roots rebuild the rule).                    *)
(* ===================================================================== *)

(** [UnivGhostR]: guarded SK subject against a ∀◇-target. *)
Lemma ad_pat_sub_g_ughost_r_transport : forall Θb Ψrep R' R,
  uskl_precise Θb Ψrep R' R ->
  forall Ψsup n Θ' Ψn Q,
  {{ ⊢ Θb }}a ->
  Ψrep [<=] Ψsup ->
  Ψsup ∩ ftag_in_uskl R' [=] empty ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  guarded_uskl R ->
  {{ empty ⨟ Θ' ⊢ˢ R ∼ Q }}ad ->
  guarded_bskl Q ->
  is_sskl Q ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  Ψn [=] empty ->
  ad_pat_sub_g n a_sub_mode_sk mode_tc Ψn Θ' R' (bskl_tophole Q).
Proof.
  intros Θb Ψrep R' R Hup; induction Hup;
    intros Ψsup n Θ' Ψn Q0 Hwfb HΨsup Hftag Hmon Hwf Hgd Hc3 HgQ HsQ Hwfq HΨe.
  - (* refl *)
    apply ad_pat_sub_g__univ_ghost_r;
      [ exact HΨe | exact Hgd | exact HgQ | exact HsQ | exact Hc3 ].
  - (* arrow cong *)
    apply ad_pat_sub_g__univ_ghost_r;
      [ exact HΨe
      | apply guarded_uskl__arrow;
          [ eapply uskl_precise_lc_l; exact Hup1
          | eapply uskl_precise_lc_l; exact Hup2 ]
      | exact HgQ | exact HsQ | ].
    pose proof (upre__arrow Hup1 Hup2 H) as Hup'.
    pose proof (ad_pat_consis_precise_upre Hup' HΨsup Hftag) as Ht.
    eapply Ht with (Ψna := empty);
      [ exact Hc3 | exact Hmon | exact Hwf
      | clear; fsetdec | clear; fsetdec | clear; fsetdec | exact Hwfq ].
  - (* all_syn cong: not a guarded subject *) inversion Hgd.
  - (* all_tag cong *) inversion Hgd.
  - (* all_inst *) inversion Hgd.
  - (* tophole cong *) inversion Hgd.
  - (* topholeg cong *) inversion Hgd.
  - (* tophole_keepg *) inversion Hgd.
  - (* hole: replace by □ via Ghost against the ∀◇-target *)
    assert (Hnode : ad_pat_sub_g n a_sub_mode_sk mode_tc Ψn Θ' R
                      (bskl_tophole Q0))
      by (apply ad_pat_sub_g__univ_ghost_r;
          [ exact HΨe | exact Hgd | exact HgQ | exact HsQ | exact Hc3 ]).
    eapply ad_pat_sub_g_hole_intro with (Ψn := Ψn) in Hnode;
      [ exact Hnode | reflexivity | exact Hwf | exact H0
      | simpl; apply a_wf_pskl__tophole;
          [ apply guarded_bskl_to_pskl; exact HgQ | exact Hwfq ]
      | clear; fsetdec ].
  - (* tophole_remove: peel via UnivGhostL (same fuel) *)
    apply ad_pat_sub_g_wrap_tophole.
    eapply IHHup with (Ψsup := Ψsup);
      [ exact Hwfb | exact HΨsup | clear - Hftag; simpl in Hftag; fsetdec
      | exact Hmon | exact Hwf | exact Hgd | exact Hc3 | exact HgQ
      | exact HsQ | exact Hwfq | exact HΨe ].
  - (* flex_l: peel via FlexMono-fold *)
    eapply ad_pat_sub_g_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψsup := Ψsup);
      [ exact Hwfb | exact HΨsup
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hmon | exact Hwf | exact Hgd | exact Hc3 | exact HgQ
      | exact HsQ | exact Hwfq | exact HΨe ].
  - (* flex_r: the subject is a defined flexible variable — unfold it *)
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (apply Hmon; exact H).
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb' ]).
    eapply IHHup with (Ψsup := Ψsup);
      [ exact Hwfb | exact HΨsup | exact Hftag | exact Hmon | exact Hwf
      | apply mono_paint_guarded;
          [ exact Hm
          | rewrite <- pskl_to_uskl_ptyp; apply pskl_to_uskl_lc;
            apply a_wf_pskl_lc with (Θ := Θ') (Δ := empty);
            apply a_wf_pskl_mono_ptyp;
              [ exact Hm
              | eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb' ] ] ]
      | eapply consis_unfold_def_subject;
          [ exact Hc3 | exact Hwf | reflexivity | exact Hb' ]
      | exact HgQ | exact HsQ | exact Hwfq | exact HΨe ].
Qed.

(** [Ghost]: the □-subject SK rule. *)
Lemma ad_pat_sub_g_ghost_transport : forall Θb Ψrep R' R,
  uskl_precise Θb Ψrep R' R ->
  forall n M Θ' Ψn P,
  R = uskl_hole ->
  {{ ⊢ Θb }}a ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  {{ Θ' ⨟ empty ⊢ₚₛ P }}a ->
  mod_comp_sk (pskl_to_bskl_inh P) M ->
  Ψn [=] empty ->
  ad_pat_sub_g n a_sub_mode_sk M Ψn Θ' R' (pskl_to_bskl_inh P).
Proof.
  intros Θb Ψrep R' R Hup; induction Hup;
    intros n M Θ' Ψn P0 HeqR Hwfb Hmon Hwf HwfP Hmc HΨe;
    try discriminate HeqR.
  - (* refl: R' = □ *)
    subst R.
    apply ad_pat_sub_g__ghost; [ exact HΨe | exact HwfP | exact Hmc ].
  - (* hole: R' = □ as well *)
    apply ad_pat_sub_g__ghost; [ exact HΨe | exact HwfP | exact Hmc ].
  - (* tophole_remove *)
    apply ad_pat_sub_g_wrap_tophole.
    eapply IHHup;
      [ exact HeqR | exact Hwfb | exact Hmon | exact Hwf
      | exact HwfP | exact Hmc | exact HΨe ].
  - (* flex_l *)
    eapply ad_pat_sub_g_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup;
      [ exact HeqR | exact Hwfb | exact Hmon | exact Hwf
      | exact HwfP | exact Hmc | exact HΨe ].
Qed.

(** [GhostG]: the ⫯-subject SK rule. *)
Lemma ad_pat_sub_g_ghostg_transport : forall Θb Ψrep R' R,
  uskl_precise Θb Ψrep R' R ->
  forall n M Θ' Ψn,
  R = uskl_holeg ->
  {{ ⊢ Θb }}a ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  mod_comp_sk bskl_hole M ->
  Ψn [=] empty ->
  ad_pat_sub_g n a_sub_mode_sk M Ψn Θ' R' bskl_hole.
Proof.
  intros Θb Ψrep R' R Hup; induction Hup;
    intros n M Θ' Ψn HeqR Hwfb Hmon Hwf Hmc HΨe;
    try discriminate HeqR.
  - (* refl: R' = ⫯ *)
    subst R.
    apply ad_pat_sub_g__ghostg; [ exact HΨe | exact Hmc ].
  - (* hole: R' = □ against the ⫯-target *)
    change bskl_hole with (pskl_to_bskl_inh pskl_hole).
    apply ad_pat_sub_g__ghost;
      [ exact HΨe | apply a_wf_pskl__hole | simpl; exact Hmc ].
  - (* tophole_remove *)
    apply ad_pat_sub_g_wrap_tophole.
    eapply IHHup;
      [ exact HeqR | exact Hwfb | exact Hmon | exact Hwf
      | exact Hmc | exact HΨe ].
  - (* flex_l *)
    eapply ad_pat_sub_g_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup;
      [ exact HeqR | exact Hwfb | exact Hmon | exact Hwf
      | exact Hmc | exact HΨe ].
Qed.

(** [Arrow]: the left premise transports at the consistency level ((2') on
    the sub-⊑ᵤ), the right premise via the main induction hypothesis
    [Hrec]; branch splits are by [diff]/[inter] with the uniform [Ψsup]. *)
Lemma ad_pat_sub_g_arrow_transport : forall Θb Ψr Rg' Rgarr,
  uskl_precise Θb Ψr Rg' Rgarr ->
  forall n NM Mg Θ' Ψfull Ψc1 Ψc2 Rg1 Rg2 Qg1 Qg2 Ψsup Ψn Ψna,
  Rgarr = uskl_arrow Rg1 Rg2 ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  {{ Ψc1 ⨟ Θ' ⊢ˢ Rg1 ∼ Qg1 }}ad ->
  ad_pat_sub_g n NM Mg Ψc2 Θ' Rg2 Qg2 ->
  Ψfull [=] Ψc1 `union` Ψc2 ->
  (forall Θb0 Ψr0 Rg2' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg2' Rg2 ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     Ψc2 [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg2' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg2) }}a ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg2') ->
     ad_pat_sub_g n NM Mg Ψn0 Θ' Rg2' Qg2) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl (bskl_arrow Qg1 Qg2)) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free Rg') ->
  ad_pat_sub_g (S n) NM (mode_fn Mg) Ψn Θ' Rg' (bskl_arrow Qg1 Qg2).
Proof.
  intros Θb Ψr Rg' Rgarr Hup; induction Hup;
    intros n NM Mg Θ' Ψfull Ψc1 Ψc2 Rg1 Rg2 Qg1 Qg2 Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf Hcl HDr HΨsplit Hrec HΨf HΨa Hdisj Hftag Hwfq Hgf;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_g_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ eapply ad_pat_sub_g__arrow; [ exact Hcl | exact HDr | exact HΨsplit ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* arrow congruence *)
    inversion HeqR; subst.
    simpl in Hwfq.
    inversion Hwfq as [ | | Θz Δz Pw1 Pw2 Hwfq1 Hwfq2 | | | ]; subst.
    simpl in Hftag.
    eapply ad_pat_sub_g__arrow with
      (Ψ1 := Ψc1 ∖ Ψsup) (Ψ2 := Ψc2 ∖ Ψsup).
    + assert (Hs1 : Ψ1 [<=] Ψsup) by (clear - HΨsup H; fsetdec).
      assert (Hf1 : Ψsup ∩ ftag_in_uskl R1' [=] empty)
        by (clear - Hftag; fsetdec).
      eapply (ad_pat_consis_precise_upre Hup1 Hs1 Hf1)
        with (Ψna := Ψc1 ∩ Ψsup);
        [ exact Hcl | exact Hmon | exact Hwf
        | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
        | clear - Hdisj; fsetdec | exact Hwfq1 ].
    + eapply Hrec with (Ψr0 := Ψ2) (Ψsup0 := Ψsup)
        (Ψna0 := Ψc2 ∩ Ψsup);
        [ exact Hup2 | exact Hwfb | clear - HΨsup H; fsetdec
        | exact Hmon | exact Hwf
        | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
        | clear - Hdisj; fsetdec | clear - Hftag; fsetdec
        | exact Hwfq2
        | intro He; specialize (Hgf He); inversion Hgf; subst; assumption ].
    + clear - HΨsplit HΨf HΨa Hdisj; fsetdec.
  - (* hole *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + subst R.
      eapply ad_pat_sub_g_hole_intro with
        (n := S n) (Ψfull := Ψfull) (R := uskl_arrow Rg1 Rg2);
        [ eapply ad_pat_sub_g__arrow; [ exact Hcl | exact HDr | exact HΨsplit ]
        | reflexivity | exact Hwf | exact H0 | exact Hwfq
        | clear - HΨf; fsetdec ].
  - (* tophole_remove *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + apply ad_pat_sub_g_wrap_tophole.
      eapply IHHup with (Ψna := Ψna);
        [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
        | exact Hcl | exact HDr | exact HΨsplit | exact Hrec
        | exact HΨf | exact HΨa | exact Hdisj
        | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq
        | intro He; discriminate He ].
  - (* flex_l *)
    eapply ad_pat_sub_g_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact Hcl | exact HDr | exact HΨsplit | exact Hrec
      | exact HΨf | exact HΨa | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq
      | intro He;
        apply mono_ptyp_to_uskl_syn_ghost_free;
        eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact H ] ].
Qed.

(** Cofinite inversions of ghost-freeness at the two quantifier heads. *)
Lemma uskl_ghost_free_all_tag_inv : forall ε R,
  uskl_ghost_free (uskl_all_tag ε R) ->
  exists L0, forall α, α `notin` L0 ->
    uskl_ghost_free (open_uskl_wrt_uskl R (uskl_var_f α)).
Proof. intros ε R Hg. inversion Hg; subst. eauto. Qed.

Lemma uskl_ghost_free_all_syn_inv : forall R,
  uskl_ghost_free (uskl_all_syn R) ->
  exists L0, forall α, α `notin` L0 ->
    uskl_ghost_free (open_uskl_wrt_uskl R (uskl_var_f α)).
Proof. intros R Hg. inversion Hg; subst. eauto. Qed.

(** [ForallL] (tagged): the precision-substitution crux.  The congruence /
    instantiation roots rebuild ForallL with the SAME instantiation [ψg],
    transporting the body-⊑ᵤ under [ψg/α] by [uskl_precise_subst]; the
    recursive call shrinks [Ψsup] by the instantiation's tags [Ψi'] (the
    node's hygiene premise keeps everything disjoint). *)
Lemma ad_pat_sub_g_forall_l_tagged_transport : forall Θb Ψr Rg' Rgall,
  uskl_precise Θb Ψr Rg' Rgall ->
  forall n NM Mg Θ' Ψfull Ψi' εg Rg0 ψg Qg Ψsup Ψn Ψna,
  Rgall = uskl_all_tag εg Rg0 ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  Mg <> mode_ti ->
  Ψi' ∩ Ψfull [=] empty ->
  Ψi' ∩ (ftag_in_uskl (uskl_all_tag εg Rg0)) [=] empty ->
  a_tags_sort NM Ψi' ψg ->
  {{ Θ' ⨟ empty ⊢ₚₛ ⌊ ψg ⌋ˢ }}a ->
  ad_pat_sub_g n NM Mg (Ψfull `union` Ψi') Θ' (open_uskl_wrt_uskl Rg0 ψg) Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' (open_uskl_wrt_uskl Rg0 ψg) ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     (Ψfull `union` Ψi') [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg'') ->
     ad_pat_sub_g n NM Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free Rg') ->
  ad_pat_sub_g (S n) NM Mg Ψn Θ' Rg' Qg.
Proof.
  intros Θb Ψr Rg' Rgall Hup; induction Hup;
    intros n NM Mg Θ' Ψfull Ψi' εg Rg0 ψg Qg Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf HMti Hictx Hihyg Htags Hwfψ HDp Hrec
      HΨf HΨa Hdisj Hftag Hwfq Hgf;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_g_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ eapply ad_pat_sub_g__forall_l_tagged with (Ψ' := Ψi') (ψ := ψg);
        [ exact HMti | exact Hictx | exact Hihyg | exact Htags
        | exact Hwfψ | exact HDp ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* all_tag congruence: rebuild ForallL-tagged with ψg *)
    inversion HeqR; subst.
    assert (Hlcψ : lc_uskl ψg)
      by (apply is_tskl_lc; inversion Htags; subst; assumption).
    pick fresh α for (L `union` dom Θb
        `union` ftvar_in_uskl R' `union` ftvar_in_uskl Rg0).
    pose proof (H α ltac:(clear - Fr; solve_notin_auto)) as Hbody.
    assert (Hsub : uskl_precise Θb Ψrep
        (open_uskl_wrt_uskl R' ψg) (open_uskl_wrt_uskl Rg0 ψg)).
    { rewrite (subst_uskl_in_uskl_intro α R' ψg ltac:(clear - Fr; solve_notin_auto)).
      rewrite (subst_uskl_in_uskl_intro α Rg0 ψg ltac:(clear - Fr; solve_notin_auto)).
      apply uskl_precise_subst;
        [ exact Hbody | exact Hlcψ | exact Hwfb | clear - Fr; fsetdec ]. }
    pose proof (uskl_precise_ftag_sub Hbody) as Hfsb.
    pose proof (uskl_precise_ftag_rep Hbody) as Hfrb.
    pose proof (ftag_in_uskl_open_var R' α) as Hov1.
    pose proof (ftag_in_uskl_open_var Rg0 α) as Hov2.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Htgψ.
    assert (Hgfψ : NM = a_sub_mode_ty -> uskl_ghost_free ψg)
      by (intro He; inversion Htags; subst;
          [ congruence | assumption ]).
    assert (Hgfo : NM = a_sub_mode_ty ->
                   uskl_ghost_free (open_uskl_wrt_uskl R' ψg)).
    { intro He.
      destruct (uskl_ghost_free_all_tag_inv (Hgf He)) as [Lg Hgb].
      pick fresh β for (Lg `union` ftvar_in_uskl R').
      rewrite (subst_uskl_in_uskl_intro β R' ψg
                 ltac:(clear - Fr0; solve_notin_auto)).
      apply uskl_ghost_free_subst;
        [ apply Hgb; clear - Fr0; fsetdec
        | apply Hgfψ; exact He
        | exact Hlcψ ]. }
    eapply ad_pat_sub_g__forall_l_tagged with (Ψ' := Ψi') (ψ := ψg).
    + exact HMti.
    + clear - Hictx HΨf; fsetdec.
    + simpl. simpl in Hihyg. clear - Hihyg Hfsb Hov1 Hov2; fsetdec.
    + exact Htags.
    + exact Hwfψ.
    + eapply Hrec with (Ψr0 := Ψrep)
        (Ψsup0 := Ψsup ∖ Ψi') (Ψna0 := Ψna);
        [ exact Hsub | exact Hwfb
        | simpl in Hihyg; clear - HΨsup Hfrb Hov2 Hihyg; fsetdec
        | exact Hmon | exact Hwf
        | clear - HΨf; fsetdec
        | clear - HΨa HΨf Hictx; fsetdec
        | clear - Hdisj; fsetdec
        | pose proof (ftag_in_uskl_open_upper R' ψg) as Hou;
          simpl in Hftag; clear - Hou Hftag Htgψ; fsetdec
        | exact Hwfq
        | exact Hgfo ].
  - (* all_inst: rebuild ForallL-UNTAGGED with ψg *)
    inversion HeqR; subst.
    assert (Hlcψ : lc_uskl ψg)
      by (apply is_tskl_lc; inversion Htags; subst; assumption).
    pick fresh α for (L `union` dom Θb
        `union` ftvar_in_uskl R' `union` ftvar_in_uskl Rg0).
    pose proof (H α ltac:(clear - Fr; solve_notin_auto)) as Hbody.
    assert (Hsub : uskl_precise Θb Ψ0
        (open_uskl_wrt_uskl R' ψg) (open_uskl_wrt_uskl Rg0 ψg)).
    { rewrite (subst_uskl_in_uskl_intro α R' ψg ltac:(clear - Fr; solve_notin_auto)).
      rewrite (subst_uskl_in_uskl_intro α Rg0 ψg ltac:(clear - Fr; solve_notin_auto)).
      apply uskl_precise_subst;
        [ exact Hbody | exact Hlcψ | exact Hwfb | clear - Fr; fsetdec ]. }
    pose proof (uskl_precise_ftag_sub Hbody) as Hfsb.
    pose proof (uskl_precise_ftag_rep Hbody) as Hfrb.
    pose proof (ftag_in_uskl_open_var R' α) as Hov1.
    pose proof (ftag_in_uskl_open_var Rg0 α) as Hov2.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Htgψ.
    assert (Hgfψ : NM = a_sub_mode_ty -> uskl_ghost_free ψg)
      by (intro He; inversion Htags; subst;
          [ congruence | assumption ]).
    assert (Hgfo : NM = a_sub_mode_ty ->
                   uskl_ghost_free (open_uskl_wrt_uskl R' ψg)).
    { intro He.
      destruct (uskl_ghost_free_all_syn_inv (Hgf He)) as [Lg Hgb].
      pick fresh β for (Lg `union` ftvar_in_uskl R').
      rewrite (subst_uskl_in_uskl_intro β R' ψg
                 ltac:(clear - Fr0; solve_notin_auto)).
      apply uskl_ghost_free_subst;
        [ apply Hgb; clear - Fr0; fsetdec
        | apply Hgfψ; exact He
        | exact Hlcψ ]. }
    eapply ad_pat_sub_g__forall_l_untagged with (Ψ' := Ψi') (ψ := ψg).
    + exact HMti.
    + clear - Hictx HΨf; fsetdec.
    + simpl. simpl in Hihyg. clear - Hihyg Hfsb Hov1 Hov2; fsetdec.
    + exact Htags.
    + exact Hwfψ.
    + eapply Hrec with (Ψr0 := Ψ0)
        (Ψsup0 := Ψsup ∖ Ψi') (Ψna0 := Ψna);
        [ exact Hsub | exact Hwfb
        | simpl in Hihyg; clear - HΨsup H1 Hfrb Hov2 Hihyg; fsetdec
        | exact Hmon | exact Hwf
        | clear - HΨf; fsetdec
        | clear - HΨa HΨf Hictx; fsetdec
        | clear - Hdisj; fsetdec
        | pose proof (ftag_in_uskl_open_upper R' ψg) as Hou;
          simpl in Hftag; clear - Hou Hftag Htgψ; fsetdec
        | exact Hwfq
        | exact Hgfo ].
  - (* hole: no_forall of an all_tag erasure is absurd *)
    subst R. simpl in H0. contradiction.
  - (* tophole_remove *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + apply ad_pat_sub_g_wrap_tophole.
      eapply IHHup with (Ψna := Ψna);
        [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
        | exact HMti | exact Hictx | exact Hihyg | exact Htags | exact Hwfψ
        | exact HDp | exact Hrec | exact HΨf | exact HΨa | exact Hdisj
        | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq
        | intro He; discriminate He ].
  - (* flex_l *)
    eapply ad_pat_sub_g_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact Hictx | exact Hihyg | exact Htags | exact Hwfψ
      | exact HDp | exact Hrec | exact HΨf | exact HΨa | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq
      | intro He;
        apply mono_ptyp_to_uskl_syn_ghost_free;
        eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact H ] ].
Qed.

(** [ForallL] (untagged): same crux machinery, subject [∀·]. *)
Lemma ad_pat_sub_g_forall_l_untagged_transport : forall Θb Ψr Rg' Rgall,
  uskl_precise Θb Ψr Rg' Rgall ->
  forall n NM Mg Θ' Ψfull Ψi' Rg0 ψg Qg Ψsup Ψn Ψna,
  Rgall = uskl_all_syn Rg0 ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  Mg <> mode_ti ->
  Ψi' ∩ Ψfull [=] empty ->
  Ψi' ∩ (ftag_in_uskl (uskl_all_syn Rg0)) [=] empty ->
  a_tags_sort NM Ψi' ψg ->
  {{ Θ' ⨟ empty ⊢ₚₛ ⌊ ψg ⌋ˢ }}a ->
  ad_pat_sub_g n NM Mg (Ψfull `union` Ψi') Θ' (open_uskl_wrt_uskl Rg0 ψg) Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' (open_uskl_wrt_uskl Rg0 ψg) ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     (Ψfull `union` Ψi') [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg'') ->
     ad_pat_sub_g n NM Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free Rg') ->
  ad_pat_sub_g (S n) NM Mg Ψn Θ' Rg' Qg.
Proof.
  intros Θb Ψr Rg' Rgall Hup; induction Hup;
    intros n NM Mg Θ' Ψfull Ψi' Rg0 ψg Qg Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf HMti Hictx Hihyg Htags Hwfψ HDp Hrec
      HΨf HΨa Hdisj Hftag Hwfq Hgf;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_g_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ eapply ad_pat_sub_g__forall_l_untagged with (Ψ' := Ψi') (ψ := ψg);
        [ exact HMti | exact Hictx | exact Hihyg | exact Htags
        | exact Hwfψ | exact HDp ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* all_syn congruence *)
    inversion HeqR; subst.
    assert (Hlcψ : lc_uskl ψg)
      by (apply is_tskl_lc; inversion Htags; subst; assumption).
    pick fresh α for (L `union` dom Θb
        `union` ftvar_in_uskl R' `union` ftvar_in_uskl Rg0).
    pose proof (H α ltac:(clear - Fr; solve_notin_auto)) as Hbody.
    assert (Hsub : uskl_precise Θb Ψrep
        (open_uskl_wrt_uskl R' ψg) (open_uskl_wrt_uskl Rg0 ψg)).
    { rewrite (subst_uskl_in_uskl_intro α R' ψg ltac:(clear - Fr; solve_notin_auto)).
      rewrite (subst_uskl_in_uskl_intro α Rg0 ψg ltac:(clear - Fr; solve_notin_auto)).
      apply uskl_precise_subst;
        [ exact Hbody | exact Hlcψ | exact Hwfb | clear - Fr; fsetdec ]. }
    pose proof (uskl_precise_ftag_sub Hbody) as Hfsb.
    pose proof (uskl_precise_ftag_rep Hbody) as Hfrb.
    pose proof (ftag_in_uskl_open_var R' α) as Hov1.
    pose proof (ftag_in_uskl_open_var Rg0 α) as Hov2.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Htgψ.
    assert (Hgfψ : NM = a_sub_mode_ty -> uskl_ghost_free ψg)
      by (intro He; inversion Htags; subst;
          [ congruence | assumption ]).
    assert (Hgfo : NM = a_sub_mode_ty ->
                   uskl_ghost_free (open_uskl_wrt_uskl R' ψg)).
    { intro He.
      destruct (uskl_ghost_free_all_syn_inv (Hgf He)) as [Lg Hgb].
      pick fresh β for (Lg `union` ftvar_in_uskl R').
      rewrite (subst_uskl_in_uskl_intro β R' ψg
                 ltac:(clear - Fr0; solve_notin_auto)).
      apply uskl_ghost_free_subst;
        [ apply Hgb; clear - Fr0; fsetdec
        | apply Hgfψ; exact He
        | exact Hlcψ ]. }
    eapply ad_pat_sub_g__forall_l_untagged with (Ψ' := Ψi') (ψ := ψg).
    + exact HMti.
    + clear - Hictx HΨf; fsetdec.
    + simpl. simpl in Hihyg. clear - Hihyg Hfsb Hov1 Hov2; fsetdec.
    + exact Htags.
    + exact Hwfψ.
    + eapply Hrec with (Ψr0 := Ψrep)
        (Ψsup0 := Ψsup ∖ Ψi') (Ψna0 := Ψna);
        [ exact Hsub | exact Hwfb
        | simpl in Hihyg; clear - HΨsup Hfrb Hov2 Hihyg; fsetdec
        | exact Hmon | exact Hwf
        | clear - HΨf; fsetdec
        | clear - HΨa HΨf Hictx; fsetdec
        | clear - Hdisj; fsetdec
        | pose proof (ftag_in_uskl_open_upper R' ψg) as Hou;
          simpl in Hftag; clear - Hou Hftag Htgψ; fsetdec
        | exact Hwfq
        | exact Hgfo ].
  - (* hole: no_forall of an all_syn erasure is absurd *)
    subst R. simpl in H0. contradiction.
  - (* tophole_remove *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + apply ad_pat_sub_g_wrap_tophole.
      eapply IHHup with (Ψna := Ψna);
        [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
        | exact HMti | exact Hictx | exact Hihyg | exact Htags | exact Hwfψ
        | exact HDp | exact Hrec | exact HΨf | exact HΨa | exact Hdisj
        | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq
        | intro He; discriminate He ].
  - (* flex_l *)
    eapply ad_pat_sub_g_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact Hictx | exact Hihyg | exact Htags | exact Hwfψ
      | exact HDp | exact Hrec | exact HΨf | exact HΨa | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq
      | intro He;
        apply mono_ptyp_to_uskl_syn_ghost_free;
        eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact H ] ].
Qed.

(** [UnivGhostL]: ∀◇-subject, SK, non-incrementing. *)
Lemma ad_pat_sub_g_ughost_l_transport : forall Θb Ψr Rg' Rgt,
  uskl_precise Θb Ψr Rg' Rgt ->
  forall n Mg Θ' Ψfull Rg0 Qg Ψsup Ψn Ψna,
  Rgt = uskl_tophole Rg0 ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  Mg <> mode_ti ->
  ad_pat_sub_g n a_sub_mode_sk Mg Ψfull Θ' Rg0 Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' Rg0 ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     Ψfull [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
     ad_pat_sub_g n a_sub_mode_sk Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
  ad_pat_sub_g n a_sub_mode_sk Mg Ψn Θ' Rg' Qg.
Proof.
  intros Θb Ψr Rg' Rgt Hup; induction Hup;
    intros n Mg Θ' Ψfull Rg0 Qg Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf HMti HDp Hrec HΨf HΨa Hdisj Hftag Hwfq;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_g_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ apply ad_pat_sub_g__univ_ghost_l; [ exact HMti | exact HDp ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* tophole congruence *)
    inversion HeqR; subst.
    apply ad_pat_sub_g__univ_ghost_l; [ exact HMti | ].
    eapply Hrec with (Ψr0 := Ψrep) (Ψsup0 := Ψsup) (Ψna0 := Ψna);
      [ exact Hup | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj
      | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq ].
  - (* hole *)
    subst R.
    eapply ad_pat_sub_g_hole_intro with
      (n := n) (Ψfull := Ψfull) (R := uskl_tophole Rg0);
      [ apply ad_pat_sub_g__univ_ghost_l; [ exact HMti | exact HDp ]
      | reflexivity | exact Hwf | exact H0 | exact Hwfq
      | clear - HΨf; fsetdec ].
  - (* tophole_remove *)
    apply ad_pat_sub_g_wrap_tophole.
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact HDp | exact Hrec | exact HΨf | exact HΨa
      | exact Hdisj | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq ].
  - (* flex_l *)
    eapply ad_pat_sub_g_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact HDp | exact Hrec | exact HΨf | exact HΨa
      | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq ].
Qed.

(** [UnivGhostLG]: ∀◈-subject, SK, non-incrementing. *)
Lemma ad_pat_sub_g_ughost_lg_transport : forall Θb Ψr Rg' Rgt,
  uskl_precise Θb Ψr Rg' Rgt ->
  forall n Mg Θ' Ψfull Rg0 Qg Ψsup Ψn Ψna,
  Rgt = uskl_topholeg Rg0 ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  Mg <> mode_ti ->
  ad_pat_sub_g n a_sub_mode_sk Mg Ψfull Θ' Rg0 Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' Rg0 ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     Ψfull [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
     ad_pat_sub_g n a_sub_mode_sk Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
  ad_pat_sub_g n a_sub_mode_sk Mg Ψn Θ' Rg' Qg.
Proof.
  intros Θb Ψr Rg' Rgt Hup; induction Hup;
    intros n Mg Θ' Ψfull Rg0 Qg Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf HMti HDp Hrec HΨf HΨa Hdisj Hftag Hwfq;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_g_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ apply ad_pat_sub_g__univ_ghost_lg; [ exact HMti | exact HDp ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* topholeg congruence *)
    inversion HeqR; subst.
    apply ad_pat_sub_g__univ_ghost_lg; [ exact HMti | ].
    eapply Hrec with (Ψr0 := Ψrep) (Ψsup0 := Ψsup) (Ψna0 := Ψna);
      [ exact Hup | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj
      | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq ].
  - (* tophole_keepg: plain ∀◇ on the ghostier side *)
    inversion HeqR; subst.
    apply ad_pat_sub_g__univ_ghost_l; [ exact HMti | ].
    eapply Hrec with (Ψr0 := Ψrep) (Ψsup0 := Ψsup) (Ψna0 := Ψna);
      [ exact Hup | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj
      | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq ].
  - (* hole *)
    subst R.
    eapply ad_pat_sub_g_hole_intro with
      (n := n) (Ψfull := Ψfull) (R := uskl_topholeg Rg0);
      [ apply ad_pat_sub_g__univ_ghost_lg; [ exact HMti | exact HDp ]
      | reflexivity | exact Hwf | exact H0 | exact Hwfq
      | clear - HΨf; fsetdec ].
  - (* tophole_remove *)
    apply ad_pat_sub_g_wrap_tophole.
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact HDp | exact Hrec | exact HΨf | exact HΨa
      | exact Hdisj | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq ].
  - (* flex_l *)
    eapply ad_pat_sub_g_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact HDp | exact Hrec | exact HΨf | exact HΨa
      | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq ].
Qed.

(** [FlexMono]: defined-flexible-variable subject, fn-mode, non-incrementing. *)
Lemma ad_pat_sub_g_flex_mono_transport : forall Θb Ψr Rg' Rgv,
  uskl_precise Θb Ψr Rg' Rgv ->
  forall n NM Mg Θ' Ψfull αg τg Qg Ψsup Ψn Ψna,
  Rgv = uskl_var_f αg ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  binds αg (abind_flex_mono_def τg) Θ' ->
  ad_pat_sub_g n NM (mode_fn Mg) Ψfull Θ' (ptyp_to_uskl_syn τg) Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' (ptyp_to_uskl_syn τg) ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     Ψfull [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg'') ->
     ad_pat_sub_g n NM (mode_fn Mg) Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free Rg') ->
  ad_pat_sub_g n NM (mode_fn Mg) Ψn Θ' Rg' Qg.
Proof.
  intros Θb Ψr Rg' Rgv Hup; induction Hup;
    intros n NM Mg Θ' Ψfull αg τg Qg Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf Hbnd HDp Hrec HΨf HΨa Hdisj Hftag Hwfq Hgf;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_g_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ eapply ad_pat_sub_g__flex_mono; [ exact Hbnd | exact HDp ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* hole *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + subst R.
      eapply ad_pat_sub_g_hole_intro with
        (n := n) (Ψfull := Ψfull) (R := uskl_var_f αg);
        [ eapply ad_pat_sub_g__flex_mono; [ exact Hbnd | exact HDp ]
        | reflexivity | exact Hwf | exact H0 | exact Hwfq
        | clear - HΨf; fsetdec ].
  - (* tophole_remove *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + apply ad_pat_sub_g_wrap_tophole.
      eapply IHHup with (Ψna := Ψna);
        [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
        | exact Hbnd | exact HDp | exact Hrec | exact HΨf | exact HΨa
        | exact Hdisj | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq
        | intro He; discriminate He ].
  - (* flex_l: another defined variable on the ghostier side *)
    eapply ad_pat_sub_g_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact Hbnd | exact HDp | exact Hrec | exact HΨf | exact HΨa
      | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq
      | intro He;
        apply mono_ptyp_to_uskl_syn_ghost_free;
        eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact H ] ].
  - (* flex_r: unfold to the definition — unique by wf *)
    inversion HeqR; subst.
    assert (Hb' : binds αg (abind_flex_mono_def τ) Θ')
      by (apply Hmon; exact H).
    assert (Hu : uniq Θ') by (apply a_wf_aenv_uniq; exact Hwf).
    pose proof (binds_unique _ _ _ _ _ Hb' Hbnd Hu) as He; inversion He; subst.
    eapply Hrec with (Ψr0 := Ψrep) (Ψsup0 := Ψsup) (Ψna0 := Ψna);
      [ exact Hup | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag | exact Hwfq
      | exact Hgf ].
Qed.

(* ===================================================================== *)
(*  P5b-ii step (3) — PRECISION-SUBSTITUTION, ⊑ᵤ-form.                     *)
(*  [lemma:precision-substitution] (subtyping-proofs.tex:1664), stated     *)
(*  over the hygienic mirror and the subject-precision relation: any      *)
(*  hygienic derivation transports to a ⊑ᵤ-ghostier subject at the SAME   *)
(*  fuel, the tag context dropping by the replaced decorations' tags.     *)
(* ===================================================================== *)

Lemma ad_pat_sub_precise_upre : forall n NM M Ψfull Θ' Rg Q,
  ad_pat_sub_g n NM M Ψfull Θ' Rg Q ->
  forall Θb Ψr Rg' Ψsup Ψn Ψna,
  uskl_precise Θb Ψr Rg' Rg ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free Rg') ->
  ad_pat_sub_g n NM M Ψn Θ' Rg' Q.
Proof.
  intros n NM M Ψfull Θ' Rg Q HD; induction HD;
    intros Θb Ψr Rg' Ψsup Ψn Ψna Hup Hwfb HΨsup Hmon Hwf
      HΨf HΨa Hdisj Hftag Hwfq Hgf.
  - (* Infer *)
    apply ad_pat_sub_g__infer;
      [ clear - H HΨf; fsetdec | | exact H1 ].
    pose proof (ad_pat_consis_precise_upre Hup HΨsup Hftag) as Ht.
    eapply Ht with (Ψna := empty);
      [ exact H0 | exact Hmon | exact Hwf
      | clear; fsetdec | clear; fsetdec | clear; fsetdec | exact Hwfq ].
  - (* Check (TY) *)
    apply ad_pat_sub_g__check;
      [ eapply uskl_precise_guarded;
          [ exact Hup | exact Hwfb | exact H | apply Hgf; reflexivity ]
      | exact H0 | ].
    pose proof (ad_pat_consis_precise_upre Hup HΨsup Hftag) as Ht.
    eapply Ht with (Ψna := Ψna);
      [ exact H1 | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwfq ].
  - (* ForallR (TY) *)
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_sub_g__forall_r with (L := L `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (H0 α ltac:(clear - Hα; solve_notin_auto)) with (Ψna := Ψna);
      [ exact Hup | exact Hwfb | exact HΨsup
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec
      | exact Hgf ].
  - (* UnivGhostR (SK) *)
    assert (HΨe : Ψn [=] empty) by (clear - H HΨf; fsetdec).
    simpl in Hwfq. destruct (a_wf_pskl_tophole_inv Hwfq) as [HgP HwbP].
    eapply ad_pat_sub_g_ughost_r_transport;
      [ exact Hup | exact Hwfb | exact HΨsup | exact Hftag
      | exact Hmon | exact Hwf | exact H0 | exact H3 | exact H1
      | exact H2 | exact HwbP | exact HΨe ].
  - (* Arrow *)
    eapply ad_pat_sub_g_arrow_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact HD | exact H0
      | intros Θb0 Ψr0 Rg2' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag
      | exact Hwfq | exact Hgf ].
  - (* ForallL tagged *)
    eapply ad_pat_sub_g_forall_l_tagged_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact H0 | exact H1 | exact H2 | exact H3
      | exact HD
      | intros Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag
      | exact Hwfq | exact Hgf ].
  - (* ForallL untagged *)
    eapply ad_pat_sub_g_forall_l_untagged_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact H0 | exact H1 | exact H2 | exact H3
      | exact HD
      | intros Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag
      | exact Hwfq | exact Hgf ].
  - (* Ghost (SK) *)
    assert (HΨe : Ψn [=] empty) by (clear - H HΨf; fsetdec).
    eapply ad_pat_sub_g_ghost_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact Hmon | exact Hwf
      | exact H0 | exact H1 | exact HΨe ].
  - (* GhostG (SK) *)
    assert (HΨe : Ψn [=] empty) by (clear - H HΨf; fsetdec).
    eapply ad_pat_sub_g_ghostg_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact Hmon | exact Hwf
      | exact H0 | exact HΨe ].
  - (* UnivGhostL (SK) *)
    eapply ad_pat_sub_g_ughost_l_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact HD
      | intros Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10
          | intro Habs; discriminate Habs ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag | exact Hwfq ].
  - (* UnivGhostLG (SK) *)
    eapply ad_pat_sub_g_ughost_lg_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact HD
      | intros Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10
          | intro Habs; discriminate Habs ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag | exact Hwfq ].
  - (* FlexMono *)
    eapply ad_pat_sub_g_flex_mono_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact HD
      | intros Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag
      | exact Hwfq | exact Hgf ].
Qed.

(* ===================================================================== *)
(*  P5c — step (3) over the LEAF-VALID mirror [ad_pat_sub_gv]             *)
(*  (Sub-ForallL item 3).                                                 *)
(*                                                                        *)
(*  Same per-rule transports as step (3); the NEW obligations are the     *)
(*  leaf refinements the [_gv] rows carry at [__infer] / [__check] /      *)
(*  [__univ_ghost_r] / [__arrow]'s domain.  Each is transported to the    *)
(*  ghostier subject by [uskl_precise_erase_refine] (item 1) at Δ = ∅ —   *)
(*  whose assumed-target-wf premise is exactly the row's [Hwfq] — and     *)
(*  across the flex-unfolding peels by                                    *)
(*  [ad_refine_pskl_unfold_def_subject] below.                            *)
(* ===================================================================== *)

(** Unfold a defined flexible variable on the SUBJECT side of a
    refinement (the ⊳-mirror of [consis_unfold_def_subject]). *)
Lemma ad_refine_pskl_unfold_def_subject : forall Θ Δ α Qt,
  {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_var_f α) ⊳ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall τ, binds α (abind_flex_mono_def τ) Θ ->
  {{ Θ ⨟ Δ ⊢ᵣₚ (ptyp_to_pskl τ) ⊳ Qt }}ad.
Proof.
  intros Θ Δ α Qt Href.
  remember (pskl_var_f α) as S eqn:HeqS.
  revert HeqS; induction Href; intros HeqS Hwf τ0 Hb;
    try discriminate HeqS.
  - (* var : source = target = the variable; unfold on the right too *)
    inversion HeqS; subst.
    eapply ad_refine_pskl__flex_r; [ exact Hb | ].
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl.
    eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb ].
  - (* flex_l : the premise IS the unfolded refinement *)
    inversion HeqS; subst.
    assert (Hu : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwf).
    pose proof (binds_unique _ _ _ _ _ H Hb Hu) as He; inversion He; subst.
    exact Href.
  - (* flex_r : recurse into the target's definition *)
    eapply ad_refine_pskl__flex_r; [ exact H | ].
    apply IHHref; [ exact HeqS | exact Hwf | exact Hb ].
Qed.

(** Tag-context congruence for the leaf-valid mirror. *)
(** Uniform refl-transport, leaf-valid ([ftag_sub] via [_forget]). *)
Lemma ad_pat_sub_gv_refl_transport : forall n NM M Ψfull Θ' R Q,
  ad_pat_sub_gv n NM M Ψfull Θ' R Q ->
  forall Ψsup Ψn Ψna,
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ ftag_in_uskl R [=] empty ->
  ad_pat_sub_gv n NM M Ψn Θ' R Q.
Proof.
  intros n NM M Ψfull Θ' R Q HD Ψsup Ψn Ψna HΨf HΨa Hftag.
  pose proof (ad_pat_sub_g_ftag_sub (ad_pat_sub_gv_forget HD)) as Hfs.
  eapply ad_pat_sub_gv_psi_cong;
    [ exact HD | clear - HΨf HΨa Hftag Hfs; fsetdec ].
Qed.

(** Wrap a ∀◇ over an SK subject at the SAME fuel, leaf-valid: the TI
    re-route through [Infer] peels the new ∀◇ off the leaf refinement
    with [__tophole_remove]. *)
Lemma ad_pat_sub_gv_wrap_tophole : forall n M Ψ Θ R Q,
  ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ R Q ->
  ad_pat_sub_gv n a_sub_mode_sk M Ψ Θ (uskl_tophole R) Q.
Proof.
  intros n M Ψ Θ R Q H.
  destruct M.
  - (* ti *)
    inversion H; subst; try congruence.
    + apply ad_pat_sub_gv__infer; [ assumption | | assumption | ].
      * apply ad_pat_consis__tophole_drop; assumption.
      * simpl. apply ad_refine_pskl__tophole_remove. assumption.
    + (* ghost: subject hole, target inh P *)
      apply ad_pat_sub_gv__infer; [ assumption | | | ].
      * apply ad_pat_consis__tophole_drop.
        apply ad_pat_consis__hole; [ clear; fsetdec | assumption ].
      * match goal with Hmc : mod_comp_sk _ mode_ti |- _ =>
          inversion Hmc; subst; assumption end.
      * simpl. rewrite bskl_to_pskl_pskl_to_bskl_inh.
        apply ad_refine_pskl__tophole_remove.
        apply ad_refine_pskl__hole. assumption.
    + (* ghostg *)
      apply ad_pat_sub_gv__infer; [ assumption | | | ].
      * apply ad_pat_consis__tophole_drop.
        apply ad_pat_consis__ghostg; clear; fsetdec.
      * match goal with Hmc : mod_comp_sk _ mode_ti |- _ =>
          inversion Hmc; subst; assumption end.
      * simpl. apply ad_refine_pskl__tophole_remove.
        apply ad_refine_pskl__hole. apply a_wf_pskl__hole.
  - (* tc *)
    apply ad_pat_sub_gv__univ_ghost_l; [ discriminate | assumption ].
  - (* fn *)
    apply ad_pat_sub_gv__univ_ghost_l; [ discriminate | assumption ].
Qed.

(** Fold a flexible definition back into its variable, leaf-valid: the
    leaf rows re-fold their refinement with [__flex_l]. *)
Lemma ad_pat_sub_gv_fold_flex : forall n NM M Ψ Θ Rτ Q,
  ad_pat_sub_gv n NM M Ψ Θ Rτ Q ->
  forall α τ,
  Rτ = ptyp_to_uskl_syn τ ->
  binds α (abind_flex_mono_def τ) Θ ->
  {{ ⊢ Θ }}a ->
  ad_pat_sub_gv n NM M Ψ Θ (uskl_var_f α) Q.
Proof.
  intros n NM M Ψ Θ Rτ Q HD; induction HD; intros α0 τ0 HeqS Hb Hwf.
  - (* infer *)
    apply ad_pat_sub_gv__infer; [ assumption | | assumption | ].
    + eapply ad_pat_consis__flex_l; [ exact Hb | ].
      rewrite <- HeqS; assumption.
    + simpl. eapply ad_refine_pskl__flex_l; [ exact Hb | ].
      rewrite <- (uskl_to_pskl_ptyp τ0). rewrite <- HeqS. assumption.
  - (* check *)
    apply ad_pat_sub_gv__check;
      [ apply guarded_uskl__var | assumption | | ].
    + eapply ad_pat_consis__flex_l; [ exact Hb | ].
      rewrite <- HeqS; assumption.
    + simpl. eapply ad_refine_pskl__flex_l; [ exact Hb | ].
      rewrite <- (uskl_to_pskl_ptyp τ0). rewrite <- HeqS. assumption.
  - (* forall_r *)
    eapply ad_pat_sub_gv__forall_r with (L := L `union` dom Θ).
    intros β Hβ.
    eapply (H0 β ltac:(clear - Hβ; solve_notin_auto) α0 τ0 HeqS);
      [ unfold binds; simpl; right; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hβ; fsetdec | exact Hwf ] ].
  - (* univ_ghost_r *)
    apply ad_pat_sub_gv__univ_ghost_r; try assumption.
    + apply guarded_uskl__var.
    + eapply ad_pat_consis__flex_l; [ exact Hb | ].
      rewrite <- HeqS; assumption.
    + simpl. eapply ad_refine_pskl__flex_l; [ exact Hb | ].
      rewrite <- (uskl_to_pskl_ptyp τ0). rewrite <- HeqS. assumption.
  - (* arrow *)
    eapply ad_pat_sub_gv__flex_mono with (τ := τ0); [ exact Hb | ].
    rewrite <- HeqS.
    eapply ad_pat_sub_gv__arrow; eassumption.
  - (* forall_l_tagged — a painted monotype has no quantifier *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* forall_l_untagged *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* ghost *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* ghostg *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* univ_ghost_l *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* univ_ghost_lg *)
    assert (Hm : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb ]).
    destruct Hm; unfold ptyp_to_uskl_syn in HeqS; simpl in HeqS;
      discriminate HeqS.
  - (* flex_mono *)
    eapply ad_pat_sub_gv__flex_mono with (τ := τ0); [ exact Hb | ].
    rewrite <- HeqS.
    eapply ad_pat_sub_gv__flex_mono; eassumption.
Qed.

(** Uniform hole-introduction, leaf-valid: the target analysis reuses the
    plain mirror via [_forget]; [Ghost] carries no leaf. *)
Lemma ad_pat_sub_gv_hole_intro : forall n n' NM M Ψfull Θ' R Q,
  ad_pat_sub_gv n NM M Ψfull Θ' R Q ->
  NM = a_sub_mode_sk ->
  {{ ⊢ Θ' }}a ->
  pskl_no_forall (uskl_to_pskl R) ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  forall Ψn, Ψn [<=] Ψfull ->
  ad_pat_sub_gv n' NM M Ψn Θ' uskl_hole Q.
Proof.
  intros n n' NM M Ψfull Θ' R Q HD HNM Hwf Hnf Hwfq Ψn HΨn.
  destruct (ad_pat_sub_g_concrete_target (ad_pat_sub_gv_forget HD) HNM Hwf Hnf)
    as [HΨe [Heq Hmc]].
  rewrite <- Heq. subst NM.
  apply ad_pat_sub_gv__ghost.
  - clear - HΨn HΨe; fsetdec.
  - exact Hwfq.
  - rewrite Heq. exact Hmc.
Qed.

(* ===================================================================== *)
(*  P5c per-rule ⊑ᵤ-transports (leaf-valid).                              *)
(* ===================================================================== *)

(** [UnivGhostR], leaf-valid: the extra [Hlf] premise is the rule's leaf
    refinement; the congruence root transports it by item 1, the flex_r
    peel unfolds it. *)
Lemma ad_pat_sub_gv_ughost_r_transport : forall Θb Ψrep R' R,
  uskl_precise Θb Ψrep R' R ->
  forall Ψsup n Θ' Ψn Q,
  {{ ⊢ Θb }}a ->
  Ψrep [<=] Ψsup ->
  Ψsup ∩ ftag_in_uskl R' [=] empty ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  guarded_uskl R ->
  {{ empty ⨟ Θ' ⊢ˢ R ∼ Q }}ad ->
  {{ Θ' ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) }}ad ->
  guarded_bskl Q ->
  is_sskl Q ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  Ψn [=] empty ->
  ad_pat_sub_gv n a_sub_mode_sk mode_tc Ψn Θ' R' (bskl_tophole Q).
Proof.
  intros Θb Ψrep R' R Hup; induction Hup;
    intros Ψsup n Θ' Ψn Q0 Hwfb HΨsup Hftag Hmon Hwf Hgd Hc3 Hlf HgQ HsQ
      Hwfq HΨe.
  - (* refl *)
    apply ad_pat_sub_gv__univ_ghost_r;
      [ exact HΨe | exact Hgd | exact HgQ | exact HsQ | exact Hc3
      | exact Hlf ].
  - (* arrow cong *)
    pose proof (upre__arrow Hup1 Hup2 H) as Hup'.
    apply ad_pat_sub_gv__univ_ghost_r;
      [ exact HΨe
      | apply guarded_uskl__arrow;
          [ eapply uskl_precise_lc_l; exact Hup1
          | eapply uskl_precise_lc_l; exact Hup2 ]
      | exact HgQ | exact HsQ | | ].
    + pose proof (ad_pat_consis_precise_upre Hup' HΨsup Hftag) as Ht.
      eapply Ht with (Ψna := empty);
        [ exact Hc3 | exact Hmon | exact Hwf
        | clear; fsetdec | clear; fsetdec | clear; fsetdec | exact Hwfq ].
    + eapply uskl_precise_erase_refine;
        [ exact Hlf | exact Hwf
        | intros β Hβ; exfalso; clear - Hβ; fsetdec
        | exact Hwfq | exact Hup' | exact Hmon | reflexivity ].
  - (* all_syn cong: not a guarded subject *) inversion Hgd.
  - (* all_tag cong *) inversion Hgd.
  - (* all_inst *) inversion Hgd.
  - (* tophole cong *) inversion Hgd.
  - (* topholeg cong *) inversion Hgd.
  - (* tophole_keepg *) inversion Hgd.
  - (* hole: replace by □ via Ghost against the ∀◇-target *)
    assert (Hnode : ad_pat_sub_gv n a_sub_mode_sk mode_tc Ψn Θ' R
                      (bskl_tophole Q0))
      by (apply ad_pat_sub_gv__univ_ghost_r;
          [ exact HΨe | exact Hgd | exact HgQ | exact HsQ | exact Hc3
          | exact Hlf ]).
    eapply ad_pat_sub_gv_hole_intro with (Ψfull := Ψn);
      [ exact Hnode | reflexivity | exact Hwf | exact H0
      | simpl; apply a_wf_pskl__tophole;
          [ apply guarded_bskl_to_pskl; exact HgQ | exact Hwfq ]
      | clear; fsetdec ].
  - (* tophole_remove: peel via UnivGhostL (same fuel) *)
    apply ad_pat_sub_gv_wrap_tophole.
    eapply IHHup with (Ψsup := Ψsup);
      [ exact Hwfb | exact HΨsup | clear - Hftag; simpl in Hftag; fsetdec
      | exact Hmon | exact Hwf | exact Hgd | exact Hc3 | exact Hlf
      | exact HgQ | exact HsQ | exact Hwfq | exact HΨe ].
  - (* flex_l: peel via FlexMono-fold *)
    eapply ad_pat_sub_gv_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψsup := Ψsup);
      [ exact Hwfb | exact HΨsup
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hmon | exact Hwf | exact Hgd | exact Hc3 | exact Hlf
      | exact HgQ | exact HsQ | exact Hwfq | exact HΨe ].
  - (* flex_r: the subject is a defined flexible variable — unfold it *)
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (apply Hmon; exact H).
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb' ]).
    assert (Hlf' : {{ Θ' ⨟ empty ⊢ᵣₚ ⌊ ptyp_to_uskl_syn τ ⌋ˢ
                     ⊳ (bskl_to_pskl Q0) }}ad).
    { rewrite uskl_to_pskl_ptyp.
      eapply ad_refine_pskl_unfold_def_subject;
        [ exact Hlf | exact Hwf | exact Hb' ]. }
    eapply IHHup with (Ψsup := Ψsup);
      [ exact Hwfb | exact HΨsup | exact Hftag | exact Hmon | exact Hwf
      | apply mono_paint_guarded;
          [ exact Hm
          | rewrite <- pskl_to_uskl_ptyp; apply pskl_to_uskl_lc;
            apply a_wf_pskl_lc with (Θ := Θ') (Δ := empty);
            apply a_wf_pskl_mono_ptyp;
              [ exact Hm
              | eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb' ] ] ]
      | eapply consis_unfold_def_subject;
          [ exact Hc3 | exact Hwf | reflexivity | exact Hb' ]
      | exact Hlf' | exact HgQ | exact HsQ | exact Hwfq | exact HΨe ].
Qed.

(** [Ghost], leaf-valid (no leaf on the rule). *)
Lemma ad_pat_sub_gv_ghost_transport : forall Θb Ψrep R' R,
  uskl_precise Θb Ψrep R' R ->
  forall n M Θ' Ψn P,
  R = uskl_hole ->
  {{ ⊢ Θb }}a ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  {{ Θ' ⨟ empty ⊢ₚₛ P }}a ->
  mod_comp_sk (pskl_to_bskl_inh P) M ->
  Ψn [=] empty ->
  ad_pat_sub_gv n a_sub_mode_sk M Ψn Θ' R' (pskl_to_bskl_inh P).
Proof.
  intros Θb Ψrep R' R Hup; induction Hup;
    intros n M Θ' Ψn P0 HeqR Hwfb Hmon Hwf HwfP Hmc HΨe;
    try discriminate HeqR.
  - (* refl: R' = □ *)
    subst R.
    apply ad_pat_sub_gv__ghost; [ exact HΨe | exact HwfP | exact Hmc ].
  - (* hole: R' = □ as well *)
    apply ad_pat_sub_gv__ghost; [ exact HΨe | exact HwfP | exact Hmc ].
  - (* tophole_remove *)
    apply ad_pat_sub_gv_wrap_tophole.
    eapply IHHup;
      [ exact HeqR | exact Hwfb | exact Hmon | exact Hwf
      | exact HwfP | exact Hmc | exact HΨe ].
  - (* flex_l *)
    eapply ad_pat_sub_gv_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup;
      [ exact HeqR | exact Hwfb | exact Hmon | exact Hwf
      | exact HwfP | exact Hmc | exact HΨe ].
Qed.

(** [GhostG], leaf-valid (no leaf on the rule). *)
Lemma ad_pat_sub_gv_ghostg_transport : forall Θb Ψrep R' R,
  uskl_precise Θb Ψrep R' R ->
  forall n M Θ' Ψn,
  R = uskl_holeg ->
  {{ ⊢ Θb }}a ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  mod_comp_sk bskl_hole M ->
  Ψn [=] empty ->
  ad_pat_sub_gv n a_sub_mode_sk M Ψn Θ' R' bskl_hole.
Proof.
  intros Θb Ψrep R' R Hup; induction Hup;
    intros n M Θ' Ψn HeqR Hwfb Hmon Hwf Hmc HΨe;
    try discriminate HeqR.
  - (* refl: R' = ⫯ *)
    subst R.
    apply ad_pat_sub_gv__ghostg; [ exact HΨe | exact Hmc ].
  - (* hole: R' = □ against the ⫯-target *)
    change bskl_hole with (pskl_to_bskl_inh pskl_hole).
    apply ad_pat_sub_gv__ghost;
      [ exact HΨe | apply a_wf_pskl__hole | simpl; exact Hmc ].
  - (* tophole_remove *)
    apply ad_pat_sub_gv_wrap_tophole.
    eapply IHHup;
      [ exact HeqR | exact Hwfb | exact Hmon | exact Hwf
      | exact Hmc | exact HΨe ].
  - (* flex_l *)
    eapply ad_pat_sub_gv_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup;
      [ exact HeqR | exact Hwfb | exact Hmon | exact Hwf
      | exact Hmc | exact HΨe ].
Qed.

(** [Arrow], leaf-valid: the domain's consistency leaf carries the
    subject refinement — transported at the congruence root by item 1. *)
Lemma ad_pat_sub_gv_arrow_transport : forall Θb Ψr Rg' Rgarr,
  uskl_precise Θb Ψr Rg' Rgarr ->
  forall n NM Mg Θ' Ψfull Ψc1 Ψc2 Rg1 Rg2 Qg1 Qg2 Ψsup Ψn Ψna,
  Rgarr = uskl_arrow Rg1 Rg2 ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  {{ Ψc1 ⨟ Θ' ⊢ˢ Rg1 ∼ Qg1 }}ad ->
  {{ Θ' ⨟ empty ⊢ᵣₚ ⌊ Rg1 ⌋ˢ ⊳ (bskl_to_pskl Qg1) }}ad ->
  ad_pat_sub_gv n NM Mg Ψc2 Θ' Rg2 Qg2 ->
  Ψfull [=] Ψc1 `union` Ψc2 ->
  (forall Θb0 Ψr0 Rg2' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg2' Rg2 ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     Ψc2 [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg2' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg2) }}a ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg2') ->
     ad_pat_sub_gv n NM Mg Ψn0 Θ' Rg2' Qg2) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl (bskl_arrow Qg1 Qg2)) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free Rg') ->
  ad_pat_sub_gv (S n) NM (mode_fn Mg) Ψn Θ' Rg' (bskl_arrow Qg1 Qg2).
Proof.
  intros Θb Ψr Rg' Rgarr Hup; induction Hup;
    intros n NM Mg Θ' Ψfull Ψc1 Ψc2 Rg1 Rg2 Qg1 Qg2 Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf Hcl Hlf1 HDr HΨsplit Hrec HΨf HΨa Hdisj Hftag
      Hwfq Hgf;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_gv_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ eapply ad_pat_sub_gv__arrow;
          [ exact Hcl | exact Hlf1 | exact HDr | exact HΨsplit ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* arrow congruence *)
    inversion HeqR; subst.
    simpl in Hwfq.
    assert (Hwfq1 : {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg1) }}a)
      by (inversion Hwfq; subst; assumption).
    assert (Hwfq2 : {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg2) }}a)
      by (inversion Hwfq; subst; assumption).
    simpl in Hftag.
    eapply ad_pat_sub_gv__arrow with
      (Ψ1 := Ψc1 ∖ Ψsup) (Ψ2 := Ψc2 ∖ Ψsup).
    + assert (Hs1 : Ψ1 [<=] Ψsup) by (clear - HΨsup H; fsetdec).
      assert (Hf1 : Ψsup ∩ ftag_in_uskl R1' [=] empty)
        by (clear - Hftag; fsetdec).
      eapply (ad_pat_consis_precise_upre Hup1 Hs1 Hf1)
        with (Ψna := Ψc1 ∩ Ψsup);
        [ exact Hcl | exact Hmon | exact Hwf
        | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
        | clear - Hdisj; fsetdec | exact Hwfq1 ].
    + eapply uskl_precise_erase_refine;
        [ exact Hlf1 | exact Hwf
        | intros β Hβ; exfalso; clear - Hβ; fsetdec
        | exact Hwfq1 | exact Hup1 | exact Hmon | reflexivity ].
    + eapply Hrec with (Ψr0 := Ψ2) (Ψsup0 := Ψsup)
        (Ψna0 := Ψc2 ∩ Ψsup);
        [ exact Hup2 | exact Hwfb | clear - HΨsup H; fsetdec
        | exact Hmon | exact Hwf
        | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
        | clear - Hdisj; fsetdec | clear - Hftag; fsetdec
        | exact Hwfq2
        | intro He; specialize (Hgf He); inversion Hgf; subst; assumption ].
    + clear - HΨsplit HΨf HΨa Hdisj; fsetdec.
  - (* hole *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + subst R.
      eapply ad_pat_sub_gv_hole_intro with
        (n := S n) (Ψfull := Ψfull) (R := uskl_arrow Rg1 Rg2);
        [ eapply ad_pat_sub_gv__arrow;
            [ exact Hcl | exact Hlf1 | exact HDr | exact HΨsplit ]
        | reflexivity | exact Hwf | exact H0 | exact Hwfq
        | clear - HΨf; fsetdec ].
  - (* tophole_remove *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + apply ad_pat_sub_gv_wrap_tophole.
      eapply IHHup with (Ψna := Ψna);
        [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
        | exact Hcl | exact Hlf1 | exact HDr | exact HΨsplit | exact Hrec
        | exact HΨf | exact HΨa | exact Hdisj
        | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq
        | intro He; discriminate He ].
  - (* flex_l *)
    eapply ad_pat_sub_gv_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact Hcl | exact Hlf1 | exact HDr | exact HΨsplit | exact Hrec
      | exact HΨf | exact HΨa | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq
      | intro He;
        apply mono_ptyp_to_uskl_syn_ghost_free;
        eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact H ] ].
Qed.

(** [ForallL] (tagged), leaf-valid — the crux machinery is unchanged
    (the rule carries no leaf; the body-⊑ᵤ transports under [ψg/α] by
    [uskl_precise_subst]). *)
Lemma ad_pat_sub_gv_forall_l_tagged_transport : forall Θb Ψr Rg' Rgall,
  uskl_precise Θb Ψr Rg' Rgall ->
  forall n NM Mg Θ' Ψfull Ψi' εg Rg0 ψg Qg Ψsup Ψn Ψna,
  Rgall = uskl_all_tag εg Rg0 ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  Mg <> mode_ti ->
  Ψi' ∩ Ψfull [=] empty ->
  Ψi' ∩ (ftag_in_uskl (uskl_all_tag εg Rg0)) [=] empty ->
  a_tags_sort NM Ψi' ψg ->
  {{ Θ' ⨟ empty ⊢ₚₛ ⌊ ψg ⌋ˢ }}a ->
  ad_pat_sub_gv n NM Mg (Ψfull `union` Ψi') Θ' (open_uskl_wrt_uskl Rg0 ψg) Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' (open_uskl_wrt_uskl Rg0 ψg) ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     (Ψfull `union` Ψi') [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg'') ->
     ad_pat_sub_gv n NM Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free Rg') ->
  ad_pat_sub_gv (S n) NM Mg Ψn Θ' Rg' Qg.
Proof.
  intros Θb Ψr Rg' Rgall Hup; induction Hup;
    intros n NM Mg Θ' Ψfull Ψi' εg Rg0 ψg Qg Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf HMti Hictx Hihyg Htags Hwfψ HDp Hrec
      HΨf HΨa Hdisj Hftag Hwfq Hgf;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_gv_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ eapply ad_pat_sub_gv__forall_l_tagged with (Ψ' := Ψi') (ψ := ψg);
        [ exact HMti | exact Hictx | exact Hihyg | exact Htags
        | exact Hwfψ | exact HDp ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* all_tag congruence: rebuild ForallL-tagged with ψg *)
    inversion HeqR; subst.
    assert (Hlcψ : lc_uskl ψg)
      by (apply is_tskl_lc; inversion Htags; subst; assumption).
    pick fresh α for (L `union` dom Θb
        `union` ftvar_in_uskl R' `union` ftvar_in_uskl Rg0).
    pose proof (H α ltac:(clear - Fr; solve_notin_auto)) as Hbody.
    assert (Hsub : uskl_precise Θb Ψrep
        (open_uskl_wrt_uskl R' ψg) (open_uskl_wrt_uskl Rg0 ψg)).
    { rewrite (subst_uskl_in_uskl_intro α R' ψg ltac:(clear - Fr; solve_notin_auto)).
      rewrite (subst_uskl_in_uskl_intro α Rg0 ψg ltac:(clear - Fr; solve_notin_auto)).
      apply uskl_precise_subst;
        [ exact Hbody | exact Hlcψ | exact Hwfb | clear - Fr; fsetdec ]. }
    pose proof (uskl_precise_ftag_sub Hbody) as Hfsb.
    pose proof (uskl_precise_ftag_rep Hbody) as Hfrb.
    pose proof (ftag_in_uskl_open_var R' α) as Hov1.
    pose proof (ftag_in_uskl_open_var Rg0 α) as Hov2.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Htgψ.
    assert (Hgfψ : NM = a_sub_mode_ty -> uskl_ghost_free ψg)
      by (intro He; inversion Htags; subst;
          [ congruence | assumption ]).
    assert (Hgfo : NM = a_sub_mode_ty ->
                   uskl_ghost_free (open_uskl_wrt_uskl R' ψg)).
    { intro He.
      destruct (uskl_ghost_free_all_tag_inv (Hgf He)) as [Lg Hgb].
      pick fresh β for (Lg `union` ftvar_in_uskl R').
      rewrite (subst_uskl_in_uskl_intro β R' ψg
                 ltac:(clear - Fr0; solve_notin_auto)).
      apply uskl_ghost_free_subst;
        [ apply Hgb; clear - Fr0; fsetdec
        | apply Hgfψ; exact He
        | exact Hlcψ ]. }
    eapply ad_pat_sub_gv__forall_l_tagged with (Ψ' := Ψi') (ψ := ψg).
    + exact HMti.
    + clear - Hictx HΨf; fsetdec.
    + simpl. simpl in Hihyg. clear - Hihyg Hfsb Hov1 Hov2; fsetdec.
    + exact Htags.
    + exact Hwfψ.
    + eapply Hrec with (Ψr0 := Ψrep)
        (Ψsup0 := Ψsup ∖ Ψi') (Ψna0 := Ψna);
        [ exact Hsub | exact Hwfb
        | simpl in Hihyg; clear - HΨsup Hfrb Hov2 Hihyg; fsetdec
        | exact Hmon | exact Hwf
        | clear - HΨf; fsetdec
        | clear - HΨa HΨf Hictx; fsetdec
        | clear - Hdisj; fsetdec
        | pose proof (ftag_in_uskl_open_upper R' ψg) as Hou;
          simpl in Hftag; clear - Hou Hftag Htgψ; fsetdec
        | exact Hwfq
        | exact Hgfo ].
  - (* all_inst: rebuild ForallL-UNTAGGED with ψg *)
    inversion HeqR; subst.
    assert (Hlcψ : lc_uskl ψg)
      by (apply is_tskl_lc; inversion Htags; subst; assumption).
    pick fresh α for (L `union` dom Θb
        `union` ftvar_in_uskl R' `union` ftvar_in_uskl Rg0).
    pose proof (H α ltac:(clear - Fr; solve_notin_auto)) as Hbody.
    assert (Hsub : uskl_precise Θb Ψ0
        (open_uskl_wrt_uskl R' ψg) (open_uskl_wrt_uskl Rg0 ψg)).
    { rewrite (subst_uskl_in_uskl_intro α R' ψg ltac:(clear - Fr; solve_notin_auto)).
      rewrite (subst_uskl_in_uskl_intro α Rg0 ψg ltac:(clear - Fr; solve_notin_auto)).
      apply uskl_precise_subst;
        [ exact Hbody | exact Hlcψ | exact Hwfb | clear - Fr; fsetdec ]. }
    pose proof (uskl_precise_ftag_sub Hbody) as Hfsb.
    pose proof (uskl_precise_ftag_rep Hbody) as Hfrb.
    pose proof (ftag_in_uskl_open_var R' α) as Hov1.
    pose proof (ftag_in_uskl_open_var Rg0 α) as Hov2.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Htgψ.
    assert (Hgfψ : NM = a_sub_mode_ty -> uskl_ghost_free ψg)
      by (intro He; inversion Htags; subst;
          [ congruence | assumption ]).
    assert (Hgfo : NM = a_sub_mode_ty ->
                   uskl_ghost_free (open_uskl_wrt_uskl R' ψg)).
    { intro He.
      destruct (uskl_ghost_free_all_syn_inv (Hgf He)) as [Lg Hgb].
      pick fresh β for (Lg `union` ftvar_in_uskl R').
      rewrite (subst_uskl_in_uskl_intro β R' ψg
                 ltac:(clear - Fr0; solve_notin_auto)).
      apply uskl_ghost_free_subst;
        [ apply Hgb; clear - Fr0; fsetdec
        | apply Hgfψ; exact He
        | exact Hlcψ ]. }
    eapply ad_pat_sub_gv__forall_l_untagged with (Ψ' := Ψi') (ψ := ψg).
    + exact HMti.
    + clear - Hictx HΨf; fsetdec.
    + simpl. simpl in Hihyg. clear - Hihyg Hfsb Hov1 Hov2; fsetdec.
    + exact Htags.
    + exact Hwfψ.
    + eapply Hrec with (Ψr0 := Ψ0)
        (Ψsup0 := Ψsup ∖ Ψi') (Ψna0 := Ψna);
        [ exact Hsub | exact Hwfb
        | simpl in Hihyg; clear - HΨsup H1 Hfrb Hov2 Hihyg; fsetdec
        | exact Hmon | exact Hwf
        | clear - HΨf; fsetdec
        | clear - HΨa HΨf Hictx; fsetdec
        | clear - Hdisj; fsetdec
        | pose proof (ftag_in_uskl_open_upper R' ψg) as Hou;
          simpl in Hftag; clear - Hou Hftag Htgψ; fsetdec
        | exact Hwfq
        | exact Hgfo ].
  - (* hole: no_forall of an all_tag erasure is absurd *)
    subst R. simpl in H0. contradiction.
  - (* tophole_remove *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + apply ad_pat_sub_gv_wrap_tophole.
      eapply IHHup with (Ψna := Ψna);
        [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
        | exact HMti | exact Hictx | exact Hihyg | exact Htags | exact Hwfψ
        | exact HDp | exact Hrec | exact HΨf | exact HΨa | exact Hdisj
        | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq
        | intro He; discriminate He ].
  - (* flex_l *)
    eapply ad_pat_sub_gv_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact Hictx | exact Hihyg | exact Htags | exact Hwfψ
      | exact HDp | exact Hrec | exact HΨf | exact HΨa | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq
      | intro He;
        apply mono_ptyp_to_uskl_syn_ghost_free;
        eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact H ] ].
Qed.

(** [ForallL] (untagged), leaf-valid. *)
Lemma ad_pat_sub_gv_forall_l_untagged_transport : forall Θb Ψr Rg' Rgall,
  uskl_precise Θb Ψr Rg' Rgall ->
  forall n NM Mg Θ' Ψfull Ψi' Rg0 ψg Qg Ψsup Ψn Ψna,
  Rgall = uskl_all_syn Rg0 ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  Mg <> mode_ti ->
  Ψi' ∩ Ψfull [=] empty ->
  Ψi' ∩ (ftag_in_uskl (uskl_all_syn Rg0)) [=] empty ->
  a_tags_sort NM Ψi' ψg ->
  {{ Θ' ⨟ empty ⊢ₚₛ ⌊ ψg ⌋ˢ }}a ->
  ad_pat_sub_gv n NM Mg (Ψfull `union` Ψi') Θ' (open_uskl_wrt_uskl Rg0 ψg) Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' (open_uskl_wrt_uskl Rg0 ψg) ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     (Ψfull `union` Ψi') [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg'') ->
     ad_pat_sub_gv n NM Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free Rg') ->
  ad_pat_sub_gv (S n) NM Mg Ψn Θ' Rg' Qg.
Proof.
  intros Θb Ψr Rg' Rgall Hup; induction Hup;
    intros n NM Mg Θ' Ψfull Ψi' Rg0 ψg Qg Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf HMti Hictx Hihyg Htags Hwfψ HDp Hrec
      HΨf HΨa Hdisj Hftag Hwfq Hgf;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_gv_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ eapply ad_pat_sub_gv__forall_l_untagged with (Ψ' := Ψi') (ψ := ψg);
        [ exact HMti | exact Hictx | exact Hihyg | exact Htags
        | exact Hwfψ | exact HDp ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* all_syn congruence *)
    inversion HeqR; subst.
    assert (Hlcψ : lc_uskl ψg)
      by (apply is_tskl_lc; inversion Htags; subst; assumption).
    pick fresh α for (L `union` dom Θb
        `union` ftvar_in_uskl R' `union` ftvar_in_uskl Rg0).
    pose proof (H α ltac:(clear - Fr; solve_notin_auto)) as Hbody.
    assert (Hsub : uskl_precise Θb Ψrep
        (open_uskl_wrt_uskl R' ψg) (open_uskl_wrt_uskl Rg0 ψg)).
    { rewrite (subst_uskl_in_uskl_intro α R' ψg ltac:(clear - Fr; solve_notin_auto)).
      rewrite (subst_uskl_in_uskl_intro α Rg0 ψg ltac:(clear - Fr; solve_notin_auto)).
      apply uskl_precise_subst;
        [ exact Hbody | exact Hlcψ | exact Hwfb | clear - Fr; fsetdec ]. }
    pose proof (uskl_precise_ftag_sub Hbody) as Hfsb.
    pose proof (uskl_precise_ftag_rep Hbody) as Hfrb.
    pose proof (ftag_in_uskl_open_var R' α) as Hov1.
    pose proof (ftag_in_uskl_open_var Rg0 α) as Hov2.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Htgψ.
    assert (Hgfψ : NM = a_sub_mode_ty -> uskl_ghost_free ψg)
      by (intro He; inversion Htags; subst;
          [ congruence | assumption ]).
    assert (Hgfo : NM = a_sub_mode_ty ->
                   uskl_ghost_free (open_uskl_wrt_uskl R' ψg)).
    { intro He.
      destruct (uskl_ghost_free_all_syn_inv (Hgf He)) as [Lg Hgb].
      pick fresh β for (Lg `union` ftvar_in_uskl R').
      rewrite (subst_uskl_in_uskl_intro β R' ψg
                 ltac:(clear - Fr0; solve_notin_auto)).
      apply uskl_ghost_free_subst;
        [ apply Hgb; clear - Fr0; fsetdec
        | apply Hgfψ; exact He
        | exact Hlcψ ]. }
    eapply ad_pat_sub_gv__forall_l_untagged with (Ψ' := Ψi') (ψ := ψg).
    + exact HMti.
    + clear - Hictx HΨf; fsetdec.
    + simpl. simpl in Hihyg. clear - Hihyg Hfsb Hov1 Hov2; fsetdec.
    + exact Htags.
    + exact Hwfψ.
    + eapply Hrec with (Ψr0 := Ψrep)
        (Ψsup0 := Ψsup ∖ Ψi') (Ψna0 := Ψna);
        [ exact Hsub | exact Hwfb
        | simpl in Hihyg; clear - HΨsup Hfrb Hov2 Hihyg; fsetdec
        | exact Hmon | exact Hwf
        | clear - HΨf; fsetdec
        | clear - HΨa HΨf Hictx; fsetdec
        | clear - Hdisj; fsetdec
        | pose proof (ftag_in_uskl_open_upper R' ψg) as Hou;
          simpl in Hftag; clear - Hou Hftag Htgψ; fsetdec
        | exact Hwfq
        | exact Hgfo ].
  - (* hole: no_forall of an all_syn erasure is absurd *)
    subst R. simpl in H0. contradiction.
  - (* tophole_remove *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + apply ad_pat_sub_gv_wrap_tophole.
      eapply IHHup with (Ψna := Ψna);
        [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
        | exact HMti | exact Hictx | exact Hihyg | exact Htags | exact Hwfψ
        | exact HDp | exact Hrec | exact HΨf | exact HΨa | exact Hdisj
        | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq
        | intro He; discriminate He ].
  - (* flex_l *)
    eapply ad_pat_sub_gv_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact Hictx | exact Hihyg | exact Htags | exact Hwfψ
      | exact HDp | exact Hrec | exact HΨf | exact HΨa | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq
      | intro He;
        apply mono_ptyp_to_uskl_syn_ghost_free;
        eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact H ] ].
Qed.

(** [UnivGhostL], leaf-valid. *)
Lemma ad_pat_sub_gv_ughost_l_transport : forall Θb Ψr Rg' Rgt,
  uskl_precise Θb Ψr Rg' Rgt ->
  forall n Mg Θ' Ψfull Rg0 Qg Ψsup Ψn Ψna,
  Rgt = uskl_tophole Rg0 ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  Mg <> mode_ti ->
  ad_pat_sub_gv n a_sub_mode_sk Mg Ψfull Θ' Rg0 Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' Rg0 ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     Ψfull [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
     ad_pat_sub_gv n a_sub_mode_sk Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
  ad_pat_sub_gv n a_sub_mode_sk Mg Ψn Θ' Rg' Qg.
Proof.
  intros Θb Ψr Rg' Rgt Hup; induction Hup;
    intros n Mg Θ' Ψfull Rg0 Qg Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf HMti HDp Hrec HΨf HΨa Hdisj Hftag Hwfq;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_gv_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ apply ad_pat_sub_gv__univ_ghost_l; [ exact HMti | exact HDp ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* tophole congruence *)
    inversion HeqR; subst.
    apply ad_pat_sub_gv__univ_ghost_l; [ exact HMti | ].
    eapply Hrec with (Ψr0 := Ψrep) (Ψsup0 := Ψsup) (Ψna0 := Ψna);
      [ exact Hup | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj
      | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq ].
  - (* hole *)
    subst R.
    eapply ad_pat_sub_gv_hole_intro with
      (n := n) (Ψfull := Ψfull) (R := uskl_tophole Rg0);
      [ apply ad_pat_sub_gv__univ_ghost_l; [ exact HMti | exact HDp ]
      | reflexivity | exact Hwf | exact H0 | exact Hwfq
      | clear - HΨf; fsetdec ].
  - (* tophole_remove *)
    apply ad_pat_sub_gv_wrap_tophole.
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact HDp | exact Hrec | exact HΨf | exact HΨa
      | exact Hdisj | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq ].
  - (* flex_l *)
    eapply ad_pat_sub_gv_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact HDp | exact Hrec | exact HΨf | exact HΨa
      | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq ].
Qed.

(** [UnivGhostLG], leaf-valid. *)
Lemma ad_pat_sub_gv_ughost_lg_transport : forall Θb Ψr Rg' Rgt,
  uskl_precise Θb Ψr Rg' Rgt ->
  forall n Mg Θ' Ψfull Rg0 Qg Ψsup Ψn Ψna,
  Rgt = uskl_topholeg Rg0 ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  Mg <> mode_ti ->
  ad_pat_sub_gv n a_sub_mode_sk Mg Ψfull Θ' Rg0 Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' Rg0 ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     Ψfull [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
     ad_pat_sub_gv n a_sub_mode_sk Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
  ad_pat_sub_gv n a_sub_mode_sk Mg Ψn Θ' Rg' Qg.
Proof.
  intros Θb Ψr Rg' Rgt Hup; induction Hup;
    intros n Mg Θ' Ψfull Rg0 Qg Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf HMti HDp Hrec HΨf HΨa Hdisj Hftag Hwfq;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_gv_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ apply ad_pat_sub_gv__univ_ghost_lg; [ exact HMti | exact HDp ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* topholeg congruence *)
    inversion HeqR; subst.
    apply ad_pat_sub_gv__univ_ghost_lg; [ exact HMti | ].
    eapply Hrec with (Ψr0 := Ψrep) (Ψsup0 := Ψsup) (Ψna0 := Ψna);
      [ exact Hup | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj
      | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq ].
  - (* tophole_keepg: plain ∀◇ on the ghostier side *)
    inversion HeqR; subst.
    apply ad_pat_sub_gv__univ_ghost_l; [ exact HMti | ].
    eapply Hrec with (Ψr0 := Ψrep) (Ψsup0 := Ψsup) (Ψna0 := Ψna);
      [ exact Hup | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj
      | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq ].
  - (* hole *)
    subst R.
    eapply ad_pat_sub_gv_hole_intro with
      (n := n) (Ψfull := Ψfull) (R := uskl_topholeg Rg0);
      [ apply ad_pat_sub_gv__univ_ghost_lg; [ exact HMti | exact HDp ]
      | reflexivity | exact Hwf | exact H0 | exact Hwfq
      | clear - HΨf; fsetdec ].
  - (* tophole_remove *)
    apply ad_pat_sub_gv_wrap_tophole.
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact HDp | exact Hrec | exact HΨf | exact HΨa
      | exact Hdisj | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq ].
  - (* flex_l *)
    eapply ad_pat_sub_gv_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HMti | exact HDp | exact Hrec | exact HΨf | exact HΨa
      | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq ].
Qed.

(** [FlexMono], leaf-valid. *)
Lemma ad_pat_sub_gv_flex_mono_transport : forall Θb Ψr Rg' Rgv,
  uskl_precise Θb Ψr Rg' Rgv ->
  forall n NM Mg Θ' Ψfull αg τg Qg Ψsup Ψn Ψna,
  Rgv = uskl_var_f αg ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  binds αg (abind_flex_mono_def τg) Θ' ->
  ad_pat_sub_gv n NM (mode_fn Mg) Ψfull Θ' (ptyp_to_uskl_syn τg) Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' (ptyp_to_uskl_syn τg) ->
     {{ ⊢ Θb0 }}a ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     {{ ⊢ Θ' }}a ->
     Ψfull [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg'') ->
     ad_pat_sub_gv n NM (mode_fn Mg) Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Qg) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free Rg') ->
  ad_pat_sub_gv n NM (mode_fn Mg) Ψn Θ' Rg' Qg.
Proof.
  intros Θb Ψr Rg' Rgv Hup; induction Hup;
    intros n NM Mg Θ' Ψfull αg τg Qg Ψsup Ψn Ψna HeqR
      Hwfb HΨsup Hmon Hwf Hbnd HDp Hrec HΨf HΨa Hdisj Hftag Hwfq Hgf;
    try discriminate HeqR.
  - (* refl *)
    subst R.
    eapply ad_pat_sub_gv_refl_transport with
      (Ψsup := Ψsup) (Ψna := Ψna);
      [ eapply ad_pat_sub_gv__flex_mono; [ exact Hbnd | exact HDp ]
      | exact HΨf | exact HΨa | exact Hftag ].
  - (* hole *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + subst R.
      eapply ad_pat_sub_gv_hole_intro with
        (n := n) (Ψfull := Ψfull) (R := uskl_var_f αg);
        [ eapply ad_pat_sub_gv__flex_mono; [ exact Hbnd | exact HDp ]
        | reflexivity | exact Hwf | exact H0 | exact Hwfq
        | clear - HΨf; fsetdec ].
  - (* tophole_remove *)
    destruct NM.
    + exfalso. specialize (Hgf eq_refl). inversion Hgf.
    + apply ad_pat_sub_gv_wrap_tophole.
      eapply IHHup with (Ψna := Ψna);
        [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
        | exact Hbnd | exact HDp | exact Hrec | exact HΨf | exact HΨa
        | exact Hdisj | clear - Hftag; simpl in Hftag; fsetdec | exact Hwfq
        | intro He; discriminate He ].
  - (* flex_l: another defined variable on the ghostier side *)
    eapply ad_pat_sub_gv_fold_flex with (τ := τ);
      [ | reflexivity | apply Hmon; exact H | exact Hwf ].
    eapply IHHup with (Ψna := Ψna);
      [ exact HeqR | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact Hbnd | exact HDp | exact Hrec | exact HΨf | exact HΨa
      | exact Hdisj
      | pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq
      | intro He;
        apply mono_ptyp_to_uskl_syn_ghost_free;
        eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact H ] ].
  - (* flex_r: unfold to the definition — unique by wf *)
    inversion HeqR; subst.
    assert (Hb' : binds αg (abind_flex_mono_def τ) Θ')
      by (apply Hmon; exact H).
    assert (Hu : uniq Θ') by (apply a_wf_aenv_uniq; exact Hwf).
    pose proof (binds_unique _ _ _ _ _ Hb' Hbnd Hu) as He; inversion He; subst.
    eapply Hrec with (Ψr0 := Ψrep) (Ψsup0 := Ψsup) (Ψna0 := Ψna);
      [ exact Hup | exact Hwfb | exact HΨsup | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag | exact Hwfq
      | exact Hgf ].
Qed.

(* ===================================================================== *)
(*  P5c main — precision-substitution over the LEAF-VALID mirror          *)
(*  ([lemma:precision-substitution], subtyping-proofs.tex:1664, in the    *)
(*  form P7b's Sub-ForallL consumes: the join carries its leaf            *)
(*  refinements through the subject swap).                                *)
(* ===================================================================== *)

Lemma ad_pat_sub_precise_upre_gv : forall n NM M Ψfull Θ' Rg Q,
  ad_pat_sub_gv n NM M Ψfull Θ' Rg Q ->
  forall Θb Ψr Rg' Ψsup Ψn Ψna,
  uskl_precise Θb Ψr Rg' Rg ->
  {{ ⊢ Θb }}a ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free Rg') ->
  ad_pat_sub_gv n NM M Ψn Θ' Rg' Q.
Proof.
  intros n NM M Ψfull Θ' Rg Q HD; induction HD;
    intros Θb Ψr Rg' Ψsup Ψn Ψna Hup Hwfb HΨsup Hmon Hwf
      HΨf HΨa Hdisj Hftag Hwfq Hgf.
  - (* Infer *)
    apply ad_pat_sub_gv__infer;
      [ clear - H HΨf; fsetdec | | exact H1 | ].
    + pose proof (ad_pat_consis_precise_upre Hup HΨsup Hftag) as Ht.
      eapply Ht with (Ψna := empty);
        [ exact H0 | exact Hmon | exact Hwf
        | clear; fsetdec | clear; fsetdec | clear; fsetdec | exact Hwfq ].
    + eapply uskl_precise_erase_refine;
        [ exact H2 | exact Hwf
        | intros β Hβ; exfalso; clear - Hβ; fsetdec
        | exact Hwfq | exact Hup | exact Hmon | reflexivity ].
  - (* Check (TY) *)
    pose proof Hwfq as HwfB.
    rewrite bskl_to_pskl_pskl_to_bskl_inh in HwfB.
    apply ad_pat_sub_gv__check;
      [ eapply uskl_precise_guarded;
          [ exact Hup | exact Hwfb | exact H | apply Hgf; reflexivity ]
      | exact H0 | | ].
    + pose proof (ad_pat_consis_precise_upre Hup HΨsup Hftag) as Ht.
      eapply Ht with (Ψna := Ψna);
        [ exact H1 | exact Hmon | exact Hwf
        | exact HΨf | exact HΨa | exact Hdisj | exact Hwfq ].
    + eapply uskl_precise_erase_refine;
        [ exact H2 | exact Hwf
        | intros β Hβ; exfalso; clear - Hβ; fsetdec
        | exact HwfB | exact Hup | exact Hmon | reflexivity ].
  - (* ForallR (TY) *)
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_sub_gv__forall_r with (L := L `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (H0 α ltac:(clear - Hα; solve_notin_auto)) with (Ψna := Ψna);
      [ exact Hup | exact Hwfb | exact HΨsup
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec
      | exact Hgf ].
  - (* UnivGhostR (SK) *)
    assert (HΨe : Ψn [=] empty) by (clear - H HΨf; fsetdec).
    simpl in Hwfq. destruct (a_wf_pskl_tophole_inv Hwfq) as [HgP HwbP].
    eapply ad_pat_sub_gv_ughost_r_transport;
      [ exact Hup | exact Hwfb | exact HΨsup | exact Hftag
      | exact Hmon | exact Hwf | exact H0 | exact H3 | exact H4
      | exact H1 | exact H2 | exact HwbP | exact HΨe ].
  - (* Arrow *)
    eapply ad_pat_sub_gv_arrow_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact H0 | exact HD | exact H1
      | intros Θb0 Ψr0 Rg2' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag
      | exact Hwfq | exact Hgf ].
  - (* ForallL tagged *)
    eapply ad_pat_sub_gv_forall_l_tagged_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact H0 | exact H1 | exact H2 | exact H3
      | exact HD
      | intros Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag
      | exact Hwfq | exact Hgf ].
  - (* ForallL untagged *)
    eapply ad_pat_sub_gv_forall_l_untagged_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact H0 | exact H1 | exact H2 | exact H3
      | exact HD
      | intros Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag
      | exact Hwfq | exact Hgf ].
  - (* Ghost (SK) *)
    assert (HΨe : Ψn [=] empty) by (clear - H HΨf; fsetdec).
    eapply ad_pat_sub_gv_ghost_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact Hmon | exact Hwf
      | exact H0 | exact H1 | exact HΨe ].
  - (* GhostG (SK) *)
    assert (HΨe : Ψn [=] empty) by (clear - H HΨf; fsetdec).
    eapply ad_pat_sub_gv_ghostg_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact Hmon | exact Hwf
      | exact H0 | exact HΨe ].
  - (* UnivGhostL (SK) *)
    eapply ad_pat_sub_gv_ughost_l_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact HD
      | intros Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10
          | intro Habs; discriminate Habs ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag | exact Hwfq ].
  - (* UnivGhostLG (SK) *)
    eapply ad_pat_sub_gv_ughost_lg_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact HD
      | intros Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10
          | intro Habs; discriminate Habs ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag | exact Hwfq ].
  - (* FlexMono *)
    eapply ad_pat_sub_gv_flex_mono_transport;
      [ exact Hup | reflexivity | exact Hwfb | exact HΨsup | exact Hmon
      | exact Hwf | exact H | exact HD
      | intros Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11;
        eapply IHHD;
          [ exact h1 | exact h2 | exact h3 | exact h4 | exact h5
          | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 ]
      | exact HΨf | exact HΨa | exact Hdisj | exact Hftag
      | exact Hwfq | exact Hgf ].
Qed.

(* ===================================================================== *)
(*  §3 of HANDOFF-section-d — lemma:precision-sub (“Precision extends     *)
(*  skeleton subtyping”, proofs.tex) — a COROLLARY of P5c.                *)
(* ===================================================================== *)

(** ⭐ THE BRIDGE: the paper's precision [P' ⊑ P] — a refinement between the
    two INHERITED paintings — is a decorated subject-precision between the
    two UNRESOLVED paintings, with NO replaced tags.  Rows map one-to-one
    ([tophole_fill] is dead: an inh painting is never [bskl_all_syn]); the
    [__hole] row supplies [upre__hole]'s ∀-freeness by
    [inh_eq_syn_no_forall] — the fill being a SYN painting is exactly what
    confines the ghost's counterpart. *)
Lemma uskl_precise_of_ad_precise : forall Θ Δ Qs Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall P' P,
  Qs = pskl_to_bskl_inh P' ->
  Qt = pskl_to_bskl_inh P ->
  uskl_precise Θ empty (pskl_to_uskl P') (pskl_to_uskl P).
Proof.
  intros Θ Δ Qs Qt H; induction H; intros Hwf F' F HeqS HeqT.
  - (* unit *)
    destruct F' as [ | | | | | | ]; simpl in HeqS; try discriminate.
    destruct F as [ | | | | | | ]; simpl in HeqT; try discriminate.
    apply upre__refl; [ constructor | clear; fsetdec ].
  - (* var *)
    destruct F' as [ | | | | | | ]; simpl in HeqS; try discriminate.
    destruct F as [ | | | | | | ]; simpl in HeqT; try discriminate.
    inversion HeqS; inversion HeqT; subst.
    apply upre__refl; [ constructor | clear; fsetdec ].
  - (* arrow *)
    destruct F' as [ | | | Fa' Fb' | | | ]; simpl in HeqS; try discriminate.
    destruct F as [ | | | Fa Fb | | | ]; simpl in HeqT; try discriminate.
    inversion HeqS; inversion HeqT; subst. simpl.
    eapply upre__arrow;
      [ apply IHad_refine_syn1; solve [ exact Hwf | reflexivity ]
      | apply IHad_refine_syn2; solve [ exact Hwf | reflexivity ]
      | clear; fsetdec ].
  - (* all : both sides are ∀ⁱ paintings of ∀ˢ skeletons *)
    destruct F' as [ | | | | F0' | | ]; simpl in HeqS; try discriminate.
    destruct F as [ | | | | F0 | | ]; simpl in HeqT; try discriminate.
    inversion HeqS; inversion HeqT; subst. simpl.
    apply upre__all_syn with (L := L).
    intros α Hα.
    rewrite <- !pskl_to_uskl_open_var.
    apply (H0 α Hα Hwf);
      [ symmetry; apply pskl_to_bskl_inh_open
      | symmetry; apply pskl_to_bskl_inh_open ].
  - (* hole : the counterpart is a syn painting, hence ∀-free and wf *)
    destruct F' as [ | | | | | | ]; simpl in HeqS; try discriminate.
    simpl. apply upre__hole;
      [ clear; fsetdec
      | rewrite uskl_to_pskl_pskl_to_uskl;
        eapply inh_eq_syn_no_forall; symmetry; exact HeqT
      | ].
    rewrite uskl_to_pskl_pskl_to_uskl.
    replace F with (bskl_to_pskl (pskl_to_bskl_syn P));
      [ | rewrite HeqT; apply bskl_to_pskl_pskl_to_bskl_inh ].
    rewrite bskl_to_pskl_pskl_to_bskl_syn. exact H.
  - (* tophole_remove *)
    destruct F' as [ | | | | | | F0' ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst. simpl.
    apply upre__tophole_remove. apply IHad_refine_syn; auto.
  - (* tophole_fill : an inh painting is never [bskl_all_syn] — dead *)
    destruct F as [ | | | | F0 | | ]; simpl in HeqT; discriminate.
  - (* tophole_keep *)
    destruct F' as [ | | | | | | F0' ]; simpl in HeqS; try discriminate.
    destruct F as [ | | | | | | F0 ]; simpl in HeqT; try discriminate.
    inversion HeqS; inversion HeqT; subst. simpl.
    apply upre__tophole.
    apply IHad_refine_syn; [ exact Hwf | reflexivity | reflexivity ].
  - (* flex_l : a definition is a MONOTYPE, so its two paintings agree *)
    destruct F' as [ | | α0 | | | | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | eassumption ]).
    simpl. eapply upre__flex_l; [ eassumption | ].
    rewrite <- pskl_to_uskl_ptyp.
    apply IHad_refine_syn;
      first [ exact Hwf | reflexivity
            | symmetry; apply mono_inh_eq_syn; exact Hm ].
  - (* flex_r *)
    destruct F as [ | | α0 | | | | ]; simpl in HeqT; try discriminate.
    inversion HeqT; subst.
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | eassumption ]).
    simpl. eapply upre__flex_r; [ eassumption | ].
    rewrite <- pskl_to_uskl_ptyp.
    apply IHad_refine_syn;
      first [ exact Hwf | reflexivity
            | symmetry; apply mono_inh_eq_syn; exact Hm ].
Qed.

(** ⭐⭐ lemma:precision-sub (proofs.tex, "Precision extends skeleton
    subtyping"), over the LEAF-VALID join and at BOTH sorts, FUEL PRESERVED
    — a corollary of P5c's precision-substitution
    [ad_pat_sub_precise_upre_gv] at [Ψrep = Ψsup = Ψna = ∅].  The wf of the
    counterpart's erasure is the paper's EXTERNAL wf side condition
    (WF-SIDE-CONDITIONS.md); the TY ghost-freeness is the motive's usual
    external condition, automatic for a painting of a TYPE. *)
Lemma ad_precise_extends_pat_sub_gv : forall n NM M Ψ Θ Δ P' P Q,
  {{ Θ ⨟ Δ ⊢ₚᵣ P' ⊑ P }}ad ->
  ad_pat_sub_gv n NM M Ψ Θ (pskl_to_uskl P) Q ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free (pskl_to_uskl P')) ->
  ad_pat_sub_gv n NM M Ψ Θ (pskl_to_uskl P') Q.
Proof.
  intros n NM M Ψ Θ Δ P' P Q Hprec HD Hwf HwfQ Hgf.
  eapply ad_pat_sub_precise_upre_gv with
    (Θb := Θ) (Ψr := empty) (Ψsup := empty) (Ψna := empty);
    [ exact HD
    | eapply uskl_precise_of_ad_precise;
        [ exact Hprec | exact Hwf | reflexivity | reflexivity ]
    | exact Hwf
    | clear; fsetdec
    | intros x b Hb; exact Hb
    | exact Hwf
    | clear; fsetdec
    | clear; fsetdec
    | clear; fsetdec
    | clear; fsetdec
    | exact HwfQ
    | exact Hgf ].
Qed.

(** The fuel-forgotten form the [ad_ctx_precise_pat] Var row consumes. *)
Lemma ad_precise_extends_pat_sub_v : forall NM M Ψ Θ Δ P' P Q,
  {{ Θ ⨟ Δ ⊢ₚᵣ P' ⊑ P }}ad ->
  ad_pat_sub_v NM M Ψ Θ (pskl_to_uskl P) Q ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free (pskl_to_uskl P')) ->
  ad_pat_sub_v NM M Ψ Θ (pskl_to_uskl P') Q.
Proof.
  intros NM M Ψ Θ Δ P' P Q Hprec [n HD] Hwf HwfQ Hgf.
  exists n. eapply ad_precise_extends_pat_sub_gv; eassumption.
Qed.
