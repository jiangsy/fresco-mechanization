(** COMPLETENESS + OPTIMALITY OF ALGORITHMIC SUBTYPING.

    Paper: [thm:complete-subtyping] (algorithmic.tex:1446); proofs
    subtyping-proofs.tex:1526-3536.  Plan: docs/DESIGN-completeness-subtyping.md.

    This file builds bottom-up.  P5a (this commit): the fuel-indexed
    measure [ad_pat_sub_n] (def in def_decl_algo_sub.v) and its bridges to
    the plain [ad_pat_sub] — [of_n] / [to_n] / [n_mono] — plus the
    fuel-preserving tvar-rename [ad_pat_sub_n_rename_tvar] that [to_n]'s
    binder cases need for the ∀α∃n → ∃n∀α swap. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_consis_precise.

Set Implicit Arguments.

(* ===================================================================== *)
(*  P5a — the fuel measure and its bridges to plain [ad_pat_sub].          *)
(* ===================================================================== *)

(** Erase the fuel: a fuel-indexed derivation IS a plain one. *)
Lemma ad_pat_sub_of_n : forall n NM M Ψ Θ R Q,
  ad_pat_sub_n n NM M Ψ Θ R Q ->
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q.
Proof.
  intros n NM M Ψ Θ R Q H. induction H.
  - eapply ad_pat_sub__infer; eauto.
  - eapply ad_pat_sub__check; eauto.
  - eapply ad_pat_sub__forall_r; eauto.
  - eapply ad_pat_sub__univ_ghost_r; eauto.
  - eapply ad_pat_sub__arrow; eauto.
  - eapply ad_pat_sub__forall_l_tagged; eauto.
  - eapply ad_pat_sub__forall_l_untagged; eauto.
  - eapply ad_pat_sub__ghost; eauto.
  - eapply ad_pat_sub__ghostg; eauto.
  - eapply ad_pat_sub__univ_ghost_l; eauto.
  - eapply ad_pat_sub__univ_ghost_lg; eauto.
  - eapply ad_pat_sub__flex_mono; eauto.
Qed.

(** One extra unit of fuel is harmless.  Each rule concludes at [S n] from
    a recursive premise at [n]; bumping the conclusion to [S (S n)] just
    applies the same constructor with its premise supplied by the IH (now
    at [S n]). *)
Lemma ad_pat_sub_n_succ : forall n NM M Ψ Θ R Q,
  ad_pat_sub_n n NM M Ψ Θ R Q ->
  ad_pat_sub_n (S n) NM M Ψ Θ R Q.
Proof.
  intros n NM M Ψ Θ R Q H. induction H.
  - eapply ad_pat_sub_n__infer; eauto.
  - eapply ad_pat_sub_n__check; eauto.
  - eapply ad_pat_sub_n__forall_r with (L := L); eauto.
  - eapply ad_pat_sub_n__univ_ghost_r; eauto.
  - eapply ad_pat_sub_n__arrow; eauto.
  - eapply ad_pat_sub_n__forall_l_tagged; eauto.
  - eapply ad_pat_sub_n__forall_l_untagged; eauto.
  - eapply ad_pat_sub_n__ghost; eauto.
  - eapply ad_pat_sub_n__ghostg; eauto.
  - eapply ad_pat_sub_n__univ_ghost_l; eauto.
  - eapply ad_pat_sub_n__univ_ghost_lg; eauto.
  - eapply ad_pat_sub_n__flex_mono; eauto.
Qed.

(** Fuel weakening: more fuel than needed is harmless. *)
Lemma ad_pat_sub_n_mono : forall n NM M Ψ Θ R Q,
  ad_pat_sub_n n NM M Ψ Θ R Q ->
  forall m, n <= m ->
  ad_pat_sub_n m NM M Ψ Θ R Q.
Proof.
  intros n NM M Ψ Θ R Q H m Hle.
  induction Hle; [ assumption | ].
  apply ad_pat_sub_n_succ; assumption.
Qed.

(** Renaming the opened rigid binder in [ad_pat_sub_n] — the fuel-preserving
    mirror of [ad_pat_sub_rename_tvar] (prop_pat_sub.v).  The fuel [n] rides
    along inertly; [to_n]'s binder cases use it to turn the cofinite family
    [∀α∉L, ∃n, …] into [∃n, ∀α∉L, …]. *)
Lemma ad_pat_sub_n_rename_tvar : forall n NM M Ψ Θ1 α Θ0 R Q β',
  ad_pat_sub_n n NM M Ψ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) R Q ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_pat_sub_n n NM M Ψ (Θ1 ++ (β' ~ abind_tvar) ++ Θ0)
      (subst_bskl_in_uskl (uskl_var_f β') α R)
      (subst_bskl_in_bskl (bskl_var_f β') α Q).
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hdom Hdefs; simpl.
  - apply ad_pat_sub_n__infer; auto.
    + apply ad_pat_consis_rename_tvar; auto.
    + change (bskl_var_f β') with (ptyp_to_bskl_syn (ptyp_var_f β')).
      apply is_sskl_subst_mono; auto using mono_ptyp.
  - rewrite subst_var_bskl_inh.
    apply ad_pat_sub_n__check.
    + change (uskl_var_f β') with (ptyp_to_uskl_syn (ptyp_var_f β')).
      apply guarded_uskl_subst_mono; auto using mono_ptyp.
    + apply guarded_pskl_subst; auto using guarded_pskl__var, lc_pskl_var_f.
    + rewrite <- subst_var_bskl_inh.
      apply ad_pat_consis_rename_tvar; auto.
  - apply ad_pat_sub_n__forall_r with (L := L `union` singleton α).
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : X `notin` L) by fsetdec.
    apply (H0 X HXL ((X ~ abind_tvar) ++ Θ1));
      [ simpl_env; reflexivity
      | simpl; repeat rewrite dom_app in *; fsetdec
      | intros β τ Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | eauto ] ].
  - apply ad_pat_sub_n__univ_ghost_r; auto.
    + change (uskl_var_f β') with (ptyp_to_uskl_syn (ptyp_var_f β')).
      apply guarded_uskl_subst_mono; auto using mono_ptyp.
    + change (bskl_var_f β') with (ptyp_to_bskl_syn (ptyp_var_f β')).
      apply guarded_bskl_subst_mono; auto using mono_ptyp.
    + change (bskl_var_f β') with (ptyp_to_bskl_syn (ptyp_var_f β')).
      apply is_sskl_subst_mono; auto using mono_ptyp.
    + apply ad_pat_consis_rename_tvar; auto.
  - specialize (IHad_pat_sub_n Θ1 ltac:(reflexivity) Hdom Hdefs).
    eapply ad_pat_sub_n__arrow.
    + eapply ad_pat_consis_rename_tvar; eauto.
    + exact IHad_pat_sub_n.
    + eassumption.
  - specialize (IHad_pat_sub_n Θ1 ltac:(reflexivity) Hdom Hdefs).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl in IHad_pat_sub_n;
      [ | apply lc_uskl_var_f ].
    eapply ad_pat_sub_n__forall_l_tagged.
    5: exact IHad_pat_sub_n.
    + assumption.
    + eassumption.
    + change (uskl_var_f β') with (ptyp_to_uskl_syn (ptyp_var_f β')).
      apply a_tags_sort_subst_mono;
        [ assumption | apply mono_ptyp__var ].
    + change (uskl_var_f β') with (ptyp_to_uskl_syn (ptyp_var_f β')).
      rewrite uskl_to_pskl_subst_mono. simpl.
      apply a_wf_pskl_rename_tvar;
        first [ assumption | clear; fsetdec ].
  - specialize (IHad_pat_sub_n Θ1 ltac:(reflexivity) Hdom Hdefs).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl in IHad_pat_sub_n;
      [ | apply lc_uskl_var_f ].
    eapply ad_pat_sub_n__forall_l_untagged.
    5: exact IHad_pat_sub_n.
    + assumption.
    + eassumption.
    + change (uskl_var_f β') with (ptyp_to_uskl_syn (ptyp_var_f β')).
      apply a_tags_sort_subst_mono;
        [ assumption | apply mono_ptyp__var ].
    + change (uskl_var_f β') with (ptyp_to_uskl_syn (ptyp_var_f β')).
      rewrite uskl_to_pskl_subst_mono. simpl.
      apply a_wf_pskl_rename_tvar;
        first [ assumption | clear; fsetdec ].
  - rewrite subst_var_bskl_inh.
    apply ad_pat_sub_n__ghost; auto.
    + apply a_wf_pskl_rename_tvar; [ assumption | clear; fsetdec ].
    + rewrite <- subst_var_bskl_inh.
      change (bskl_var_f β') with (ptyp_to_bskl_syn (ptyp_var_f β')).
      apply mod_comp_sk_subst_mono; auto using mono_ptyp.
  - apply ad_pat_sub_n__ghostg; auto.
  - apply ad_pat_sub_n__univ_ghost_l; auto.
  - apply ad_pat_sub_n__univ_ghost_lg; auto.
  - destruct_if as [-> | Hne].
    + exfalso.
      match goal with
      | Hb : binds _ (abind_flex_mono_def _) _ |- _ =>
          unfold binds in Hb; apply in_app_or in Hb;
          destruct Hb as [Hb | Hb];
          [ apply binds_In in Hb; simpl_env in *; fsetdec | ];
          apply in_app_or in Hb; destruct Hb as [Hb | Hb];
          [ destruct Hb as [Heq | Habs]; [ inversion Heq | inversion Habs ]
          | apply binds_In in Hb; simpl_env in *; fsetdec ]
      end.
    + match goal with
      | Hb0 : binds ?a (abind_flex_mono_def _) (_ ++ _ ++ _) |- _ =>
          assert (Hb' : binds a (abind_flex_mono_def τ) (Θ1 ++ Θ0))
            by (eapply binds_strip_mid;
                [ exact Hb0 | intro He; inversion He ])
      end.
      eapply ad_pat_sub_n__flex_mono.
      { unfold binds in Hb' |- *. apply in_app_or in Hb'.
        apply in_or_app.
        destruct Hb' as [Hb' | Hb'];
          [ left; exact Hb' | right; simpl; right; exact Hb' ]. }
      specialize (IHad_pat_sub_n Θ1 ltac:(reflexivity) Hdom Hdefs).
      rewrite subst_bskl_in_uskl_fresh_eq in IHad_pat_sub_n;
        [ exact IHad_pat_sub_n | ].
      rewrite ftvar_in_uskl_ptyp_syn. eauto.
Qed.

(** Every plain derivation has some fuel.  Binder cases pick a fresh
    witness, read off its fuel, and transport that same fuel to every
    other opening via [ad_pat_sub_n_rename_tvar]. *)
Lemma ad_pat_sub_to_n : forall NM M Ψ Θ R Q,
  a_wf_aenv Θ ->
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q ->
  exists n, ad_pat_sub_n n NM M Ψ Θ R Q.
Proof.
  intros NM M Ψ Θ R Q Hwf H. revert Hwf. induction H; intros Hwf.
  - exists 1. eapply ad_pat_sub_n__infer; eauto.
  - exists 1. eapply ad_pat_sub_n__check; eauto.
  - (* forall_r — pick a fresh witness, read off its fuel, transport by rename *)
    pick fresh α0 for
      (L `union` dom Θ `union` ftvar_in_uskl T `union` ftvar_in_bskl B).
    assert (Hwf0 : a_wf_aenv ((α0 ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    destruct (H0 α0 ltac:(fsetdec) Hwf0) as [n0 Hn0].
    exists (S n0).
    eapply ad_pat_sub_n__forall_r with
      (L := L `union` dom Θ `union` ftvar_in_uskl T
            `union` ftvar_in_bskl B `union` singleton α0).
    intros X HX.
    rewrite (subst_bskl_in_bskl_intro α0);
      [ | clear - Fr; fsetdec ].
    rewrite <- (subst_bskl_in_uskl_fresh_eq T (uskl_var_f X) α0);
      [ | clear - Fr; fsetdec ].
    replace ((X ~ abind_tvar) ++ Θ)
       with (nil ++ (X ~ abind_tvar) ++ Θ) by (simpl_env; reflexivity).
    apply ad_pat_sub_n_rename_tvar.
    + simpl_env. exact Hn0.
    + simpl_env. clear - Fr; fsetdec.
    + intros β τ Hb. simpl_env in Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; [ exact Hwf | exact Hb ]).
      clear - Fr Hsc; fsetdec.
  - exists 1. eapply ad_pat_sub_n__univ_ghost_r; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__arrow; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__forall_l_tagged; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__forall_l_untagged; eauto.
  - exists 1. eapply ad_pat_sub_n__ghost; eauto.
  - exists 1. eapply ad_pat_sub_n__ghostg; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__univ_ghost_l; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__univ_ghost_lg; eauto.
  - destruct (IHad_pat_sub Hwf) as [n Hn].
    exists (S n). eapply ad_pat_sub_n__flex_mono; eauto.
Qed.

(* ===================================================================== *)
(*  P5b — partial-precision-complete + precision-substitution.            *)
(*  See docs/DESIGN-completeness-subtyping.md §5.1 for the case-plan.     *)
(* ===================================================================== *)

(** The solved tag context of partial precision is contained in [ψ]'s tags —
    the invariant that makes the [tophole_fill] case of partial-precision-
    complete vacuous. *)
Lemma ad_partial_precise_tags_sub : forall Θ Δ Ψ P ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Ψt, d_tags_skl Ψt ψ -> Ψ [<=] Ψt.
Proof.
  intros Θ Δ Ψ P ψ Hwf H. induction H; intros Ψt Hdt.
  - apply d_tags_skl_unit_inv in Hdt. fsetdec.
  - apply d_tags_skl_var_inv in Hdt. fsetdec.
  - apply d_tags_skl_arrow_inv in Hdt as [Ψt1 [Ψt2 [Hd1 [Hd2 [_ Heqt]]]]].
    specialize (IHad_partial_precise1 Hwf _ Hd1).
    specialize (IHad_partial_precise2 Hwf _ Hd2).
    fsetdec.
  - apply d_tags_skl_all_etag_inv in Hdt as [L0 [Ψt0 [Hd0 [Hεt Heqt]]]].
    pick fresh X for (L `union` L0).
    specialize (H0 X ltac:(fsetdec) Hwf _ (Hd0 X ltac:(fsetdec))).
    fsetdec.
  - fsetdec.
  - eapply IHad_partial_precise; eauto.
  - (* tophole_fill: the recursive premise keeps Ψ but drops the ε tag;
       here the sub-derivation extends Θ with the rigid X *)
    apply d_tags_skl_all_etag_inv in Hdt as [L0 [Ψt0 [Hd0 [Hεt Heqt]]]].
    pick fresh X for (L `union` L0 `union` dom Θ).
    assert (Hwf' : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    specialize (H0 X ltac:(fsetdec) Hwf' _ (Hd0 X ltac:(fsetdec))).
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
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ ψ ->
  Θ ⨟ Δ ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ ⌊ ψ ⌋ˢ.
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
  - (* forall: ψ = all_etag ε ψ0, P = all_syn P0 *)
    apply a_tags_sort_all_etag_inv in Htags as [Lt [Ψt [Hta [Hεt Hun]]]].
    apply a_wf_pskl_all_inv in Hwfp as [Lw Hwbody].
    apply ad_refine_syn__all with (L := L `union` Lt `union` Lw `union` dom Θ
       `union` ftvar_in_pskl P `union` ftvar_in_uskl ψ).
    intros X HX.
    assert (Hs0 : Ψ0 [<=] Ψt) by
      (eapply (ad_partial_precise_tags_sub Hwf (H X ltac:(fsetdec)));
        exact (a_tags_sort_d_tags (Hta X ltac:(fsetdec)))).
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
    apply a_tags_sort_all_etag_inv in Htags as [Lt [Ψt [Hta [Hεt Hun]]]].
    pick fresh X for (L `union` Lt `union` dom Θ).
    assert (Hwf' : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (Hsub : Ψ [<=] Ψt) by
      (eapply (ad_partial_precise_tags_sub Hwf' (H X ltac:(fsetdec)));
        exact (a_tags_sort_d_tags (Hta X ltac:(fsetdec)))).
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
      * intros X HX. right.
        eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfτ | exact HX ].
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
(*  [ad_pat_sub_g] (def_decl_algo_sub_hyg.v; DESIGN §5.4).                 *)
(* ===================================================================== *)

(** Erase hygiene + fuel: a hygienic derivation is a plain one. *)
Lemma ad_pat_sub_g_of : forall n NM M Ψ Θ R Q,
  ad_pat_sub_g n NM M Ψ Θ R Q ->
  Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q.
Proof.
  intros n NM M Ψ Θ R Q H. induction H.
  - eapply ad_pat_sub__infer; eauto.
  - eapply ad_pat_sub__check; eauto.
  - eapply ad_pat_sub__forall_r; eauto.
  - eapply ad_pat_sub__univ_ghost_r; eauto.
  - eapply ad_pat_sub__arrow; eauto.
  - eapply ad_pat_sub__forall_l_tagged; eauto.
  - eapply ad_pat_sub__forall_l_untagged; eauto.
  - eapply ad_pat_sub__ghost; eauto.
  - eapply ad_pat_sub__ghostg; eauto.
  - eapply ad_pat_sub__univ_ghost_l; eauto.
  - eapply ad_pat_sub__univ_ghost_lg; eauto.
  - eapply ad_pat_sub__flex_mono; eauto.
Qed.

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
    pose proof (H0 α ltac:(clear - Fr; fsetdec)) as Hα.
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
    pose proof (ftag_in_uskl_ptyp_syn τ) as Hpt.
    clear - Hpt IHad_pat_sub_g; fsetdec.
Qed.

(** Wrap a ⊤◇ over an SK subject at the SAME fuel — [UnivGhostL] is
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
  a_wf_aenv Θ ->
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
    eapply (H0 β ltac:(clear - Hβ; fsetdec) α0 τ0 HeqS);
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
  a_wf_aenv Θ ->
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
  a_wf_aenv Θ' ->
  pskl_no_forall (uskl_to_pskl R) ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
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

(** Ghost-freeness is closed under substituting a ghost-free skeleton. *)
Lemma uskl_ghost_free_subst : forall R ψ α,
  uskl_ghost_free R ->
  uskl_ghost_free ψ ->
  lc_uskl ψ ->
  uskl_ghost_free (subst_bskl_in_uskl ψ α R).
Proof.
  intros R ψ α HS; revert α; induction HS; intros X0 Hψ Hlc; simpl.
  - apply uskl_ghost_free__unit.
  - destruct_if as [-> | Hne]; [ exact Hψ | apply uskl_ghost_free__var ].
  - apply uskl_ghost_free__arrow; [ apply IHHS1 | apply IHHS2 ]; assumption.
  - apply uskl_ghost_free__all_etag with (L := L `union` singleton X0).
    intros Y HY.
    assert (HYX : X0 <> Y) by (clear - HY; fsetdec).
    rewrite (subst_bskl_in_uskl_open_uskl_wrt_uskl_var S ψ X0 Y HYX Hlc).
    apply H0; [ clear - HY; fsetdec | assumption | assumption ].
  - apply uskl_ghost_free__all_syn with (L := L `union` singleton X0).
    intros Y HY.
    assert (HYX : X0 <> Y) by (clear - HY; fsetdec).
    rewrite (subst_bskl_in_uskl_open_uskl_wrt_uskl_var S ψ X0 Y HYX Hlc).
    apply H0; [ clear - HY; fsetdec | assumption | assumption ].
Qed.

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
    UnivGhostR reconstructions; the ghostier side must not grow a ⊤◇ or
    hole head, which [uskl_ghost_free]—TY—or the case analysis—SK refl /
    congruence roots—supplies). *)
Lemma uskl_precise_guarded : forall Θb Ψrep R' R,
  uskl_precise Θb Ψrep R' R ->
  a_wf_aenv Θb ->
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
(*  with the rule's data as named arguments (the ⊤◇/flex peels recurse on  *)
(*  the smaller ⊑ᵤ; congruence roots rebuild the rule).                    *)
(* ===================================================================== *)

(** [UnivGhostR]: guarded SK subject against a ⊤◇-target. *)
Lemma ad_pat_sub_g_ughost_r_transport : forall Θb Ψrep R' R,
  uskl_precise Θb Ψrep R' R ->
  forall Ψsup n Θ' Ψn Q,
  a_wf_aenv Θb ->
  Ψrep [<=] Ψsup ->
  Ψsup ∩ ftag_in_uskl R' [=] empty ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  a_wf_aenv Θ' ->
  guarded_uskl R ->
  empty ⨟ Θ' ⊢ₛᵃ R ∼ Q ->
  guarded_bskl Q ->
  is_sskl Q ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
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
  - (* all_etag cong *) inversion Hgd.
  - (* all_inst *) inversion Hgd.
  - (* tophole cong *) inversion Hgd.
  - (* topholeg cong *) inversion Hgd.
  - (* tophole_keepg *) inversion Hgd.
  - (* hole: replace by □ via Ghost against the ⊤◇-target *)
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
      | pose proof (ftag_in_uskl_ptyp_syn τ) as Hpt; clear - Hpt; fsetdec
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
  a_wf_aenv Θb ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  a_wf_aenv Θ' ->
  Θ' ⨟ empty ⊢ₚₛᵃ P ->
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
  a_wf_aenv Θb ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  a_wf_aenv Θ' ->
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
  a_wf_aenv Θb ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  a_wf_aenv Θ' ->
  Ψc1 ⨟ Θ' ⊢ₛᵃ Rg1 ∼ Qg1 ->
  ad_pat_sub_g n NM Mg Ψc2 Θ' Rg2 Qg2 ->
  Ψfull [=] Ψc1 `union` Ψc2 ->
  (forall Θb0 Ψr0 Rg2' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg2' Rg2 ->
     a_wf_aenv Θb0 ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     a_wf_aenv Θ' ->
     Ψc2 [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg2' [=] empty ->
     Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qg2) ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg2') ->
     ad_pat_sub_g n NM Mg Ψn0 Θ' Rg2' Qg2) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl (bskl_arrow Qg1 Qg2)) ->
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
      | pose proof (ftag_in_uskl_ptyp_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq
      | intro He;
        apply mono_ptyp_to_uskl_syn_ghost_free;
        eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact H ] ].
Qed.

(** Cofinite inversions of ghost-freeness at the two quantifier heads. *)
Lemma uskl_ghost_free_all_etag_inv : forall ε R,
  uskl_ghost_free (uskl_all_etag ε R) ->
  exists L0, forall X, X `notin` L0 ->
    uskl_ghost_free (open_uskl_wrt_uskl R (uskl_var_f X)).
Proof. intros ε R Hg. inversion Hg; subst. eauto. Qed.

Lemma uskl_ghost_free_all_syn_inv : forall R,
  uskl_ghost_free (uskl_all_syn R) ->
  exists L0, forall X, X `notin` L0 ->
    uskl_ghost_free (open_uskl_wrt_uskl R (uskl_var_f X)).
Proof. intros R Hg. inversion Hg; subst. eauto. Qed.

(** [ForallL] (tagged): the precision-substitution crux.  The congruence /
    instantiation roots rebuild ForallL with the SAME instantiation [ψg],
    transporting the body-⊑ᵤ under [ψg/X] by [uskl_precise_subst]; the
    recursive call shrinks [Ψsup] by the instantiation's tags [Ψi'] (the
    node's hygiene premise keeps everything disjoint). *)
Lemma ad_pat_sub_g_forall_l_tagged_transport : forall Θb Ψr Rg' Rgall,
  uskl_precise Θb Ψr Rg' Rgall ->
  forall n NM Mg Θ' Ψfull Ψi' εg Rg0 ψg Qg Ψsup Ψn Ψna,
  Rgall = uskl_all_etag εg Rg0 ->
  a_wf_aenv Θb ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  a_wf_aenv Θ' ->
  Mg <> mode_ti ->
  Ψi' ∩ Ψfull [=] empty ->
  Ψi' ∩ (ftag_in_uskl (uskl_all_etag εg Rg0)) [=] empty ->
  a_tags_sort NM Ψi' ψg ->
  Θ' ⨟ empty ⊢ₚₛᵃ ⌊ ψg ⌋ˢ ->
  ad_pat_sub_g n NM Mg (Ψfull `union` Ψi') Θ' (open_uskl_wrt_uskl Rg0 ψg) Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' (open_uskl_wrt_uskl Rg0 ψg) ->
     a_wf_aenv Θb0 ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     a_wf_aenv Θ' ->
     (Ψfull `union` Ψi') [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qg) ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg'') ->
     ad_pat_sub_g n NM Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qg) ->
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
  - (* all_etag congruence: rebuild ForallL-tagged with ψg *)
    inversion HeqR; subst.
    assert (Hlcψ : lc_uskl ψg)
      by (apply is_tskl_lc; inversion Htags; subst; assumption).
    pick fresh X for (L `union` dom Θb
        `union` ftvar_in_uskl R' `union` ftvar_in_uskl Rg0).
    pose proof (H X ltac:(clear - Fr; fsetdec)) as Hbody.
    assert (Hsub : uskl_precise Θb Ψrep
        (open_uskl_wrt_uskl R' ψg) (open_uskl_wrt_uskl Rg0 ψg)).
    { rewrite (subst_bskl_in_uskl_intro X R' ψg ltac:(clear - Fr; fsetdec)).
      rewrite (subst_bskl_in_uskl_intro X Rg0 ψg ltac:(clear - Fr; fsetdec)).
      apply uskl_precise_subst;
        [ exact Hbody | exact Hlcψ | exact Hwfb | clear - Fr; fsetdec ]. }
    pose proof (uskl_precise_ftag_sub Hbody) as Hfsb.
    pose proof (uskl_precise_ftag_rep Hbody) as Hfrb.
    pose proof (ftag_in_uskl_open_var R' X) as Hov1.
    pose proof (ftag_in_uskl_open_var Rg0 X) as Hov2.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Htgψ.
    assert (Hgfψ : NM = a_sub_mode_ty -> uskl_ghost_free ψg)
      by (intro He; inversion Htags; subst;
          [ congruence | assumption ]).
    assert (Hgfo : NM = a_sub_mode_ty ->
                   uskl_ghost_free (open_uskl_wrt_uskl R' ψg)).
    { intro He.
      destruct (uskl_ghost_free_all_etag_inv (Hgf He)) as [Lg Hgb].
      pick fresh Y for (Lg `union` ftvar_in_uskl R').
      rewrite (subst_bskl_in_uskl_intro Y R' ψg
                 ltac:(clear - Fr0; fsetdec)).
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
    pick fresh X for (L `union` dom Θb
        `union` ftvar_in_uskl R' `union` ftvar_in_uskl Rg0).
    pose proof (H X ltac:(clear - Fr; fsetdec)) as Hbody.
    assert (Hsub : uskl_precise Θb Ψ0
        (open_uskl_wrt_uskl R' ψg) (open_uskl_wrt_uskl Rg0 ψg)).
    { rewrite (subst_bskl_in_uskl_intro X R' ψg ltac:(clear - Fr; fsetdec)).
      rewrite (subst_bskl_in_uskl_intro X Rg0 ψg ltac:(clear - Fr; fsetdec)).
      apply uskl_precise_subst;
        [ exact Hbody | exact Hlcψ | exact Hwfb | clear - Fr; fsetdec ]. }
    pose proof (uskl_precise_ftag_sub Hbody) as Hfsb.
    pose proof (uskl_precise_ftag_rep Hbody) as Hfrb.
    pose proof (ftag_in_uskl_open_var R' X) as Hov1.
    pose proof (ftag_in_uskl_open_var Rg0 X) as Hov2.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Htgψ.
    assert (Hgfψ : NM = a_sub_mode_ty -> uskl_ghost_free ψg)
      by (intro He; inversion Htags; subst;
          [ congruence | assumption ]).
    assert (Hgfo : NM = a_sub_mode_ty ->
                   uskl_ghost_free (open_uskl_wrt_uskl R' ψg)).
    { intro He.
      destruct (uskl_ghost_free_all_syn_inv (Hgf He)) as [Lg Hgb].
      pick fresh Y for (Lg `union` ftvar_in_uskl R').
      rewrite (subst_bskl_in_uskl_intro Y R' ψg
                 ltac:(clear - Fr0; fsetdec)).
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
  - (* hole: no_forall of an all_etag erasure is absurd *)
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
      | pose proof (ftag_in_uskl_ptyp_syn τ) as Hpt; clear - Hpt; fsetdec
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
  a_wf_aenv Θb ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  a_wf_aenv Θ' ->
  Mg <> mode_ti ->
  Ψi' ∩ Ψfull [=] empty ->
  Ψi' ∩ (ftag_in_uskl (uskl_all_syn Rg0)) [=] empty ->
  a_tags_sort NM Ψi' ψg ->
  Θ' ⨟ empty ⊢ₚₛᵃ ⌊ ψg ⌋ˢ ->
  ad_pat_sub_g n NM Mg (Ψfull `union` Ψi') Θ' (open_uskl_wrt_uskl Rg0 ψg) Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' (open_uskl_wrt_uskl Rg0 ψg) ->
     a_wf_aenv Θb0 ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     a_wf_aenv Θ' ->
     (Ψfull `union` Ψi') [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qg) ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg'') ->
     ad_pat_sub_g n NM Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qg) ->
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
    pick fresh X for (L `union` dom Θb
        `union` ftvar_in_uskl R' `union` ftvar_in_uskl Rg0).
    pose proof (H X ltac:(clear - Fr; fsetdec)) as Hbody.
    assert (Hsub : uskl_precise Θb Ψrep
        (open_uskl_wrt_uskl R' ψg) (open_uskl_wrt_uskl Rg0 ψg)).
    { rewrite (subst_bskl_in_uskl_intro X R' ψg ltac:(clear - Fr; fsetdec)).
      rewrite (subst_bskl_in_uskl_intro X Rg0 ψg ltac:(clear - Fr; fsetdec)).
      apply uskl_precise_subst;
        [ exact Hbody | exact Hlcψ | exact Hwfb | clear - Fr; fsetdec ]. }
    pose proof (uskl_precise_ftag_sub Hbody) as Hfsb.
    pose proof (uskl_precise_ftag_rep Hbody) as Hfrb.
    pose proof (ftag_in_uskl_open_var R' X) as Hov1.
    pose proof (ftag_in_uskl_open_var Rg0 X) as Hov2.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Htgψ.
    assert (Hgfψ : NM = a_sub_mode_ty -> uskl_ghost_free ψg)
      by (intro He; inversion Htags; subst;
          [ congruence | assumption ]).
    assert (Hgfo : NM = a_sub_mode_ty ->
                   uskl_ghost_free (open_uskl_wrt_uskl R' ψg)).
    { intro He.
      destruct (uskl_ghost_free_all_syn_inv (Hgf He)) as [Lg Hgb].
      pick fresh Y for (Lg `union` ftvar_in_uskl R').
      rewrite (subst_bskl_in_uskl_intro Y R' ψg
                 ltac:(clear - Fr0; fsetdec)).
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
      | pose proof (ftag_in_uskl_ptyp_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq
      | intro He;
        apply mono_ptyp_to_uskl_syn_ghost_free;
        eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact H ] ].
Qed.

(** [UnivGhostL]: ⊤◇-subject, SK, non-incrementing. *)
Lemma ad_pat_sub_g_ughost_l_transport : forall Θb Ψr Rg' Rgt,
  uskl_precise Θb Ψr Rg' Rgt ->
  forall n Mg Θ' Ψfull Rg0 Qg Ψsup Ψn Ψna,
  Rgt = uskl_tophole Rg0 ->
  a_wf_aenv Θb ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  a_wf_aenv Θ' ->
  Mg <> mode_ti ->
  ad_pat_sub_g n a_sub_mode_sk Mg Ψfull Θ' Rg0 Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' Rg0 ->
     a_wf_aenv Θb0 ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     a_wf_aenv Θ' ->
     Ψfull [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qg) ->
     ad_pat_sub_g n a_sub_mode_sk Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qg) ->
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
      | pose proof (ftag_in_uskl_ptyp_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq ].
Qed.

(** [UnivGhostLG]: ⊤̇◇-subject, SK, non-incrementing. *)
Lemma ad_pat_sub_g_ughost_lg_transport : forall Θb Ψr Rg' Rgt,
  uskl_precise Θb Ψr Rg' Rgt ->
  forall n Mg Θ' Ψfull Rg0 Qg Ψsup Ψn Ψna,
  Rgt = uskl_topholeg Rg0 ->
  a_wf_aenv Θb ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  a_wf_aenv Θ' ->
  Mg <> mode_ti ->
  ad_pat_sub_g n a_sub_mode_sk Mg Ψfull Θ' Rg0 Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' Rg0 ->
     a_wf_aenv Θb0 ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     a_wf_aenv Θ' ->
     Ψfull [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qg) ->
     ad_pat_sub_g n a_sub_mode_sk Mg Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qg) ->
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
  - (* tophole_keepg: plain ⊤◇ on the ghostier side *)
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
      | pose proof (ftag_in_uskl_ptyp_syn τ) as Hpt; clear - Hpt; fsetdec
      | exact Hwfq ].
Qed.

(** [FlexMono]: defined-flexible-variable subject, fn-mode, non-incrementing. *)
Lemma ad_pat_sub_g_flex_mono_transport : forall Θb Ψr Rg' Rgv,
  uskl_precise Θb Ψr Rg' Rgv ->
  forall n NM Mg Θ' Ψfull αg τg Qg Ψsup Ψn Ψna,
  Rgv = uskl_var_f αg ->
  a_wf_aenv Θb ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  a_wf_aenv Θ' ->
  binds αg (abind_flex_mono_def τg) Θ' ->
  ad_pat_sub_g n NM (mode_fn Mg) Ψfull Θ' (ptyp_to_uskl_syn τg) Qg ->
  (forall Θb0 Ψr0 Rg'' Ψsup0 Ψn0 Ψna0,
     uskl_precise Θb0 Ψr0 Rg'' (ptyp_to_uskl_syn τg) ->
     a_wf_aenv Θb0 ->
     Ψr0 [<=] Ψsup0 ->
     (forall x b, binds x b Θb0 -> binds x b Θ') ->
     a_wf_aenv Θ' ->
     Ψfull [=] Ψn0 `union` Ψna0 ->
     Ψna0 [<=] Ψsup0 ->
     Ψsup0 ∩ Ψn0 [=] empty ->
     Ψsup0 ∩ ftag_in_uskl Rg'' [=] empty ->
     Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qg) ->
     (NM = a_sub_mode_ty -> uskl_ghost_free Rg'') ->
     ad_pat_sub_g n NM (mode_fn Mg) Ψn0 Θ' Rg'' Qg) ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Qg) ->
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
      | pose proof (ftag_in_uskl_ptyp_syn τ) as Hpt; clear - Hpt; fsetdec
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
  a_wf_aenv Θb ->
  Ψr [<=] Ψsup ->
  (forall x b, binds x b Θb -> binds x b Θ') ->
  a_wf_aenv Θ' ->
  Ψfull [=] Ψn `union` Ψna ->
  Ψna [<=] Ψsup ->
  Ψsup ∩ Ψn [=] empty ->
  Ψsup ∩ ftag_in_uskl Rg' [=] empty ->
  Θ' ⨟ empty ⊢ₚₛᵃ (bskl_to_pskl Q) ->
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
    eapply (H0 α ltac:(clear - Hα; fsetdec)) with (Ψna := Ψna);
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
