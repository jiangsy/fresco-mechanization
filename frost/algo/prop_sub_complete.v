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
Lemma ad_pat_sub_n_rename_tvar : forall n NM M Ψ Θ1 α Θ0 S Q Y,
  ad_pat_sub_n n NM M Ψ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) S Q ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_pat_sub_n n NM M Ψ (Θ1 ++ (Y ~ abind_tvar) ++ Θ0)
      (subst_bskl_in_uskl (uskl_var_f Y) α S)
      (subst_bskl_in_bskl (bskl_var_f Y) α Q).
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hdom Hdefs; simpl.
  - apply ad_pat_sub_n__infer; auto.
    + apply ad_pat_consis_rename_tvar; auto.
    + change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
      apply is_sskl_subst_mono; auto using mono_ptyp.
  - rewrite subst_var_bskl_inh.
    apply ad_pat_sub_n__check.
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
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
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply guarded_uskl_subst_mono; auto using mono_ptyp.
    + change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
      apply guarded_bskl_subst_mono; auto using mono_ptyp.
    + change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
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
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply a_tags_sort_subst_mono;
        [ assumption | apply mono_ptyp__var ].
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
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
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      apply a_tags_sort_subst_mono;
        [ assumption | apply mono_ptyp__var ].
    + change (uskl_var_f Y) with (ptyp_to_uskl_syn (ptyp_var_f Y)).
      rewrite uskl_to_pskl_subst_mono. simpl.
      apply a_wf_pskl_rename_tvar;
        first [ assumption | clear; fsetdec ].
  - rewrite subst_var_bskl_inh.
    apply ad_pat_sub_n__ghost; auto.
    + apply a_wf_pskl_rename_tvar; [ assumption | clear; fsetdec ].
    + rewrite <- subst_var_bskl_inh.
      change (bskl_var_f Y) with (ptyp_to_bskl_syn (ptyp_var_f Y)).
      apply mod_comp_sk_subst_mono; auto using mono_ptyp.
  - apply ad_pat_sub_n__ghostg; auto.
  - apply ad_pat_sub_n__univ_ghost_l; auto.
  - apply ad_pat_sub_n__univ_ghost_lg; auto.
  - match goal with
    | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hne]
    end.
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
