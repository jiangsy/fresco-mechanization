Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.consistency.prop_consis_precise.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_precise.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.subtyping.prop_rigid_substitution.
Require Import src.fresco.algo.subtyping.prop_solve_extension.

Set Implicit Arguments.

Lemma a_solve_eq_complete_rsubst_var :
  forall NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0,
  {{ ⊢ Θ }}a ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  rsubst_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  rsubst_leaf NM Θ Δρ Ψρ ψsub ψa ->

  exists Pa, {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa }}a /\
    forall Δ', Δ [<=] Δ' ->
    {{ Θ ⨟ Δ' ⊢ˢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad.
Proof.
  intros NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0
    HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf.
  destruct Hleaf as (α & Ψ'' & Heqψa & HαΔρ & Htagsub & Hwfsub & HΨρ).
  subst ψa.
  pose proof (Hfresh α HαΔρ) as (HXb & Hκav & Hdef).
  assert (HαΔ : α `in` Δ) by (clear - Hdelta HαΔρ; fsetdec).
  pose proof (Hapart α HαΔρ) as Hsh.
  destruct (ad_ppre_delta_var_inv Hpre eq_refl HwfΘ HαΔ HXb Hdef Hsh)
    as (Heqm & HΨie).
  assert (HeqPi : Pi = pskl_var_f α)
    by (eapply msubst_pskl_var_inv; eassumption).
  assert (HΨ'e : Ψ' [=] empty)
    by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
  assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
  exists Pi. split.
  - rewrite HeqPi. apply a_solve_eq__var.
  - intros Δ' Hsub'.
    rewrite Heqm.
    apply ad_ppre__var. clear - HΨie HΨae; fsetdec.
Qed.

Lemma uskl_rsubst_no_ghost : forall NM Θ Δρ Ψρ R ψ Ψ',
  uskl_rsubst NM Θ Δρ Ψρ R ψ -> a_tags_sort NM Ψ' ψ -> uskl_no_ghost R.
Proof.
  intros NM Θ Δρ Ψρ R ψ Ψ' Hr Ht.
  apply uskl_no_ghost_of_dskl. eapply uskl_rsubst_is_dskl; [ exact Hr | ].
  inversion Ht; assumption.
Qed.

Lemma uskl_no_ghost_open_inv : forall R α,
  uskl_no_ghost (open_uskl_wrt_uskl R (uskl_var_f α)) -> uskl_no_ghost R.
Proof.
  intros R α. unfold open_uskl_wrt_uskl. generalize 0.
  induction R; intros k Hk; simpl in *; eauto.
  destruct Hk; split; eauto.
Qed.

Lemma binds_swap_mid : forall (α : atom) (b : abind) Θ1 Θ0 α1 β1 c c',
  binds α b (Θ1 ++ (α1 ~ c) ++ Θ0) -> α <> α1 ->
  binds α b (Θ1 ++ (β1 ~ c') ++ Θ0).
Proof.
  intros α b Θ1 Θ0 α1 β1 c c' Hb Hne.
  unfold binds in *.
  apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [Hb | Hb]; [ left; exact Hb | right ].
  simpl in Hb. destruct Hb as [Heq | Hb].
  - inversion Heq; subst. contradiction.
  - simpl. right. exact Hb.
Qed.

Lemma ad_partial_precise_rename_tvar : forall Θfull Δ Ψ P ψ,
  {{ Θfull ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall α1 β1 Θ1 Θ0,
  uniq Θfull ->
  Θfull = Θ1 ++ (α1 ~ abind_tvar) ++ Θ0 ->
  β1 `notin` dom Θfull ->
  β1 `notin` Δ ->
  β1 `notin` ftvar_in_pskl P ->
  β1 `notin` ftvar_in_uskl ψ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θfull ->
     α1 `notin` ftvar_in_ptyp τ /\ β1 `notin` ftvar_in_ptyp τ) ->
  {{ (Θ1 ++ (β1 ~ abind_tvar) ++ Θ0) ⨟ Δ ⊢ˢ
    (subst_pskl_in_pskl (pskl_var_f β1) α1 P)
    ⊑ᵖ[ Ψ ] (subst_uskl_in_uskl (uskl_var_f β1) α1 ψ) }}ad.
Proof.
  intros Θfull Δ Ψ P ψ H; induction H;
    intros α1 β1 Θ1 Θ0 Hu Heq HWd Hβ2Δ HWP Hβ2ψ Hdefs; subst; simpl in *.
  -  apply ad_ppre__unit; assumption.
  -
    destruct (eq_var α α1) as [-> | Hne].
    + repeat (destruct_if as [_ | Hc]; [ | exfalso; apply Hc; reflexivity ]).
      apply ad_ppre__var; assumption.
    + repeat (destruct_if as [Hc | _]; [ exfalso; apply Hne; exact Hc | ]).
      apply ad_ppre__var; assumption.
  -
    eapply ad_ppre__arrow;
      [ apply IHad_partial_precise1;
          [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
          | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ]
      | apply IHad_partial_precise2;
          [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
          | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ]
      | assumption ].
  -
    eapply ad_ppre__forall with
      (L := L `union` singleton α1 `union` singleton β1
              `union` Δ `union` dom (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0));
      [ | eassumption ].
    intros β Hβ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ; fsetdec | apply lc_pskl_var_f ].
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    assert (Hu' : uniq ((β ~ abind_tvar) ++ Θ1 ++ (α1 ~ abind_tvar) ++ Θ0))
      by (apply uniq_push; [ exact Hu | clear - Hβ; solve_notin ]).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) α1 β1
             ((β ~ abind_tvar) ++ Θ1) Θ0 Hu' eq_refl);
      [ simpl; clear - HWd Hβ; solve_notin
      | clear - Hβ2Δ Hβ; fsetdec
      | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P
                      (pskl_var_f β)) as Hup;
        simpl in Hup; clear - HWP Hβ Hup; fsetdec
      | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                      (uskl_var_f β)) as Hup;
        simpl in Hup; clear - Hβ2ψ Hβ Hup; fsetdec
      | intros αd τ Hb;
        apply Hdefs with (α := αd);
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
          [ discriminate Hc | exact Hb' ] ].
  -
    assert (Hα2ψ : α1 `notin` ftvar_in_uskl ψ \/ α1 `in` ftvar_in_uskl ψ)
      by (destruct (AtomSetProperties.In_dec α1 (ftvar_in_uskl ψ));
          [ right | left ]; assumption).
    apply ad_ppre__ghost; [ assumption | ].
    pose proof (ftvar_in_uskl_subst_uskl_in_uskl_upper ψ (uskl_var_f β1) α1)
      as Hup. simpl in Hup.
    match goal with Hint : Δ ∩ _ [=] empty |- _ =>
      clear - Hint Hβ2Δ Hup; fsetdec end.
  -
    apply ad_ppre__univ_ghost_remove.
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ].
  -
    eapply ad_ppre__univ_ghost_fill with
      (L := L `union` singleton α1 `union` singleton β1
              `union` Δ `union` dom (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0)).
    intros β Hβ.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    replace (pskl_univ_ghost (subst_pskl_in_pskl (pskl_var_f β1) α1 P))
      with (subst_pskl_in_pskl (pskl_var_f β1) α1 (pskl_univ_ghost P))
      by reflexivity.
    assert (Hu' : uniq ((β ~ abind_tvar) ++ Θ1 ++ (α1 ~ abind_tvar) ++ Θ0))
      by (apply uniq_push; [ exact Hu | clear - Hβ; solve_notin ]).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) α1 β1
             ((β ~ abind_tvar) ++ Θ1) Θ0 Hu' eq_refl);
      [ simpl; clear - HWd Hβ; solve_notin
      | exact Hβ2Δ
      | simpl; clear - HWP; solve_notin
      | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                      (uskl_var_f β)) as Hup;
        simpl in Hup; clear - Hβ2ψ Hβ Hup; fsetdec
      | intros αd τ Hb;
        apply Hdefs with (α := αd);
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
          [ discriminate Hc | exact Hb' ] ].
  -
    apply ad_ppre__univ_ghost_keep.
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ].
  -
    assert (Hne : α <> α1).
    { intro; subst.
      assert (Hbz : binds α1 abind_tvar (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      pose proof (binds_unique _ _ _ _ _ H Hbz Hu) as Hc; discriminate Hc. }
    destruct_if as [Hc | _]; [ exfalso; apply Hne; exact Hc | ].
    destruct (Hdefs _ _ H) as [Hα2τ Hβ2τ].
    eapply ad_ppre__flex_l;
      [ eapply binds_swap_mid; [ exact H | exact Hne ] | ].
    assert (Hfr : α1 `notin` ftvar_in_pskl (ptyp_to_pskl τ))
      by (rewrite ftvar_ptyp_to_pskl; exact Hα2τ).
    rewrite <- (subst_pskl_in_pskl_fresh_eq (ptyp_to_pskl τ)
                  (pskl_var_f β1) α1 Hfr).
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | rewrite ftvar_ptyp_to_pskl; exact Hβ2τ
      | clear - Hβ2ψ; solve_notin | exact Hdefs ].
  -
    assert (Hne : α <> α1).
    { intro; subst.
      assert (Hbz : binds α1 abind_tvar (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      pose proof (binds_unique _ _ _ _ _ H Hbz Hu) as Hc; discriminate Hc. }
    destruct_if as [Hc | _]; [ exfalso; apply Hne; exact Hc | ].
    destruct (Hdefs _ _ H) as [Hα2τ Hβ2τ].
    eapply ad_ppre__flex_r;
      [ eapply binds_swap_mid; [ exact H | exact Hne ] | ].
    assert (Hfr : α1 `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ))
      by (rewrite ftvar_ptyp_to_uskl_syn; exact Hα2τ).
    rewrite <- (subst_uskl_in_uskl_fresh_eq (ptyp_to_uskl_syn τ)
               (uskl_var_f β1) α1 Hfr).
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | clear - HWP; solve_notin
      | rewrite ftvar_ptyp_to_uskl_syn; exact Hβ2τ | exact Hdefs ].
Qed.

Lemma ad_partial_precise_rename_head : forall Θ Δ Ψ P ψR α α',
  {{ ⊢ Θ }}a ->
  α `notin` dom Θ `union` ftvar_in_pskl P `union` ftvar_in_uskl ψR ->
  α' `notin` add α (dom Θ `union` Δ `union` ftvar_in_pskl P
                     `union` ftvar_in_uskl ψR) ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ]
       (open_uskl_wrt_uskl ψR (uskl_var_f α)) }}ad ->
  {{ ((α' ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ]
       (open_uskl_wrt_uskl ψR (uskl_var_f α')) }}ad.
Proof.
  intros Θ Δ Ψ P ψR α α' Hwf Hα Hα' H.
  pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR (uskl_var_f α)) as Hup.
  simpl in Hup.
  pose proof (@ad_partial_precise_rename_tvar _ _ _ _ _ H α α' nil Θ) as Hren.
  simpl in Hren.
  rewrite (subst_pskl_in_pskl_fresh_eq _ (pskl_var_f α') α) in Hren
    by solve_notin_auto.
  rewrite <- (subst_uskl_in_uskl_intro α ψR (uskl_var_f α')) in Hren
    by solve_notin_auto.
  apply Hren.
  - apply a_wf_aenv_uniq. apply a_wf_aenv__tvar.
    + solve_notin_auto.
    + exact Hwf.
  - reflexivity.
  - solve_notin_auto.
  - solve_notin_auto.
  - solve_notin_auto.
  - clear - Hup Hα'. fsetdec.
  - intros αd τ Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'].
    + discriminate Hc.
    + pose proof (a_wf_aenv_def_ftv_dom _ _ Hwf Hb') as Hd.
      split; solve_notin_auto.
Qed.

Definition aenv_split (Θf Θtv Θr : aenv) : Prop :=
  (forall x (b : abind), binds x b Θf <-> binds x b Θtv \/ binds x b Θr) /\
  dom Θf [=] dom Θtv `union` dom Θr /\
  (dom Θtv) ∩ dom Θr [=] empty.

Lemma aenv_split_nil : forall Θf, aenv_split Θf nil Θf.
Proof.
  intros Θf; split; [ | split ].
  - intros x b; split; intros Hb;
      [ right; exact Hb
      | destruct Hb as [Hb | Hb]; [ inversion Hb | exact Hb ] ].
  - simpl. clear; fsetdec.
  - simpl. clear; fsetdec.
Qed.

Lemma aenv_split_cons_tv : forall Θf Θtv Θr α,
  aenv_split Θf Θtv Θr -> α `notin` dom Θf ->
  aenv_split ((α ~ abind_tvar) ++ Θf) ((α ~ abind_tvar) ++ Θtv) Θr.
Proof.
  intros Θf Θtv Θr α (Hbs & Hdom & Hdisj) Hα; split; [ | split ].
  - intros x b; split.
    + intros Hb.
      unfold binds in Hb; simpl in Hb.
      destruct Hb as [Heq | Hb];
        [ left; unfold binds; simpl; left; exact Heq | ].
      apply Hbs in Hb.
      destruct Hb as [Hb | Hb];
        [ left; unfold binds; simpl; right; exact Hb | right; exact Hb ].
    + intros Hor.
      unfold binds; simpl.
      destruct Hor as [Hb | Hb];
        [ unfold binds in Hb; simpl in Hb;
          destruct Hb as [Heq | Hb];
          [ left; exact Heq | right; apply Hbs; left; exact Hb ]
        | right; apply Hbs; right; exact Hb ].
  - simpl. clear - Hdom; fsetdec.
  - simpl. clear - Hdisj Hdom Hα; fsetdec.
Qed.

Lemma aenv_split_cons_r : forall Θf Θtv Θr α,
  aenv_split Θf Θtv Θr -> α `notin` dom Θf ->
  aenv_split ((α ~ abind_tvar) ++ Θf) Θtv ((α ~ abind_tvar) ++ Θr).
Proof.
  intros Θf Θtv Θr α (Hbs & Hdom & Hdisj) Hα; split; [ | split ].
  - intros x b; split.
    + intros Hb.
      unfold binds in Hb; simpl in Hb.
      destruct Hb as [Heq | Hb];
        [ right; unfold binds; simpl; left; exact Heq | ].
      apply Hbs in Hb.
      destruct Hb as [Hb | Hb];
        [ left; exact Hb | right; unfold binds; simpl; right; exact Hb ].
    + intros Hor.
      unfold binds; simpl.
      destruct Hor as [Hb | Hb];
        [ right; apply Hbs; left; exact Hb
        | unfold binds in Hb; simpl in Hb;
          destruct Hb as [Heq | Hb];
          [ left; exact Heq | right; apply Hbs; right; exact Hb ] ].
  - simpl. clear - Hdom; fsetdec.
  - simpl. clear - Hdisj Hdom Hα; fsetdec.
Qed.

Lemma aenv_split_sub_r : forall Θf Θtv Θr,
  aenv_split Θf Θtv Θr ->
  forall x (b : abind), binds x b Θr -> binds x b Θf.
Proof.
  intros Θf Θtv Θr (Hbs & _ & _) x b Hb. apply Hbs. right; exact Hb.
Qed.

Lemma aenv_split_dom_r : forall Θf Θtv Θr,
  aenv_split Θf Θtv Θr -> dom Θr [<=] dom Θf.
Proof.
  intros Θf Θtv Θr (_ & Hdom & _). clear - Hdom; fsetdec.
Qed.

Lemma aenv_split_binds_def_r : forall Θf Θtv Θr α τ,
  aenv_split Θf Θtv Θr ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  binds α (abind_flex_mono_def τ) Θf ->
  binds α (abind_flex_mono_def τ) Θr.
Proof.
  intros Θf Θtv Θr α τ (Hbs & _ & _) Htvs Hb.
  apply Hbs in Hb.
  destruct Hb as [Hb | Hb]; [ | exact Hb ].
  pose proof (Htvs _ _ Hb) as Hc; discriminate Hc.
Qed.

Lemma refine_msubst_rigid_nonvar_absurd : forall Θ Θ0 Θtv Θr Δr κ β Q,
  aenv_split Θ Θtv Θr ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ Θ0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  binds β abind_tvar Θ0 ->
  {{ Θr ⨟ Δr ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β))) ⊳ Q }}ad ->
  (forall β0, Q <> bskl_var_f β0) ->
  False.
Proof.
  intros Θ Θ0 Θtv Θr Δr κ β Q Hsp HwfΘ HwfΘ0 Hκ Hrig Href Hnv.
  rewrite (msubst_pskl_tvar_id β HwfΘ0 Hκ Hrig) in Href. simpl in Href.
  eapply (ad_refine_syn_rigid_var_nonvar_absurd Href).
  - intros x b Hb. eapply aenv_split_sub_r; eassumption.
  - apply a_wf_aenv_uniq. exact HwfΘ.
  - eapply a_inc_binds_tvar; eassumption.
  - exact Hnv.
Qed.

Lemma ad_refine_syn_ghost_target_delta_dom : forall Θ Δ Qh Q,
  {{ Θ ⨟ Δ ⊢ᵣ Qh ⊳ Q }}ad ->
  Qh = bskl_ghost ->
  forall x, x `in` ftvar_in_bskl Q -> x `in` Δ -> x `in` dom Θ.
Proof.
  intros Θ Δ Qh Q H; induction H; intros Heq x Hx HxΔ; try discriminate Heq.
  -
    exfalso. rewrite ftvar_pskl_to_bskl_syn in Hx.
    clear - H Hx HxΔ; fsetdec.
  -
    simpl in Hx. apply AtomSetImpl.singleton_1 in Hx; subst x.
    eapply binds_In; eassumption.
Qed.

Lemma ghost_refine_target_ftv_dom_r : forall Θ Θtv Θr Δr Q,
  aenv_split Θ Θtv Θr ->
  Δr [=] dom Θtv ->
  {{ Θr ⨟ Δr ⊢ᵣ bskl_ghost ⊳ Q }}ad ->
  (forall γ, γ `in` ftvar_in_bskl Q -> a_binds_tvar γ Θ) ->
  ftvar_in_bskl Q [<=] dom Θr.
Proof.
  intros Θ Θtv Θr Δr Q (_ & Hdom & _) HΔr Hr Hbt x Hx.
  assert (Hd : x `in` dom Θ)
    by (destruct (Hbt x Hx) as [Hb | [Hb | (τx & Hb)]];
        eapply binds_In; exact Hb).
  destruct (AtomSetProperties.In_dec x Δr) as [HxΔ | HxΔ].
  - exact (ad_refine_syn_ghost_target_delta_dom Hr eq_refl Hx HxΔ).
  - clear - Hd Hdom HΔr HxΔ; fsetdec.
Qed.

Lemma refine_primary_to_plain_split : forall Θf Θtv Θr Δr Q' Q,
  {{ Θr ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  aenv_split Θf Θtv Θr ->
  {{ Θf ⨟ empty ⊢ᵣ Q' ⊳ Q }}ad.
Proof.
  intros Θf Θtv Θr Δr Q' Q H Hsp.
  eapply ad_refine_syn_delta_mono with (Δ0 := Δr); [ | clear; fsetdec ].
  eapply ad_refine_syn_weaken;
    [ exact H | intros x b Hb; eapply aenv_split_sub_r; eassumption ].
Qed.

Lemma consis_subject_ftv_bag_bound : forall Ψ Θf R Q Θtv Θr,
  {{ Ψ ⨟ Θf ⊢ˢ R ∼ Q }}ad ->
  aenv_split Θf Θtv Θr ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  {{ ⊢ Θr }}a ->
  ftvar_in_uskl R [<=] ftvar_in_bskl Q `union` dom Θr.
Proof.
  intros Ψ Θf R Q Θtv Θr H Hsp Htvs HwfΘr.
  intros x Hx.
  destruct (ad_pat_consis_ftv_bound H Hx) as [Hin | (α & τ & Hb & Hor)].
  - clear - Hin; fsetdec.
  - assert (Hbr : binds α (abind_flex_mono_def τ) Θr)
      by (eapply aenv_split_binds_def_r; eassumption).
    destruct Hor as [-> | Hτ].
    + pose proof (binds_In _ _ _ _ Hbr) as Hd. clear - Hd; fsetdec.
    + assert (Hd : ftvar_in_ptyp τ [<=] dom Θr)
        by (eapply a_wf_aenv_def_ftv_dom; eassumption).
      clear - Hτ Hd; fsetdec.
Qed.

Definition solve_eq_complete_var_post (Θ Θr : aenv) (κ : metasubst) (Δ Ψi Ψa : atoms)
    (ψa : uskl) (κ' : metasubst) (Pa : pskl) : Prop :=
  forall Δ',
    Δ' ∩ Δ [=] empty ->
    Δ' ∩ dom Θr [=] empty ->
    delta_def_fresh Δ' Θ ->
    {{ Θ ⨟ (Δ `union` Δ') ⊢ˢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad.

Definition solve_eq_complete_var_concl (Θ0 Θ Θw Θr : aenv) (κ : metasubst) (Δ Ψi Ψa : atoms)
    (ψa : uskl) (Pi P0 : pskl) (L : atoms) : Prop :=
  solve_ext Θ0 Θw Pi P0 L (solve_eq_complete_var_post Θ Θr κ Δ Ψi Ψa ψa).

Lemma solve_eq_complete_var_univ_ghost_both : forall Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi' P0' L,
  solve_eq_complete_var_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi' P0' L ->
  solve_eq_complete_var_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa (pskl_univ_ghost Pi') (pskl_univ_ghost P0') L.
Proof.
  intros Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi' P0' L
         (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hq).
  exists Ξ, (pskl_univ_ghost Pa), κ'.
  repeat split; try assumption.
  - apply a_solve_eq__univ_ghost_both; exact Hs.
  - intros Δ' HS1 HS2 HS3. cbn [msubst_pskl].
    apply ad_ppre__univ_ghost_remove. exact (Hq Δ' HS1 HS2 HS3).
Qed.

Lemma solve_eq_complete_var_step : forall Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi P0 Pi' P0' L,
  (forall Ξ Pa, {{ Θ0 ⊢ₑ Pi' ∼ P0' ⤳ Ξ ⨾ Pa }}a -> {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a) ->
  solve_eq_complete_var_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi' P0' L ->
  solve_eq_complete_var_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi P0 L.
Proof.
  intros Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi P0 Pi' P0' L Hstep H.
  eapply solve_ext_step;
    [ exact Hstep | intros κ0 Pa0 Hq; exact Hq | exact H ].
Qed.

Lemma uskl_rsubst_all_tag_cases : forall NM Θ Δρ Ψρ ε R ψ Ψ,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_all_tag ε R) ψ ->
  a_tags_sort NM Ψ ψ ->
  rsubst_leaf NM Θ Δρ Ψρ (uskl_all_tag ε R) ψ \/
  exists L R', ψ = uskl_all_tag ε R' /\
    forall α, α `notin` L ->
      uskl_rsubst NM Θ Δρ Ψρ (open_uskl_wrt_uskl R (uskl_var_f α))
                            (open_uskl_wrt_uskl R' (uskl_var_f α)).
Proof.
  intros * Hrho Htags.
  destruct (uskl_rsubst_all_tag_l_inv Hrho) as [[-> Hempty] | [Hleaf | Hbody]];
    [ | auto | auto ].
  destruct (a_tags_sort_all_tag_inv Htags) as (L & Ψ0 & Hbody & _ & _).
  right. exists L, R. split; [ reflexivity | ].
  intros α Hα. apply ursubst__refl; [ | exact Hempty ].
  apply is_dskl_lc. destruct (Hbody α Hα); assumption.
Qed.

Lemma uskl_rsubst_arrow_cases : forall NM Θ Δρ Ψρ R1 R2 ψ Ψ,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_arrow R1 R2) ψ ->
  a_tags_sort NM Ψ ψ ->
  rsubst_leaf NM Θ Δρ Ψρ (uskl_arrow R1 R2) ψ \/
  exists R1' R2' Ψ1 Ψ2, ψ = uskl_arrow R1' R2' /\
    uskl_rsubst NM Θ Δρ Ψ1 R1 R1' /\
    uskl_rsubst NM Θ Δρ Ψ2 R2 R2' /\ Ψρ [=] Ψ1 `union` Ψ2.
Proof.
  intros * Hrho Htags.
  destruct (uskl_rsubst_arrow_l_inv Hrho) as [[-> Hempty] | [Hleaf | Hbody]];
    [ | auto | auto ].
  assert (Hd : is_dskl (uskl_arrow R1 R2)) by (inversion Htags; assumption).
  right. exists R1, R2, empty, empty.
  split; [ reflexivity | ].
  split; [ apply ursubst__refl;
    [ apply is_dskl_lc; inversion Hd; assumption | clear; fsetdec ] | ].
  split; [ apply ursubst__refl;
    [ apply is_dskl_lc; inversion Hd; assumption | clear; fsetdec ] | ].
  clear - Hempty; fsetdec.
Qed.

Lemma uskl_rsubst_dot_univ_ghost_cases : forall NM Θ Δρ Ψρ R ψ Ψ,
  uskl_rsubst NM Θ Δρ Ψρ (uskl_dot_univ_ghost R) ψ ->
  a_tags_sort NM Ψ ψ ->
  rsubst_leaf NM Θ Δρ Ψρ (uskl_dot_univ_ghost R) ψ \/
  exists R', ψ = uskl_dot_univ_ghost R' /\ uskl_rsubst NM Θ Δρ Ψρ R R'.
Proof.
  intros * Hrho Htags.
  destruct (uskl_rsubst_dot_univ_ghost_l_inv Hrho)
    as [[-> Hempty] | [Hleaf | Hbody]]; [ | auto | auto ].
  pose proof (a_tags_sort_dot_univ_ghost_inv Htags) as Hbody.
  right. exists R. split; [ reflexivity | ].
  apply ursubst__refl; [ apply is_dskl_lc; destruct Hbody; assumption | exact Hempty ].
Qed.

Lemma ad_partial_precise_msubst_fold : forall Θ κ Δ Δ' Ψc PaR ψR α α',
  a_wf_aenv Θ ->
  (forall p, In p κ -> ftvar_in_ptyp (snd p) [<=] dom Θ) ->
  α `notin` Δ `union` dom Θ `union` dom κ `union` ftvar_in_uskl ψR ->
  α' `notin` Δ `union` Δ' `union` dom Θ `union` dom κ
    `union` ftvar_in_uskl ψR `union` singleton α
    `union` ftvar_in_pskl (msubst_pskl κ PaR) ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ add α (Δ `union` remove α Δ')
     ⊢ˢ msubst_pskl κ PaR ⊑ᵖ[ Ψc ]
       open_uskl_wrt_uskl ψR (uskl_var_f α) }}ad ->
  {{ Θ ⨟ add α' (Δ `union` Δ')
     ⊢ˢ msubst_pskl κ (open_pskl_wrt_pskl
          (close_pskl_wrt_pskl α PaR) (pskl_var_f α'))
     ⊑ᵖ[ Ψc ] open_uskl_wrt_uskl ψR (uskl_var_f α') }}ad.
Proof.
  intros Θ κ Δ Δ' Ψc PaR ψR α α' HwfΘ HimavX HXf HX'f Hrun.
  assert (Hst : {{ Θ ⨟ add α (Δ `union` remove α Δ')
    ⊢ˢ msubst_pskl κ PaR ⊑ᵖ[ Ψc ]
      open_uskl_wrt_uskl ψR (uskl_var_f α) }}ad)
    by (eapply ad_partial_precise_strengthen_tvar; exact Hrun).
  assert (Hrn : {{ Θ ⨟ add α' (remove α (add α (Δ `union` remove α Δ')))
    ⊢ˢ subst_pskl_in_pskl (pskl_var_f α') α (msubst_pskl κ PaR)
    ⊑ᵖ[ Ψc ] subst_uskl_in_uskl (uskl_var_f α') α
      (open_uskl_wrt_uskl ψR (uskl_var_f α)) }}ad).
  { eapply ad_partial_precise_rename;
      [ exact Hst
      | clear; fsetdec
      | clear - HXf; solve_notin
      | clear - HX'f; solve_notin
      | clear - HX'f; solve_notin
      | clear - HX'f; solve_notin
      | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                      (uskl_var_f α)) as Hup;
        simpl in Hup; clear - HX'f Hup; destruct_notin; fsetdec
      | intros αd τ Hbd;
        assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
          by (eapply a_wf_aenv_def_ftv_dom; eauto);
        split; [ clear - Hd HXf; destruct_notin; fsetdec
               | clear - Hd HX'f; destruct_notin; fsetdec ] ]. }
  rewrite <- (subst_uskl_in_uskl_intro α ψR (uskl_var_f α')) in Hrn
    by (clear - HXf; solve_notin).
  rewrite msubst_pskl_subst_var_paired in Hrn;
    [ | clear - HXf; solve_notin
      | clear - HX'f; solve_notin
      | intros p Hp; pose proof (HimavX p Hp) as Hd;
        clear - Hd HXf; destruct_notin; solve_notin_auto ].
  rewrite (subst_pskl_in_pskl_spec PaR (pskl_var_f α') α) in Hrn.

  eapply ad_partial_precise_delta_cong;
    [ eapply ad_partial_precise_delta_weaken_fresh
        with (Δ' := Δ' ∩ singleton α); [ exact Hrn | | ]
    | clear - HXf HX'f; destruct_notin; fsetdec ].
  - pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                  (uskl_var_f α')) as Hup.
    simpl in Hup. apply inter_empty_pointwise; intros y Hy.
    assert (Heqy : y = α) by (clear - Hy; fsetdec).
    subst y. clear - HXf HX'f Hup; destruct_notin; fsetdec.
  - intros Yd αd τ HYd Hbd.
    assert (Heqy : Yd = α) by (clear - HYd; fsetdec).
    subst Yd.
    assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
      by (eapply a_wf_aenv_def_ftv_dom; eauto).
    clear - Hd HXf; destruct_notin; fsetdec.
Qed.

Lemma ad_partial_precise_forall_close :
  forall Θ Θw κ κX Δ Δ' Ψc Ψ ε ψR PaX α,
  {{ ⊢ Θ }}a ->
  (forall p, In p κ -> ftvar_in_ptyp (snd p) [<=] dom Θ) ->
  Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κX ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  msubst_lc (κX ++ κ) ->
  α `notin` Δ `union` dom Θ `union` dom κX `union` dom κ
    `union` ftvar_in_uskl ψR ->
  Ψ [=] add ε Ψc ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ add α (Δ `union` remove α Δ')
     ⊢ˢ msubst_pskl (κX ++ κ) PaX ⊑ᵖ[ Ψc ]
       open_uskl_wrt_uskl ψR (uskl_var_f α) }}ad ->
  {{ Θ ⨟ (Δ `union` Δ') ⊢ˢ
     pskl_all_syn (msubst_pskl (κX ++ κ) (close_pskl_wrt_pskl α PaX))
     ⊑ᵖ[ Ψ ] uskl_all_tag ε ψR }}ad.
Proof.
  intros Θ Θw κ κX Δ Δ' Ψc Ψ ε ψR PaX α HwfΘ Himav HFX Hmon HlcκX Hα HΨ Hrun.
  apply ad_ppre__forall with (Ψ0 := Ψc)
    (L := Δ `union` Δ' `union` dom Θ `union` dom κX `union` dom κ
       `union` ftvar_in_uskl ψR `union` singleton α
       `union` ftvar_in_pskl (msubst_pskl (κX ++ κ) PaX)).
  - intros α' HX'.
    apply ad_partial_precise_weaken_tvar.
    rewrite <- msubst_pskl_open_lc.
    + eapply ad_partial_precise_msubst_fold.
      * exact HwfΘ.
      * intros p Hp. apply in_app_or in Hp. destruct Hp as [Hp | Hp].
        -- pose proof (forall_wf_mono_images_dom HFX p Hp) as Hd.
           pose proof (aenv_binds_dom_sub _ _ Hmon) as Hdw.
           clear - Hd Hdw; fsetdec.
        -- exact (Himav p Hp).
      * rewrite dom_app. clear - Hα. solve_notin_auto.
      * rewrite dom_app. clear - HX'. solve_notin_auto.
      * exact Hrun.
    + exact HlcκX.
    + rewrite dom_app. clear - HX'. solve_notin_auto.
  - exact HΨ.
Qed.

Theorem a_solve_eq_complete_var_gen :
  forall NM Θ Θ0 Θw Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  aenv_split Θ Θtv Θr ->
  aenv_split Θ0 Θtv Θ0r ->
  {{ ⊢ Θr }}a ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  Δr [=] dom Θtv ->
  Δρ ∩ dom Θtv [=] empty ->
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->

  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, a_flex_tvar Θ0 α ->
     ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θw) ->
  uskl_rsubst NM Θ Δρ Ψρ ψsub ψa ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  Ψρ ∩ Ψ' [=] empty ->
  rsubst_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  {{ Ψsub ⨟ Θ ⊢ˢ ψsub ∼ Q }}ad ->
  {{ Θr ⨟ Δr ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  solve_eq_complete_var_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi P0 L.
Proof.
  intros NM Θ Θ0 Θw Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv HwfΘ HwfΘ0 HwfΘw Hmon Hnr
         HwfPi HwfP0 Hκ Hκw Hrho Htags
         Hsub Hinter Hfresh Hdelta Hapart Hdfresh Hpre
         Hsubeq1 Hsubeq2 Hconsis Hrefine.
  revert NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa ψa Pi P0
         HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv HwfΘ HwfΘ0 Hmon Hnr
         HwfPi HwfP0 Hκ Hκw Hrho Htags
         Hsub Hinter Hfresh Hdelta Hapart Hdfresh Hpre
         Hsubeq1 Hsubeq2 Hrefine.
  induction Hconsis; intros
    NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa ψa Pi P0
    HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv HwfΘ HwfΘ0 Hmon Hnr
    HwfPi HwfP0 Hκ Hκw Hrho Htags
    Hsub Hinter Hfresh Hdelta Hapart Hdfresh Hpre
    Hsubeq1 Hsubeq2 Hrefine Lav HLav;

  assert (Hdefs : forall α0 τ0, binds α0 (abind_flex_mono_def τ0) Θ ->
                    binds α0 (abind_flex_mono_def τ0) Θw)
    by (intros α0 τ0 Hb; destruct (Hnr _ _ Hb) as [Hb' | Hc];
        [ exact Hb' | discriminate Hc ]).
  -
    assert (Hrefine' : {{ Θ ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_unit }}ad)
      by (eapply refine_primary_to_plain_split; eassumption).
    destruct (uskl_rsubst_unit_l_inv Hrho) as [[-> HΨρ] | Hleaf].
    + assert (HΨ'e : Ψ' [=] empty)
        by (exact (d_tags_skl_unit_inv (a_tags_sort_d_tags Htags))).
      assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
      assert (Hsz : size_pskl Pi + size_pskl P0
                      <= size_pskl Pi + size_pskl P0) by lia.
      destruct (a_solve_eq_unit (Θ := Θ) (Δ := Δ)
                  Hsz HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre Hrefine')
        as (Pa & Hsolve & Hprec).
      eapply solve_ext_nil; [ exact Hsolve | ].
      intros Δ' HS1 HS2 HS3. cbn [app].
      eapply ad_partial_precise_psi_cong;
        [ eapply ad_partial_precise_delta_weaken_fresh;
            [ exact Hprec | simpl; clear; fsetdec | exact HS3 ]
        | clear - HΨae; fsetdec ].
    + destruct (@a_solve_eq_complete_rsubst_var _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil; [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. cbn [app]. apply Hq. clear; fsetdec.
  -
    assert (Hrefine' : {{ Θ ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (bskl_var_f α) }}ad)
      by (eapply refine_primary_to_plain_split; eassumption).
    assert (Hbα : a_binds_tvar α Θw \/ binds α abind_tvar Θ).
    { match goal with Hb : a_binds_tvar α Θ |- _ =>
        destruct Hb as [Hrig | [Hfm | (τx & Hfd)]];
          [ right; exact Hrig
          | destruct (Hnr _ _ Hfm) as [Hb' | Hc];
              [ left; right; left; exact Hb' | discriminate Hc ]
          | destruct (Hnr _ _ Hfd) as [Hb' | Hc];
              [ left; right; right; exists τx; exact Hb' | discriminate Hc ] ]
      end. }
    destruct (uskl_rsubst_var_l_inv Hrho) as [[-> HΨρ] | Hleaf].
    + assert (HΨ'e : Ψ' [=] empty)
        by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
      assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
      assert (Hsz : size_pskl Pi + size_pskl P0
                      <= size_pskl Pi + size_pskl P0) by lia.
      eapply solve_ext_post_solve;
        [ | exact (a_solve_eq_var (Θ := Θ) (Θw := Θw) (Δ := Δ)
                     Hsz HwfΘ HwfΘ0 HwfΘw Hmon Hdefs
                     HwfPi HwfP0 Hκ Hbα Hdfresh Hpre Hrefine' HLav) ].
      intros Ξ0 κ' Pa Hsolve Hprec Δ' HS1 HS2 HS3.
      destruct (AtomSetProperties.In_dec α (dom Θr)) as [HinR | HninR].
      *
        eapply ad_partial_precise_psi_cong;
          [ eapply ad_partial_precise_delta_weaken_fresh;
              [ exact Hprec
              | simpl; clear - HS2 HinR; fsetdec
              | exact HS3 ]
          | clear - HΨae; fsetdec ].
      *
        assert (HαΔr : α `in` Δr).
        { assert (Hdα : α `in` dom Θ)
            by (match goal with Hb : a_binds_tvar α Θ |- _ =>
                  destruct Hb as [Hb | [Hb | (τx & Hb)]];
                  eapply binds_In; exact Hb
                end).
          pose proof (proj1 (proj2 HspΘ)) as HdomΘ.
          clear - Hdα HdomΘ HninR HΔrd; fsetdec. }
        assert (HnhP0d : pskl_no_ghost P0).
        { eapply msubst_pskl_no_ghost_inv with (κ := κ).
          eapply ad_refine_inh_deltar_var_rhs_no_ghost;
            [ exact Hrefine | reflexivity | reflexivity | exact HninR
            | exact HαΔr ]. }
        assert (HnhPa : pskl_no_ghost Pa)
          by (eapply a_solve_eq_no_ghost_p0; eassumption).
        eapply ad_partial_precise_psi_cong;
          [ eapply ad_partial_precise_no_ghost_subject_delta_mono;
              [ exact Hprec | apply msubst_pskl_no_ghost; exact HnhPa
              | clear; fsetdec ]
          | clear - HΨae; fsetdec ].
    + destruct (@a_solve_eq_complete_rsubst_var _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil; [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. cbn [app]. apply Hq. clear; fsetdec.
  -
    assert (HwfΘr2 := HwfΘr).
    destruct (uskl_rsubst_arrow_cases Hrho Htags)
      as [Hleaf | (ψa1 & ψa2 & Ψρ1 & Ψρ2 & -> & Hrho1 & Hrho2 & HΨρs)].
    { destruct (@a_solve_eq_complete_rsubst_var _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec. }
    { rename Htags into Htags0, Hpre into Hpre0.
      destruct (a_tags_sort_arrow_inv Htags0)
        as (Ψ'1 & Ψ'2 & Htags1 & Htags2 & HΨ'disj & HΨ's).
      assert (Hng1 : uskl_no_ghost R1)
        by (apply uskl_no_ghost_of_dskl; eapply uskl_rsubst_is_dskl;
              [ exact Hrho1 | inversion Htags1; assumption ]).
      assert (Hng2 : uskl_no_ghost R2)
        by (apply uskl_no_ghost_of_dskl; eapply uskl_rsubst_is_dskl;
              [ exact Hrho2 | inversion Htags2; assumption ]).

      assert (Hft1 : Ψ1 [<=] Ψρ1 `union` Ψ'1).
      { pose proof (ad_pat_consis_ftag_sub Hconsis1) as Ha.
        pose proof (uskl_rsubst_ftag_sub Hrho1) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags1)) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hft2 : Ψ2 [<=] Ψρ2 `union` Ψ'2).
      { pose proof (ad_pat_consis_ftag_sub Hconsis2) as Ha.
        pose proof (uskl_rsubst_ftag_sub Hrho2) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags2)) as Hc.
        clear - Ha Hb Hc; fsetdec. }

      assert (Hbs1 : Ψ1 [<=] Ψρ1 `union` (Ψ1 ∩ Ψ'1))
        by (clear - Hft1; fsetdec).
      assert (Hbs2 : Ψ2 [<=] Ψρ2 `union` (Ψ2 ∩ Ψ'2))
        by (clear - Hft2; fsetdec).
      assert (Hba1 : Ψ1 ∩ Ψ'1 [<=] Ψ1) by (clear; fsetdec).
      assert (Hba2 : Ψ2 ∩ Ψ'2 [<=] Ψ2) by (clear; fsetdec).
      assert (Hint1 : Ψρ1 ∩ Ψ'1 [=] empty)
        by (clear - Hinter HΨρs HΨ's; fsetdec).
      assert (Hint2 : Ψρ2 ∩ Ψ'2 [=] empty)
        by (clear - Hinter HΨρs HΨ's; fsetdec).
      assert (HΨaeq : Ψa [=] (Ψ1 ∩ Ψ'1)
                        `union` (Ψ2 ∩ Ψ'2)).
      { clear - Hsubeq1 Hsubeq2 H Hsub Hinter HΨρs HΨ's Hft1 Hft2; fsetdec. }

      assert (HψaB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr ->
                ftvar_in_uskl (uskl_arrow ψa1 ψa2)
                  [<=] dom Θr `union` Δρ).
      { intros HQB.
        assert (HftR : ftvar_in_uskl (uskl_arrow R1 R2) [<=]
                  ftvar_in_bskl (bskl_arrow Q1 Q2) `union` dom Θr)
          by (eapply consis_subject_ftv_bag_bound;
                [ eapply ad_pat_consis__arrow; eassumption
                | exact HspΘ | exact Htvs | exact HwfΘr ]).
        assert (HftA : ftvar_in_uskl (uskl_arrow ψa1 ψa2) [<=]
                  ftvar_in_uskl (uskl_arrow R1 R2) `union` Δρ).
        { apply uskl_rsubst_ftv_target_bound with (NM := NM) (Θ := Θ)
            (Ψρ := Ψρ).
          eapply ursubst__arrow; eassumption. }
        clear - HQB HftR HftA; fsetdec. }

      assert (VACR : {{ Θr ⨟ Δr ⊢ᵣ bskl_ghost ⊳ (bskl_arrow Q1 Q2) }}ad ->
                     Ψa [=] empty).
      { intros Hrh.
        pose proof (ad_refine_syn_ghost_sskl Hrh eq_refl
                      (lc_bskl_arrow _ _ (ad_pat_consis_target_lc Hconsis1 Hng1)
                                     (ad_pat_consis_target_lc Hconsis2 Hng2)))
          as Hss.
        assert (HskQ1 : is_sskl Q1) by (inversion Hss; subst; assumption).
        assert (HskQ2 : is_sskl Q2) by (inversion Hss; subst; assumption).
        assert (HΨ1e : Ψ1 [=] empty)
          by (eapply ad_pat_consis_sskl_tags; eassumption).
        assert (HΨ2e : Ψ2 [=] empty)
          by (eapply ad_pat_consis_sskl_tags; eassumption).
        clear - Hsubeq2 H HΨ1e HΨ2e; fsetdec. }
      assert (FLEXMONO : forall β,
        a_flex_tvar Θ0 β ->
        {{ Θr ⨟ Δr ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β)))
             ⊳ (bskl_arrow Q1 Q2) }}ad ->
        Ψa [=] empty /\
        (exists τa1 τa2, mono_ptyp τa1 /\ mono_ptyp τa2 /\
           ψa1 = ptyp_to_uskl_syn τa1 /\ ψa2 = ptyp_to_uskl_syn τa2 /\
           a_wf_ptyp Θ (ptyp_arrow τa1 τa2) /\
           ftvar_in_ptyp (ptyp_arrow τa1 τa2) [<=] dom Θw `union` Δ)).
      { intros β Hflxβ Hrefβ.
        assert (Hml : mono_ptyp (msubst_lookup κ β))
          by (eapply a_inc_lookup_mono; eauto).
        simpl in Hrefβ.
        rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefβ.
        assert (Hmi : bskl_monoish (bskl_arrow Q1 Q2))
          by (eapply ad_refine_mono_paint_rhs_monoish;
                [ exact HwfΘr | exact Hrefβ | reflexivity | exact Hml ]).
        assert (Hmi1 : bskl_monoish Q1) by (inversion Hmi; assumption).
        assert (Hmi2 : bskl_monoish Q2) by (inversion Hmi; assumption).

        assert (Htsk1 : is_dskl R1)
          by (eapply uskl_rsubst_is_dskl;
                [ exact Hrho1 | inversion Htags1; assumption ]).
        assert (Htsk2 : is_dskl R2)
          by (eapply uskl_rsubst_is_dskl;
                [ exact Hrho2 | inversion Htags2; assumption ]).
        destruct (ad_pat_consis_monoish_counterpart Hconsis1 HwfΘ Htsk1 Hmi1)
          as (HΨ1e & τ1' & Hm1' & HeqR1).
        destruct (ad_pat_consis_monoish_counterpart Hconsis2 HwfΘ Htsk2 Hmi2)
          as (HΨ2e & τ2' & Hm2' & HeqR2).

        destruct (uskl_rsubst_mono_target Hrho1 HeqR1 Hm1')
          as (τa1 & Heq1 & Hma1).
        destruct (uskl_rsubst_mono_target Hrho2 HeqR2 Hm2')
          as (τa2 & Heq2 & Hma2).
        assert (Hcons' : {{ Ψ ⨟ Θ ⊢ˢ (uskl_arrow R1 R2) ∼ (bskl_arrow Q1 Q2) }}ad)
          by (eapply ad_pat_consis__arrow; eassumption).
        assert (Hrefβ' : {{ Θ ⨟ empty ⊢ᵣ
                  (ptyp_to_bskl_syn (msubst_lookup κ β)) ⊳ (bskl_arrow Q1 Q2) }}ad)
          by (eapply refine_primary_to_plain_split; eassumption).

        assert (Hwfsub : a_wf_ptyp Θ (ptyp_arrow τ1' τ2')).
        { eapply ad_pat_consis_mono_subject_wf;
            [ exact Hcons' | rewrite HeqR1, HeqR2; reflexivity
            | apply mono_ptyp__arrow; assumption ]. }
        assert (Hdefw : forall α0 τ0, binds α0 (abind_flex_mono_def τ0) Θ ->
                  α0 `in` dom Θw /\ ftvar_in_ptyp τ0 [<=] dom Θw).
        { intros α0 τ0 Hb.
          pose proof (Hdefs _ _ Hb) as Hbw.
          split; [ eapply binds_In; exact Hbw
                 | eapply a_wf_aenv_def_ftv_dom; eassumption ]. }
        assert (HftQ : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θw).
        { eapply ad_refine_mono_paint_ftv_bound;
            [ exact HwfΘ | exact Hrefβ' | reflexivity | exact Hml
            | exact (Hκw β Hflxβ) | exact Hdefw ]. }
        assert (HftR : (ftvar_in_uskl R1) `union` (ftvar_in_uskl R2)
                       [<=] dom Θw).
        { pose proof (consis_subject_ftv_defs_bound Hcons' Hdefw) as Ht.
          cbn [ftvar_in_uskl ftvar_in_bskl] in Ht, HftQ.
          clear - Ht HftQ; fsetdec. }

        assert (Hftar : (ftvar_in_ptyp τa1) `union` (ftvar_in_ptyp τa2)
                        [<=] (ftvar_in_uskl R1) `union` (ftvar_in_uskl R2)
                             `union` Δρ).
        { pose proof (uskl_rsubst_ftv_target_bound
                        (ursubst__arrow Hrho1 Hrho2 HΨρs)) as Hb.
          rewrite Heq1, Heq2 in Hb.
          cbn [ftvar_in_uskl] in Hb.
          rewrite !ftvar_ptyp_to_uskl_syn in Hb.
          clear - Hb; fsetdec. }
        assert (Hwfar : a_wf_ptyp Θ (ptyp_arrow τa1 τa2)).
        { apply mono_ptyp_wf; [ apply mono_ptyp__arrow; assumption | ].
          intros α0 Hα0. cbn [ftvar_in_ptyp] in Hα0.
          destruct (mem α0 Δρ) eqn:Em;
            [ apply mem_iff in Em; rename Em into Hin
            | apply not_mem_iff in Em; rename Em into Hnin ].
          -
            destruct (Hfresh α0 Hin) as (Hb & _ & _). left; exact Hb.
          -
            eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfsub | ].
            assert (Hin' : α0 `in` (ftvar_in_uskl R1) `union`
                                   (ftvar_in_uskl R2))
              by (clear - Hftar Hα0 Hnin; fsetdec).
            rewrite HeqR1, HeqR2 in Hin'.
            rewrite !ftvar_ptyp_to_uskl_syn in Hin'.
            cbn [ftvar_in_ptyp]. clear - Hin'; fsetdec. }
        split; [ clear - Hsubeq2 H HΨ1e HΨ2e; fsetdec | ].
        exists τa1, τa2. repeat split; try assumption.
        cbn [ftvar_in_ptyp]. clear - Hftar HftR Hdelta; fsetdec. }

      assert (CORE : forall n Pi P0 Ψi,
        size_pskl Pi + size_pskl P0 <= n ->
        {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
        {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
        (forall α, α `in` Δρ ->
           α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
        {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_arrow ψa1 ψa2) }}ad ->
        {{ Θr ⨟ Δr ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0))
              ⊳ (bskl_arrow Q1 Q2) }}ad ->
        solve_eq_complete_var_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa (uskl_arrow ψa1 ψa2) Pi P0 Lav).
      { intros n; induction n as [ | n IHn ];
          intros Pi0 P00 Ψi0 Hn HwfPi0 HwfP00 Hapart0 Hpre1
            Hrefine1.
        { pose proof (size_pskl_min Pi0); pose proof (size_pskl_min P00);
          lia. }
        destruct Pi0 as [ | nb | β | Pi1 Pi2 | Pib | | Pi' ].
        -
          simpl in Hpre1. inversion Hpre1.
        -  inversion HwfPi0.
        -
          assert (HΨ'e : Ψ' [=] empty).
          { eapply ad_partial_precise_mono_subject_target_tags_empty
              with (τ := msubst_lookup κ β);
              [ exact HwfΘ | exact Hpre1 | reflexivity
              | eapply a_inc_lookup_mono; eauto
              | exact (a_tags_sort_d_tags Htags0) ]. }
          assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
          eapply solve_ext_nil with (Pa := (pskl_var_f β)); [ apply a_solve_eq__var | ].
          intros Δ' HS1 HS2 HS3.
          eapply ad_partial_precise_psi_cong;
            [ eapply ad_partial_precise_no_ghost_subject_delta_mono;
                [ exact Hpre1
                | apply msubst_pskl_no_ghost; simpl; exact I
                | clear; fsetdec ]
            | clear - HΨae; fsetdec ].
        -
          assert (HwfPi1 : {{ Θ0 ⨟ empty ⊢ₚₛ Pi1 }}a)
            by (inversion HwfPi0; assumption).
          assert (HwfPi2 : {{ Θ0 ⨟ empty ⊢ₚₛ Pi2 }}a)
            by (inversion HwfPi0; assumption).
          destruct P00 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          +
            simpl in Hrefine1. inversion Hrefine1.
          +  inversion HwfP00.
          +
            inversion HwfP00; subst;
            match goal with Hb : a_binds_tvar β _ |- _ =>
              rename Hb into Habt end.
            destruct Habt as [Hrig | Hflx].
            *
              exfalso.
              eapply refine_msubst_rigid_nonvar_absurd with (Θ0 := Θ0) (6 := Hrefine1); eauto.
              intros β0 Hcc; discriminate Hcc.
            *
              destruct (FLEXMONO β Hflx Hrefine1)
                as (HΨae
                    & (τa1 & τa2 & Hma1 & Hma2 & Heq1 & Heq2 & Hwfar
                       & Hftar)).
              assert (HΨie : Ψi0 [=] empty).
              { rewrite Heq1, Heq2 in Hpre1.
                eapply ad_ppre_mono_tags_empty
                  with (τ := ptyp_arrow τa1 τa2);
                  [ exact HwfΘ | exact Hpre1 | reflexivity
                  | apply mono_ptyp__arrow; assumption ]. }
              assert (Hmar : mono_ptyp (ptyp_arrow τa1 τa2))
                by (apply mono_ptyp__arrow; assumption).
              assert (Hpre1' : {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ (pskl_arrow Pi1 Pi2))
                        ⊑ᵖ[ Ψi0 ] (ptyp_to_uskl_syn (ptyp_arrow τa1 τa2)) }}ad).
              { change (ptyp_to_uskl_syn (ptyp_arrow τa1 τa2))
                  with (uskl_arrow (ptyp_to_uskl_syn τa1)
                                   (ptyp_to_uskl_syn τa2)).
                rewrite <- Heq1, <- Heq2. exact Hpre1. }
              destruct (@a_guess_ty_witness_mono_gen
                          (size_pskl (pskl_arrow Pi1 Pi2)) Θ0 Θ Θw κ Δ Ψi0
                          (ptyp_arrow τa1 τa2) (pskl_arrow Pi1 Pi2)
                          ltac:(reflexivity) HwfΘ HwfΘw Hmon Hdefs
                          HwfPi0 Hmar Hwfar Hftar Hpre1' Lav)
                as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
              exists Ξg, (ptyp_to_pskl Ag), κg.
              split; [ apply a_solve_eq__flex_r;
                         [ exact Hflx
                         | split; [ eapply a_wf_pskl_lc; exact HwfPi0
                                  | intros Hf; inversion Hf ]
                         | apply nonghost_pskl__arrow
                         | apply Hgu; exact HLav ] | ].
              split; [ exact Hfmg | ].
              split; [ exact Hug | ].
              split; [ exact Hkg | ].
              split; [ exact Hfrg | ].
              split; [ exact HFg | ].
              intros Δ' HS1 HS2 HS3.
              rewrite Heq1, Heq2.
              change (uskl_arrow (ptyp_to_uskl_syn τa1)
                                 (ptyp_to_uskl_syn τa2))
                with (ptyp_to_uskl_syn (ptyp_arrow τa1 τa2)).
              eapply ad_partial_precise_psi_cong;
                [ eapply ad_partial_precise_no_ghost_subject_delta_mono;
                    [ exact Hqg
                    | apply msubst_pskl_no_ghost; apply ptyp_to_pskl_no_ghost
                    | clear; fsetdec ]
                | clear - HΨie HΨae; fsetdec ].
          +
            assert (HwfP01 : {{ Θ0 ⨟ empty ⊢ₚₛ P01 }}a)
              by (inversion HwfP00; assumption).
            assert (HwfP02 : {{ Θ0 ⨟ empty ⊢ₚₛ P02 }}a)
              by (inversion HwfP00; assumption).
            simpl in Hrefine1.
            destruct (ad_refine_arrow_arrow_inv Hrefine1) as [Hrb1 Hrb2].
            simpl in Hpre1.
            destruct (ad_partial_precise_arrow_arrow_inv Hpre1)
              as (Ψib1 & Ψib2 & Hpb1 & Hpb2 & HΨis).
            assert (Hsubk1 : Ψib1 `union` (Ψ1 ∩ Ψ'1)
                               [<=] Ψ'1).
            { assert (Hts : Ψib1 [<=] Ψ'1)
                by (eapply ad_partial_precise_tags_sub;
                      [ exact HwfΘ | exact Hpb1
                      | exact (a_tags_sort_d_tags Htags1) ]).
              clear - Hts; fsetdec. }
            assert (Hsubk2 : Ψib2 `union` (Ψ2 ∩ Ψ'2)
                               [<=] Ψ'2).
            { assert (Hts : Ψib2 [<=] Ψ'2)
                by (eapply ad_partial_precise_tags_sub;
                      [ exact HwfΘ | exact Hpb2
                      | exact (a_tags_sort_d_tags Htags2) ]).
              clear - Hts; fsetdec. }
            assert (Hapart1 : forall α, α `in` Δρ ->
                      α `notin` pskl_shielded_ftv (msubst_pskl κ Pi1)).
            { intros α0 HX0; pose proof (Hapart0 α0 HX0) as Hs0;
              simpl in Hs0; clear - Hs0; fsetdec. }
            assert (Hapart2 : forall α, α `in` Δρ ->
                      α `notin` pskl_shielded_ftv (msubst_pskl κ Pi2)).
            { intros α0 HX0; pose proof (Hapart0 α0 HX0) as Hs0;
              simpl in Hs0; clear - Hs0; fsetdec. }
            destruct (IHHconsis1 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ1 Ψ'1 _ _
                        ψa1 Pi1 P01
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 Hmon Hnr HwfPi1 HwfP01 Hκ Hκw Hrho1 Htags1
                        Hsubk1 Hint1 Hfresh Hdelta Hapart1 Hdfresh Hpb1 Hbs1 Hba1 Hrb1
                        (Lav `union` ftvar_in_pskl Pi1
                           `union` ftvar_in_pskl Pi2
                           `union` ftvar_in_pskl P01
                           `union` ftvar_in_pskl P02)
                        ltac:(clear - HLav; solve_notin_auto))
              as (Ξ1 & Pa1 & κa & Hs1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hq1).
            destruct (IHHconsis2 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ2 Ψ'2 _ _
                        ψa2 Pi2 P02
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 Hmon Hnr HwfPi2 HwfP02 Hκ Hκw Hrho2 Htags2
                        Hsubk2 Hint2 Hfresh Hdelta Hapart2 Hdfresh Hpb2 Hbs2 Hba2 Hrb2
                        (Lav `union` ftvar_in_pskl Pi1
                           `union` ftvar_in_pskl Pi2
                           `union` ftvar_in_pskl P01
                           `union` ftvar_in_pskl P02
                           `union` dom Ξ1)
                        ltac:(clear - HLav; solve_notin_auto))
              as (Ξ2 & Pa2 & κb & Hs2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hq2).
            assert (Hdκa : dom κa [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).
            assert (Hdκb : dom κb [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
            assert (HPa1 : ftvar_in_pskl Pa1
                     [<=] ftvar_in_pskl Pi1 `union` ftvar_in_pskl P01
                            `union` dom Ξ1)
              by (eapply a_solve_eq_ftv; exact Hs1).
            assert (HPa2 : ftvar_in_pskl Pa2
                     [<=] ftvar_in_pskl Pi2 `union` ftvar_in_pskl P02
                            `union` dom Ξ2)
              by (eapply a_solve_eq_ftv; exact Hs2).
            assert (HΞ12 : forall x, x `in` dom Ξ1 -> x `notin` dom Ξ2).
            { intros x Hx Hc. specialize (Hfr2 x Hc). clear - Hfr2 Hx; fsetdec. }
            assert (Hdisj : disjoint Ξ2 Ξ1).
            { unfold disjoint. intros x Hx.
              assert (Hin1 : x `in` dom Ξ1) by (clear - Hx; fsetdec).
              specialize (HΞ12 x Hin1). clear - Hx HΞ12; fsetdec. }
            assert (Hs2' : {{ (Ξ1 ++ Θ0) ⊢ₑ Pi2 ∼ P02 ⤳ Ξ2 ⨾ Pa2 }}a).
            { eapply a_solve_eq_weaken_flex_block;
                [ exact Hs2 | exact Hfm1
                | intros x Hx; specialize (Hfr1 x Hx);
                  pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd;
                  clear - Hfr1 Hd HLav; fsetdec
                | intros x Hx; specialize (Hfr1 x Hx); clear - Hfr1; fsetdec
                | intros x Hx; pose proof (HΞ12 x Hx) as Hne;
                  specialize (Hfr1 x Hx); clear - Hfr1 Hne HPa2; fsetdec
                | exact HΞ12 ]. }
            assert (Heq1 : msubst_pskl (nil ++ κb ++ (κa ++ κ)) Pa1
                           = msubst_pskl (nil ++ (κa ++ κ)) Pa1).
            { apply msubst_pskl_mid_skip. intros x Hx.
              assert (Hin : x `in` dom Ξ2) by (clear - Hx Hdκb; fsetdec).
              specialize (Hfr2 x Hin). clear - Hfr2 HPa1; fsetdec. }
            cbn [app] in Heq1.
            assert (Heq2 : msubst_pskl (κb ++ κa ++ κ) Pa2
                           = msubst_pskl (κb ++ κ) Pa2).
            { apply msubst_pskl_mid_skip. intros x Hx.
              assert (Hin : x `in` dom Ξ1) by (clear - Hx Hdκa; fsetdec).
              pose proof (HΞ12 x Hin) as Hne.
              specialize (Hfr1 x Hin). clear - Hfr1 Hne HPa2; fsetdec. }
            exists (Ξ2 ++ Ξ1), (pskl_arrow Pa1 Pa2), (κb ++ κa).
            split; [ apply a_solve_eq__arrow; eassumption | ].
            split; [ apply all_flex_mono_app; assumption | ].
            split; [ clear - Hu1 Hu2 Hdisj; solve_uniq | ].
            split; [ rewrite ! keys_app; rewrite Hk1, Hk2; reflexivity | ].
            split; [ intros x Hx; rewrite dom_app in Hx;
                     destruct (union_1 Hx) as [Hin2 | Hin1];
                       [ specialize (Hfr2 x Hin2); clear - Hfr2; fsetdec
                       | specialize (Hfr1 x Hin1); clear - Hfr1; fsetdec ] | ].
            split; [ apply Forall_app; split; assumption | ].
            intros Δ' HS1 HS2 HS3.
            rewrite list_app_assoc. cbn [msubst_pskl].
            rewrite Heq1, Heq2.
            eapply ad_ppre__arrow;
              [ exact (Hq1 Δ' HS1 HS2 HS3) | exact (Hq2 Δ' HS1 HS2 HS3) | ].
            clear - HΨis HΨaeq; fsetdec.
          +
            simpl in Hrefine1. inversion Hrefine1.
          +
            simpl in Hrefine1.
            assert (HΨae : Ψa [=] empty) by (apply VACR; exact Hrefine1).
            assert (HQB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr).
            { eapply ghost_refine_target_ftv_dom_r;
                [ exact HspΘ | exact HΔrd | exact Hrefine1 | ].
              intros γ Hγ; simpl in Hγ.
              destruct (AtomSetImpl.union_1 Hγ) as [Hγ1 | Hγ2];
                [ exact (ad_pat_consis_target_binds Hconsis1 Hng1 Hγ1)
                | exact (ad_pat_consis_target_binds Hconsis2 Hng2 Hγ2) ]. }
            eapply solve_ext_nil with (Pa := (pskl_arrow Pi1 Pi2));
              [ apply a_solve_eq__ghost_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨae; fsetdec ].
          +
            assert (HwfP0' : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a)
              by (apply a_wf_pskl_univ_ghost_body; exact HwfP00).
            simpl in Hrefine1.
            inversion Hrefine1; subst.
            match goal with
            | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _ }}ad
              |- _ =>
              eapply solve_eq_complete_var_step;
                [ | exact (IHn (pskl_arrow Pi1 Pi2) P0' Ψi0
                             ltac:(simpl in Hn; simpl; lia)
                             HwfPi0 HwfP0' Hapart0
                             Hpre1 Hin) ]
            end.
            intros Ξ0 Pa0 Hs0. apply a_solve_eq__univ_ghost_r_guarded;
              [ apply guarded_pskl__arrow;
                  [ eapply a_wf_pskl_lc; exact HwfPi1
                  | eapply a_wf_pskl_lc; exact HwfPi2 ]
              | exact Hs0 ].
        -
          simpl in Hpre1. inversion Hpre1.
        -
          simpl in Hpre1.
          assert (HΨie : Ψi0 [=] empty) by (inversion Hpre1; assumption).
          assert (Hhd : Δ ∩
                    (ftvar_in_uskl (uskl_arrow ψa1 ψa2)) [=] empty)
            by (inversion Hpre1; assumption).
          simpl in Hhd.
          destruct P00 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          +
            simpl in Hrefine1. inversion Hrefine1.
          +  inversion HwfP00.
          +
            inversion HwfP00; subst;
            match goal with Hb : a_binds_tvar β _ |- _ =>
              rename Hb into Habt end.
            destruct Habt as [Hrig | Hflx].
            * exfalso.
              eapply refine_msubst_rigid_nonvar_absurd with (Θ0 := Θ0) (6 := Hrefine1); eauto.
              intros β0 Hcc; discriminate Hcc.
            *
              destruct (FLEXMONO β Hflx Hrefine1)
                as (HΨae & (τa1 & τa2 & Hma1 & Hma2 & Heq1 & Heq2 & _ & _)).
              destruct (uskl_rsubst_clean_eq Hrho1
                          ltac:(clear - Hhd Hdelta; fsetdec)) as [HeqR1 _].
              destruct (uskl_rsubst_clean_eq Hrho2
                          ltac:(clear - Hhd Hdelta; fsetdec)) as [HeqR2 _].
              assert (Hcons' : {{ Ψ ⨟ Θ ⊢ˢ (uskl_arrow ψa1 ψa2)
                                 ∼ (bskl_arrow Q1 Q2) }}ad)
                by (rewrite <- HeqR1, <- HeqR2;
                    eapply ad_pat_consis__arrow; eassumption).
              assert (Hml : mono_ptyp (msubst_lookup κ β))
                by (eapply a_inc_lookup_mono; eauto).
              assert (Hrefβ : {{ Θ ⨟ empty ⊢ᵣ (ptyp_to_bskl_syn (msubst_lookup κ β))
                                 ⊳ (bskl_arrow Q1 Q2) }}ad).
              { pose proof Hrefine1 as Hr. simpl in Hr.
                rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hr.
                eapply refine_primary_to_plain_split; eassumption. }
              eapply solve_ext_nil with (Pa := (pskl_var_f β)); [ apply a_solve_eq__ghost_l | ].
              intros Δ' HS1 HS2 HS3.
              assert (Hq : {{ Θ ⨟ (Δ `union` Δ') ⊢ˢ (msubst_pskl κ (pskl_var_f β))
                             ⊑ᵖ[ empty ] (uskl_arrow ψa1 ψa2) }}ad).
              { simpl. rewrite Heq1, Heq2.
                change (uskl_arrow (ptyp_to_uskl_syn τa1) (ptyp_to_uskl_syn τa2))
                  with (ptyp_to_uskl_syn (ptyp_arrow τa1 τa2)).
                eapply mono_paint_paint_refine_consis_partial_precise with (Δr := empty);
                  [ exact Hcons' | exact HwfΘ | rewrite Heq1, Heq2; reflexivity
                  | apply mono_ptyp__arrow; assumption
                  | clear; fsetdec | exact Hml | exact Hrefβ ]. }
              eapply ad_partial_precise_psi_cong;
                [ exact Hq | clear - HΨie HΨae; fsetdec ].
          +
            assert (HwfP01 : {{ Θ0 ⨟ empty ⊢ₚₛ P01 }}a)
              by (inversion HwfP00; assumption).
            assert (HwfP02 : {{ Θ0 ⨟ empty ⊢ₚₛ P02 }}a)
              by (inversion HwfP00; assumption).
            simpl in Hrefine1.
            destruct (ad_refine_arrow_arrow_inv Hrefine1) as [Hrb1 Hrb2].
            assert (Hp01 : {{ Θ ⨟ Δ ⊢ˢ msubst_pskl κ pskl_ghost
                             ⊑ᵖ[ empty ] ψa1 }}ad).
            { simpl. apply ad_ppre__ghost;
                [ clear; fsetdec | clear - Hhd; fsetdec ]. }
            assert (Hp02 : {{ Θ ⨟ Δ ⊢ˢ msubst_pskl κ pskl_ghost
                             ⊑ᵖ[ empty ] ψa2 }}ad).
            { simpl. apply ad_ppre__ghost;
                [ clear; fsetdec | clear - Hhd; fsetdec ]. }
            assert (Hsubk01 : empty `union` (Ψ1 ∩ Ψ'1)
                                [<=] Ψ'1) by (clear; fsetdec).
            assert (Hsubk02 : empty `union` (Ψ2 ∩ Ψ'2)
                                [<=] Ψ'2) by (clear; fsetdec).
            destruct (IHHconsis1 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ1 Ψ'1 _ _
                        ψa1 pskl_ghost P01
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 Hmon Hnr
                        ltac:(apply a_wf_pskl__ghost) HwfP01
                        Hκ Hκw
                        Hrho1 Htags1 Hsubk01 Hint1 Hfresh Hdelta
                        ltac:(intros α0 HX0; simpl; auto)
                        Hdfresh Hp01 Hbs1 Hba1 Hrb1 Lav HLav)
              as (Ξ1 & Pa1 & κa & Hs1 & _ & _ & Hk1 & _ & _ & Hq1).
            destruct (IHHconsis2 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ2 Ψ'2 _ _
                        ψa2 pskl_ghost P02
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 Hmon Hnr
                        ltac:(apply a_wf_pskl__ghost) HwfP02
                        Hκ Hκw
                        Hrho2 Htags2 Hsubk02 Hint2 Hfresh Hdelta
                        ltac:(intros α0 HX0; simpl; auto)
                        Hdfresh Hp02 Hbs2 Hba2 Hrb2 Lav HLav)
              as (Ξ2 & Pa2 & κb & Hs2 & _ & _ & Hk2 & _ & _ & Hq2).
            destruct (a_solve_eq_ghost_subject_inv Hs1) as [HΞ1e HPa1e].
            destruct (a_solve_eq_ghost_subject_inv Hs2) as [HΞ2e HPa2e].
            subst Ξ1 Pa1 Ξ2 Pa2.
            destruct κa as [ | ? ? ];
              [ | unfold keys in Hk1; simpl in Hk1; discriminate ].
            destruct κb as [ | ? ? ];
              [ | unfold keys in Hk2; simpl in Hk2; discriminate ].
            eapply solve_ext_nil with (Pa := (pskl_arrow P01 P02));
              [ apply a_solve_eq__ghost_l | ].
            intros Δ' HS1 HS2 HS3.
            cbn [app msubst_pskl]. eapply ad_ppre__arrow;
              [ exact (Hq1 Δ' HS1 HS2 HS3) | exact (Hq2 Δ' HS1 HS2 HS3) | ].
            clear - HΨie HΨaeq; fsetdec.
          +
            simpl in Hrefine1. inversion Hrefine1.
          +
            simpl in Hrefine1.
            assert (HΨae : Ψa [=] empty) by (apply VACR; exact Hrefine1).
            assert (HQB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr).
            { eapply ghost_refine_target_ftv_dom_r;
                [ exact HspΘ | exact HΔrd | exact Hrefine1 | ].
              intros γ Hγ; simpl in Hγ.
              destruct (AtomSetImpl.union_1 Hγ) as [Hγ1 | Hγ2];
                [ exact (ad_pat_consis_target_binds Hconsis1 Hng1 Hγ1)
                | exact (ad_pat_consis_target_binds Hconsis2 Hng2 Hγ2) ]. }
            eapply solve_ext_nil with (Pa := pskl_ghost); [ apply a_solve_eq__ghost_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨae; fsetdec ].
          +
            assert (HwfP0' : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a)
              by (apply a_wf_pskl_univ_ghost_body; exact HwfP00).
            simpl in Hrefine1.
            inversion Hrefine1; subst.
            match goal with
            | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _ }}ad
              |- _ =>
              destruct (IHn pskl_ghost P0' Ψi0
                          ltac:(simpl in Hn; simpl; lia)
                          ltac:(apply a_wf_pskl__ghost) HwfP0'
                          ltac:(intros α0 HX0; simpl; auto)
                          Hpre1 Hin)
                as (Ξ' & Pa' & κ' & Hs' & _ & _ & Hk' & _ & _ & Hq')
            end.
            destruct (a_solve_eq_ghost_subject_inv Hs') as [HΞ'e HPa'e].
            subst Ξ' Pa'.
            destruct κ' as [ | ? ? ];
              [ | unfold keys in Hk'; simpl in Hk'; discriminate ].
            eapply solve_ext_nil with (Pa := (pskl_univ_ghost P0'));
              [ apply a_solve_eq__ghost_l | ].
            intros Δ' HS1 HS2 HS3.
            cbn [app msubst_pskl]. apply ad_ppre__univ_ghost_remove.
            exact (Hq' Δ' HS1 HS2 HS3).
        -
          assert (HgPi' : guarded_pskl Pi')
            by (inversion HwfPi0; assumption).
          assert (HwfPi' : {{ Θ0 ⨟ empty ⊢ₚₛ Pi' }}a)
            by (apply a_wf_pskl_univ_ghost_body; exact HwfPi0).
          simpl in Hpre1.
          inversion Hpre1; subst.
          match goal with
          | Hp' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_arrow ψa1 ψa2 }}ad
            |- _ => rename Hp' into Hpre'
          end.
          assert (Hapart' : forall α, α `in` Δρ ->
                    α `notin` pskl_shielded_ftv (msubst_pskl κ Pi')).
          { intros α0 HX0.
            pose proof (Hapart0 α0 HX0) as Hsh0. simpl in Hsh0.
            pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi')).
            fsetdec. }
          destruct P00 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          +
            eapply solve_eq_complete_var_step;
              [ intros Ξ0 Pa0 Hs; apply a_solve_eq__univ_ghost_l_guarded;
                  [ apply guarded_pskl__unit | exact Hs ]
              | exact (IHn Pi' pskl_unit Ψi0
                        ltac:(simpl in Hn; simpl; lia)
                        HwfPi' HwfP00 Hapart' Hpre' Hrefine1) ].
          +  inversion HwfP00.
          +
            eapply solve_eq_complete_var_step;
              [ intros Ξ0 Pa0 Hs; apply a_solve_eq__univ_ghost_l_guarded;
                  [ apply guarded_pskl__var | exact Hs ]
              | exact (IHn Pi' (pskl_var_f β) Ψi0
                        ltac:(simpl in Hn; simpl; lia)
                        HwfPi' HwfP00 Hapart' Hpre' Hrefine1) ].
          +
            assert (HwfP01 : {{ Θ0 ⨟ empty ⊢ₚₛ P01 }}a)
              by (inversion HwfP00; assumption).
            assert (HwfP02 : {{ Θ0 ⨟ empty ⊢ₚₛ P02 }}a)
              by (inversion HwfP00; assumption).
            eapply solve_eq_complete_var_step;
              [ intros Ξ0 Pa0 Hs; apply a_solve_eq__univ_ghost_l_guarded;
                  [ apply guarded_pskl__arrow;
                      [ eapply a_wf_pskl_lc; exact HwfP01
                      | eapply a_wf_pskl_lc; exact HwfP02 ]
                  | exact Hs ]
              | exact (IHn Pi' (pskl_arrow P01 P02) Ψi0
                        ltac:(simpl in Hn; simpl; lia)
                        HwfPi' HwfP00 Hapart' Hpre' Hrefine1) ].
          +
            simpl in Hrefine1. inversion Hrefine1.
          +
            simpl in Hrefine1.
            assert (HΨae : Ψa [=] empty) by (apply VACR; exact Hrefine1).
            assert (HQB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr).
            { eapply ghost_refine_target_ftv_dom_r;
                [ exact HspΘ | exact HΔrd | exact Hrefine1 | ].
              intros γ Hγ; simpl in Hγ.
              destruct (AtomSetImpl.union_1 Hγ) as [Hγ1 | Hγ2];
                [ exact (ad_pat_consis_target_binds Hconsis1 Hng1 Hγ1)
                | exact (ad_pat_consis_target_binds Hconsis2 Hng2 Hγ2) ]. }
            eapply solve_ext_nil with (Pa := (pskl_univ_ghost Pi'));
              [ apply a_solve_eq__ghost_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨae; fsetdec ].
          +
            assert (HwfP0' : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a)
              by (apply a_wf_pskl_univ_ghost_body; exact HwfP00).
            simpl in Hrefine1.
            inversion Hrefine1; subst.
            match goal with
            | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _ }}ad
              |- _ =>
              apply (solve_eq_complete_var_univ_ghost_both
                       (IHn Pi' P0' Ψi0
                          ltac:(simpl in Hn; lia)
                          HwfPi' HwfP0' Hapart'
                          Hpre' Hin))
            end. }
      assert (Hsz : size_pskl Pi + size_pskl P0
                      <= size_pskl Pi + size_pskl P0) by lia.
      eapply CORE; eassumption. }
  -
    assert (HwfΘr2 := HwfΘr).
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hκ).
    assert (Himav : forall p, In p κ -> ftvar_in_ptyp (snd p) [<=] dom Θ)
      by (intros p Hp; eapply a_inc_image_ftv_dom; eassumption).
    destruct (uskl_rsubst_all_tag_cases Hrho Htags)
      as [Hleaf | (Lr & ψR & -> & Hrhof)].
    { destruct (@a_solve_eq_complete_rsubst_var _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec. }
    { rename Htags into Htags0, Hpre into Hpre0.
      destruct (a_tags_sort_all_tag_inv Htags0)
        as (Lt & Ψ0' & Htagsf & Hεnin & HΨ'eq).
      assert (HngR : uskl_no_ghost (uskl_all_tag ε R)).
      { pick fresh αf for (Lr `union` Lt). simpl.
        apply (uskl_no_ghost_open_inv R αf).
        eapply uskl_rsubst_no_ghost;
          [ apply Hrhof | apply Htagsf ]; clear - Fr; solve_notin. }

      assert (Hεa : ε `in` Ψa)
        by (clear - H1 Hsubeq1 Hinter HΨ'eq; fsetdec).

      assert (HbF : Ψ0 [<=] Ψρ `union` Ψ0').
      { pick fresh αf for (L `union` Lr `union` Lt).
        pose proof (ad_pat_consis_ftag_sub
                      (H αf ltac:(clear - Fr; solve_notin))) as Ha.
        pose proof (uskl_rsubst_ftag_sub
                      (Hrhof αf ltac:(clear - Fr; solve_notin))) as Hb.
        pose proof (d_tags_skl_ftag
                      (a_tags_sort_d_tags
                         (Htagsf αf ltac:(clear - Fr; solve_notin)))) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hsubeq1b : Ψ0 [<=] Ψρ `union` (remove ε Ψa))
        by (clear - H1 Hsubeq1 HbF Hεnin HΨ'eq Hinter; fsetdec).
      assert (Hsubeq2b : (remove ε Ψa) [<=] Ψ0)
        by (clear - H1 Hsubeq2; fsetdec).
      assert (Hintb : Ψρ ∩ Ψ0' [=] empty)
        by (clear - Hinter HΨ'eq; fsetdec).
      assert (Hdomsub : dom Θr [<=] dom Θ)
        by (eapply aenv_split_dom_r; exact HspΘ).

      destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
      -  simpl in Hrefine. inversion Hrefine.
      -  inversion HwfP0.
      -
        exfalso.
        assert (Habt : a_binds_tvar β Θ0)
          by (inversion HwfP0; subst; assumption).
        destruct Habt as [Hrig | Hflx].
        + eapply refine_msubst_rigid_nonvar_absurd with (Θ0 := Θ0) (6 := Hrefine); eauto.
          intros β0 Hcc; discriminate Hcc.
        + assert (Hml : mono_ptyp (msubst_lookup κ β))
            by (eapply a_inc_lookup_mono; eauto).
          simpl in Hrefine.
          rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
          eapply ad_refine_mono_paint_allinh_rhs_absurd;
            [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
            | exact Hml ].
      -  simpl in Hrefine. inversion Hrefine.
      -
        destruct (a_wf_pskl_all_inv_empty HwfP0) as (Lw0 & HwfP0f).
        assert (Hreff : exists Lq, forall α, α `notin` Lq ->
          {{ Θr ⨟ (add α Δr) ⊢ᵣ
            pskl_to_bskl_inh (msubst_pskl κ
              (open_pskl_wrt_pskl P0b (pskl_var_f α)))
            ⊳ open_bskl_wrt_bskl Q (bskl_var_f α) }}ad).
        { simpl in Hrefine.
          inversion Hrefine; subst.
          match goal with
          | Hf : forall α0, α0 `notin` ?L0 -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
            exists (L0 `union` dom κ); intros α0 Hα0;
            rewrite msubst_pskl_open_lc;
              [ | exact Hlcκ | clear - Hα0; fsetdec ];
            rewrite pskl_to_bskl_inh_open;
            eapply ad_refine_syn_defs_mono;
              [ apply Hf; clear - Hα0; fsetdec
              | intros β τ Hb;
                destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
                [ discriminate | exact Hb' ] ]
          end. }
        destruct Hreff as (Lq & Hreff).

        assert (IHX : forall α Pi0 Ψi0 Δx,
          α `notin` (L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b) ->
          Δρ [<=] Δx -> Δx [<=] add α Δ ->
          {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ Pi0 }}a ->
          (forall α0, α0 `in` Δρ ->
             α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi0)) ->
          {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δx ⊢ˢ (msubst_pskl κ Pi0)
              ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψR (uskl_var_f α)) }}ad ->
          Ψi0 [<=] Ψ0' ->
          exists Ξ0 Pa0 κ0,
            {{ ((α ~ abind_tvar) ++ Θ0) ⊢ₑ Pi0 ∼
               (open_pskl_wrt_pskl P0b (pskl_var_f α)) ⤳ Ξ0 ⨾ Pa0 }}a /\
            all_flex_mono Ξ0 /\
            uniq Ξ0 /\
            keys κ0 = keys Ξ0 /\
            (forall α0, α0 `in` dom Ξ0 -> α0 `notin` (add α Lav)) /\
            Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ0 /\
            forall Δ', Δ' ∩ Δx [=] empty ->
              Δ' ∩ dom Θr [=] empty ->
              delta_def_fresh Δ' ((α ~ abind_tvar) ++ Θ) ->
              {{ ((α ~ abind_tvar) ++ Θ) ⨟ (Δx `union` Δ')
                ⊢ˢ (msubst_pskl (κ0 ++ κ) Pa0)
                  ⊑ᵖ[ Ψi0 `union` (remove ε Ψa) ]
                  (open_uskl_wrt_uskl ψR (uskl_var_f α)) }}ad).
        { intros α Pi0 Ψi0 Δx HXf HΔρx HΔxs HwfPi0 Hapart0 Hpre0x HΨi0s.
          assert (HαΘ : α `notin` dom Θ) by (clear - HXf; solve_notin).
          destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HαΘ)
            as (_ & Hmonα & Hnrα & Hκwα).
          apply (H0 α ltac:(clear - HXf; solve_notin)
                   NM ((α ~ abind_tvar) ++ Θ0)
                   ((α ~ abind_tvar) ++ Θtv) Θr Θ0r κ
                   Δx Δρ (add α Δr) Ψρ Ψ0' Ψi0 (remove ε Ψa)
                   (open_uskl_wrt_uskl ψR (uskl_var_f α))
                   Pi0 (open_pskl_wrt_pskl P0b (pskl_var_f α)));
            try assumption.
          - apply aenv_split_cons_tv; [ exact HspΘ | clear - HXf; solve_notin ].
          - apply aenv_split_cons_tv; [ exact HspΘ0 | clear - HXf; solve_notin ].
          - intros x b Hb.
            destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
              [ exact Heqb | exact (Htvs _ _ Hb') ].
          - simpl. clear - HΔrd; fsetdec.
          - simpl. clear - HΔρtv HXf; destruct_notin; fsetdec.
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ ].
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ0 ].
          - apply HwfP0f. clear - HXf; solve_notin.
          - apply a_inc__tvar with (Ξ := (@nil (atom * abind)));
              [ exact Hκ | apply a_suffix__nil ].
          - eapply uskl_rsubst_weaken;
              [ apply Hrhof; clear - HXf; solve_notin
              | intros x b Hb; apply binds_cons_3; exact Hb ].
          - apply Htagsf. clear - HXf; solve_notin.
          - clear - HΨi0s Hsub HΨ'eq; fsetdec.
          - apply rsubst_fresh_weaken_tvar; exact Hfresh.
          - intros Yd αd τ HYd Hbd.
            eapply (@delta_def_fresh_open_tvar Δ Θ α);
              [ exact HwfΘ | clear - HXf; solve_notin | exact Hdfresh
              | apply HΔxs; exact HYd | exact Hbd ].
          - apply Hreff. clear - HXf; solve_notin.
          - rewrite ftvar_in_aenv_cons_tvar. clear - HLav; fsetdec. }

        destruct Pi as [ | nb | β | Pi1 Pi2 | Pib | | Pi' ].
        +  simpl in Hpre0. inversion Hpre0.
        +  inversion HwfPi.
        +
          exfalso.
          assert (HΨ'e : Ψ' [=] empty).
          { eapply ad_partial_precise_mono_subject_target_tags_empty
              with (τ := msubst_lookup κ β);
              [ exact HwfΘ | exact Hpre0 | reflexivity
              | eapply a_inc_lookup_mono; eauto
              | exact (a_tags_sort_d_tags Htags0) ]. }
          assert (Hcon : ε `in` empty).
          { apply (proj1 (HΨ'e ε)). apply (proj2 (HΨ'eq ε)).
            clear; fsetdec. }
          clear - Hcon; fsetdec.
        +  simpl in Hpre0. inversion Hpre0.
        +
          destruct (a_wf_pskl_all_inv_empty HwfPi) as (Lwi & HwfPif).
          destruct (ad_partial_precise_msubst_all_tag_inv HwfΘ Hlcκ Htagsf Hpre0)
            as (Lp & Ψi' & HpreF & HΨis & HΨi's).
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
               `union` Lwi `union` Lp `union` ftvar_in_pskl Pib).
          destruct (IHX α (open_pskl_wrt_pskl Pib (pskl_var_f α)) Ψi'
                      (add α Δ)
                      ltac:(clear - Fr; solve_notin)
                      ltac:(clear - Hdelta; solve_notin_auto)
                      ltac:(clear; solve_notin_auto)
                      (HwfPif α ltac:(clear - Fr; solve_notin))
                      ltac:(intros α0 HX0;
                            pose proof (Hapart α0 HX0) as Hs0;
                            simpl in Hs0;
                            rewrite msubst_pskl_open_lc;
                              [ | exact Hlcκ | clear - Fr; solve_notin ];
                            pose proof (pskl_shielded_ftv_open_upper
                              (msubst_pskl κ Pib) (pskl_var_f α)) as Hup;
                            simpl in Hup;
                            assert (HneX0 : α0 <> α)
                              by (clear - HX0 Fr; destruct_notin; fsetdec);
                            clear - Hs0 Hup HneX0; fsetdec)
                      ltac:(eapply ad_partial_precise_weaken;
                              [ apply HpreF; clear - Fr; solve_notin
                              | intros x b Hb; apply binds_cons_3;
                                exact Hb ])
                      HΨi's)
            as (ΞX & PaX & κX & HsX & HfmX & HuX & HkX & HfrX & HFX & HqX).
          assert (HαΞ : α `notin` dom ΞX)
            by (intros Hin; exact (HfrX α Hin ltac:(clear; solve_notin_auto))).
          assert (HdκX : dom κX [=] dom ΞX) by (apply keys_eq_dom; exact HkX).
          assert (HlcκX : msubst_lc (κX ++ κ))
            by (eapply msubst_lc_app_wf; eassumption).
          exists ΞX, (pskl_all_syn (close_pskl_wrt_pskl α PaX)), κX.
          split.
          {
            apply a_solve_eq__forall with (β := α);
              [ clear - Fr; solve_notin | exact HsX ]. }
          split; [ exact HfmX | ].
          split; [ exact HuX | ].
          split; [ exact HkX | ].
          split; [ intros α0 Hα0; pose proof (HfrX α0 Hα0) as Hn;
                   clear - Hn; fsetdec | ].
          split; [ exact HFX | ].
          intros Δ' HS1 HS2 HS3.
          simpl.
          assert (Hrun : {{ ((α ~ abind_tvar) ++ Θ) ⨟
                    (add α (Δ `union` (remove α Δ'))) ⊢ˢ
                    (msubst_pskl (κX ++ κ) PaX)
                    ⊑ᵖ[ Ψi' `union` (remove ε Ψa) ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α)) }}ad).
          { eapply ad_partial_precise_delta_cong;
              [ apply (HqX (remove α Δ'));
                [ clear - HS1; destruct_notin; fsetdec
                | simpl; clear - HS2; fsetdec
                | intros Yd αd τ HYd Hbd;
                  destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                    as [[_ Hc] | Hbd']; [ discriminate Hc | ];
                  eapply HS3; [ clear - HYd; fsetdec | exact Hbd' ] ]
              | clear; fsetdec ]. }
          eapply ad_partial_precise_forall_close
            with (1 := HwfΘ) (2 := Himav) (3 := HFX) (4 := Hmon) (5 := HlcκX)
                 (8 := Hrun).
          { clear - Fr HαΞ HdκX; destruct_notin; solve_notin_auto. }
          { clear - HΨis Hεa; fsetdec. }
        +
          assert (HΨie : Ψi [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          assert (Hhd : Δ ∩
                    (ftvar_in_uskl (uskl_all_tag ε ψR)) [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          simpl in Hhd.
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b).
          assert (Hp0X : {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ˢ
                    (msubst_pskl κ pskl_ghost) ⊑ᵖ[ empty ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α)) }}ad).
          { simpl. apply ad_ppre__ghost; [ clear; fsetdec | ].
            pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                          (uskl_var_f α)) as Hup.
            simpl in Hup. clear - Hhd Hup Fr; destruct_notin; fsetdec. }
          eapply solve_ext_nil with (Pa := (pskl_all_syn P0b));
            [ apply a_solve_eq__ghost_l | ].
          intros Δ' HS1 HS2 HS3.
          simpl.
          apply ad_ppre__forall with
            (L := L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b `union` Δ')
            (Ψ0 := empty `union` (remove ε Ψa));
            [ | clear - HΨie Hεa; fsetdec ].
          intros α' HX'.
          rewrite <- msubst_pskl_open_lc;
            [ | exact Hlcκ | clear - HX'; solve_notin ].
          assert (Hp0X' : {{ ((α' ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ˢ
                    (msubst_pskl κ pskl_ghost) ⊑ᵖ[ empty ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α')) }}ad).
          { simpl. apply ad_ppre__ghost; [ clear; fsetdec | ].
            pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                          (uskl_var_f α')) as Hup.
            simpl in Hup. clear - Hhd Hup HX'; destruct_notin; fsetdec. }
          destruct (IHX α' pskl_ghost empty Δ
                      ltac:(clear - HX'; solve_notin)
                      Hdelta
                      ltac:(clear; solve_notin_auto)
                      ltac:(apply a_wf_pskl__ghost)
                      ltac:(intros α0 HX0; simpl; auto)
                      Hp0X'
                      ltac:(clear; solve_notin_auto))
            as (Ξ0 & Pa0 & κ0 & Hs0 & _ & _ & Hk0 & _ & _ & Hq0).
          destruct (a_solve_eq_ghost_subject_inv Hs0) as [HΞ0e HPa0]; subst.
          destruct κ0 as [ | ? ? ];
            [ | unfold keys in Hk0; simpl in Hk0; discriminate ].
          cbn [app] in Hq0.
          assert (HqS : {{ ((α' ~ abind_tvar) ++ Θ) ⨟
                    (Δ `union` (add α' Δ')) ⊢ˢ
                    (msubst_pskl κ (open_pskl_wrt_pskl P0b (pskl_var_f α')))
                    ⊑ᵖ[ empty `union` (remove ε Ψa) ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α')) }}ad).
          { apply (Hq0 (add α' Δ')).
            - clear - HS1 HX'; destruct_notin; fsetdec.
            - clear - HS2 HX' Hdomsub; destruct_notin; fsetdec.
            - intros Yd αd τ HYd Hbd.
              destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
                [ discriminate Hc | ].
              destruct (Yd == α') as [-> | Hne].
              + assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                  by (eapply a_wf_aenv_def_ftv_dom; eassumption).
                clear - Hd HX'; destruct_notin; fsetdec.
              + eapply HS3; [ clear - HYd Hne; fsetdec | exact Hbd' ]. }
          eapply ad_partial_precise_delta_cong;
            [ exact HqS
            | clear; fsetdec ].
        +
          assert (Hg : guarded_pskl Pi' /\ ({{ Θ0 ⨟ empty ⊢ₚₛ Pi' }}a))
            by (split; [ inversion HwfPi; assumption | apply a_wf_pskl_univ_ghost_body; exact HwfPi ]).
          destruct Hg as [HgPi' HwfPi'].
          assert (Hdisj :
            ({{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ]
               (uskl_all_tag ε ψR) }}ad) \/
            (exists Lf, forall α, α `notin` Lf ->
               {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ˢ
                 pskl_univ_ghost (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ]
                 (open_uskl_wrt_uskl ψR (uskl_var_f α)) }}ad)).
          { simpl in Hpre0. inversion Hpre0; subst;
              [ left; assumption | right; eexists; eassumption ]. }
          destruct Hdisj as [Hrem | (Lf & HF)].
          *
            exfalso.
            inversion HgPi'; subst.
            -- simpl in Hrem. inversion Hrem.
            -- assert (HΨ'e : Ψ' [=] empty).
               { eapply ad_partial_precise_mono_subject_target_tags_empty
                   with (τ := msubst_lookup κ α);
                   [ exact HwfΘ | exact Hrem | reflexivity
                   | eapply a_inc_lookup_mono; eauto
                   | exact (a_tags_sort_d_tags Htags0) ]. }
               assert (Hcon : ε `in` empty).
          { apply (proj1 (HΨ'e ε)). apply (proj2 (HΨ'eq ε)).
            clear; fsetdec. }
          clear - Hcon; fsetdec.
            -- simpl in Hrem. inversion Hrem.
          *
            assert (HΨiS : Ψi [<=] Ψ0').
            { pick fresh αp for (Lf `union` Lt `union` dom Θ).
              assert (HwfΘx : {{ ⊢ ((αp ~ abind_tvar) ++ Θ) }}a)
                by (apply a_wf_aenv__tvar;
                    [ clear - Fr; solve_notin | exact HwfΘ ]).
              eapply ad_partial_precise_tags_sub;
                [ exact HwfΘx
                | apply HF; clear - Fr; solve_notin
                | exact (a_tags_sort_d_tags
                          (Htagsf αp ltac:(clear - Fr; solve_notin))) ]. }
            pick fresh α for
              (L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
                 `union` Lf `union` ftvar_in_pskl Pi').
            destruct (IHX α (pskl_univ_ghost Pi') Ψi Δ
                        ltac:(clear - Fr; solve_notin)
                        Hdelta
                        ltac:(clear; solve_notin_auto)
                        ltac:(eapply a_wf_pskl_weaken;
                              [ intros x b Hb; apply binds_cons_3;
                                exact Hb
                              | exact HwfPi ])
                        Hapart
                        (HF α ltac:(clear - Fr; solve_notin))
                        HΨiS)
              as (ΞX & PaX & κX & HsX & HfmX & HuX & HkX & HfrX & HFX & HqX).
            assert (HαΞ : α `notin` dom ΞX)
              by (intros Hin; exact (HfrX α Hin ltac:(clear; solve_notin_auto))).
            assert (HdκX : dom κX [=] dom ΞX) by (apply keys_eq_dom; exact HkX).
            assert (HlcκX : msubst_lc (κX ++ κ))
              by (eapply msubst_lc_app_wf; eassumption).
            exists ΞX, (pskl_all_syn (close_pskl_wrt_pskl α PaX)), κX.
            split.
            {
              apply a_solve_eq__univ_ghost_l_all with (β := α);
                [ clear - Fr; solve_notin | exact HsX ]. }
            split; [ exact HfmX | ].
            split; [ exact HuX | ].
            split; [ exact HkX | ].
            split; [ intros α0 Hα0; pose proof (HfrX α0 Hα0) as Hn;
                     clear - Hn; fsetdec | ].
            split; [ exact HFX | ].
            intros Δ' HS1 HS2 HS3.
            simpl.
            assert (Hrun : {{ ((α ~ abind_tvar) ++ Θ) ⨟
                      (add α (Δ `union` (remove α Δ'))) ⊢ˢ
                      (msubst_pskl (κX ++ κ) PaX)
                      ⊑ᵖ[ Ψi `union` (remove ε Ψa) ]
                      (open_uskl_wrt_uskl ψR (uskl_var_f α)) }}ad).
            { eapply ad_partial_precise_delta_cong;
                [ apply (HqX (add α Δ'));
                  [ clear - HS1 Fr; destruct_notin; fsetdec
                  | clear - HS2 Fr Hdomsub; destruct_notin; fsetdec
                  | intros Yd αd τ HYd Hbd;
                    destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                      as [[_ Hc] | Hbd']; [ discriminate Hc | ];
                    destruct (Yd == α) as [-> | Hne];
                    [ assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                        by (eapply a_wf_aenv_def_ftv_dom; eassumption);
                      clear - Hd Fr; destruct_notin; fsetdec
                    | eapply HS3;
                      [ clear - HYd Hne; fsetdec | exact Hbd' ] ] ]
                | clear; fsetdec ]. }
            eapply ad_partial_precise_forall_close
              with (1 := HwfΘ) (2 := Himav) (3 := HFX) (4 := Hmon) (5 := HlcκX)
                   (8 := Hrun).
            { clear - Fr HαΞ HdκX; destruct_notin; solve_notin_auto. }
            { clear - Hεa; fsetdec. }
      -
        exfalso.
        simpl in Hrefine.
        inversion Hrefine; subst.
        match goal with
        | Heq : pskl_to_bskl_syn ?P = bskl_all_inh _ |- _ =>
          destruct P; simpl in Heq; discriminate Heq
        | Heq : bskl_all_inh _ = pskl_to_bskl_syn ?P |- _ =>
          destruct P; simpl in Heq; discriminate Heq
        end.
      -
        exfalso.
        assert (Hg : guarded_pskl P0' /\ ({{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a)).
        { split; [ inversion HwfP0; assumption
                 | apply a_wf_pskl_univ_ghost_body; exact HwfP0 ]. }
        destruct Hg as [HgP0' HwfP0'].
        simpl in Hrefine.
        inversion Hrefine; subst.
        inversion HgP0'; subst.
        + match goal with
          | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ }}ad
            |- _ => simpl in Hin; inversion Hin
          end.
        +
          match goal with
          | Hwv : {{ _ ⨟ _ ⊢ₚₛ pskl_var_f ?v }}a,
            Hin : {{ _ ⨟ _ ⊢ᵣ
              pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _ }}ad |- _ =>
            assert (Habt : a_binds_tvar v Θ0)
              by (inversion Hwv; subst; assumption);
            destruct Habt as [Hrig | Hflx];
            [ eapply refine_msubst_rigid_nonvar_absurd with (Θ0 := Θ0) (6 := Hin); eauto;
              intros β0 Hcc; discriminate Hcc
            | let Hml := fresh in
              assert (Hml : mono_ptyp (msubst_lookup κ v))
                by (eapply a_inc_lookup_mono; eauto);
              simpl in Hin;
              rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
              eapply ad_refine_mono_paint_allinh_rhs_absurd;
                [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                | exact Hml ] ]
          end.
        + match goal with
          | Hin : {{ _ ⨟ _ ⊢ᵣ
              pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _ }}ad
            |- _ => simpl in Hin; inversion Hin
          end. }
  -
    destruct (uskl_rsubst_all_syn_l_inv Hrho)
      as [[-> _] | [Hleaf | (L' & R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  -
    assert (HwfΘr2 := HwfΘr).
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hκ).
    assert (Himav : forall p, In p κ -> ftvar_in_ptyp (snd p) [<=] dom Θ)
      by (intros p Hp; eapply a_inc_image_ftv_dom; eassumption).
    destruct (uskl_rsubst_all_tag_cases Hrho Htags)
      as [Hleaf | (Lr & ψR & -> & Hrhof)].
    { destruct (@a_solve_eq_complete_rsubst_var _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec. }
    { rename Htags into Htags0, Hpre into Hpre0.
      destruct (a_tags_sort_all_tag_inv Htags0)
        as (Lt & Ψ0' & Htagsf & Hεnin & HΨ'eq).
      assert (HngR : uskl_no_ghost (uskl_all_tag ε R)).
      { pick fresh αf for (Lr `union` Lt). simpl.
        apply (uskl_no_ghost_open_inv R αf).
        eapply uskl_rsubst_no_ghost;
          [ apply Hrhof | apply Htagsf ]; clear - Fr; solve_notin. }
      assert (Hdomsub : dom Θr [<=] dom Θ)
        by (eapply aenv_split_dom_r; exact HspΘ).

      assert (HbF : Ψ [<=] Ψρ `union` Ψ0').
      { pick fresh αf for (L `union` Lr `union` Lt).
        pose proof (ad_pat_consis_ftag_sub
                      (H αf ltac:(clear - Fr; solve_notin))) as Ha.
        pose proof (uskl_rsubst_ftag_sub
                      (Hrhof αf ltac:(clear - Fr; solve_notin))) as Hb.
        pose proof (d_tags_skl_ftag
                      (a_tags_sort_d_tags
                         (Htagsf αf ltac:(clear - Fr; solve_notin)))) as Hc.
        clear - Ha Hb Hc; fsetdec. }

      assert (HΨaΨ0' : Ψa [<=] Ψ0')
        by (clear - Hsubeq2 HbF Hinter HΨ'eq Hsub; fsetdec).
      assert (Hintb : Ψρ ∩ Ψ0' [=] empty)
        by (clear - Hinter HΨ'eq; fsetdec).

      assert (Hrhow : uskl_rsubst NM Θ Δρ Ψρ (uskl_all_tag ε R)
                        (uskl_all_tag ε ψR))
        by (eapply ursubst__all_tag with (L := Lr); exact Hrhof).
      assert (HψaB : ftvar_in_bskl Q [<=] dom Θr ->
                ftvar_in_uskl (uskl_all_tag ε ψR) [<=] dom Θr `union` Δρ).
      { intros HQB.
        assert (HftR : ftvar_in_uskl (uskl_all_tag ε R) [<=]
                  ftvar_in_bskl (bskl_all_syn Q) `union` dom Θr)
          by (eapply consis_subject_ftv_bag_bound;
                [ eapply ad_pat_consis__forall_syn_tagged; exact H
                | exact HspΘ | exact Htvs | exact HwfΘr ]).
        pose proof (uskl_rsubst_ftv_target_bound Hrhow) as HftA.
        simpl in *. clear - HQB HftR HftA; fsetdec. }

      destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
      -  simpl in Hrefine. inversion Hrefine.
      -  inversion HwfP0.
      -
        exfalso.
        assert (Habt : a_binds_tvar β Θ0)
          by (inversion HwfP0; subst; assumption).
        destruct Habt as [Hrig | Hflx].
        + eapply refine_msubst_rigid_nonvar_absurd with (Θ0 := Θ0) (6 := Hrefine); eauto.
          intros β0 Hcc; discriminate Hcc.
        + assert (Hml : mono_ptyp (msubst_lookup κ β))
            by (eapply a_inc_lookup_mono; eauto).
          simpl in Hrefine.
          rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
          eapply ad_refine_mono_paint_allsyn_rhs_absurd;
            [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
            | exact Hml ].
      -  simpl in Hrefine. inversion Hrefine.
      -
        exfalso. simpl in Hrefine. inversion Hrefine.
      -
        simpl in Hrefine.
        pose proof (ad_refine_syn_ghost_sskl Hrefine eq_refl
                      ltac:(eapply ad_pat_consis_target_lc;
                            [ eapply ad_pat_consis__forall_syn_tagged
                                with (ε := ε); exact H
                            | exact HngR ]))
          as Hss.
        assert (HΨe : Ψ [=] empty).
        { eapply ad_pat_consis_sskl_tags;
            [ eapply ad_pat_consis__forall_syn_tagged; exact H
            | exact HwfΘ | exact Hss ]. }
        assert (HΨae : Ψa [=] empty) by (clear - Hsubeq2 HΨe; fsetdec).
        assert (HQB : ftvar_in_bskl Q [<=] dom Θr).
        { assert (Ht : ftvar_in_bskl (bskl_all_syn Q) [<=] dom Θr).
          { eapply ghost_refine_target_ftv_dom_r;
              [ exact HspΘ | exact HΔrd | exact Hrefine | ].
            eapply ad_pat_consis_target_binds;
              [ eapply ad_pat_consis__forall_syn_tagged with (ε := ε); exact H
              | exact HngR ]. }
          simpl in Ht; exact Ht. }
        eapply solve_ext_nil with (Pa := Pi); [ apply a_solve_eq__ghost_r | ].
        intros Δ' HS1 HS2 HS3.
        eapply ad_partial_precise_psi_cong;
          [ eapply ad_partial_precise_delta_weaken_fresh;
              [ exact Hpre0
              | pose proof (HψaB HQB) as Hbb;
                clear - Hbb HS1 HS2 Hdelta; fsetdec
              | exact HS3 ]
          | clear - HΨae; fsetdec ].
      -
        assert (HgP0' : guarded_pskl P0') by (inversion HwfP0; assumption).
        assert (HwfP0'0 : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a)
          by (apply a_wf_pskl_univ_ghost_body; exact HwfP0).
        simpl in Hrefine.
        assert (Hrefb : exists Lq, forall α, α `notin` Lq ->
          {{ ((α ~ abind_tvar) ++ Θr) ⨟ Δr ⊢ᵣ
            (bskl_univ_ghost (pskl_to_bskl_inh (msubst_pskl κ P0')))
            ⊳ open_bskl_wrt_bskl Q (bskl_var_f α) }}ad).
        { inversion Hrefine; subst.
          -
            exfalso. inversion HgP0'; subst.
            + match goal with
              | Hin : {{ _ ⨟ _ ⊢ᵣ
                  pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ }}ad |- _ =>
                simpl in Hin; inversion Hin
              end.
            + match goal with
              | Hin : {{ _ ⨟ _ ⊢ᵣ
                  pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _ }}ad |- _ =>
                let Hml := fresh in
                assert (Hml : mono_ptyp (msubst_lookup κ v))
                  by (eapply a_inc_lookup_mono; eauto);
                simpl in Hin;
                rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
                eapply ad_refine_mono_paint_allsyn_rhs_absurd;
                  [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                  | exact Hml ]
              end.
            + match goal with
              | Hin : {{ _ ⨟ _ ⊢ᵣ
                  pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _ }}ad |- _ =>
                simpl in Hin; inversion Hin
              end.
          -
            rename H6 into Hfill; rename L0 into Lfill.
            exists Lfill; exact Hfill. }
        destruct Hrefb as (Lrb & Hrefb).
        assert (IHX : forall α0 Pi0 Ψi0 P0i Δx,
          α0 `notin` (L `union` Lr `union` Lt `union` Lrb
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0') ->
          Δρ [<=] Δx -> Δx [<=] add α0 Δ ->
          {{ ((α0 ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ Pi0 }}a ->
          {{ ((α0 ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ P0i }}a ->
          (forall α00, α00 `in` Δρ ->
             α00 `notin` pskl_shielded_ftv (msubst_pskl κ Pi0)) ->
          {{ ((α0 ~ abind_tvar) ++ Θ) ⨟ Δx ⊢ˢ (msubst_pskl κ Pi0)
              ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψR (uskl_var_f α0)) }}ad ->
          Ψi0 [<=] Ψ0' ->
          {{ ((α0 ~ abind_tvar) ++ Θr) ⨟ Δr ⊢ᵣ
             (pskl_to_bskl_inh (msubst_pskl κ P0i))
             ⊳ open_bskl_wrt_bskl Q (bskl_var_f α0) }}ad ->
          exists Ξ0 Pa0 κ0,
            {{ ((α0 ~ abind_tvar) ++ Θ0) ⊢ₑ Pi0 ∼ P0i ⤳ Ξ0 ⨾ Pa0 }}a /\
            all_flex_mono Ξ0 /\
            uniq Ξ0 /\
            keys κ0 = keys Ξ0 /\
            (forall α00, α00 `in` dom Ξ0 -> α00 `notin` (add α0 Lav)) /\
            Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ0 /\
            forall Δ', Δ' ∩ Δx [=] empty ->
              Δ' ∩ (dom ((α0 ~ abind_tvar) ++ Θr)) [=] empty ->
              delta_def_fresh Δ' ((α0 ~ abind_tvar) ++ Θ) ->
              {{ ((α0 ~ abind_tvar) ++ Θ) ⨟ (Δx `union` Δ')
                ⊢ˢ (msubst_pskl (κ0 ++ κ) Pa0)
                  ⊑ᵖ[ Ψi0 `union` Ψa ]
                  (open_uskl_wrt_uskl ψR (uskl_var_f α0)) }}ad).
        { intros α0 Pi0 Ψi0 P0i Δx HXf HΔρx HΔxs HwfPi0 HwfP0i Hapart0
                 Hpre0x HΨi0s Hrefi.
          assert (Hα0Θ : α0 `notin` dom Θ) by (clear - HXf; solve_notin).
          destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) Hα0Θ)
            as (_ & Hmonα & Hnrα & Hκwα).
          apply (H0 α0 ltac:(clear - HXf; solve_notin)
                   NM ((α0 ~ abind_tvar) ++ Θ0)
                   Θtv ((α0 ~ abind_tvar) ++ Θr)
                   ((α0 ~ abind_tvar) ++ Θ0r) κ
                   Δx Δρ Δr Ψρ Ψ0' Ψi0 Ψa
                   (open_uskl_wrt_uskl ψR (uskl_var_f α0))
                   Pi0 P0i); try assumption.
          - apply aenv_split_cons_r;
              [ exact HspΘ | clear - HXf; solve_notin ].
          - apply aenv_split_cons_r;
              [ exact HspΘ0 | clear - HXf; solve_notin ].
          - apply a_wf_aenv__tvar;
              [ clear - HXf Hdomsub; destruct_notin; fsetdec
              | exact HwfΘr ].
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ ].
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ0 ].
          - apply a_inc__tvar with (Ξ := (@nil (atom * abind)));
              [ exact Hκ | apply a_suffix__nil ].
          - eapply uskl_rsubst_weaken;
              [ apply Hrhof; clear - HXf; solve_notin
              | intros x b Hb; apply binds_cons_3; exact Hb ].
          - apply Htagsf. clear - HXf; solve_notin.
          - clear - HΨi0s HΨaΨ0'; fsetdec.
          - apply rsubst_fresh_weaken_tvar; exact Hfresh.
          - intros Yd αd τ HYd Hbd.
            eapply (@delta_def_fresh_open_tvar Δ Θ α0);
              [ exact HwfΘ | clear - HXf; solve_notin | exact Hdfresh
              | apply HΔxs; exact HYd | exact Hbd ].
          - rewrite ftvar_in_aenv_cons_tvar. clear - HLav; fsetdec. }

        destruct Pi as [ | nb | β | Pi1 Pi2 | Pib | | Pi' ].
        +
          simpl in Hpre0. inversion Hpre0.
        +  inversion HwfPi.
        +
          exfalso.
          assert (HΨ'e : Ψ' [=] empty).
          { eapply ad_partial_precise_mono_subject_target_tags_empty
              with (τ := msubst_lookup κ β);
              [ exact HwfΘ | exact Hpre0 | reflexivity
              | eapply a_inc_lookup_mono; eauto
              | exact (a_tags_sort_d_tags Htags0) ]. }
          clear - HΨ'e HΨ'eq Hεnin; fsetdec.
        +  simpl in Hpre0. inversion Hpre0.
        +
          destruct (a_wf_pskl_all_inv_empty HwfPi) as (Lwi & HwfPif).
          destruct (ad_partial_precise_msubst_all_tag_inv HwfΘ Hlcκ Htagsf Hpre0)
            as (Lp & Ψi' & HpreF & HΨis & HΨi's).
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lrb
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0'
               `union` Lwi `union` Lp `union` ftvar_in_pskl Pib).
          destruct (IHX α (open_pskl_wrt_pskl Pib (pskl_var_f α)) Ψi'
                      (pskl_univ_ghost P0') (add α Δ)
                      ltac:(clear - Fr; solve_notin)
                      ltac:(clear - Hdelta; solve_notin_auto)
                      ltac:(clear; solve_notin_auto)
                      (HwfPif α ltac:(clear - Fr; solve_notin))
                      ltac:(eapply a_wf_pskl_weaken;
                            [ intros x b Hb; apply binds_cons_3; exact Hb
                            | exact HwfP0 ])
                      ltac:(intros α0 HX0;
                            pose proof (Hapart α0 HX0) as Hs0;
                            simpl in Hs0;
                            rewrite msubst_pskl_open_lc;
                              [ | exact Hlcκ | clear - Fr; solve_notin ];
                            pose proof (pskl_shielded_ftv_open_upper
                              (msubst_pskl κ Pib) (pskl_var_f α)) as Hup;
                            simpl in Hup;
                            assert (HneX0 : α0 <> α)
                              by (clear - HX0 Fr; destruct_notin; fsetdec);
                            clear - Hs0 Hup HneX0; fsetdec)
                      ltac:(eapply ad_partial_precise_weaken;
                              [ apply HpreF; clear - Fr; solve_notin
                              | intros x b Hb; apply binds_cons_3;
                                exact Hb ])
                      HΨi's
                      ltac:(apply Hrefb; clear - Fr; solve_notin))
            as (ΞX & PaX & κX & HsX & HfmX & HuX & HkX & HfrX & HFX & HqX).
          assert (HαΞ : α `notin` dom ΞX)
            by (intros Hin; exact (HfrX α Hin ltac:(clear; solve_notin_auto))).
          assert (HdκX : dom κX [=] dom ΞX) by (apply keys_eq_dom; exact HkX).
          assert (HlcκX : msubst_lc (κX ++ κ))
            by (eapply msubst_lc_app_wf; eassumption).
          exists ΞX, (pskl_all_syn (close_pskl_wrt_pskl α PaX)), κX.
          split.
          {
            apply a_solve_eq__all_l_univ_ghost with (β := α);
              [ clear - Fr; solve_notin | exact HsX ]. }
          split; [ exact HfmX | ].
          split; [ exact HuX | ].
          split; [ exact HkX | ].
          split; [ intros α0 Hα0; pose proof (HfrX α0 Hα0) as Hn;
                   clear - Hn; fsetdec | ].
          split; [ exact HFX | ].
          intros Δ' HS1 HS2 HS3.
          simpl.
          assert (Hrun : {{ ((α ~ abind_tvar) ++ Θ) ⨟
                    (add α (Δ `union` (remove α Δ'))) ⊢ˢ
                    (msubst_pskl (κX ++ κ) PaX) ⊑ᵖ[ Ψi' `union` Ψa ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α)) }}ad).
          { eapply ad_partial_precise_delta_cong;
              [ apply (HqX (remove α Δ'));
                [ clear - HS1; destruct_notin; fsetdec
                | simpl; clear - HS2; fsetdec
                | intros Yd αd τ HYd Hbd;
                  destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                    as [[_ Hc] | Hbd']; [ discriminate Hc | ];
                  eapply HS3; [ clear - HYd; fsetdec | exact Hbd' ] ]
              | clear; fsetdec ]. }
          eapply ad_partial_precise_forall_close
            with (1 := HwfΘ) (2 := Himav) (3 := HFX) (4 := Hmon) (5 := HlcκX)
                 (8 := Hrun).
          { clear - Fr HαΞ HdκX; destruct_notin; solve_notin_auto. }
          { clear - HΨis; fsetdec. }
        +
          assert (HΨie : Ψi [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          assert (Hhd : Δ ∩
                    (ftvar_in_uskl (uskl_all_tag ε ψR)) [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          simpl in Hhd.
          eapply solve_ext_nil with (Pa := (pskl_univ_ghost P0')); [ apply a_solve_eq__ghost_l | ].
          intros Δ' HS1 HS2 HS3.
          simpl.
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lrb
             `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` ftvar_in_aenv Θ0
             `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
             `union` ftvar_in_pskl P0' `union` Δ').
          destruct (IHX α pskl_ghost Ψi (pskl_univ_ghost P0') Δ
                      ltac:(clear - Fr; solve_notin)
                      Hdelta
                      ltac:(clear; solve_notin_auto)
                      ltac:(apply a_wf_pskl__ghost)
                      ltac:(eapply a_wf_pskl_weaken;
                            [ intros x b Hb; apply binds_cons_3; exact Hb
                            | exact HwfP0 ])
                      ltac:(intros α0 HX0; simpl; auto)
                      ltac:(simpl; apply ad_ppre__ghost;
                            [ exact HΨie
                            | pose proof
                                (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                   (uskl_var_f α)) as Hup;
                              simpl in Hup; clear - Hhd Hup Fr;
                              destruct_notin; fsetdec ])
                      ltac:(clear - HΨie; solve_notin_auto)
                      ltac:(apply Hrefb; clear - Fr; solve_notin))
            as (ΞX & PaX & κX & HsX & _ & _ & HkX & _ & _ & HqX).

          destruct (a_solve_eq_ghost_subject_inv HsX) as [HΞXe HPaXe]; subst.
          destruct κX as [ | ? ? ];
            [ | unfold keys in HkX; simpl in HkX; discriminate ].
          cbn [app] in HqX.

          assert (HXPaX : α `notin` ftvar_in_pskl
                    (msubst_pskl κ (pskl_univ_ghost P0'))).
          { apply msubst_pskl_ftv_avoid.
            - intros p Hp; pose proof (Himav p Hp) as Hb;
                clear - Hb Fr; destruct_notin; fsetdec.
            - simpl;
              assert (HXP0' : α `notin` ftvar_in_pskl P0')
                by (pose proof (a_wf_pskl_ftv_dom HwfP0'0) as Hd;
                    clear - Hd Fr; destruct_notin; fsetdec);
              exact HXP0'. }
          apply ad_ppre__univ_ghost_fill with (ε := ε)
            (L := Δ `union` Δ' `union` dom Θ `union` dom Θ0 `union` dom κ
               `union` singleton ε `union` singleton α `union` Δρ
               `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl (msubst_pskl κ P0')).
          intros α' HX'.
          assert (HS3' : delta_def_fresh Δ' ((α ~ abind_tvar) ++ Θ)).
          { intros Yd αd τ HYd Hbd.
            destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
              [ discriminate Hc | exact (HS3 Yd αd τ HYd Hbd') ]. }
          pose proof (HqX Δ' HS1
                        ltac:(simpl; clear - HS2 Fr; destruct_notin; solve_notin_auto)
                        HS3') as Hq1.
          apply ad_partial_precise_rename_head with (α := α) (4 := Hq1).
          * exact HwfΘ.
          * simpl in HXPaX. clear - Fr HXPaX. solve_notin_auto.
          * simpl in HXPaX |- *. clear - HX' HXPaX. solve_notin_auto.
        +
          assert (HgPi'w : guarded_pskl Pi' /\ ({{ Θ0 ⨟ empty ⊢ₚₛ Pi' }}a))
            by (split; [ inversion HwfPi; assumption | apply a_wf_pskl_univ_ghost_body; exact HwfPi ]).
          destruct HgPi'w as [HgPi' HwfPi'].
          assert (Hdisj :
            ({{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ] (uskl_all_tag ε ψR) }}ad) \/
            (exists Lf, forall α, α `notin` Lf ->
               {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ˢ
                 pskl_univ_ghost (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ]
                 (open_uskl_wrt_uskl ψR (uskl_var_f α)) }}ad)).
          { simpl in Hpre0. inversion Hpre0; subst;
              [ left; assumption | right; eexists; eassumption ]. }
          destruct Hdisj as [Hrem | (Lf & HF)].
          *
            exfalso. inversion HgPi'; subst.
            -- simpl in Hrem. inversion Hrem.
            -- assert (HΨ'e : Ψ' [=] empty).
               { eapply ad_partial_precise_mono_subject_target_tags_empty
                   with (τ := msubst_lookup κ α);
                   [ exact HwfΘ | exact Hrem | reflexivity
                   | eapply a_inc_lookup_mono; eauto
                   | exact (a_tags_sort_d_tags Htags0) ]. }
               clear - HΨ'e HΨ'eq Hεnin; fsetdec.
            -- simpl in Hrem. inversion Hrem.
          *
            assert (HΨiS : Ψi [<=] Ψ0').
            { pick fresh αp for (Lf `union` Lt `union` dom Θ).
              assert (HwfΘx : {{ ⊢ ((αp ~ abind_tvar) ++ Θ) }}a)
                by (apply a_wf_aenv__tvar;
                    [ clear - Fr; solve_notin | exact HwfΘ ]).
              eapply ad_partial_precise_tags_sub;
                [ exact HwfΘx
                | apply HF; clear - Fr; solve_notin
                | exact (a_tags_sort_d_tags
                          (Htagsf αp ltac:(clear - Fr; solve_notin))) ]. }
            pick fresh α for
              (L `union` Lr `union` Lt `union` Lrb
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0' `union` Lf `union` ftvar_in_pskl Pi').
            destruct (IHX α (pskl_univ_ghost Pi') Ψi (pskl_univ_ghost P0') Δ
                        ltac:(clear - Fr; solve_notin)
                        Hdelta
                        ltac:(clear; solve_notin_auto)
                        ltac:(eapply a_wf_pskl_weaken;
                              [ intros x b Hb; apply binds_cons_3; exact Hb
                              | exact HwfPi ])
                        ltac:(eapply a_wf_pskl_weaken;
                              [ intros x b Hb; apply binds_cons_3; exact Hb
                              | exact HwfP0 ])
                        Hapart
                        (HF α ltac:(clear - Fr; solve_notin))
                        HΨiS
                        ltac:(apply Hrefb; clear - Fr; solve_notin))
              as (ΞX & PaX & κX & HsX & HfmX & HuX & HkX & HfrX & HFX & HqX).
            assert (HsX0 : {{ Θ0 ⊢ₑ (pskl_univ_ghost Pi') ∼ (pskl_univ_ghost P0')
                      ⤳ ΞX ⨾ PaX }}a)
              by (eapply a_solve_eq_strengthen_tvar; exact HsX).
            assert (HαΞ : α `notin` dom ΞX)
              by (intros Hin; exact (HfrX α Hin ltac:(clear; solve_notin_auto))).
            assert (HdκX : dom κX [=] dom ΞX) by (apply keys_eq_dom; exact HkX).
            assert (HimX : forall p, In p (κX ++ κ) ->
                      α `notin` ftvar_in_ptyp (snd p)).
            { intros p Hp. apply in_app_or in Hp; destruct Hp as [Hp | Hp].
              - assert (Hd := forall_wf_mono_images_dom HFX p Hp).
                assert (Hdw : dom Θw [<=] dom Θ)
                  by (apply aenv_binds_dom_sub; exact Hmon).
                clear - Hd Hdw Fr; destruct_notin; fsetdec.
              - pose proof (Himav p Hp) as Hb;
                  clear - Hb Fr; destruct_notin; fsetdec. }
            assert (HXPaX : α `notin`
                      ftvar_in_pskl (msubst_pskl (κX ++ κ) PaX)).
            { apply msubst_pskl_ftv_avoid; [ exact HimX | ].
              pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ _ HsX) as Hfsub;
                simpl in Hfsub.
              assert (HXPi' : α `notin` ftvar_in_pskl Pi')
                by (pose proof (a_wf_pskl_ftv_dom HwfPi') as Hd;
                    clear - Hd Fr; simpl in Hd; destruct_notin; fsetdec).
              assert (HXP0' : α `notin` ftvar_in_pskl P0')
                by (pose proof (a_wf_pskl_ftv_dom HwfP0'0) as Hd;
                    clear - Hd Fr; destruct_notin; fsetdec).
              clear - Hfsub HXPi' HXP0' HαΞ; fsetdec. }
            assert (Hpaform : exists Pbody, PaX = pskl_univ_ghost Pbody).
            { inversion HsX;
                solve [ eexists; reflexivity
                      | match goal with
                        | Hg : guarded_pskl (pskl_univ_ghost _) |- _ =>
                          inversion Hg
                        end ]. }
            destruct Hpaform as [Pbody Hpeq]; subst PaX.
            exists ΞX, (pskl_univ_ghost Pbody), κX.
            split; [ exact HsX0 | ].
            split; [ exact HfmX | ].
            split; [ exact HuX | ].
            split; [ exact HkX | ].
            split; [ intros α0 Hα0; pose proof (HfrX α0 Hα0) as Hn;
                     clear - Hn; fsetdec | ].
            split; [ exact HFX | ].
            intros Δ' HS1 HS2 HS3.
            simpl.
            apply ad_ppre__univ_ghost_fill with (ε := ε)
              (L := Δ `union` Δ' `union` dom Θ `union` dom Θ0 `union` dom κ
                 `union` dom κX
                 `union` singleton ε `union` singleton α `union` Δρ
                 `union` ftvar_in_uskl ψR
                 `union` ftvar_in_pskl (msubst_pskl (κX ++ κ) Pbody)).
            intros α' HX'.

            assert (HS3' : delta_def_fresh Δ' ((α ~ abind_tvar) ++ Θ)).
            { intros Yd αd τ HYd Hbd.
              destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
                [ discriminate Hc | exact (HS3 Yd αd τ HYd Hbd') ]. }
            pose proof (HqX (remove α Δ')
                          ltac:(clear - HS1; solve_notin_auto)
                          ltac:(simpl; clear - HS2; solve_notin_auto)
                          ltac:(intros Yd αd τ HYd Hbd;
                                eapply HS3';
                                  [ clear - HYd; solve_notin_auto | exact Hbd ]))
              as Hq1.
            eapply ad_partial_precise_delta_cong.
            -- eapply ad_partial_precise_delta_weaken_fresh
                with (Δ' := Δ' ∩ singleton α).
              ++ apply ad_partial_precise_rename_head with (α := α) (4 := Hq1).
                ** exact HwfΘ.
                ** simpl in HXPaX. clear - Fr HXPaX. solve_notin_auto.
                ** simpl in HXPaX |- *. clear - HX' HXPaX. solve_notin_auto.
              ++ pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                              (uskl_var_f α')) as Hup.
                simpl in Hup.
                apply inter_empty_pointwise. intros y Hy.
                assert (Heqy : y = α) by (clear - Hy; fsetdec).
                subst y. clear - Fr HX' Hup; destruct_notin; fsetdec.
              ++ intros Yd αd τ HYd Hbd.
                assert (Heqy : Yd = α) by (clear - HYd; fsetdec).
                subst Yd.
                destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'].
                ** discriminate Hc.
                ** pose proof (a_wf_aenv_def_ftv_dom _ _ HwfΘ Hbd') as Hd.
                  clear - Hd Fr; destruct_notin; fsetdec.
            -- clear; fsetdec.
    Unshelve. all: match goal with |- εvar => exact ε | |- _ => idtac end.
    }
  -
    destruct (uskl_rsubst_all_syn_l_inv Hrho)
      as [[-> _] | [Hleaf | (L' & R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  -
    assert (Hrefine' : {{ Θ ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_ghost }}ad)
      by (eapply refine_primary_to_plain_split; eassumption).
    destruct (uskl_rsubst_dot_ghost_l_inv Hrho) as [[-> HΨρ] | Hleaf].
    + assert (HΨ'e : Ψ' [=] empty)
        by (exact (d_tags_skl_dot_ghost_inv (a_tags_sort_d_tags Htags))).
      assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
      destruct (a_solve_eq_ghostg HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre Hrefine')
        as (Pa & Hsolve & Hprec).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hsolve | ].
      intros Δ' HS1 HS2 HS3.
      eapply ad_partial_precise_psi_cong;
        [ eapply ad_partial_precise_delta_weaken_fresh;
            [ exact Hprec | simpl; clear; fsetdec | exact HS3 ]
        | clear - HΨae; fsetdec ].
    + destruct (@a_solve_eq_complete_rsubst_var _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
  -
    assert (HwfΘr2 := HwfΘr).
    destruct (uskl_rsubst_dot_univ_ghost_cases Hrho Htags)
      as [Hleaf | (ψa0 & -> & Hrho0)].
    { destruct (@a_solve_eq_complete_rsubst_var _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec. }
    { rename Htags into Htags0, Hpre into Hpre0.
      assert (Htags1 : a_tags_sort NM Ψ' ψa0)
        by (apply a_tags_sort_dot_univ_ghost_inv; exact Htags0).
      assert (HngR : uskl_no_ghost R)
        by (eapply uskl_rsubst_no_ghost; eassumption).
      assert (HψaB : ftvar_in_bskl Q [<=] dom Θr ->
                ftvar_in_uskl ψa0 [<=] dom Θr `union` Δρ).
      { intros HQB.
        assert (HftR : ftvar_in_uskl R [<=]
                  ftvar_in_bskl Q `union` dom Θr)
          by (eapply consis_subject_ftv_bag_bound; eassumption).
        pose proof (uskl_rsubst_ftv_target_bound Hrho0) as HftA.
        clear - HQB HftR HftA; fsetdec. }
      destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
      -
        simpl in Hpre0. inversion Hpre0.
      -  inversion HwfPi.
      -
        exfalso. simpl in Hpre0.
        eapply ad_ppre_mono_paint_dot_univ_ghost_absurd;
          [ exact HwfΘ | exact Hpre0 | reflexivity | reflexivity
          | eapply a_inc_lookup_mono; eauto ].
      -  simpl in Hpre0. inversion Hpre0.
      -  simpl in Hpre0. inversion Hpre0.
      -
        destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
        +  simpl in Hrefine. inversion Hrefine.
        +  inversion HwfP0.
        +
          exfalso. simpl in Hrefine.
          assert (Hml : mono_ptyp (msubst_lookup κ β))
            by (eapply a_inc_lookup_mono; eauto).
          rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
          eapply ad_refine_mono_paint_univ_ghost_rhs_absurd;
            [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
            | exact Hml ].
        +  simpl in Hrefine. inversion Hrefine.
        +  simpl in Hrefine. inversion Hrefine.
        +
          simpl in Hrefine.
          pose proof (ad_refine_syn_ghost_sskl Hrefine eq_refl
                        (lc_bskl_univ_ghost _ (ad_pat_consis_target_lc Hconsis HngR))) as Hss.
          assert (HskQ : is_sskl Q) by (inversion Hss; subst; assumption).
          pose proof (ad_pat_consis_sskl_tags Hconsis HwfΘ HskQ) as HΨe.
          assert (HQB : ftvar_in_bskl Q [<=] dom Θr).
          { assert (Ht : ftvar_in_bskl (bskl_univ_ghost Q) [<=] dom Θr).
            { eapply ghost_refine_target_ftv_dom_r;
                [ exact HspΘ | exact HΔrd | exact Hrefine | ].
              exact (ad_pat_consis_target_binds Hconsis HngR). }
            simpl in Ht; exact Ht. }
          eapply solve_ext_nil with (Pa := pskl_ghost); [ apply a_solve_eq__ghost_r | ].
          intros Δ' HS1 HS2 HS3.
          eapply ad_partial_precise_psi_cong;
            [ eapply ad_partial_precise_delta_weaken_fresh;
                [ exact Hpre0
                | simpl;
                  pose proof (HψaB HQB) as Hbb;
                  clear - Hbb HS1 HS2 Hdelta; fsetdec
                | exact HS3 ]
            | clear - HΨe Hsubeq2; fsetdec ].
        +
          assert (HwfP0' : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a)
            by (apply a_wf_pskl_univ_ghost_body; exact HwfP0).
          assert (HgP0' : guarded_pskl P0')
            by (inversion HwfP0; assumption).
          simpl in Hrefine.
          inversion Hrefine; subst.
          *
            exfalso. inversion HgP0'; subst.
            -- match goal with
               | Hin : {{ _ ⨟ _ ⊢ᵣ
                   pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ }}ad |- _ =>
                 simpl in Hin; inversion Hin
               end.
            -- match goal with
               | Hin : {{ _ ⨟ _ ⊢ᵣ
                   pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _ }}ad
                 |- _ =>
                 let Hml := fresh in
                 assert (Hml : mono_ptyp (msubst_lookup κ v))
                   by (eapply a_inc_lookup_mono; eauto);
                 simpl in Hin;
                 rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
                 eapply ad_refine_mono_paint_univ_ghost_rhs_absurd;
                   [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                   | exact Hml ]
               end.
            -- match goal with
               | Hin : {{ _ ⨟ _ ⊢ᵣ
                   pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _ }}ad
                 |- _ =>
                 simpl in Hin; inversion Hin
               end.
          *
            assert (Hhp0 : {{ Θ ⨟ Δ ⊢ˢ
                      msubst_pskl κ pskl_ghost ⊑ᵖ[ Ψi ] ψa0 }}ad).
            { simpl. simpl in Hpre0. inversion Hpre0; subst.
              match goal with
              | HΨE : Ψi [=] empty,
                Hint : _ ∩ _ [=] empty |- _ =>
                apply ad_ppre__ghost; [ exact HΨE | ];
                simpl in Hint; exact Hint
              end. }
            match goal with
            | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ Q }}ad
              |- _ =>
              destruct (IHHconsis NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr
                          Ψρ Ψ' Ψi Ψa ψa0 pskl_ghost P0'
                          HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                          HwfΘ HwfΘ0 Hmon Hnr
                          ltac:(apply a_wf_pskl__ghost) HwfP0'
                          Hκ Hκw
                          Hrho0 Htags1 Hsub Hinter Hfresh Hdelta
                          ltac:(intros α0 HX0; simpl; auto)
                          Hdfresh
                          Hhp0 Hsubeq1 Hsubeq2 Hin Lav HLav)
                as (Ξ' & Pa' & κ' & Hs' & _ & _ & Hk' & _ & _ & Hq')
            end.

            destruct (a_solve_eq_ghost_subject_inv Hs') as [HΞ'e HPa']; subst.
            destruct κ' as [ | ? ? ];
              [ | unfold keys in Hk'; simpl in Hk'; discriminate ].
            eapply solve_ext_nil with (Pa := (pskl_univ_ghost P0'));
              [ apply a_solve_eq__ghost_l | ].
            intros Δ' HS1 HS2 HS3.
            cbn [app]. simpl. apply ad_ppre__univ_ghost_keep.
            exact (Hq' Δ' HS1 HS2 HS3).
      -
        assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
        assert (HwfPi' : {{ Θ0 ⨟ empty ⊢ₚₛ Pi' }}a) by (apply a_wf_pskl_univ_ghost_body; exact HwfPi).
        simpl in Hpre0. inversion Hpre0; subst.
        +
          exfalso. inversion HgPi'; subst.
          * match goal with
            | Hp' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ pskl_unit ⊑ᵖ[ _ ] _ }}ad |- _ =>
                simpl in Hp'; inversion Hp'
            end.
          * match goal with
            | Hp' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ (pskl_var_f ?v) ⊑ᵖ[ _ ] _ }}ad |- _ =>
                simpl in Hp';
                eapply ad_ppre_mono_paint_dot_univ_ghost_absurd;
                  [ exact HwfΘ | exact Hp' | reflexivity | reflexivity
                  | eapply a_inc_lookup_mono; eauto ]
            end.
          * match goal with
            | Hp' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ (pskl_arrow _ _) ⊑ᵖ[ _ ] _ }}ad |- _ =>
                simpl in Hp'; inversion Hp'
            end.
        +
          match goal with
          | Hp' : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] ψa0 }}ad |- _ =>
            rename Hp' into Hpre1
          end.
          assert (Hapart' : forall α, α `in` Δρ ->
                    α `notin` pskl_shielded_ftv (msubst_pskl κ Pi')).
          { intros α0 HX0.
            pose proof (Hapart α0 HX0) as Hsh. simpl in Hsh.
            pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi')).
            fsetdec. }
          destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          *  simpl in Hrefine. inversion Hrefine.
          *  inversion HwfP0.
          *
            exfalso. simpl in Hrefine.
            assert (Hml : mono_ptyp (msubst_lookup κ β))
              by (eapply a_inc_lookup_mono; eauto).
            rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
            eapply ad_refine_mono_paint_univ_ghost_rhs_absurd;
              [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
              | exact Hml ].
          *  simpl in Hrefine. inversion Hrefine.
          *  simpl in Hrefine. inversion Hrefine.
          *
            simpl in Hrefine.
            pose proof (ad_refine_syn_ghost_sskl Hrefine eq_refl
                        (lc_bskl_univ_ghost _ (ad_pat_consis_target_lc Hconsis HngR))) as Hss.
            assert (HskQ : is_sskl Q) by (inversion Hss; subst; assumption).
            pose proof (ad_pat_consis_sskl_tags Hconsis HwfΘ HskQ) as HΨe.
            assert (HQB : ftvar_in_bskl Q [<=] dom Θr).
            { assert (Ht : ftvar_in_bskl (bskl_univ_ghost Q) [<=] dom Θr).
              { eapply ghost_refine_target_ftv_dom_r;
                  [ exact HspΘ | exact HΔrd | exact Hrefine | ].
                exact (ad_pat_consis_target_binds Hconsis HngR). }
              simpl in Ht; exact Ht. }
            eapply solve_ext_nil with (Pa := (pskl_univ_ghost Pi'));
              [ apply a_solve_eq__ghost_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ simpl; apply ad_ppre__univ_ghost_keep;
                eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨe Hsubeq2; fsetdec ].
          *
            assert (HwfP0' : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a)
              by (apply a_wf_pskl_univ_ghost_body; exact HwfP0).
            assert (HgP0' : guarded_pskl P0')
              by (inversion HwfP0; assumption).
            simpl in Hrefine.
            inversion Hrefine; subst.
            --
               exfalso. inversion HgP0'; subst.
               ++ match goal with
                  | Hin : {{ _ ⨟ _ ⊢ᵣ
                      pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ }}ad |- _ =>
                    simpl in Hin; inversion Hin
                  end.
               ++ match goal with
                  | Hin : {{ _ ⨟ _ ⊢ᵣ
                      pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _ }}ad
                    |- _ =>
                    let Hml := fresh in
                    assert (Hml : mono_ptyp (msubst_lookup κ v))
                      by (eapply a_inc_lookup_mono; eauto);
                    simpl in Hin;
                    rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
                    eapply ad_refine_mono_paint_univ_ghost_rhs_absurd;
                      [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                      | exact Hml ]
                  end.
               ++ match goal with
                  | Hin : {{ _ ⨟ _ ⊢ᵣ
                      pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _ }}ad
                    |- _ =>
                    simpl in Hin; inversion Hin
                  end.
            --
               match goal with
               | Hin : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ Q }}ad
                 |- _ =>
                 destruct (IHHconsis NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr
                             Ψρ Ψ' Ψi Ψa ψa0 Pi' P0'
                             HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                             HwfΘ HwfΘ0 Hmon Hnr HwfPi' HwfP0' Hκ Hκw
                             Hrho0 Htags1 Hsub Hinter Hfresh Hdelta
                             Hapart' Hdfresh
                             Hpre1 Hsubeq1 Hsubeq2 Hin Lav HLav)
                   as (Ξ' & Pa' & κ' & Hs' & Hfm' & Hu' & Hk' & Hfr' & HF' & Hq')
               end.

               exists Ξ', (pskl_univ_ghost Pa'), κ'.
               split; [ apply a_solve_eq__univ_ghost_both; exact Hs' | ].
               split; [ exact Hfm' | ].
               split; [ exact Hu' | ].
               split; [ exact Hk' | ].
               split; [ exact Hfr' | ].
               split; [ exact HF' | ].
               intros Δ' HS1 HS2 HS3.
               simpl. apply ad_ppre__univ_ghost_keep.
               exact (Hq' Δ' HS1 HS2 HS3). }
  -
    destruct (uskl_rsubst_ghost_l_inv Hrho) as [[-> _] | Hleaf].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
  -
    destruct (uskl_rsubst_univ_ghost_l_inv Hrho)
      as [[-> _] | [Hleaf | (R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  -
    destruct (uskl_rsubst_univ_ghost_l_inv Hrho)
      as [[-> _] | [Hleaf | (R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  -
    destruct (uskl_rsubst_univ_ghost_l_inv Hrho)
      as [[-> _] | [Hleaf | (R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  -
    destruct (uskl_rsubst_var_l_inv Hrho) as [[-> HΨρ] | Hleaf];
      [ | destruct (@a_solve_eq_complete_rsubst_var _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                      HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
            as (Pa & Hs & Hq);
          eapply solve_ext_nil with (Pa := Pa);
            [ exact Hs
            | intros Δ' HS1 HS2 HS3; apply Hq; clear; fsetdec ] ].
    assert (HΨ'e : Ψ' [=] empty)
      by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
    assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | exact H ]).
    assert (HΨie : Ψi [=] empty)
      by (eapply ad_ppre_mono_tags_empty with (τ := ptyp_var_f α);
            [ exact HwfΘ | exact Hpre | reflexivity | apply mono_ptyp__var ]).
    destruct (IHHconsis NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr empty empty Ψi empty
                (ptyp_to_uskl_syn τ) Pi P0
                HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                HwfΘ HwfΘ0 Hmon Hnr HwfPi HwfP0 Hκ Hκw
                ltac:(apply ursubst__refl;
                        [ apply mono_ptyp_to_uskl_syn_lc; exact Hmd
                        | solve_notin_auto ])
                ltac:(apply a_tags_sort_mono_paint; exact Hmd)
                ltac:(clear - HΨie; solve_notin_auto)
                ltac:(clear; solve_notin_auto)
                Hfresh Hdelta Hapart Hdfresh
                ltac:(eapply ad_ppre_flexdef_target_unfold;
                        [ exact HwfΘ | exact Hdfresh | exact Hpre
                        | reflexivity | eassumption ])
                ltac:(clear - Hsubeq1 HΨρ HΨae; solve_notin_auto)
                ltac:(clear; solve_notin_auto)
                Hrefine Lav HLav)
      as (Ξ0 & Pa & κ0 & Hsolve & Hfm0 & Hu0 & Hk0 & Hfr0 & HF0 & Hprec).
    exists Ξ0, Pa, κ0.
    split; [ exact Hsolve | ].
    split; [ exact Hfm0 | ].
    split; [ exact Hu0 | ].
    split; [ exact Hk0 | ].
    split; [ exact Hfr0 | ].
    split; [ exact HF0 | ].
    intros Δ' HS1 HS2 HS3.
    eapply ad_partial_precise_psi_cong;
      [ eapply ad_ppre__flex_r;
          [ eassumption | exact (Hprec Δ' HS1 HS2 HS3) ]
      | clear - HΨae; fsetdec ].
  -
    assert (HwfΘr2 := HwfΘr).
    assert (Hbdef : binds α (abind_flex_mono_def τ) Θr).
    { eapply aenv_split_binds_def_r;
        [ exact HspΘ | exact Htvs | eassumption ]. }
    eapply IHHconsis; try eassumption.
    assert (HdfΘr : delta_def_fresh Δr Θr).
    { intros β α0 τ0 Hβ Hb Hin.
      assert (HβR : β `in` dom Θr)
        by (eapply a_wf_aenv_def_ftv_dom_in; eassumption).
      pose proof (proj2 (proj2 HspΘ)) as Hdisj.
      clear - Hβ HβR HΔrd Hdisj; fsetdec. }
    eapply ad_refine_flexdef_target_unfold;
      [ exact HwfΘr | exact HdfΘr | exact Hrefine | reflexivity | exact Hbdef ].
Qed.

Theorem a_solve_eq_complete_var :
  forall NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  uskl_rsubst NM Θ Δρ Ψρ ψsub ψa ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  Ψρ ∩ Ψ' [=] empty ->
  rsubst_fresh Δρ Θ κ -> Δρ [<=] Δ ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  {{ Ψsub ⨟ Θ ⊢ˢ ψsub ∼ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->

  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists Ξ Pa κ',
    {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a /\
    all_flex_mono Ξ /\ uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad.

Proof.
  intros NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hrho Htags Hsub Hinter Hfresh Hdelta
         Hapart Hdfresh Hpre Hsubeq1 Hsubeq2 Hconsis Hrefine L HL.
  destruct (@a_solve_eq_complete_var_gen NM Θ Θ0 Θ nil Θ Θ0 κ Δ Δρ empty
              Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0
              (aenv_split_nil Θ) (aenv_split_nil Θ0) HwfΘ
              ltac:(intros x b Hb; destruct Hb)
              ltac:(simpl; clear; solve_notin_auto)
              ltac:(clear; solve_notin_auto)
              HwfΘ HwfΘ0 HwfΘ
              ltac:(intros x b Hb; exact Hb)
              ltac:(intros x b Hb; left; exact Hb)
              HwfPi HwfP0 Hκ
              ltac:(intros α Hf;
                    eapply a_inc_lookup_flex_ftv_dom; eassumption)
              Hrho Htags Hsub Hinter Hfresh
              Hdelta Hapart Hdfresh Hpre Hsubeq1 Hsubeq2 Hconsis
              Hrefine L HL)
    as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hfam).
  exists Ξ, Pa, κ'.
  split; [ exact Hs | ].
  split; [ exact Hfm | ].
  split; [ exact Hu | ].
  split; [ exact Hk | ].
  split; [ exact Hfr | ].
  split; [ exact HF | ].
  eapply ad_partial_precise_delta_cong;
    [ apply (Hfam empty);
      [ clear; fsetdec | clear; fsetdec
      | intros β α τ Hβ Hb; exfalso; clear - Hβ; fsetdec ]
    | clear; fsetdec ].
Qed.

Theorem a_solve_eq_complete_var_at :
  forall NM Θ0 Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, a_flex_tvar Θ0 α ->
     ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θw) ->
  uskl_rsubst NM Θ Δρ Ψρ ψsub ψa ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  Ψρ ∩ Ψ' [=] empty ->
  rsubst_fresh Δρ Θ κ -> Δρ [<=] Δ ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  {{ Ψsub ⨟ Θ ⊢ˢ ψsub ∼ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists Ξ Pa κ',
    {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a /\
    all_flex_mono Ξ /\ uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ' /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad.
Proof.
  intros NM Θ0 Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfPi HwfP0 Hκ Hκw
         Hrho Htags Hsub Hinter Hfresh Hdelta
         Hapart Hdfresh Hpre Hsubeq1 Hsubeq2 Hconsis Hrefine L HL.
  destruct (@a_solve_eq_complete_var_gen NM Θ Θ0 Θw nil Θ Θ0 κ Δ Δρ empty
              Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0
              (aenv_split_nil Θ) (aenv_split_nil Θ0) HwfΘ
              ltac:(intros x b Hb; destruct Hb)
              ltac:(simpl; clear; solve_notin_auto)
              ltac:(clear; solve_notin_auto)
              HwfΘ HwfΘ0 HwfΘw Hmon Hnr
              HwfPi HwfP0 Hκ Hκw
              Hrho Htags Hsub Hinter Hfresh
              Hdelta Hapart Hdfresh Hpre Hsubeq1 Hsubeq2 Hconsis
              Hrefine L HL)
    as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hfam).
  exists Ξ, Pa, κ'. repeat split; try assumption.
  eapply ad_partial_precise_delta_cong;
    [ apply (Hfam empty);
      [ clear; fsetdec | clear; fsetdec
      | intros β α τ Hβ Hb; exfalso; clear - Hβ; fsetdec ]
    | clear; fsetdec ].
Qed.
