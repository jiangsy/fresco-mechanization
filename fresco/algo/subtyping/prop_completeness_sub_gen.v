Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.prop_tag.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_mod_compat.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.consistency.prop_consis_precise.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.deco_algo.prop_decorate_sub.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo.consistency.prop_precision_recovery.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.subtyping.prop_sub_msubst_equiv.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.deco_algo.prop_soundness_sub.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo.consistency.prop_consis_precise.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_precise.
Require Import src.fresco.algo.subtyping.prop_completeness_look.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.prop_wf_preservation.

Set Implicit Arguments.

Local Ltac destr_join :=
  repeat match goal with
         | Hj : ad_consis_join _ _ _ _ |- _ =>
             let Hc := fresh "Hjc" in let Hr := fresh "Hjr" in
             destruct Hj as [Hc Hr];
             try rewrite bskl_to_pskl_pskl_to_bskl_inh in Hr
         end.

Lemma uskl_wf_ftv_dom : forall Θ Δ ψ,
  {{ Θ ⨟ Δ ⊢ₚₛ ⌊ ψ ⌋ˢ }}a -> ftvar_in_uskl ψ [<=] dom Θ.
Proof.
  intros Θ Δ ψ H.
  pose proof (a_wf_pskl_ftv_dom H) as Hd.
  rewrite ftvar_in_pskl_uskl_to_pskl in Hd. exact Hd.
Qed.

Definition sub_complete_concl
  (n : nat) (NM : a_sub_mode) (M : mode)
  (Θ0 : aenv) (P0 P : pskl) (R R' : uskl) (Ψ : atoms)
  (Θ : aenv) (κ : metasubst) (Q : bskl) : Prop :=

  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->

  ⌊ R ⌋ˢ = P ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⊢ R' ≡ᵘ (msubst_uskl_syn κ R) }}a ->
  ad_pat_sub_fuel n NM M Ψ Θ R' Q ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  (NM = a_sub_mode_ty -> uskl_ghost_free R') ->

  exists P1 Θ1,
    a_sub NM M P0 Θ0 P P1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         {{ Θ ⨟ empty ⊢ₚᵣ
           (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Q) }}ad).

Definition sub_flex_complete_concl
  (n : nat) (NM : a_sub_mode) (M : mode)
  (Θ0 Ξ : aenv) (α : atom) (P0 : pskl) (R' : uskl) (Ψ : atoms)
  (Θ : aenv) (κ : metasubst) (Q : bskl) : Prop :=
  a_decls Ξ ->
  dom Ξ [<=] ftvar_in_pskl P0 ->
  {{ ⊢ (Ξ ++ Θ0) }}a -> {{ ⊢ Θ }}a ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_flex_tvar Θ0 α ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat (mode_fn M) P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat (mode_fn M) P0) ->
  κ ∷ (Ξ ++ Θ0) ⊑ Θ ->
  {{ Θ ⊢ R' ≡ᵘ (ptyp_to_uskl_syn (msubst_lookup κ α)) }}a ->
  ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ R' Q ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  exists P1 Θ1,
    a_sub_flex NM M P0 Θ0 Ξ α P1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ (Ξ ++ Θ0) ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv (Ξ ++ Θ0) κ (msubst_compose ζ κ1) Θ /\
         {{ Θ ⨟ empty ⊢ₚᵣ
           (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Q) }}ad).

Definition a_sub_complete_bundle : Prop :=
  forall n,
    (forall NM M Θ0 P0 P R R' Ψ Θ κ Q,
       sub_complete_concl n NM M Θ0 P0 P R R' Ψ Θ κ Q) /\
    (forall NM M Θ0 Ξ α P0 R' Ψ Θ κ Q,
       sub_flex_complete_concl n NM M Θ0 Ξ α P0 R' Ψ Θ κ Q).

Check sub_complete_concl.
Check sub_flex_complete_concl.
Check a_sub_complete_bundle.

Lemma msubst_bskl_pskl_to_bskl_syn : forall κ P,
  msubst_bskl κ (pskl_to_bskl_syn P) = pskl_to_bskl_syn (msubst_pskl κ P).
Proof. intros κ P; induction P; cbn; f_equal; auto. Qed.

Lemma tyequiv_mono_paint_ghost_free : forall Θ R' τ,
  {{ Θ ⊢ R' ≡ᵘ (ptyp_to_uskl_syn τ) }}a ->
  mono_ptyp τ -> a_wf_ptyp Θ τ ->
  uskl_ghost_free R'.
Proof.
  intros Θ R' τ Hrel Hm Hwf.
  destruct (a_uskl_tyequiv_mono_r_inv Hrel eq_refl Hm Hwf)
    as [τ' [-> [Hm' _]]].
  apply mono_ptyp_to_uskl_syn_ghost_free. exact Hm'.
Qed.

Lemma ad_pat_sub_fuel_ti_refine : forall n NM Ψ Θ R Q,
  ad_pat_sub_fuel n NM mode_ti Ψ Θ R Q ->
  {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) }}ad.
Proof.
  intros n NM Ψ Θ R Q H; inversion H; subst; try congruence.
  -
    match goal with Hj : ad_consis_join _ _ _ _ |- _ =>
      exact (ad_consis_join_refine Hj) end.
  -
    cbn. rewrite bskl_to_pskl_pskl_to_bskl_inh.
    apply ad_refine_pskl__ghost. clear; fsetdec.
  -
    cbn. apply ad_refine_pskl__ghost. clear; fsetdec.
Qed.

Lemma msubst_uskl_syn_ghost_inv : forall κ R,
  msubst_uskl_syn κ R = uskl_ghost -> R = uskl_ghost.
Proof.
  intros κ R; destruct R; cbn; try discriminate; [ | reflexivity ].
  unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  destruct (msubst_lookup κ α); cbn; discriminate.
Qed.

Lemma ad_pat_sub_fuel_ghost_target_inh : forall n M Ψ Θ Q,
  ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ uskl_ghost Q ->
  pskl_to_bskl_inh (bskl_to_pskl Q) = Q.
Proof.
  intros n M Ψ Θ Q H; inversion H; subst; destr_join.
  -  eapply consis_ghost_target_inh; eassumption.
  -
    match goal with Hg : guarded_uskl uskl_ghost |- _ => inversion Hg end.
  -  rewrite bskl_to_pskl_pskl_to_bskl_inh; reflexivity.
Qed.

Lemma a_sub_complete_ghost_input : forall M Θ0 P0 Θ κ Q,
  {{ ⊢ Θ0 }}a ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  pskl_to_bskl_inh (bskl_to_pskl Q) = Q ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  exists P1 Θ1,
    a_sub a_sub_mode_sk M P0 Θ0 pskl_ghost P1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         {{ Θ ⨟ empty ⊢ₚᵣ
           (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Q) }}ad).
Proof.
  intros M Θ0 P0 Θ κ Q Hwf0 Hmc Hinc HQ Hrs.
  exists P0, Θ0. split.
  - destruct M as [ | | M0 ].
    + inversion Hmc; subst. apply a_sub__infer.
    + apply a_sub__ghost; discriminate.
    + apply a_sub__ghost; discriminate.
  - intros κ1 Hid Hinc1. exists κ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | split; [ exact Hfact | ] ].

    unfold ad_precise.
    rewrite msubst_bskl_pskl_to_bskl_syn, bskl_to_pskl_pskl_to_bskl_syn, HQ.
    exact Hrs.
Qed.

Lemma a_sub_complete_ghost : forall n M Θ0 P0 P R R' Ψ Θ κ Q,
  R' = uskl_ghost ->
  sub_complete_concl n a_sub_mode_sk M Θ0 P0 P R R' Ψ Θ κ Q.
Proof.
  intros n M Θ0 P0 P R R' Ψ Θ κ Q HT.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
  subst R'.

  pose proof (a_uskl_tyequiv_ghost_l_inv Hrel) as Hsubj.

  pose proof (msubst_uskl_syn_ghost_inv κ R Hsubj) as HR; subst R.
  cbn in HeqP; subst P.

  assert (HQ : pskl_to_bskl_inh (bskl_to_pskl Q) = Q)
    by (eapply ad_pat_sub_fuel_ghost_target_inh; exact Hsub).

  apply a_sub_complete_ghost_input; auto.
Qed.

Lemma msubst_uskl_syn_dot_ghost_inv : forall κ R,
  msubst_uskl_syn κ R = uskl_dot_ghost -> R = uskl_dot_ghost.
Proof.
  intros κ R; destruct R; cbn; try discriminate; [ | reflexivity ].
  unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  destruct (msubst_lookup κ α); cbn; discriminate.
Qed.

Lemma ad_pat_consis_dot_ghost_target_inh : forall Ψ Θ Q,
  {{ Ψ ⨟ Θ ⊢ˢ uskl_dot_ghost ∼ Q }}ad ->
  pskl_to_bskl_inh (bskl_to_pskl Q) = Q.
Proof. intros Ψ Θ Q H; inversion H; subst; reflexivity. Qed.

Lemma ad_pat_sub_fuel_dot_ghost_target_inh : forall n M Ψ Θ Q,
  ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ uskl_dot_ghost Q ->
  pskl_to_bskl_inh (bskl_to_pskl Q) = Q.
Proof.
  intros n M Ψ Θ Q H; inversion H; subst; destr_join.
  -  eapply ad_pat_consis_dot_ghost_target_inh; eassumption.
  -
    match goal with Hg : guarded_uskl uskl_dot_ghost |- _ => inversion Hg end.
  -  reflexivity.
Qed.

Lemma a_sub_complete_ghostg : forall n M Θ0 P0 P R R' Ψ Θ κ Q,
  R' = uskl_dot_ghost ->
  sub_complete_concl n a_sub_mode_sk M Θ0 P0 P R R' Ψ Θ κ Q.
Proof.
  intros n M Θ0 P0 P R R' Ψ Θ κ Q HT.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
  subst R'.
  pose proof (a_uskl_tyequiv_dot_ghost_l_inv Hrel) as Hsubj.
  pose proof (msubst_uskl_syn_dot_ghost_inv κ R Hsubj) as HR; subst R.
  cbn in HeqP; subst P.
  assert (HQ : pskl_to_bskl_inh (bskl_to_pskl Q) = Q)
    by (eapply ad_pat_sub_fuel_dot_ghost_target_inh; exact Hsub).
  apply a_sub_complete_ghost_input; auto.
Qed.

Lemma a_wf_pskl_ftv_dom_pointwise : forall Θ P,
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  forall α, α `in` ftvar_in_pskl P -> α `in` dom Θ.
Proof.
  intros Θ P Hwf α Hα.
  pose proof (a_wf_pskl_ftv_dom Hwf) as Hs. clear - Hs Hα. fsetdec.
Qed.

Lemma a_consis_ghost_p0_output : forall Δ1 Δ2 Θ0 P0 P P' Θ1,
  a_consis Δ1 Δ2 Θ0 P0 P P' Θ1 ->
  P0 = pskl_ghost ->
  P' = P.
Proof.
  intros Δ1 Δ2 Θ0 P0 P P' Θ1 H; induction H; intros Heq;
    try discriminate Heq.
  -  exact Heq.
  -
    subst; match goal with Hg : guarded_pskl pskl_ghost |- _ => inversion Hg end.
  -  reflexivity.
  -  reflexivity.
Qed.

Lemma a_inc_equiv_precise_msubst_var : forall Θ0 κ σ Θ Δ α,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  κ ∷ Θ0 ⊑ Θ -> σ ∷ Θ0 ⊑ Θ ->
  (forall α0, a_binds_tvar α0 Θ0 ->
     {{ Θ ⊢ (msubst_lookup κ α0) ≡ᵗ (msubst_lookup σ α0) }}a) ->
  a_binds_tvar α Θ0 ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_pskl κ (pskl_var_f α)) ⊑ (msubst_pskl σ (pskl_var_f α)) }}ad.
Proof.
  intros Θ0 κ σ Θ Δ α Hwf0 Hwfth Hκ Hσ Hie Hbt.
  assert (Hmκ : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact Hκ).
  assert (Hmσ : mono_ptyp (msubst_lookup σ α))
    by (eapply a_inc_lookup_mono; exact Hσ).
  unfold ad_precise; cbn [msubst_pskl].
  rewrite (ptyp_to_bskl_inh_syn_eq Hmκ), (ptyp_to_bskl_inh_syn_eq Hmσ).
  apply tyequiv_mono_refine_syn; try assumption.
  -
    apply Hie; exact Hbt.
  -
    intros β Hβ.
    eapply a_wf_ptyp_ftv_tvarish; [ | exact Hβ ].
    eapply a_inc_lookup_wf; eassumption.
Qed.

Lemma a_inc_equiv_precise_msubst_aux : forall Θs Δ0 P,
  {{ Θs ⨟ Δ0 ⊢ₚₛ P }}a ->
  forall Θ0 κ σ Θ Δ,
    (forall α, a_binds_tvar α Θs -> a_binds_tvar α Θ0) ->
    {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
    κ ∷ Θ0 ⊑ Θ -> σ ∷ Θ0 ⊑ Θ ->
    (forall α, a_binds_tvar α Θ0 ->
       {{ Θ ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup σ α) }}a) ->
    {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_pskl κ P) ⊑ (msubst_pskl σ P) }}ad.
Proof.
  intros Θs Δ0 P Hwf.
  induction Hwf as [ Θs Δ0 | Θs Δ0 α Hbt
                   | Θs Δ0 P1 P2 Hwf1 IH1 Hwf2 IH2
                   | L Θs Δ0 P0 Hwf0 IH0
                   | Θs Δ0
                   | Θs Δ0 P0 Hg Hwf0 IH0 ];
    intros Θ0 κ σ Θ Δ Hmap Hwf0' Hwfth Hκ Hσ Hie.
  -  unfold ad_precise; cbn. apply ad_refine_syn__unit.
  -
    eapply a_inc_equiv_precise_msubst_var with (Θ0 := Θ0); try eassumption.
    apply Hmap; exact Hbt.
  -
    unfold ad_precise; cbn [msubst_pskl pskl_to_bskl_inh].
    apply ad_refine_syn_arrow_intro;
      [ eapply IH1 | eapply IH2 ]; eassumption.
  -
    unfold ad_precise; cbn [msubst_pskl pskl_to_bskl_inh].
    apply ad_refine_syn_all_intro
      with (L := L `union` dom κ `union` dom σ `union` dom Θ0 `union` dom Θ).
    intros α Hα.
    assert (Hακ : α `notin` dom κ) by (clear - Hα; fsetdec).
    assert (Hασ : α `notin` dom σ) by (clear - Hα; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Hα; fsetdec).
    assert (HαΘ : α `notin` dom Θ) by (clear - Hα; fsetdec).
    assert (HαL : α `notin` L) by (clear - Hα; fsetdec).
    rewrite <- (pskl_to_bskl_inh_open (msubst_pskl κ P0) α).
    rewrite <- (pskl_to_bskl_inh_open (msubst_pskl σ P0) α).
    rewrite <- (@msubst_pskl_open Θ0 κ Θ P0 α Hκ Hακ).
    rewrite <- (@msubst_pskl_open Θ0 σ Θ P0 α Hσ Hασ).
    apply (IH0 α HαL ((α ~ abind_tvar) ++ Θ0)).
    + intros β Hβ. apply a_binds_tvar_cons_tvar.
      destruct (a_binds_tvar_cons_tvar_inv Hβ) as [-> | Hβ']; auto.
    + apply a_wf_aenv__tvar; assumption.
    + apply a_wf_aenv__tvar; assumption.
    + exact (@a_inc__tvar Θ0 κ Θ nil α Hκ a_suffix__nil).
    + exact (@a_inc__tvar Θ0 σ Θ nil α Hσ a_suffix__nil).
    + intros β Hβ.
      destruct (a_binds_tvar_cons_tvar_inv Hβ) as [-> | Hβ'].
      * rewrite (@msubst_lookup_notin κ α Hακ), (@msubst_lookup_notin σ α Hασ).
        apply a_tyequiv__refl. constructor.
      * apply (@a_tyequiv_weaken_cons Θ (α ~ abind_tvar)). apply Hie; exact Hβ'.
  -
    unfold ad_precise; cbn.
    apply (@ad_refine_syn__ghost Θ Δ pskl_ghost). cbn. clear; fsetdec.
  -
    unfold ad_precise; cbn [msubst_pskl pskl_to_bskl_inh].
    apply ad_refine_syn_univ_ghost_keep_intro.
    apply (IH0 Θ0); try assumption.
    intros β Hβ. apply Hmap.
    apply a_binds_tvar_aenv_minus in Hβ. apply Hβ.
Qed.

Lemma a_inc_equiv_precise_msubst_gen : forall Θ0 Δ0 P,
  {{ Θ0 ⨟ Δ0 ⊢ₚₛ P }}a ->
  forall κ σ Θ Δ,
    {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
    κ ∷ Θ0 ⊑ Θ -> σ ∷ Θ0 ⊑ Θ ->
    (forall α, a_binds_tvar α Θ0 ->
       {{ Θ ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup σ α) }}a) ->
    {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_pskl κ P) ⊑ (msubst_pskl σ P) }}ad.
Proof.
  intros Θ0 Δ0 P Hwf κ σ Θ Δ Hwf0 Hwfth Hκ Hσ Hie.
  apply (a_inc_equiv_precise_msubst_aux Hwf (Θ0 := Θ0)); try assumption.
  intros α Hα; exact Hα.
Qed.

Corollary a_inc_equiv_precise_msubst : forall Θ0 Δ0 P κ σ Θ Δ,
  {{ Θ0 ⨟ Δ0 ⊢ₚₛ P }}a ->
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  κ ∷ Θ0 ⊑ Θ -> σ ∷ Θ0 ⊑ Θ ->
  a_inc_equiv Θ0 κ σ Θ ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_pskl κ P) ⊑ (msubst_pskl σ P) }}ad.
Proof.
  intros Θ0 Δ0 P κ σ Θ Δ HwfP Hwf0 Hwfth Hκ Hσ Hie.
  eapply a_inc_equiv_precise_msubst_gen; try eassumption.
  intros α Hbt. eapply prop_context_normalization.a_inc_equiv_lookup_tvar; eassumption.
Qed.

Corollary a_inc_equiv_precise_msubst_flip : forall Θ0 Δ0 P κ σ Θ Δ,
  {{ Θ0 ⨟ Δ0 ⊢ₚₛ P }}a ->
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  κ ∷ Θ0 ⊑ Θ -> σ ∷ Θ0 ⊑ Θ ->
  a_inc_equiv Θ0 κ σ Θ ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_pskl σ P) ⊑ (msubst_pskl κ P) }}ad.
Proof.
  intros Θ0 Δ0 P κ σ Θ Δ HwfP Hwf0 Hwfth Hκ Hσ Hie.
  eapply a_inc_equiv_precise_msubst_gen; try eassumption.
  intros α Hbt. apply a_tyequiv__sym.
  eapply prop_context_normalization.a_inc_equiv_lookup_tvar; eassumption.
Qed.

Lemma a_sub_complete_ghost_p0_precision : forall Θ0 P Θ κ Q,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P)) ∼ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ bskl_ghost ⊳ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣₚ (msubst_pskl κ P) ⊳ (bskl_to_pskl Q) }}ad ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl κ P) ⊑ (bskl_to_pskl Q) }}ad.
Proof.
  intros Θ0 P Θ κ Q Hwf0 Hwfth HwfP Hinc Hconsis Hrs Hrp HwfQ.

  destruct (a_consis_complete Hwf0 (a_wf_pskl__ghost Θ0 empty)
              HwfP Hinc Hwfth Hconsis Hrs Hrp HwfQ)
    as [P1 [Θ1 [Hrun Hopt]]].

  pose proof (a_consis_ghost_p0_output Hrun eq_refl) as HP1; subst P1.

  destruct (a_consis_sound_aux Hrun Hwf0 (a_wf_pskl__ghost Θ0 empty) HwfP
              (@rig_empty _) (@no_flex_dep_empty _) (@faf_empty _))
    as [[[κ1 [Hid Hinc1]] _] [Hwf1 _]].

  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].

  assert (Hσ : msubst_compose ζ κ1 ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose; eassumption).
  assert (Hscope : a_scope_pskl Θ0 P)
    by (exact (a_scope_pskl_of_wf HwfP)).
  assert (Heqσ : msubst_pskl (msubst_compose ζ κ1) P = msubst_pskl ζ P)
    by (exact (msubst_compose_id_pskl Hwf0 Hwf1 Hid Hinc1 Hζ Hscope)).
  unfold ad_precise in Hprec.
  rewrite msubst_bskl_pskl_to_bskl_syn, bskl_to_pskl_pskl_to_bskl_syn in Hprec.
  rewrite <- Heqσ in Hprec.

  pose proof (a_inc_equiv_precise_msubst empty HwfP Hwf0 Hwfth Hinc Hσ Hie)
    as Hstab.
  unfold ad_precise in Hstab |- *.
  eapply ad_refine_syn_trans;
    [ exact Hprec | exact Hwfth | clear; intros α Hα; fsetdec | | exact Hstab ].
  rewrite bskl_to_pskl_pskl_to_bskl_inh. exact HwfQ.
Qed.

Lemma ad_pat_sub_fuel_ti_consis : forall n NM Ψ Θ R Q,
  ad_pat_sub_fuel n NM mode_ti Ψ Θ R Q ->
  {{ empty ⨟ Θ ⊢ˢ R ∼ Q }}ad.
Proof.
  intros n NM Ψ Θ R Q H; inversion H; subst; try congruence; destr_join;
    try assumption;
    try (apply ad_pat_consis__ghost; [ reflexivity ]);
    try (apply ad_pat_consis__ghostg; reflexivity).
Qed.

Lemma tyequiv_slack_consis : forall Θ R' κ R P Ψ Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ R' ≡ᵘ (msubst_uskl_syn κ R) }}a ->
  ⌊ R ⌋ˢ = P ->
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ Q }}ad ->
  {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P)) ∼ Q }}ad.
Proof.
  intros Θ R' κ R P Ψ Q Hwf Hrel HeqP Hc.
  pose proof (a_uskl_tyequiv_erase Hrel) as He.
  rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in He.
  apply (proj1 (skl_tyequiv_consis_transport He Hwf (fun x b Hb => Hb))).
  exact (ad_pat_consis_strip_tags Hc).
Qed.

Lemma tyequiv_slack_refine : forall Θ R' κ R P Pt,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ R' ≡ᵘ (msubst_uskl_syn κ R) }}a ->
  ⌊ R ⌋ˢ = P ->
  {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R' ⌋ˢ ⊳ Pt }}ad ->
  {{ Θ ⨟ empty ⊢ᵣₚ (msubst_pskl κ P) ⊳ Pt }}ad.
Proof.
  intros Θ R' κ R P Pt Hwf Hrel HeqP Hr.
  pose proof (a_uskl_tyequiv_erase Hrel) as He.
  rewrite uskl_to_pskl_msubst_uskl_syn, HeqP in He.
  exact (proj1 (skl_tyequiv_refine_pskl_transport He Hwf (fun x b Hb => Hb)) _ _ Hr).
Qed.

Lemma a_sub_complete_infer : forall n NM Θ0 P0 P R R' Ψ Θ κ Q,
  sub_complete_concl n NM mode_ti Θ0 P0 P R R' Ψ Θ κ Q.
Proof.
  intros n NM Θ0 P0 P R R' Ψ Θ κ Q.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.

  pose proof (tyequiv_slack_refine _ _ Hwfth Hrel HeqP (ad_pat_sub_fuel_ti_refine Hsub))
    as Hrp1.

  assert (HP0 : P0 = pskl_ghost).
  { destruct NM;
      [ pose proof (HmodTY eq_refl) as Hm | pose proof (HmodSK eq_refl) as Hm ];
      inversion Hm; reflexivity. }
  subst P0. cbn in Hrs.

  exists P, Θ0. split; [ apply a_sub__infer | ].
  intros κ1 Hid Hinc1. exists κ.
  destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
  split; [ exact Hout | split; [ exact Hfact | ] ].

  unfold ad_precise.
  rewrite msubst_bskl_pskl_to_bskl_syn, bskl_to_pskl_pskl_to_bskl_syn.
  change ({{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl κ P) ⊑ (bskl_to_pskl Q) }}ad).

  pose proof (tyequiv_slack_consis _ _ Hwfth Hrel HeqP (ad_pat_sub_fuel_ti_consis Hsub))
    as Hc.
  exact (a_sub_complete_ghost_p0_precision Hwf0 Hwfth HwfP Hinc Hc Hrs Hrp1 HwfQ).
Qed.

Lemma ad_refine_pskl_univ_ghost_r_shape : forall Θ Δ P Q,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ (pskl_univ_ghost Q) }}ad ->
  P = pskl_ghost \/ exists P', P = pskl_univ_ghost P'.
Proof.
  intros Θ Δ P Q H.
  remember (pskl_univ_ghost Q) as Qt eqn:HQ. revert Q HQ.
  induction H; intros Qx HQ; try discriminate HQ.
  -  left; reflexivity.
  -  right; eauto.
  -  right; eauto.
  -
    exfalso.
    destruct (IHad_refine_pskl Qx HQ) as [Hc | [P0 Hc]];
      destruct τ; cbn in Hc; discriminate Hc.
Qed.

Lemma guarded_uskl_erase_not_ghost : forall R,
  guarded_uskl R ->
  ⌊ R ⌋ˢ <> pskl_ghost /\ (forall P, ⌊ R ⌋ˢ <> pskl_univ_ghost P).
Proof.
  intros R H; inversion H; subst; cbn;
    (split; [ discriminate | intros; discriminate ]).
Qed.

Lemma guarded_uskl_msubst_erase : forall κ R,
  guarded_uskl (msubst_uskl_syn κ R) ->
  lc_pskl ⌊ R ⌋ˢ ->
  guarded_pskl ⌊ R ⌋ˢ.
Proof.
  intros κ R Hg Hlc; destruct R; cbn in Hg |- *;
    try (inversion Hg; fail);
    try (inversion Hlc; fail);
    [ apply guarded_pskl__unit
    | apply guarded_pskl__var
    | inversion Hlc; subst; apply guarded_pskl__arrow; assumption ].
Qed.

Lemma ad_refine_syn_ghost_univ_ghost_inv : forall Θ Δ Q,
  {{ Θ ⨟ Δ ⊢ᵣ bskl_ghost ⊳ (bskl_univ_ghost Q) }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ bskl_ghost ⊳ Q }}ad.
Proof.
  intros Θ Δ Q H; inversion H; subst.
  destruct P; cbn in *; try discriminate.
  match goal with HQ : bskl_univ_ghost _ = bskl_univ_ghost _ |- _ =>
    inversion HQ; subst end.
  apply ad_refine_syn__ghost; assumption.
Qed.

Lemma a_sub_complete_univ_ghost_r : forall n Θ0 P0 P R R' Ψ Θ κ Q,
  guarded_uskl R' ->
  guarded_bskl Q ->
  {{ empty ⨟ Θ ⊢ˢ R' ∼ᵣ Q }}ad ->
  sub_complete_concl n a_sub_mode_sk mode_tc Θ0 P0 P R R' Ψ Θ κ (bskl_univ_ghost Q).
Proof.
  intros n Θ0 P0 P R R' Ψ Θ κ Q HgT HgQ Hj.
  destruct Hj as [Hrow Hrfn].
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.

  assert (HP0 : P0 = pskl_ghost)
    by (pose proof (HmodSK eq_refl) as Hm; inversion Hm; reflexivity).
  subst P0. cbn in Hrs.

  assert (HgP : guarded_pskl P).
  { rewrite <- HeqP. eapply guarded_uskl_msubst_erase;
      [ eapply a_uskl_tyequiv_guarded; eassumption
      | rewrite HeqP; eapply a_wf_pskl_lc; exact HwfP ]. }
  exists (pskl_univ_ghost P), Θ0.
  split; [ apply a_sub__univ_ghost_r; exact HgP | ].
  intros κ1 Hid Hinc1. exists κ.
  destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
  split; [ exact Hout | split; [ exact Hfact | ] ].
  pose proof (tyequiv_slack_consis _ _ Hwfth Hrel HeqP Hrow) as Hc.
  assert (Hrs' : {{ Θ ⨟ empty ⊢ᵣ bskl_ghost ⊳ Q }}ad)
    by (apply ad_refine_syn_ghost_univ_ghost_inv; exact Hrs).
  pose proof (tyequiv_slack_refine _ _ Hwfth Hrel HeqP Hrfn) as Hrp.
  assert (HwfQ' : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a).
  { cbn in HwfQ. inversion HwfQ; subst.
    rewrite aenv_minus_empty in *. assumption. }
  pose proof (a_sub_complete_ghost_p0_precision Hwf0 Hwfth HwfP Hinc Hc Hrs' Hrp
                HwfQ') as Hcore.

  unfold ad_precise in Hcore |- *.
  rewrite msubst_bskl_pskl_to_bskl_syn.
  cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
  rewrite bskl_to_pskl_pskl_to_bskl_syn.
  apply ad_refine_syn_univ_ghost_keep_intro; exact Hcore.
Qed.

Lemma a_sub_complete_check : forall n Θ0 P0 P R R' Ψ Θ κ B,
  guarded_uskl R' ->
  guarded_pskl B ->
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ᵣ (pskl_to_bskl_inh B) }}ad ->
  guarded_pskl P0 ->
  {{ Θ ⨟ empty ⊢ₚₛ B }}a ->
  sub_complete_concl n a_sub_mode_ty mode_tc Θ0 P0 P R R' Ψ Θ κ (pskl_to_bskl_inh B).
Proof.
  intros n Θ0 P0 P R R' Ψ Θ κ B HgT HgB Hj HgP0 HwfB.
  pose proof (ad_consis_join_consis Hj) as Hrow.
  pose proof (ad_consis_join_inh_refine _ Hj) as Hrfn.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.

  assert (Hrp : {{ Θ ⨟ empty ⊢ᵣₚ (msubst_pskl κ P) ⊳ (bskl_to_pskl (pskl_to_bskl_inh B)) }}ad).
  { rewrite bskl_to_pskl_pskl_to_bskl_inh.
    exact (tyequiv_slack_refine _ _ Hwfth Hrel HeqP Hrfn). }

  assert (HgP : guarded_pskl P).
  { rewrite <- HeqP. eapply guarded_uskl_msubst_erase;
      [ eapply a_uskl_tyequiv_guarded; eassumption
      | rewrite HeqP; eapply a_wf_pskl_lc; exact HwfP ]. }
  assert (HgfP : pskl_ghost_free P).
  { rewrite <- HeqP.
    eapply msubst_pskl_ghost_free_inv with (κ := κ).
    rewrite <- uskl_to_pskl_msubst_uskl_syn.
    apply uskl_ghost_free_to_pskl.
    eapply a_uskl_tyequiv_ghost_free; [ exact Hrel | exact (Hgf eq_refl) ]. }

  pose proof (tyequiv_slack_consis _ _ Hwfth Hrel HeqP Hrow) as Hc.
  destruct (a_consis_complete Hwf0 HwfP0 HwfP Hinc Hwfth Hc Hrs Hrp HwfQ)
    as [P1 [Θ1 [Hrun Hopt]]].
  destruct (a_consis_sound_aux Hrun Hwf0 HwfP0 HwfP
              (@rig_empty _) (@no_flex_dep_empty _) (@faf_empty _))
    as [_ [Hwf1 _]].

  exists P0, Θ1. split;
    [ apply a_sub__check;
        [ exact HgfP
        | apply a_ty_mode_compat_tc_ghost_free; exact (HmodTY eq_refl)
        | exact HgP | exact HgP0 | exists P1; exact Hrun ] | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
  exists ζ. split; [ exact Hζ | split; [ exact Hie | ] ].

  assert (Hσ : msubst_compose ζ κ1 ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose; eassumption).
  assert (Hscope : a_scope_pskl Θ0 P0)
    by (exact (a_scope_pskl_of_wf HwfP0)).
  assert (Heqσ : msubst_pskl (msubst_compose ζ κ1) P0 = msubst_pskl ζ P0)
    by (exact (msubst_compose_id_pskl Hwf0 Hwf1 Hid Hinc1 Hζ Hscope)).
  pose proof (a_inc_equiv_precise_msubst_flip empty HwfP0 Hwf0 Hwfth Hinc Hσ Hie)
    as Hstab.
  rewrite Heqσ in Hstab.
  unfold ad_precise in Hstab |- *.
  rewrite msubst_bskl_pskl_to_bskl_syn, bskl_to_pskl_pskl_to_bskl_syn.
  rewrite bskl_to_pskl_pskl_to_bskl_inh.
  eapply ad_refine_syn_trans;
    [ exact Hrs
    | exact Hwfth | clear; intros α Hα; fsetdec
    | rewrite bskl_to_pskl_pskl_to_bskl_inh; exact HwfB
    | exact Hstab ].
Qed.

Lemma msubst_compose_id_lookup : forall w ζ α,
  is_id_msubst w ->
  α `in` dom w ->
  msubst_lookup (msubst_compose ζ w) α = msubst_lookup ζ α.
Proof.
  induction w as [ | [β τ] w' IHw ]; intros ζ α Hid Hα; cbn in *.
  - exfalso; clear - Hα; fsetdec.
  - inversion Hid; subst.
    match goal with
    | Hie : is_id_entry _ |- _ =>
        unfold is_id_entry in Hie; cbn in Hie; subst τ
    end.
    lazymatch goal with
    | |- context [ if ?c then _ else _ ] => destruct c as [Heq | Hne]
    end.
    + subst. cbn. reflexivity.
    + apply IHw; [ assumption | clear - Hα Hne; fsetdec ].
Qed.

Lemma msubst_uskl_syn_compose_id : forall R w ζ,
  is_id_msubst w ->
  (forall α, α `in` ftvar_in_uskl R ->
     α `in` dom w \/ (α `notin` dom w /\ α `notin` dom ζ)) ->
  msubst_uskl_syn (msubst_compose ζ w) R = msubst_uskl_syn ζ R.
Proof.
  intros R w ζ Hid Hcov. apply msubst_uskl_syn_agree.
  intros α Hα. destruct (Hcov α Hα) as [Hin | [Hw Hζ]].
  - apply msubst_compose_id_lookup; assumption.
  - rewrite (msubst_lookup_notin ζ Hζ).
    apply msubst_lookup_notin.
    pose proof (dom_msubst_compose ζ w) as Hd.
    clear - Hw Hd; fsetdec.
Qed.

Lemma a_sub_complete_arrow : forall n NM M Θ0 P0 P Ra Rb R1' R2' Ψ Θ κ Q1 Q2,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  sub_complete_concl (S n) NM (mode_fn M) Θ0 P0 P (uskl_arrow Ra Rb)
    (uskl_arrow R1' R2') Ψ Θ κ (bskl_arrow Q1 Q2).
Proof.
  intros n NM M Θ0 P0 P Ra Rb R1' R2' Ψ Θ κ Q1 Q2 IH.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
  cbn in HeqP. subst P.
  cbn in Hrel.
  destruct (a_uskl_tyequiv_arrow_arrow_inv Hwfth Hrel) as [Hrel1 Hrel2].

  inversion Hsub; subst.
  match goal with
  | Hj : {{ _ ⨟ Θ ⊢ˢ R1' ∼ᵣ Q1 }}ad,
    Hs2 : ad_pat_sub_fuel _ _ _ _ Θ R2' Q2 |- _ =>
      rename Hs2 into Hsub2; destruct Hj as [Hj1 Hrfn1]
  end.

  assert (Hsplit : exists P0a P0b, P0 = pskl_arrow P0a P0b /\
            (NM = a_sub_mode_sk -> a_sk_mode_compat M P0b) /\
            (NM = a_sub_mode_ty -> a_ty_mode_compat M P0b)).
  { destruct NM.
    - pose proof (HmodTY eq_refl) as Hm; inversion Hm; subst.
      do 2 eexists. split; [ reflexivity | ].
      split; [ intro Hc; discriminate Hc | intro; assumption ].
    - pose proof (HmodSK eq_refl) as Hm; inversion Hm; subst.
      do 2 eexists. split; [ reflexivity | ].
      split; [ intro; assumption | intro Hc; discriminate Hc ]. }
  destruct Hsplit as [P0a [P0b [-> [HmodSKb HmodTYb]]]].

  assert (HwfP0a : {{ Θ0 ⨟ empty ⊢ₚₛ P0a }}a) by (inversion HwfP0; assumption).
  assert (HwfP0b : {{ Θ0 ⨟ empty ⊢ₚₛ P0b }}a) by (inversion HwfP0; assumption).
  assert (HwfPa : {{ Θ0 ⨟ empty ⊢ₚₛ ⌊ Ra ⌋ˢ }}a) by (inversion HwfP; assumption).
  assert (HwfPb : {{ Θ0 ⨟ empty ⊢ₚₛ ⌊ Rb ⌋ˢ }}a) by (inversion HwfP; assumption).

  cbn in Hrs.
  inversion Hrs; subst.
  match goal with
  | Ha : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0a)) ⊳ Q1 }}ad,
    Hb : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0b)) ⊳ Q2 }}ad |- _ =>
      rename Ha into Hrs1; rename Hb into Hrs2
  end.

  pose proof (tyequiv_slack_consis _ _ Hwfth Hrel1 eq_refl Hj1) as Hc1.
  pose proof (tyequiv_slack_refine _ _ Hwfth Hrel1 eq_refl Hrfn1) as Hrp1.
  destruct (a_consis_complete Hwf0 HwfP0a HwfPa Hinc Hwfth Hc1
              Hrs1 Hrp1 ltac:(simpl in HwfQ; inversion HwfQ; assumption))
    as [Q1' [Θ1 [Hrun1 Hopt1]]].

  destruct (a_consis_sound_aux Hrun1 Hwf0 HwfP0a HwfPa
              (@rig_empty _) (@no_flex_dep_empty _) (@faf_empty _))
    as [[[w1 [Hidw1 Hincw1]] Hdefs1] [Hwf1 [_ [_ [Hsol1 _]]]]].
  destruct (Hopt1 w1 Hidw1 Hincw1) as [ζ1 [Hζ1 [Hie1 Hprec1]]].

  assert (HwfP0b1 : {{ Θ1 ⨟ empty ⊢ₚₛ P0b }}a).
  { eapply a_wf_pskl_isub; [ exact HwfP0b | ].
    split; [ exists w1; split; assumption | exact Hdefs1 ]. }
  assert (HwfPb1 : {{ Θ1 ⨟ empty ⊢ₚₛ ⌊ Rb ⌋ˢ }}a).
  { eapply a_wf_pskl_isub; [ exact HwfPb | ].
    split; [ exists w1; split; assumption | exact Hdefs1 ]. }
  assert (Hσ : msubst_compose ζ1 w1 ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose; eassumption).
  assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
  assert (Hlcζ1 : msubst_lc ζ1) by (eapply a_inc_msubst_lc; exact Hζ1).
  assert (Hlcc1 : msubst_lc (msubst_compose ζ1 w1))
    by (apply msubst_lc_compose;
        [ exact Hlcζ1 | eapply is_id_msubst_values_lc; exact Hidw1 ]).

  assert (Hcov : forall α, α `in` ftvar_in_uskl Rb -> a_binds_tvar α Θ0).
  { intros α Hα.
    assert (Hα' : α `in` ftvar_in_pskl ⌊ Rb ⌋ˢ)
      by (rewrite ftvar_in_pskl_uskl_to_pskl; exact Hα).
    exact (a_wf_pskl_ftv_binds HwfPb Hα'). }

  assert (Hnotflex : forall α, binds α abind_tvar Θ0 ->
            α `notin` dom w1 /\ α `notin` dom ζ1).
  { intros α Hb. split.
    - intros Hα. pose proof (a_inc_dom_flex Hincw1 Hα) as Hf.
      destruct Hf as [Hb' | [τ Hb']];
        pose proof (binds_unique _ _ _ _ _ Hb Hb'
                      (a_wf_aenv_uniq Hwf0)) as Hc;
        discriminate Hc.
    - intros Hα. pose proof (a_inc_dom_flex Hζ1 Hα) as Hf.
      assert (Hb1 : binds α abind_tvar Θ1)
        by (eapply a_inc_binds_tvar; eassumption).
      destruct Hf as [Hb' | [τ Hb']];
        pose proof (binds_unique _ _ _ _ _ Hb1 Hb'
                      (a_wf_aenv_uniq Hwf1)) as Hc;
        discriminate Hc. }

  assert (Hlcb : lc_uskl Rb)
    by (apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact HwfPb).
  assert (Hgen : {{ Θ ⊢ (msubst_uskl_syn κ Rb) ≡ᵘ
                     (msubst_uskl_syn (msubst_compose ζ1 w1) Rb) }}a).
  { eapply a_inc_equiv_msubst_uskl;
      [ exact Hlcb
      | intros α Hα; left; apply Hcov; exact Hα
      | exact Hie1 | exact Hinc | exact Hσ | exact Hwf0 ]. }
  assert (Hcollapse : msubst_uskl_syn (msubst_compose ζ1 w1) Rb
                      = msubst_uskl_syn ζ1 Rb).
  { apply msubst_uskl_syn_compose_id; [ exact Hidw1 | ].
    intros α Hα. pose proof (Hcov α Hα) as Hb.
    destruct Hb as [Hb | [Hb | [τ Hb]]].
    - right. apply Hnotflex. exact Hb.
    - left. eapply a_inc_flex_dom;
        [ exact Hincw1 | exact Hwf0 | left; exact Hb ].
    - left. eapply a_inc_flex_dom;
        [ exact Hincw1 | exact Hwf0 | right; exists τ; exact Hb ]. }
  assert (Hslack : {{ Θ ⊢ R2' ≡ᵘ (msubst_uskl_syn ζ1 Rb) }}a).
  { rewrite <- Hcollapse.
    eapply a_uskl_tyequiv_trans; eassumption. }

  assert (HscP0b : a_scope_pskl Θ0 P0b)
    by (exact (a_scope_pskl_of_wf HwfP0b)).
  assert (Heqb0 : {{ Θ ⊢ (msubst_pskl κ P0b) ≡ˢ (msubst_pskl ζ1 P0b) }}a).
  { replace (msubst_pskl ζ1 P0b)
      with (msubst_pskl (msubst_compose ζ1 w1) P0b)
      by (eapply msubst_compose_id_pskl;
          [ exact Hwf0 | exact Hwf1 | exact Hidw1 | exact Hincw1
          | exact Hζ1 | exact HscP0b ]).
    eapply a_inc_equiv_msubst_pskl; eassumption. }
  destruct (skl_tyequiv_refine_syn_transport Heqb0 Hwfth
              (fun x b Hb => Hb)) as [Hrst _].
  pose proof (Hrst _ _ Hrs2) as Hrs2'.

  assert (HwfQ2 : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q2) }}a)
    by (cbn in HwfQ; inversion HwfQ; assumption).

  assert (Hgf2 : NM = a_sub_mode_ty -> uskl_ghost_free R2')
    by (intro HNM; pose proof (Hgf HNM) as Hga; inversion Hga; assumption).

  destruct (IH NM M Θ1 P0b (⌊ Rb ⌋ˢ) Rb R2' _ Θ ζ1 Q2
              Hwf1 Hwfth HwfP0b1 HwfPb1 HmodSKb HmodTYb eq_refl Hζ1
              Hslack Hsub2 Hrs2' HwfQ2 Hgf2)
    as [Q2' [Θ2 [Hrun2 Hopt2]]].

  exists (pskl_arrow Q1' Q2'), Θ2. split.
  { eapply a_sub__arrow; eassumption. }

  intros κf Hidf Hincf.
  destruct (a_sub_sound Hrun2 Hwf1 HwfP0b1 HwfPb1 HmodSKb HmodTYb)
    as [[[w2 [Hidw2 Hincw2]] Hdefs2] [Hwf2 _]].
  destruct (Hopt2 w2 Hidw2 Hincw2) as [ζ2 [Hζ2 [Hie2 Hprec2]]].
  assert (Heqw : w1 = κf) by (eapply is_id_inc_unique; eauto).
  subst κf.
  exists ζ2. split; [ exact Hζ2 | ]. split.
  { eapply a_inc_equiv_glue with
      (Θmid := Θ1) (Θfin := Θ2) (κ1b := w2) (ζ1 := ζ1);
      [ exact Hwf0 | exact Hwf1 | exact Hwf2 | exact Hwfth
      | exact Hidw1 | exact Hidw2
      | intros α Hα;
        pose proof (a_inc_dom_flex Hincw1 Hα) as Hfα;
        eapply a_inc_flex_dom; [ exact Hincw2 | exact Hwf1 | ];
        eapply (proj2 (proj2 a_assign_unify_consis_flex_preserve)); eassumption
      | exact Hincw1 | exact Hincw2 | exact Hζ1 | exact Hζ2
      | exact Hie1 | exact Hie2 ]. }

  assert (HscQ1' : a_scope_pskl Θ1 Q1')
    by (exact (a_scope_pskl_of_wf
                 (a_consis_output_wf_nil Hrun1 Hwf0 HwfP0a HwfPa))).
  assert (Hlcζ2 : msubst_lc ζ2) by (eapply a_inc_msubst_lc; exact Hζ2).
  assert (Hlcc2 : msubst_lc (msubst_compose ζ2 w2))
    by (apply msubst_lc_compose;
        [ exact Hlcζ2 | eapply is_id_msubst_values_lc; exact Hidw2 ]).
  assert (Heqζ : {{ Θ ⊢ (msubst_pskl ζ1 Q1') ≡ˢ (msubst_pskl ζ2 Q1') }}a).
  { replace (msubst_pskl ζ2 Q1')
      with (msubst_pskl (msubst_compose ζ2 w2) Q1')
      by (eapply msubst_compose_id_pskl;
          [ exact Hwf1 | exact Hwf2 | exact Hidw2 | exact Hincw2
          | exact Hζ2 | exact HscQ1' ]).
    eapply a_inc_equiv_msubst_pskl; eassumption. }
  unfold ad_precise in Hprec1, Hprec2 |- *.
  rewrite msubst_bskl_pskl_to_bskl_syn in Hprec1, Hprec2 |- *.
  rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec1, Hprec2 |- *.
  cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
  apply ad_refine_syn_arrow_intro.
  -
    destruct (skl_tyequiv_refine_syn_transport Heqζ Hwfth
                (fun x b Hb => Hb)) as [Hpt _].
    apply Hpt. exact Hprec1.
  -
    exact Hprec2.
Qed.

Lemma a_sub_ty_tc_output : forall P0 Θ0 P P1 Θ1,
  a_sub a_sub_mode_ty mode_tc P0 Θ0 P P1 Θ1 ->
  P1 = P0.
Proof.
  intros P0 Θ0 P P1 Θ1 H.
  remember a_sub_mode_ty as NM eqn:HNM.
  remember mode_tc as M eqn:HM.
  induction H; try discriminate HNM; try discriminate HM; auto.
Qed.

Lemma is_id_inc_dom_mono : forall κ Θ0 Θ,
  is_id_msubst κ ->
  κ ∷ Θ0 ⊑ Θ ->
  dom Θ0 [<=] dom Θ.
Proof.
  intros κ Θ0 Θ Hid Hinc; revert Hid; induction Hinc; intros Hid; simpl.
  - clear; fsetdec.
  -
    inversion Hid; subst.
    match goal with Hie : is_id_entry _ |- _ =>
      unfold is_id_entry in Hie; cbn in Hie; subst end.
    match goal with Hwfv : a_wf_ptyp _ (ptyp_var_f _) |- _ =>
      inversion Hwfv; subst end.
    match goal with Hbt : a_binds_tvar _ _ |- _ =>
      destruct Hbt as [Hb | [Hb | [τ0 Hb]]]; apply binds_In in Hb end;
    match goal with IH0 : is_id_msubst _ -> _ |- _ =>
      specialize (IH0 ltac:(assumption)) end;
    match goal with IH0 : dom _ [<=] dom _ |- _ =>
      clear - IH0 Hb; fsetdec end.
  -
    inversion Hid; subst.
    match goal with Hie : is_id_entry _ |- _ =>
      unfold is_id_entry in Hie; cbn in Hie; subst end.
    match goal with Hwfv : a_wf_ptyp _ (ptyp_var_f _) |- _ =>
      inversion Hwfv; subst end.
    match goal with Hbt : a_binds_tvar _ _ |- _ =>
      destruct Hbt as [Hb | [Hb | [τ0 Hb]]]; apply binds_In in Hb end;
    match goal with IH0 : is_id_msubst _ -> _ |- _ =>
      specialize (IH0 ltac:(assumption)) end;
    match goal with IH0 : dom _ [<=] dom _ |- _ =>
      clear - IH0 Hb; fsetdec end.
  -
    specialize (IHHinc Hid). rewrite ! dom_app. simpl.
    clear - IHHinc; fsetdec.
  -
    specialize (IHHinc Hid). rewrite ! dom_app. simpl.
    clear - IHHinc; fsetdec.
  -
    specialize (IHHinc Hid). rewrite ! dom_app. simpl.
    clear - IHHinc; fsetdec.
Qed.

Lemma msubst_compose_id_app_agree : forall κf κa ζ,
  is_id_msubst κf ->
  (forall x, x `in` dom κf -> x `notin` dom κa) ->
  msubst_compose (κa ++ ζ) κf = msubst_compose ζ κf.
Proof.
  induction κf as [ | [x τ] κf IH ]; intros κa ζ Hid Hdisj; simpl.
  - reflexivity.
  - inversion Hid; subst.
    match goal with Hie : is_id_entry _ |- _ =>
      unfold is_id_entry in Hie; cbn in Hie; subst end.
    f_equal.
    + f_equal. simpl.
      apply msubst_lookup_app_notin.
      apply Hdisj. simpl. clear; fsetdec.
    + apply IH; [ assumption | ].
      intros y Hy. apply Hdisj. simpl. clear - Hy; fsetdec.
Qed.

Lemma ad_refine_syn_all_inh_r_shape : forall Θ Δ Qs B,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ (bskl_all_inh B) }}ad ->
  (exists A, Qs = bskl_all_inh A) \/ (exists Q0, Qs = bskl_univ_ghost Q0).
Proof.
  intros Θ Δ Qs B H.
  remember (bskl_all_inh B) as T eqn:HT. revert B HT.
  induction H; intros B0 HT; try discriminate HT.
  -  left; eauto.
  -
    destruct P; simpl in HT; discriminate HT.
  -  right; eauto.
  -
    exfalso.
    destruct (IHad_refine_syn _ HT) as [[A HA] | [Q0 HQ0]];
      destruct τ; simpl in *; try discriminate HA; try discriminate HQ0.
Qed.

Lemma pskl_to_bskl_inh_all_inh_inv : forall X A,
  pskl_to_bskl_inh X = bskl_all_inh A ->
  exists X0, X = pskl_all_syn X0 /\ A = pskl_to_bskl_inh X0.
Proof.
  intros X A HA; destruct X; simpl in HA; inversion HA; subst.
  eexists; split; reflexivity.
Qed.

Lemma pskl_to_bskl_inh_univ_ghost_inv : forall X Q,
  pskl_to_bskl_inh X = bskl_univ_ghost Q ->
  exists X0, X = pskl_univ_ghost X0.
Proof.
  intros X Q HQ; destruct X; simpl in HQ; inversion HQ; subst.
  eexists; reflexivity.
Qed.

Lemma msubst_pskl_all_syn_inv : forall Θ0 κ Θ P0 X,
  κ ∷ Θ0 ⊑ Θ ->
  msubst_pskl κ P0 = pskl_all_syn X ->
  exists P0', P0 = pskl_all_syn P0' /\ X = msubst_pskl κ P0'.
Proof.
  intros Θ0 κ Θ P0 X Hinc Heq.
  destruct P0; simpl in Heq; try discriminate Heq.
  -
    exfalso.
    pose proof (a_inc_lookup_mono α Hinc) as Hm.
    destruct (msubst_lookup κ α); simpl in Heq;
      try discriminate Heq; inversion Hm.
  - inversion Heq; subst. eexists; split; reflexivity.
Qed.

Lemma msubst_pskl_univ_ghost_inv : forall Θ0 κ Θ P0 X,
  κ ∷ Θ0 ⊑ Θ ->
  msubst_pskl κ P0 = pskl_univ_ghost X ->
  exists P0', P0 = pskl_univ_ghost P0'.
Proof.
  intros Θ0 κ Θ P0 X Hinc Heq.
  destruct P0; simpl in Heq; try discriminate Heq; eauto.
  exfalso.
  pose proof (a_inc_lookup_mono α Hinc) as Hm.
  destruct (msubst_lookup κ α); simpl in Heq;
    try discriminate Heq; inversion Hm.
Qed.

Lemma ptyp_to_pskl_not_univ_ghost : forall A X,
  ptyp_to_pskl A <> pskl_univ_ghost X.
Proof. intros A X; destruct A; simpl; discriminate. Qed.

Lemma ptyp_to_pskl_all_syn_inv : forall A X,
  ptyp_to_pskl A = pskl_all_syn X ->
  exists A0, A = ptyp_all A0 /\ X = ptyp_to_pskl A0.
Proof.
  intros A X HX; destruct A; simpl in HX; inversion HX; subst.
  eexists; split; reflexivity.
Qed.

Lemma a_sub_complete_forall_r : forall n Θ0 P0 P R R' Ψ Θ κ B L,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  (forall α, α `notin` L ->
     ad_pat_sub_fuel n a_sub_mode_ty mode_tc Ψ ((α ~ abind_tvar) ++ Θ) R'
       (open_bskl_wrt_bskl B (bskl_var_f α))) ->
  sub_complete_concl (S n) a_sub_mode_ty mode_tc Θ0 P0 P R R' Ψ Θ κ
    (bskl_all_inh B).
Proof.
  intros n Θ0 P0 P R R' Ψ Θ κ B L IH Hjoin.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
  pose proof (HmodTY eq_refl) as Hmty.
  assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).

  destruct (ad_refine_syn_all_inh_r_shape Hrs) as [[As HAs] | [Q0 HQ0]].
  2: { exfalso.
       destruct (@pskl_to_bskl_inh_univ_ghost_inv _ _ HQ0) as [X0 HX0].
       destruct (@msubst_pskl_univ_ghost_inv _ _ _ _ _ Hinc HX0) as [P0t HP0t].
       subst P0. inversion Hmty.
       match goal with
       | He : ptyp_to_pskl _ = pskl_univ_ghost _ |- _ =>
           eapply ptyp_to_pskl_not_univ_ghost; exact He
       | He : pskl_univ_ghost _ = ptyp_to_pskl _ |- _ =>
           eapply ptyp_to_pskl_not_univ_ghost; symmetry; exact He
       end. }
  destruct (@pskl_to_bskl_inh_all_inh_inv _ _ HAs) as [X [HX HAseq]].
  destruct (@msubst_pskl_all_syn_inv _ _ _ _ _ Hinc HX) as [P0' [HP0eq HXeq]].
  subst P0 X As.
  inversion Hmty; subst.
  match goal with
  | He : ptyp_to_pskl _ = pskl_all_syn _ |- _ => rename He into HA
  | He : pskl_all_syn _ = ptyp_to_pskl _ |- _ =>
      symmetry in He; rename He into HA
  end.
  destruct (@ptyp_to_pskl_all_syn_inv _ _ HA) as [A0 [HAeq HP0'eq]].
  subst.
  cbn [msubst_pskl pskl_to_bskl_inh] in Hrs.

  inversion Hrs; subst.
  match goal with
  | Hn : forall α, α `notin` ?Lx -> ad_refine_syn _ _ _ _ |- _ =>
      rename Hn into Hfill
  end.
  cbn in HwfQ.
  destruct (a_wf_pskl_all_inv HwfQ) as [Lw HwQbody].
  match type of Hfill with
  | forall α, α `notin` ?Lx -> _ =>
      destruct (atom_fresh
        (L `union` Lx `union` Lw `union` dom Θ0 `union` dom Θ `union` dom κ
           `union` ftvar_in_pskl (ptyp_to_pskl A0) `union` ftvar_in_bskl B
           `union` ftvar_in_pskl ⌊ R ⌋ˢ)) as [α Fr]
  end.
  assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; solve_notin_auto).
  assert (HαΘ : α `notin` dom Θ) by (clear - Fr; solve_notin_auto).
  assert (Hακ : α `notin` dom κ) by (clear - Fr; solve_notin_auto).

  assert (Hwf0' : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
    by (apply a_wf_aenv__tvar; eassumption).
  assert (Hwfth' : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
    by (apply a_wf_aenv__tvar; eassumption).
  assert (HwfP0α : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                     (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α)) }}a).
  { eapply a_wf_pskl_all_syn_open_tvar;
      [ exact HwfP0 | clear - Fr; solve_notin_auto ]. }
  assert (HwfPα : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ ⌊ R ⌋ˢ }}a)
    by (apply (a_wf_pskl_tvar_mono HwfP); intros β' Hβ';
        apply a_binds_tvar_cons_tvar; right; exact Hβ').
  assert (HmodSKα : a_sub_mode_ty = a_sub_mode_sk ->
            a_sk_mode_compat mode_tc
              (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α)))
    by (intro Hc; discriminate Hc).
  assert (HmodTYα : a_sub_mode_ty = a_sub_mode_ty ->
            a_ty_mode_compat mode_tc
              (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))).
  { intros _. rewrite <- ptyp_to_pskl_open. apply a_ty_mode_compat__tc. }
  assert (Hinc' : κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑ ((α ~ abind_tvar) ++ Θ)).
  { apply (a_inc__tvar (Ξ:=nil) α Hinc).
    apply a_decls_suffix. apply a_decls__nil. }
  assert (Hrel' : {{ ((α ~ abind_tvar) ++ Θ) ⊢ R' ≡ᵘ (msubst_uskl_syn κ R) }}a)
    by (apply a_uskl_tyequiv_weaken_cons; exact Hrel).
  pose proof (Hjoin α ltac:(clear - Fr; solve_notin_auto)) as Hjoinα.
  assert (Hrsα : {{ ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ (pskl_to_bskl_inh
               (msubst_pskl κ
                  (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α)))) ⊳ (open_bskl_wrt_bskl B (bskl_var_f α)) }}ad).
  { pose proof (Hfill α ltac:(clear - Fr; solve_notin_auto)) as Hf0.
    rewrite <- pskl_to_bskl_inh_open in Hf0.
    rewrite <- (msubst_pskl_open_lc (ptyp_to_pskl A0) Hlcκ Hακ) in Hf0.
    eapply ad_refine_syn_delta_mono; [ exact Hf0 | clear; fsetdec ]. }
  assert (HwfQα : {{ ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
                    (bskl_to_pskl (open_bskl_wrt_bskl B (bskl_var_f α))) }}a).
  { rewrite bskl_to_pskl_open.
    eapply a_wf_pskl_delta_mono;
      [ apply HwQbody; clear - Fr; solve_notin_auto
      | intros β _ Hβ; clear - Hβ; fsetdec ]. }

  destruct (IH a_sub_mode_ty mode_tc ((α ~ abind_tvar) ++ Θ0)
              (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))
              (⌊ R ⌋ˢ) R R' Ψ ((α ~ abind_tvar) ++ Θ) κ
              (open_bskl_wrt_bskl B (bskl_var_f α))
              Hwf0' Hwfth' HwfP0α HwfPα HmodSKα HmodTYα eq_refl Hinc'
              Hrel' Hjoinα Hrsα HwfQα Hgf)
    as [P1 [Θo [Hrun Hopt]]].
  pose proof (a_sub_ty_tc_output Hrun) as ->.

  destruct (a_sub_sound Hrun Hwf0' HwfP0α HwfPα HmodSKα HmodTYα)
    as [[[w1 [Hidw1 Hincw1]] Hdefs1] [HwfΘo _]].
  destruct (a_inc_tvar_inv Hincw1) as [Ξj [Θ1 [-> [Hsufj Hincw1']]]].
  assert (HuqΘo : uniq (Ξj ++ (α ~ abind_tvar) ++ Θ1))
    by (apply a_wf_aenv_uniq; exact HwfΘo).
  assert (HαΞj : α `notin` dom Ξj)
    by (clear - HuqΘo; simpl_env in HuqΘo; destruct_uniq;
        unfold disjoint in *; simpl_env in *; fsetdec).
  assert (HαΘ1 : α `notin` dom Θ1)
    by (clear - HuqΘo; simpl_env in HuqΘo; destruct_uniq;
        unfold disjoint in *; simpl_env in *; fsetdec).
  assert (Hdom01 : dom Θ0 [<=] dom Θ1)
    by (eapply is_id_inc_dom_mono; eassumption).
  assert (HdisjΞ0 : forall γ, γ `in` dom Ξj -> γ `notin` dom Θ0).
  { intros γ Hγ Hc.
    assert (HγΘ1 : γ `in` dom Θ1) by (clear - Hdom01 Hc; fsetdec).
    clear - HuqΘo Hγ HγΘ1. simpl_env in HuqΘo. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (HuqJ : uniq (Ξj ++ Θ0)).
  { pose proof (a_wf_aenv_uniq Hwf0) as Huq0.
    pose proof HuqΘo as Huq'. simpl_env in Huq'. destruct_uniq.
    assert (Hdisj0 : disjoint Ξj Θ0)
      by (unfold disjoint in *; simpl_env in *; fsetdec).
    solve_uniq. }

  exists (pskl_all_syn (ptyp_to_pskl A0)), Θ1.
  split.
  { eapply a_sub__forall_r with (α := α) (Ξ := Ξj);
      [ exact (ptyp_to_pskl_ghost_free (ptyp_all A0))
      | exact Hsufj | exact HuqJ | | exact Hrun ].
    rewrite dom_app.
    clear - Fr HαΞj HαΘ1. simpl in Fr. solve_notin_auto. }

  intros κf Hidf Hincf.
  assert (Hincf' : κf ∷ ((α ~ abind_tvar) ++ Θ0) ⊑
                     (Ξj ++ (α ~ abind_tvar) ++ Θ1)).
  { apply (a_inc__tvar (Ξ:=Ξj) α Hincf). exact Hsufj. }
  destruct (Hopt κf Hidf Hincf') as [ζ' [Hζ' [Hie' Hprec']]].

  destruct (@a_inc_peel_suffix _ _ _ _ Hsufj Hζ')
    as [κa [ζ [-> [Hdomκa Hζmid]]]].
  pose proof (a_inc_tvar_head_inv Hζmid) as Hζfin.
  exists ζ. split; [ exact Hζfin | ]. split.
  {
    pose proof (a_inc_equiv_tvar_head_inv Hie') as Hie2.
    assert (Hcomp : msubst_compose (κa ++ ζ) κf = msubst_compose ζ κf).
    { apply msubst_compose_id_app_agree; [ exact Hidf | ].
      intros x Hx Hc.
      assert (HxΘ0 : x `in` dom Θ0).
      { destruct (a_inc_dom_flex Hincf Hx) as [Hb | [τ Hb]];
          apply binds_In in Hb; exact Hb. }
      eapply HdisjΞ0; [ | exact HxΘ0 ].
      clear - Hdomκa Hc; fsetdec. }
    rewrite Hcomp in Hie2. exact Hie2. }
  {
    assert (Hαζ : α `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζfin Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
    assert (Hlcζ : msubst_lc ζ) by (eapply a_inc_msubst_lc; exact Hζfin).
    assert (Himgζ : forall α1 τ, In (α1, τ) ζ -> α `notin` ftvar_in_ptyp τ).
    { intros α1 τ Hin.
      pose proof (a_inc_images_ftv_dom Hζfin _ _ Hin) as Hsc.
      clear - Hsc HαΘ. fsetdec. }

    unfold ad_precise in Hprec' |- *.
    rewrite msubst_bskl_pskl_to_bskl_syn in Hprec' |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec' |- *.
    assert (Hagree : msubst_pskl (κa ++ ζ)
                       (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))
                   = msubst_pskl ζ
                       (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))).
    { apply msubst_pskl_agree. intros β Hβ.
      apply msubst_lookup_app_notin.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    (ptyp_to_pskl A0) (pskl_var_f α)) as Hup.
      simpl in Hup.
      destruct (β == α) as [-> | Hne].
      - clear - Hdomκa HαΞj. fsetdec.
      - assert (HβA0 : β `in` ftvar_in_pskl (ptyp_to_pskl A0))
          by (clear - Hβ Hup Hne; fsetdec).
        assert (HβΘ0 : β `in` dom Θ0).
        { destruct (a_wf_pskl_ftv_binds HwfP0
                      (α := β) ltac:(simpl; clear - HβA0; solve_notin_auto))
            as [Hb | [Hb | [τ Hb]]]; eapply binds_In; exact Hb. }
        intro Hc. eapply HdisjΞ0; [ | exact HβΘ0 ].
        clear - Hdomκa Hc; fsetdec. }
    rewrite Hagree in Hprec'.
    rewrite (msubst_pskl_open_lc (ptyp_to_pskl A0) Hlcζ Hαζ) in Hprec'.
    rewrite bskl_to_pskl_open in Hprec'.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
    apply ad_refine_syn_all_intro with
      (L := singleton α `union` dom Θ `union` dom Θ1
            `union` ftvar_in_pskl (ptyp_to_pskl A0) `union` ftvar_in_bskl B
            `union` dom κa `union` dom ζ).
    intros β Hβ.

    pose proof Hprec' as Hp0.
    assert (Hgfsrc : bskl_ghost_free
              (pskl_to_bskl_inh
                 (open_pskl_wrt_pskl (msubst_pskl ζ (ptyp_to_pskl A0))
                    (pskl_var_f α)))).
    { apply pskl_to_bskl_inh_ghost_free.
      rewrite (msubst_pskl_embed_ptyp ζ A0).
      rewrite <- ptyp_to_pskl_open.
      apply ptyp_to_pskl_ghost_free. }
    pose proof (@ad_refine_syn_ghost_free_strip_rename _ _ _ _ Hp0
                  nil α Θ β
                  ltac:(simpl_env; reflexivity)
                  Hgfsrc Hwfth'
                  ltac:(apply a_wf_aenv_uniq; exact Hwfth')
                  ltac:(intros γ Hγ; simpl_env; solve_notin_auto)) as Hp1.

    rewrite subst_var_bskl_inh in Hp1.
    rewrite subst_var_bskl_inh in Hp1.
    rewrite <- (msubst_pskl_open_lc (ptyp_to_pskl A0) Hlcζ Hαζ) in Hp1.
    assert (Hβζ : β `notin` dom ζ) by (clear - Hβ; fsetdec).
    rewrite (msubst_pskl_subst_var ζ
               (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f α))
               Hαζ Hβζ Himgζ) in Hp1.
    rewrite <- (subst_pskl_in_pskl_intro α (ptyp_to_pskl A0)
                  (pskl_var_f β) ltac:(clear - Fr; solve_notin_auto)) in Hp1.
    rewrite <- (subst_pskl_in_pskl_intro α (bskl_to_pskl B)
                  (pskl_var_f β)) in Hp1.
    2: { pose proof (ftvar_bskl_to_pskl B) as Hfb.
         clear - Fr Hfb. simpl in Fr. fsetdec. }
    rewrite (msubst_pskl_open_lc (ptyp_to_pskl A0) Hlcζ Hβζ) in Hp1.
    rewrite pskl_to_bskl_inh_open in Hp1.
    rewrite pskl_to_bskl_inh_open in Hp1.
    pose proof (ad_refine_syn_defs_mono Hp1 ((β ~ abind_tvar) ++ Θ)
                  ltac:(intros γ τ Hb; unfold binds; simpl; right; exact Hb))
      as Hp2.
    eapply ad_refine_syn_delta_mono; [ exact Hp2 | clear; fsetdec ]. }
Qed.

Lemma msubst_uskl_syn_pskl_to_uskl : forall κ P,
  msubst_uskl_syn κ (pskl_to_uskl P) = pskl_to_uskl (msubst_pskl κ P).
Proof.
  intros κ P; induction P; cbn; try solve [ f_equal; auto ].
  symmetry; apply pskl_to_uskl_ptyp.
Qed.

Lemma ftag_in_uskl_pskl_to_uskl : forall P,
  ftag_in_uskl (pskl_to_uskl P) [=] empty.
Proof. induction P; simpl; fsetdec. Qed.

Lemma a_wf_pskl_all_open : forall Θ P X,
  {{ Θ ⨟ empty ⊢ₚₛ (pskl_all_syn P) }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ X }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ (open_pskl_wrt_pskl P X) }}a.
Proof.
  intros Θ P X Hall HX.
  destruct (a_wf_pskl_all_inv Hall) as [Lw Hb].
  destruct (atom_fresh (Lw `union` dom Θ `union` ftvar_in_pskl P))
    as [γ Frγ].
  rewrite (subst_pskl_in_pskl_intro γ P X ltac:(clear - Frγ; solve_notin_auto)).
  eapply a_wf_pskl_subst_tvar;
    [ apply Hb; clear - Frγ; fsetdec
    | clear; fsetdec
    | clear; fsetdec
    | | exact HX ].
  intros β Hβ Hne.
  destruct (a_binds_tvar_cons_tvar_inv Hβ) as [-> | Hβ']; [ congruence | exact Hβ' ].
Qed.

Lemma a_inc_same_length : forall Θ0 ζ1 Θ1,
  ζ1 ∷ Θ0 ⊑ Θ1 ->
  forall ζ2 Θ2, ζ2 ∷ Θ0 ⊑ Θ2 ->
  length ζ1 = length ζ2.
Proof.
  intros Θ0 ζ1 Θ1 H; induction H; intros ζx Θx Hx; inversion Hx; subst;
    simpl; try reflexivity; try (f_equal; eapply IHa_inc; eassumption);
    eauto.
Qed.

Lemma app_inj_tail_length : forall (A : Type) (l1 l2 m1 m2 : list A),
  l1 ++ l2 = m1 ++ m2 -> length l2 = length m2 -> l1 = m1 /\ l2 = m2.
Proof.
  intros A l1 l2 m1 m2 Heq Hlen.
  assert (Hl1 : length l1 = length m1).
  { pose proof (f_equal (@length _) Heq) as HL.
    rewrite ! app_length in HL. lia. }
  revert m1 Heq Hl1; induction l1; intros [ | b m1 ] Heq Hl1;
    simpl in *; try discriminate Hl1; auto.
  injection Heq as -> Heq.
  destruct (IHl1 _ Heq ltac:(lia)) as [-> ->]. auto.
Qed.

Lemma pskl_to_uskl_ptyp_ghost_free : forall A,
  lc_ptyp A ->
  uskl_ghost_free (pskl_to_uskl (ptyp_to_pskl A)).
Proof.
  intros A Hlc; induction Hlc; cbn.
  - apply uskl_ghost_free__unit.
  - apply uskl_ghost_free__var.
  - apply uskl_ghost_free__arrow; assumption.
  - apply uskl_ghost_free__all_syn with (L := empty).
    intros α _.
    change (uskl_var_f α) with (pskl_to_uskl (pskl_var_f α)).
    rewrite <- pskl_to_uskl_open.
    rewrite <- ptyp_to_pskl_open.
    auto.
Qed.

Lemma pskl_to_uskl_paint_ghost_free : forall Pp,
  lc_pskl Pp ->
  forall A, Pp = ptyp_to_pskl A ->
  uskl_ghost_free (pskl_to_uskl Pp).
Proof.
  intros Pp Hlc; induction Hlc; intros A0 HeqA;
    destruct A0; cbn in HeqA; try discriminate HeqA; cbn.
  - apply uskl_ghost_free__unit.
  - apply uskl_ghost_free__var.
  - injection HeqA as HeqA1 HeqA2.
    apply uskl_ghost_free__arrow;
      [ eapply IHHlc1; exact HeqA1 | eapply IHHlc2; exact HeqA2 ].
  - injection HeqA as HeqA0.
    apply uskl_ghost_free__all_syn with (L := empty).
    intros α _.
    change (uskl_var_f α) with (pskl_to_uskl (pskl_var_f α)).
    rewrite <- pskl_to_uskl_open.
    eapply H0 with (A := open_ptyp_wrt_ptyp A0 (ptyp_var_f α)).
    rewrite HeqA0. symmetry. apply ptyp_to_pskl_open.
Qed.

Lemma uskl_all_hd_msubst : forall κ o R,
  msubst_uskl_syn κ (uskl_all_hd o R) = uskl_all_hd o (msubst_uskl_syn κ R).
Proof. intros κ [ε | ] R; reflexivity. Qed.

Lemma uskl_all_hd_lc_inv : forall o R,
  lc_uskl (uskl_all_hd o R) ->
  forall β, lc_uskl (open_uskl_wrt_uskl R (uskl_var_f β)).
Proof. intros [ε | ] R H; inversion H; subst; assumption. Qed.

Lemma a_uskl_tyequiv_all_hd_inv : forall Θ o R R',
  {{ Θ ⊢ (uskl_all_hd o R) ≡ᵘ (uskl_all_hd o R') }}a ->
  exists L, forall α, α `notin` L ->
    {{ Θ ⊢ (open_uskl_wrt_uskl R (uskl_var_f α)) ≡ᵘ
        (open_uskl_wrt_uskl R' (uskl_var_f α)) }}a.
Proof.
  intros Θ [ε | ] R R' H;
    [ destruct (a_uskl_tyequiv_all_tag_l_inv H) as (X0 & L & HX & HL)
    | destruct (a_uskl_tyequiv_all_syn_l_inv H) as (X0 & L & HX & HL) ];
    inversion HX; subst; exists L; exact HL.
Qed.

Lemma uskl_ghost_free_all_hd_inv : forall o R,
  uskl_ghost_free (uskl_all_hd o R) ->
  exists L0, forall α, α `notin` L0 ->
    uskl_ghost_free (open_uskl_wrt_uskl R (uskl_var_f α)).
Proof.
  intros [ε | ] R H;
    [ apply uskl_ghost_free_all_tag_inv in H | apply uskl_ghost_free_all_syn_inv in H ];
    exact H.
Qed.

Lemma a_sub_complete_forall_l_hd :
  forall n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q o Ψa ψa,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  M <> mode_ti ->
  Ψa ∩ Ψ [=] empty ->
  Ψa ∩ (ftag_in_uskl Rj) [=] empty ->
  a_tags_sort NM Ψa ψa ->
  {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψa ⌋ˢ }}a ->
  ad_pat_sub_fuel n NM M (Ψ `union` Ψa) Θ (open_uskl_wrt_uskl Rj ψa) Q ->
  (guarded_pskl P0 \/ P0 = pskl_ghost) ->
  sub_complete_concl (S n) NM M Θ0 P0 P (uskl_all_hd o Rb)
    (uskl_all_hd o Rj) Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q o Ψa ψa
    IH HMti HΨaΨ HΨaftag Htags Hwfψa HD HP0wlog.
  unfold sub_complete_concl.
  intros Hwf0 Hwfth HwfP0 HwfP HmodSK HmodTY HeqP Hinc Hrel Hsub Hrs HwfQ Hgf.
  rewrite uskl_all_hd_erase in HeqP. subst P.

  assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hinc).
  assert (Htskψa : is_dskl ψa) by (inversion Htags; subst; assumption).
  assert (Hdtags : d_tags_skl Ψa ψa) by (inversion Htags; subst; assumption).
  assert (Hlcψa : lc_uskl ψa) by (apply is_dskl_lc; exact Htskψa).
  assert (Hlcall : lc_uskl (uskl_all_hd o Rb))
    by (apply lc_uskl_of_pskl; rewrite uskl_all_hd_erase;
        eapply a_wf_pskl_lc; exact HwfP).
  assert (Hlcb : forall β, lc_uskl (open_uskl_wrt_uskl Rb (uskl_var_f β)))
    by (exact (@uskl_all_hd_lc_inv _ _ Hlcall)).
  assert (Hlcjall : lc_uskl (uskl_all_hd o Rj))
    by (exact (proj1 (a_uskl_tyequiv_lc Hrel))).
  assert (Hlcj : forall β, lc_uskl (open_uskl_wrt_uskl Rj (uskl_var_f β)))
    by (exact (@uskl_all_hd_lc_inv _ _ Hlcjall)).

  assert (Hftvb : ftvar_in_uskl Rb [<=] dom Θ0).
  { intros β Hβ.
    pose proof (a_wf_pskl_ftv_dom_pointwise HwfP) as Hsc.
    assert (Hβp : β `in` ftvar_in_pskl (pskl_all_syn ⌊ Rb ⌋ˢ)).
    { change (ftvar_in_pskl (pskl_all_syn ⌊ Rb ⌋ˢ))
        with (ftvar_in_pskl ⌊ Rb ⌋ˢ).
      rewrite ftvar_in_pskl_uskl_to_pskl. exact Hβ. }
    apply Hsc. exact Hβp. }

  rewrite uskl_all_hd_msubst in Hrel.
  destruct (@a_uskl_tyequiv_all_hd_inv _ _ _ _ Hrel) as [Le Hrelb].
  assert (Hftjb : ftag_in_uskl Rj [=] ftag_in_uskl Rb).
  { destruct (atom_fresh Le) as [β Frβ].
    pose proof (a_uskl_tyequiv_ftag (Hrelb β Frβ)) as Hf.
    rewrite (ftag_in_uskl_open_var Rj β) in Hf.
    rewrite (ftag_in_uskl_open_var (msubst_uskl_syn κ Rb) β) in Hf.
    rewrite (ftag_in_uskl_msubst_uskl_syn κ Rb) in Hf.
    exact Hf. }

  destruct (atom_fresh
    (Le `union` dom Θ0 `union` dom Θ `union` dom κ
       `union` ftvar_in_uskl Rb `union` ftvar_in_pskl ⌊ Rb ⌋ˢ
       `union` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
       `union` ftvar_in_uskl (msubst_uskl_syn κ Rb))) as [α Fr].
  assert (Hbody_eq : {{ Θ ⊢ (open_uskl_wrt_uskl (msubst_uskl_syn κ Rb) ψa)
                       ≡ᵘ (open_uskl_wrt_uskl Rj ψa) }}a).
  { eapply a_uskl_tyequiv_open with (L := Le);
      [ intros β Hβ; exact (a_uskl_tyequiv_sym (Hrelb β Hβ))
      | exact Hlcψa ]. }
  assert (Hsubty : ad_pat_sub_fuel n NM M (Ψ `union` Ψa) Θ
                     (subst_uskl_in_uskl ψa α
                        (msubst_uskl_syn κ
                           (open_uskl_wrt_uskl Rb (uskl_var_f α)))) Q).
  { rewrite (msubst_uskl_syn_open Rb Hinc
               (α := α) ltac:(clear - Fr; solve_notin_auto)).
    rewrite <- (subst_uskl_in_uskl_intro α (msubst_uskl_syn κ Rb) ψa
                  ltac:(clear - Fr; solve_notin_auto)).
    eapply ad_pat_sub_fuel_tyequiv_subject; eassumption. }
  assert (HwfSubj : {{ Θ ⨟ empty ⊢ₚₛ
            (uskl_to_pskl
               (subst_uskl_in_uskl ψa α
                  (msubst_uskl_syn κ
                     (open_uskl_wrt_uskl Rb (uskl_var_f α))))) }}a).
  { rewrite (msubst_uskl_syn_open Rb Hinc
               (α := α) ltac:(clear - Fr; solve_notin_auto)).
    rewrite <- (subst_uskl_in_uskl_intro α (msubst_uskl_syn κ Rb) ψa
                  ltac:(clear - Fr; solve_notin_auto)).
    rewrite uskl_to_pskl_open_gen.
    apply a_wf_pskl_all_open; [ | exact Hwfψa ].
    assert (HwfPθ : {{ Θ ⨟ empty ⊢ₚₛ (msubst_pskl κ (pskl_all_syn ⌊ Rb ⌋ˢ)) }}a).
    { eapply a_wf_pskl_msubst_inc;
        [ exact Hinc | exact Hwf0 | exact HwfP
        | intros β Hβ; exfalso; clear - Hβ; fsetdec
        | intros β γ _ _ _; clear; fsetdec ]. }
    cbn in HwfPθ.
    rewrite (uskl_to_pskl_msubst_uskl_syn κ Rb).
    exact HwfPθ. }
  destruct (@a_extract_complete_gen n NM M Θ0 Θ κ Ψa
              (Ψ `union` Ψa) ψa Q
              (open_pskl_wrt_pskl ⌊ Rb ⌋ˢ (pskl_var_f α)) P0
              (open_uskl_wrt_uskl Rb (uskl_var_f α)) α
              Hwfth Hwf0 HwfP0 HmodSK HmodTY Hinc
              ltac:(clear - Fr; solve_notin_auto) ltac:(clear - Fr; solve_notin_auto)
              (uskl_to_pskl_open Rb α)
              ltac:(pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                                  Rb (uskl_var_f α)) as Hup;
                    cbn in Hup; clear - Hup Hftvb; fsetdec)
              (Hlcb α) Htags
              ltac:(rewrite (ftag_in_uskl_open_var Rb α);
                    cbn in HΨaftag; clear - HΨaftag Hftjb; solve_notin_auto)
              ltac:(assert (Hdψ : ftvar_in_uskl ψa [<=] dom Θ)
                      by (eapply uskl_wf_ftv_dom; exact Hwfψa);
                    clear - Hdψ; solve_notin_auto)
              Hwfψa
              ltac:(pose proof (ad_pat_sub_fuel_ftag_sub HD) as Hfs;
                    pose proof (ftag_in_uskl_open_upper Rj ψa) as Hou;
                    pose proof (d_tags_skl_ftag Hdtags) as Htg;
                    rewrite (ftag_in_uskl_open_var Rb α);
                    clear - Hfs Hou Htg Hftjb; fsetdec)
              ltac:(clear; solve_notin_auto)
              Hsubty HwfSubj
              Hrs HwfQ)
    as (Ξ & Pa & κa & Hlook & HwfPa & HwfΞΘ0 & HdeclsΞ & Hkeys
        & Hinca & Hie0 & Hpre).

  assert (Hdomκa : dom κa [=] dom Ξ) by (apply keys_eq_dom; exact Hkeys).
  assert (HdomΞ : forall β, β `in` dom Ξ -> β `notin` dom Θ0).
  { intros β Hβ Hc.
    pose proof (a_wf_aenv_uniq HwfΞΘ0) as Hu.
    clear - Hu Hβ Hc. solve_uniq. }
  assert (HwfPaΘ : {{ Θ ⨟ empty ⊢ₚₛ (msubst_pskl (κa ++ κ) Pa) }}a).
  { eapply a_wf_pskl_msubst_inc;
      [ exact Hinca | exact HwfΞΘ0 | exact HwfPa
      | intros β Hβ; exfalso; clear - Hβ; fsetdec
      | intros β γ _ _ _; clear; fsetdec ]. }
  assert (HlcψPa : lc_uskl (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))
    by (apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; exact HwfPaΘ).
  assert (Hupair : uskl_precise Θ Ψa
                     (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)) ψa).
  { eapply uskl_precise_of_precise with (Θ := Θ);
      [ exact Hpre | exact Hwfth
      | rewrite bskl_to_pskl_pskl_to_bskl_inh; exact Hwfψa
      | reflexivity | reflexivity
      | exact Htskψa | exact Hdtags ]. }
  destruct (uskl_precise_open_into Rj Hlcj Hupair Hlcψa)
    as [Ψrep' [HΨrep' Hopen_pair]].
  assert (Hgfswap : NM = a_sub_mode_ty ->
            uskl_ghost_free
              (open_uskl_wrt_uskl Rj
                 (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))).
  { intro HeqNM. subst NM.
    assert (HgfPa : uskl_ghost_free
                      (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))).
    { inversion Hlook; subst.
      match goal with Hg : a_guess _ a_sub_mode_ty _ _ _ |- _ =>
        inversion Hg; subst end.
      rewrite msubst_pskl_embed_ptyp in HwfPaΘ |- *.
      eapply pskl_to_uskl_paint_ghost_free;
        [ eapply a_wf_pskl_lc; exact HwfPaΘ | reflexivity ]. }
    destruct (@uskl_ghost_free_all_hd_inv _ _ (Hgf eq_refl)) as [Lg Hgb].
    destruct (atom_fresh (Lg `union` ftvar_in_uskl Rj)) as [γ Frγ].
    rewrite (subst_uskl_in_uskl_intro γ Rj
               (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))
               ltac:(clear - Frγ; solve_notin_auto)).
    apply uskl_ghost_free_subst;
      [ apply Hgb; clear - Frγ; fsetdec | exact HgfPa | exact HlcψPa ]. }
  assert (HDswap : ad_pat_sub_fuel n NM M Ψ Θ
            (open_uskl_wrt_uskl Rj
               (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))) Q).
  { eapply ad_pat_sub_precise_upre_fuel with
      (Ψsup := Ψa) (Ψna := Ψa) (Ψr := Ψrep');
      [ exact HD | exact Hopen_pair | exact Hwfth
      | destruct HΨrep' as [He | He]; rewrite He; clear; fsetdec
      | intros x b0 Hb0; exact Hb0
      | exact Hwfth
      | clear; fsetdec
      | clear; fsetdec
      | exact HΨaΨ
      | pose proof (ftag_in_uskl_open_upper Rj
                      (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa))) as Hou;
        pose proof (ftag_in_uskl_pskl_to_uskl
                      (msubst_pskl (κa ++ κ) Pa)) as Hemb;
        cbn in HΨaftag; clear - Hou Hemb HΨaftag Hftjb; fsetdec
      | exact HwfQ
      | exact Hgfswap ]. }

  assert (Hmon0 : forall x (b : abind), binds x b Θ0 -> binds x b (Ξ ++ Θ0))
    by (intros x b0 Hb0; unfold binds in *; apply in_or_app; right;
        exact Hb0).
  assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
    by (eapply a_wf_pskl_weaken; eassumption).
  assert (HeqPnew : ⌊ open_uskl_wrt_uskl Rb (pskl_to_uskl Pa) ⌋ˢ
                    = open_pskl_wrt_pskl ⌊ Rb ⌋ˢ Pa).
  { rewrite uskl_to_pskl_open_gen.
    rewrite uskl_to_pskl_pskl_to_uskl. reflexivity. }
  assert (HwfPnew : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
                      (open_pskl_wrt_pskl ⌊ Rb ⌋ˢ Pa) }}a).
  { apply a_wf_pskl_all_open; [ | exact HwfPa ].
    eapply a_wf_pskl_weaken; eassumption. }
  assert (Hcollapse : msubst_uskl_syn (κa ++ κ) Rb = msubst_uskl_syn κ Rb).
  { apply msubst_uskl_syn_agree. intros β Hβ.
    apply msubst_lookup_app_notin.
    assert (HβΘ0 : β `in` dom Θ0) by (clear - Hβ Hftvb; fsetdec).
    intro Hc.
    apply (HdomΞ β); [ clear - Hc Hdomκa; fsetdec | exact HβΘ0 ]. }
  assert (Hslack : {{ Θ ⊢ (open_uskl_wrt_uskl Rj
                          (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))
                     ≡ᵘ (msubst_uskl_syn (κa ++ κ)
                           (open_uskl_wrt_uskl Rb (pskl_to_uskl Pa))) }}a).
  { assert (Hro : msubst_uskl_syn (κa ++ κ)
                    (open_uskl_wrt_uskl Rb (pskl_to_uskl Pa))
                = open_uskl_wrt_uskl (msubst_uskl_syn (κa ++ κ) Rb)
                    (msubst_uskl_syn (κa ++ κ) (pskl_to_uskl Pa))).
    { unfold open_uskl_wrt_uskl.
      apply (msubst_uskl_syn_open_rec Rb (pskl_to_uskl Pa) 0 Hinca). }
    rewrite Hro. rewrite Hcollapse.
    rewrite msubst_uskl_syn_pskl_to_uskl.
    eapply a_uskl_tyequiv_open with (L := Le);
      [ intros β Hβ; exact (Hrelb β Hβ)
      | exact HlcψPa ]. }
  assert (HrsΞ : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl (κa ++ κ) P0)) ⊳ Q }}ad).
  { assert (HP0c : msubst_pskl (κa ++ κ) P0 = msubst_pskl κ P0).
    { apply msubst_pskl_agree. intros β Hβ.
      apply msubst_lookup_app_notin.
      assert (HβΘ0 : β `in` dom Θ0)
        by (apply (a_wf_pskl_ftv_dom_pointwise HwfP0); exact Hβ).
      intro Hc.
      apply (HdomΞ β); [ clear - Hc Hdomκa; fsetdec | exact HβΘ0 ]. }
    rewrite HP0c. exact Hrs. }
  destruct (IH NM M (Ξ ++ Θ0) P0 (open_pskl_wrt_pskl ⌊ Rb ⌋ˢ Pa)
              (open_uskl_wrt_uskl Rb (pskl_to_uskl Pa))
              (open_uskl_wrt_uskl Rj
                 (pskl_to_uskl (msubst_pskl (κa ++ κ) Pa)))
              Ψ Θ (κa ++ κ) Q
              HwfΞΘ0 Hwfth HwfP0' HwfPnew HmodSK HmodTY HeqPnew Hinca
              Hslack HDswap HrsΞ HwfQ Hgfswap)
    as [P1 [Θ1 [Hrun Hopt]]].

  exists P1, Θ1. split.
  {
    eapply a_sub__forall_l with (α := α) (Ξ := Ξ) (P1 := Pa);
      [ exact HMti | exact HP0wlog
      | clear - Fr; solve_notin_auto
      | exact Hlook
      | apply a_wf_aenv_uniq; exact HwfΞΘ0
      | exact HwfPa
      | exact Hrun ]. }

  intros κf Hidf Hincf.
  destruct (a_sub_sound Hrun HwfΞΘ0 HwfP0' HwfPnew HmodSK HmodTY)
    as [[[w [Hidw Hincw]] Hdefs] [HwfΘ1 _]].
  destruct (Hopt w Hidw Hincw) as [ζ' [Hζ' [Hie' Hprec']]].
  exists ζ'. split; [ exact Hζ' | ]. split.
  {
    destruct (@a_inc_peel_suffix Ξ Θ0 w Θ1
                (a_decls_suffix HdeclsΞ) Hincw)
      as [wa [wb [-> [Hdomwa Hincwb]]]].
    assert (Hidwb : is_id_msubst wb).
    { unfold is_id_msubst in *. apply Forall_app in Hidw. tauto. }
    assert (Heqwb : wb = κf)
      by (eapply is_id_inc_unique; eassumption).
    subst wb.
    assert (Hcompw : msubst_compose ζ' (wa ++ κf)
                   = msubst_compose ζ' wa ++ msubst_compose ζ' κf)
      by (unfold msubst_compose; apply List.map_app).
    rewrite Hcompw in Hie'.
    assert (Hinccomp : (msubst_compose ζ' wa ++ msubst_compose ζ' κf)
                         ∷ (Ξ ++ Θ0) ⊑ Θ).
    { rewrite <- Hcompw.
      eapply a_inc_compose; eassumption. }
    destruct (@a_inc_equiv_inc_peel_suffix Ξ Θ0 (κa ++ κ)
                (msubst_compose ζ' wa ++ msubst_compose ζ' κf) Θ
                (a_decls_suffix HdeclsΞ) Hie' Hinca Hinccomp)
      as [κ1b [κ2b [Hie2 [Hib1 [Hib2 [[p1 [Hp1 Hd1]] [p2 [Hp2 Hd2]]]]]]]].
    assert (Hlen1 : length κ = length κ1b)
      by (symmetry; eapply a_inc_same_length; eassumption).
    destruct (app_inj_tail_length κa κ p1 κ1b Hp1 Hlen1) as [_ Heqκ1b].
    subst κ1b.
    assert (Hlen2 : length (msubst_compose ζ' κf) = length κ2b).
    { assert (Hl2a : length κ2b = length κ)
        by (eapply a_inc_same_length; eassumption).
      assert (Hl2b : length κf = length κ)
        by (eapply a_inc_same_length; eassumption).
      unfold msubst_compose. rewrite List.map_length.
      clear - Hl2a Hl2b; lia. }
    destruct (app_inj_tail_length (msubst_compose ζ' wa)
                (msubst_compose ζ' κf) p2 κ2b Hp2 Hlen2) as [_ Heqκ2b].
    subst κ2b.
    exact Hie2. }
  { exact Hprec'. }
Qed.

Lemma a_sub_complete_forall_l_tagged :
  forall n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q ε Ψa ψa,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  M <> mode_ti ->
  Ψa ∩ Ψ [=] empty ->
  Ψa ∩ (ftag_in_uskl (uskl_all_tag ε Rj)) [=] empty ->
  a_tags_sort NM Ψa ψa ->
  {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψa ⌋ˢ }}a ->
  ad_pat_sub_fuel n NM M (Ψ `union` Ψa) Θ (open_uskl_wrt_uskl Rj ψa) Q ->
  (guarded_pskl P0 \/ P0 = pskl_ghost) ->
  sub_complete_concl (S n) NM M Θ0 P0 P (uskl_all_tag ε Rb)
    (uskl_all_tag ε Rj) Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q ε Ψa ψa IH HMti HΨaΨ HΨaftag.
  apply (@a_sub_complete_forall_l_hd n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q (Some ε));
    [ exact IH | exact HMti | exact HΨaΨ | cbn in HΨaftag; clear - HΨaftag; fsetdec ].
Qed.

Lemma a_sub_complete_forall_l_untagged :
  forall n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q Ψa ψa,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  M <> mode_ti ->
  Ψa ∩ Ψ [=] empty ->
  Ψa ∩ (ftag_in_uskl (uskl_all_syn Rj)) [=] empty ->
  a_tags_sort NM Ψa ψa ->
  {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψa ⌋ˢ }}a ->
  ad_pat_sub_fuel n NM M (Ψ `union` Ψa) Θ (open_uskl_wrt_uskl Rj ψa) Q ->
  (guarded_pskl P0 \/ P0 = pskl_ghost) ->
  sub_complete_concl (S n) NM M Θ0 P0 P (uskl_all_syn Rb)
    (uskl_all_syn Rj) Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q Ψa ψa IH HMti HΨaΨ HΨaftag.
  exact (@a_sub_complete_forall_l_hd n NM M Θ0 P0 P Rb Rj Ψ Θ κ Q None
           Ψa ψa IH HMti HΨaΨ HΨaftag).
Qed.

Lemma a_sub_flex_sound : forall NM M P0 Θ0 Ξ α A Θ1,
  a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ Θ0) }}a ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_binds_tvar α (Ξ ++ Θ0) ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat (mode_fn M) P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat (mode_fn M) P0) ->
  (Ξ ++ Θ0) ⊴ Θ1 /\ {{ ⊢ Θ1 }}a.
Proof.
  intros NM M P0 Θ0 Ξ α A Θ1 Hrun Hdecls Hwf HwfP0 Hαb Hmod Hgf.
  assert (Htag : a_subtag_flex NM M P0 Θ0 Ξ α A Θ1).
  { eapply (proj2 a_sub_decorate_bundle);
      [ exact Hrun | exact Hdecls | exact Hwf | exact HwfP0 | exact Hαb
      | intros HSK; apply a_sk_mode_compat_mod_comp_sk; apply Hmod; exact HSK
      | intros _; eapply a_wf_pskl_top_guarded; exact HwfP0 ]. }
  destruct ((proj2 a_subtag_sound_bundle) _ _ _ _ _ _ _ _ Htag
              Hwf Hdecls HwfP0 Hαb
              ltac:(intros HSK; apply a_sk_mode_compat_mod_comp_sk;
                    apply Hmod; exact HSK)
              Hgf)
    as [Hisub [HwfΘ1 _]].
  split; assumption.
Qed.

Lemma a_suffix_binds : forall Ξ γ bd,
  a_suffix Ξ -> binds γ bd Ξ -> a_suffix_binding bd.
Proof.
  intros Ξ γ bd H; induction H; intros Hb; [ inversion Hb | ].
  analyze_binds Hb; auto.
Qed.

Lemma a_inc_binds_provenance : forall Θs κ Θt γ bd,
  κ ∷ Θs ⊑ Θt ->
  binds γ bd Θt ->
  a_suffix_binding bd \/ γ `in` dom Θs.
Proof.
  intros Θs κ Θt γ bd H; induction H; intros Hb.
  - left; eapply a_suffix_binds; eassumption.
  - destruct (IHa_inc Hb) as [h | h];
      [ left; exact h | right; simpl_env; clear - h; fsetdec ].
  - destruct (IHa_inc Hb) as [h | h];
      [ left; exact h | right; simpl_env; clear - h; fsetdec ].
  - analyze_binds Hb;
      [ left; eapply a_suffix_binds; eassumption
      | right; simpl_env; clear; fsetdec
      | destruct (IHa_inc BindsTac0) as [h | h];
          [ left; exact h | right; simpl_env; clear - h; fsetdec ] ].
  - analyze_binds Hb;
      [ left; eapply a_suffix_binds; eassumption
      | right; simpl_env; clear; fsetdec
      | destruct (IHa_inc BindsTac0) as [h | h];
          [ left; exact h | right; simpl_env; clear - h; fsetdec ] ].
  - analyze_binds Hb;
      [ left; eapply a_suffix_binds; eassumption
      | right; simpl_env; clear; fsetdec
      | destruct (IHa_inc BindsTac0) as [h | h];
          [ left; exact h | right; simpl_env; clear - h; fsetdec ] ].
Qed.

Lemma a_sub_flex_out_flex_only : forall NM M P0 Θ0 Ξ α A Θ1 β,
  a_sub_flex NM M P0 Θ0 Ξ α A Θ1 ->
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ Θ0) }}a ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_binds_tvar α (Ξ ++ Θ0) ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat (mode_fn M) P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat (mode_fn M) P0) ->
  β `notin` dom (Ξ ++ Θ0) ->
  forall bd, binds β bd Θ1 ->
    bd = abind_flex_mono \/ exists τ, bd = abind_flex_mono_def τ.
Proof.
  intros * Hrun Hdecls Hwf HwfP0 Hαb Hmod Hgf Hβ bd Hb.
  destruct (a_sub_flex_sound Hrun Hdecls Hwf HwfP0 Hαb Hmod Hgf)
    as [[[w [Hidw Hincw]] _] _].
  assert (Hprov : a_suffix_binding bd \/ β `in` dom (Ξ ++ Θ0))
    by (eapply a_inc_binds_provenance; eassumption).
  destruct Hprov as [h | h];
    [ inversion h; subst; [ left; reflexivity | right; eexists; reflexivity ]
    | exfalso; clear - h Hβ; fsetdec ].
Qed.

Lemma a_inc_strip_flex_mid : forall Ξ β Θ0 κ Θ,
  a_decls Ξ ->
  κ ∷ (Ξ ++ (β ~ abind_flex_mono) ++ Θ0) ⊑ Θ ->
  exists κ1 τ κ2,
    κ = κ1 ++ (β, τ) :: κ2 /\ length κ1 = length Ξ /\ dom κ1 [=] dom Ξ /\
    (κ1 ++ κ2) ∷ (Ξ ++ Θ0) ⊑ Θ /\ a_wf_ptyp Θ τ /\ mono_ptyp τ /\
    κ2 ∷ Θ0 ⊑ Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH]; intros β Θ0 κ Θ Hsuf Hinc.
  - simpl in Hinc.
    inversion Hinc as [ | Θa κa Θb αa τa Hi Hw Hm | | | | ]; subst.
    exists nil, τa, κa. simpl.
    split; [ reflexivity | split; [ reflexivity | ] ].
    split; [ clear; fsetdec | ].
    split; [ exact Hi | ]. split; [ assumption | ]. split; assumption.
  - inversion Hsuf as [ | ? ? Hsuf' ]; subst; simpl in Hinc.
    inversion Hinc as [ | Θa κa Θb αa τa Hi Hw Hm | | | | ]; subst.
    destruct (IH _ _ _ _ Hsuf' Hi)
      as [κ1 [τ [κ2 [-> [Hd [Hdom [Hinc2 [Hwτ [Hmτ Hi2]]]]]]]]].
    exists ((x, τa) :: κ1), τ, κ2. simpl.
    split; [ reflexivity | ].
    split; [ rewrite Hd; reflexivity | ].
    split; [ rewrite Hdom; clear; fsetdec | ].
    split; [ apply a_inc__flex; eassumption | ].
    split; [ assumption | ]. split; assumption.
Qed.

Lemma a_inc_strip_flex_def_mid : forall Ξ β τ0 Θ0 κ Θ,
  a_decls Ξ ->
  κ ∷ (Ξ ++ (β ~ abind_flex_mono_def τ0) ++ Θ0) ⊑ Θ ->
  exists κ1 τ κ2,
    κ = κ1 ++ (β, τ) :: κ2 /\ length κ1 = length Ξ /\ dom κ1 [=] dom Ξ /\
    (κ1 ++ κ2) ∷ (Ξ ++ Θ0) ⊑ Θ /\
    {{ Θ ⊢ τ ≡ᵗ (msubst_ptyp κ2 τ0) }}a /\ a_wf_ptyp Θ τ /\ mono_ptyp τ /\
    κ2 ∷ Θ0 ⊑ Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH]; intros β τ0 Θ0 κ Θ Hsuf Hinc.
  - simpl in Hinc.
    inversion Hinc as [ | | Θa κa Θb αa τa τb Hi Hw Hm He | | | ]; subst.
    exists nil, τb, κa. simpl.
    split; [ reflexivity | split; [ reflexivity | ] ].
    split; [ clear; fsetdec | ].
    split; [ exact Hi | ]. split; [ exact He | ].
    split; [ assumption | ]. split; assumption.
  - inversion Hsuf as [ | ? ? Hsuf' ]; subst; simpl in Hinc.
    inversion Hinc as [ | Θa κa Θb αa τa Hi Hw Hm | | | | ]; subst.
    destruct (IH _ _ _ _ _ Hsuf' Hi)
      as [κ1 [τ [κ2 [-> [Hd [Hdom [Hinc2 [Heq [Hwτ [Hmτ Hi2]]]]]]]]]].
    exists ((x, τa) :: κ1), τ, κ2. simpl.
    split; [ reflexivity | ].
    split; [ rewrite Hd; reflexivity | ].
    split; [ rewrite Hdom; clear; fsetdec | ].
    split; [ apply a_inc__flex; eassumption | ].
    split; [ exact Heq | ]. split; [ assumption | ]. split; assumption.
Qed.

Lemma a_inc_equiv_insert_flex_mid : forall Ξ κ1 κ2 σ1 σ2 β τ Θ0 Θ,
  a_decls Ξ ->
  length κ1 = length Ξ ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ ->
  length σ1 = length Ξ ->
  {{ Θ ⊢ τ ≡ᵗ τ }}a ->
  a_inc_equiv (Ξ ++ (β ~ abind_flex_mono) ++ Θ0)
              (κ1 ++ (β, τ) :: κ2) (σ1 ++ (β, τ) :: σ2) Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH];
    intros κ1 κ2 σ1 σ2 β τ Θ0 Θ Hd Hlk He Hls Hτ.
  - destruct κ1; [ | discriminate ]. destruct σ1; [ | discriminate ].
    simpl in *. apply a_inc_equiv__flex; eassumption.
  - inversion Hd as [ | ? ? Hd' ]; subst.
    destruct κ1 as [| [k1a k1b] κ1']; [ discriminate | ].
    destruct σ1 as [| [s1a s1b] σ1']; [ discriminate | ].
    simpl in He.
    inversion He as [ | Θa κa σa Θb αa τ1 τ2 Hie Heq | | | | ]; subst.
    simpl. apply a_inc_equiv__flex; [ | exact Heq ].
    apply IH; [ exact Hd' | simpl in Hlk; lia | exact Hie
              | simpl in Hls; lia | exact Hτ ].
Qed.

Lemma ad_pat_sub_target_scope_ty : forall M Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_ty | M ] R ⩽ Qt }}ad ->
  uskl_no_ghost R ->
  a_scope_pskl Θ (bskl_to_pskl Qt).
Proof.
  intros M Ψ Θ R Qt H.
  remember a_sub_mode_ty as NM eqn:HNM.
  induction H; intros Hng; try discriminate HNM; destr_join.
  -  eapply ad_pat_consis_target_scope; eassumption.
  -  eapply ad_pat_consis_target_scope; eassumption.
  -
    simpl. apply a_scope_pskl_all_of_open with (L := L).
    intros α Hα. rewrite <- bskl_to_pskl_open. apply H0; assumption.
  -
    destruct Hng as [Hng1 Hng2].
    destruct (ad_pat_consis_target_scope Hjc Hng1) as [Hl1 Hb1].
    destruct (IHad_pat_sub HNM Hng2) as [Hl2 Hb2].
    split; [ simpl; constructor; assumption | ].
    intros γ Hγ; simpl in Hγ. apply union_1 in Hγ as [Hγ | Hγ]; auto.
  -
    subst. apply IHad_pat_sub; [ reflexivity | ].
    apply uskl_no_ghost_open; [ exact Hng | ].
    apply uskl_no_ghost_of_ghost_free. inversion H2; assumption.
  -
    subst. apply IHad_pat_sub; [ reflexivity | ].
    apply uskl_no_ghost_open; [ exact Hng | ].
    apply uskl_no_ghost_of_ghost_free. inversion H2; assumption.
  -  apply IHad_pat_sub; [ exact HNM | apply uskl_no_ghost_ptyp ].
Qed.

Lemma a_inc_kswap_paint : forall α β κ Θ0 Θ P,
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (forall bd, binds α bd Θ0 ->
    bd = abind_flex_mono \/ exists τ, bd = abind_flex_mono_def τ) ->
  β `notin` dom Θ0 `union` ftvar_in_pskl P `union` singleton α ->
  msubst_bskl (kswap_msubst α β κ) (pskl_to_bskl_syn (swap_pskl α β P)) =
    msubst_bskl κ (pskl_to_bskl_syn P).
Proof.
  intros α β κ Θ0 Θ P Hinc Hwf Hflex Hfresh.
  apply msubst_bskl_kswap_paint.
  - clear - Hfresh; fsetdec.
  - intros Hin. pose proof (@a_inc_keys_dom κ Θ0 Θ β Hinc Hin) as Hdom.
    clear - Hdom Hfresh; fsetdec.
  - clear - Hfresh; fsetdec.
  - destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P)) as [Hin | Hout];
      [ right | left; exact Hout ].
    apply (a_wf_pskl_ftv_binds Hwf) in Hin.
    eapply a_inc_flex_in_keys; [exact Hinc |].
    destruct Hin as [Hb | Hb]; [ | exact Hb ].
    destruct (Hflex abind_tvar Hb) as [Heq | [τ Heq]]; discriminate.
Qed.

Lemma a_sub_flex_optimal_fresh : forall NM M P0 Θ0 Ξ α P1 Θ1 Θ κ Q β,
  a_sub_flex NM M P0 Θ0 Ξ α P1 Θ1 ->
  a_decls Ξ -> {{ ⊢ (Ξ ++ Θ0) }}a ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_binds_tvar α (Ξ ++ Θ0) ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat (mode_fn M) P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat (mode_fn M) P0) ->
  β `notin` dom (Ξ ++ Θ0) -> β `notin` ftvar_in_pskl P0 ->
  (forall κ1, is_id_msubst κ1 -> κ1 ∷ (Ξ ++ Θ0) ⊑ Θ1 ->
    exists ζ, ζ ∷ Θ1 ⊑ Θ /\
      a_inc_equiv (Ξ ++ Θ0) κ (msubst_compose ζ κ1) Θ /\
      {{ Θ ⨟ empty ⊢ₚᵣ (msubst_bskl ζ (pskl_to_bskl_syn P1))
         ⊑ (bskl_to_pskl Q) }}ad) ->
  exists P2 Θ2,
    a_sub_flex NM M P0 Θ0 Ξ α P2 Θ2 /\
    {{ ⊢ Θ2 }}a /\ β `notin` dom Θ2 /\ β `notin` ftvar_in_pskl P2 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ (Ξ ++ Θ0) ⊑ Θ2 ->
      exists ζ, ζ ∷ Θ2 ⊑ Θ /\
        a_inc_equiv (Ξ ++ Θ0) κ (msubst_compose ζ κ1) Θ /\
        {{ Θ ⨟ empty ⊢ₚᵣ (msubst_bskl ζ (pskl_to_bskl_syn P2))
           ⊑ (bskl_to_pskl Q) }}ad).
Proof.
  intros NM M P0 Θ0 Ξ α P1 Θ1 Θ κ Q β
    Hrun Hdecls Hwf HwfP0 Hα Hsk Hty Hβ HβP0 Hopt.
  destruct (a_sub_flex_sound Hrun Hdecls Hwf HwfP0 Hα Hsk Hty)
    as [[[w [Hidw Hincw]] Hdefs] HwfΘ1].
  assert (HwfP1 : {{ Θ1 ⨟ empty ⊢ₚₛ P1 }}a)
    by (eapply a_sub_flex_output_wf; eauto).
  assert (Hflex : forall bd, binds β bd Θ1 ->
      bd = abind_flex_mono \/ exists τ, bd = abind_flex_mono_def τ)
    by (eapply a_sub_flex_out_flex_only; eauto).
  assert (Hβinput : β `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
      `union` ftvar_in_pskl P0).
  { pose proof (a_wf_aenv_ftv_dom Hwf) as Hftv.
    rewrite ftvar_in_aenv_app in Hftv. clear - Hftv Hβ HβP0; fsetdec. }
  assert (Hβα : β <> α).
  { pose proof (a_binds_tvar_in_dom Hα) as Hin. clear - Hin Hβ; fsetdec. }
  destruct (atom_fresh (dom Θ1 `union` ftvar_in_aenv Θ1
    `union` ftvar_in_pskl P1 `union` dom (Ξ ++ Θ0)
    `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Ξ
    `union` ftvar_in_pskl P0 `union` singleton α `union` singleton β)) as [β1 Hfr].
  assert (Hrun' : a_sub_flex NM M P0 Θ0 Ξ α
      (swap_pskl β β1 P1) (swap_aenv β β1 Θ1)).
  { apply a_sub_flex_swap_junk; auto; clear - Hfr; solve_notin_auto. }
  assert (Hwf' : {{ ⊢ swap_aenv β β1 Θ1 }}a).
  { destruct (a_sub_flex_sound Hrun' Hdecls Hwf HwfP0 Hα Hsk Hty); tauto. }
  exists (swap_pskl β β1 P1), (swap_aenv β β1 Θ1).
  repeat apply conj; auto.
  - apply swap_junk_dom_out. clear - Hfr; solve_notin_auto.
  - intros Hin. apply swap_pskl_ftv_in_rev in Hin.
    rewrite swap_atom_l in Hin. clear - Hin Hfr; fsetdec.
  - intros κ1 Hid Hinc1.
    assert (Heq : w = κ1) by (eapply is_id_inc_unique; eauto).
    subst w. destruct (Hopt κ1 Hid Hincw) as [ζ [Hζ [Hie Hprec]]].
    exists (kswap_msubst β β1 ζ). split.
    + apply a_inc_kswap; auto; clear - Hfr; solve_notin_auto.
    + assert (Hkeys : forall γ, List.In γ (List.map fst κ1) ->
          γ <> β /\ γ <> β1).
      { intros γ Hin. pose proof (@a_inc_keys_dom κ1 (Ξ ++ Θ0) _ γ Hinc1 Hin)
          as Hdom. clear - Hdom Hβ Hfr; split; intro; subst; fsetdec. }
      rewrite (msubst_compose_kswap_id β β1 ζ κ1 Hid Hkeys).
      split; [exact Hie |].
      rewrite (@a_inc_kswap_paint β β1 ζ Θ1 Θ P1 Hζ HwfP1 Hflex)
        by (clear - Hfr; solve_notin_auto).
      exact Hprec.
Qed.

Lemma a_sub_flex_complete_depend : forall n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q,
  (forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
     length Ξ' <= S (length Ξ) ->
     sub_flex_complete_concl n NM M Θ0 Ξ' α' P0' R'' Ψ' Θ'' κ' Q') ->
  α <> β ->
  β `in` ftvar_in_pskl P0 ->
  sub_flex_complete_concl n NM M ((β ~ abind_flex_mono) ++ Θ0) Ξ α P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q IH Hne Hin.
  unfold sub_flex_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.
  assert (Hdecls' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
    by (apply a_decls_app;
        [ exact HdeclsΞ | apply (a_decls__cons β); apply a_decls__nil ]).
  assert (Hdom' : dom (Ξ ++ (β ~ abind_flex_mono)) [<=] ftvar_in_pskl P0)
    by (simpl_env; clear - HdomΞ Hin; fsetdec).
  simpl_env in Hdom'.

  assert (Hfα' : a_flex_tvar Θ0 α).
  { destruct Hfα as [Hb | [τ0 Hb]]; [ left | right; exists τ0 ];
      (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He _] | Hb'];
       [ exfalso; apply Hne; exact He | exact Hb' ]). }
  assert (Hlen : length (Ξ ++ (β ~ abind_flex_mono)) <= S (length Ξ))
    by (rewrite app_length; simpl; lia).
  specialize (IH (Ξ ++ (β ~ abind_flex_mono)) α P0 R' Ψ Θ κ Q Hlen).
  unfold sub_flex_complete_concl in IH.
  simpl_env in IH.
  destruct (IH Hdecls' Hdom' Hwf Hwfth HwfP0 Hfα' HmodSK HmodTY Hinc Hslack HD
              Hrs HwfQ)
    as [P1 [Θ1 [Hrun Hopt]]].
  exists P1, Θ1. split.
  - apply a_sub_flex__depend; eassumption.
  - intros κf Hidf Hincf.
    destruct (Hopt κf Hidf Hincf) as [ζ [Hζ [Hie Hprec]]].
    exists ζ. split; [ exact Hζ | split; eassumption ].
Qed.

Lemma a_sub_flex_complete_skip : forall n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q,

  (forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
     length Ξ' <= S (length Ξ) ->
     sub_flex_complete_concl n NM M Θ0 Ξ' α' P0' R'' Ψ' Θ'' κ' Q') ->
  α <> β ->
  β `notin` ftvar_in_pskl P0 ->
  sub_flex_complete_concl n NM M ((β ~ abind_flex_mono) ++ Θ0) Ξ α P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q IH Hne Hnin.
  unfold sub_flex_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.

  assert (Huq : uniq (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; eassumption).
  assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
    by (eapply a_wf_pskl_strip_mid; eassumption).
  assert (Hfα' : a_flex_tvar Θ0 α).
  { destruct Hfα as [Hb | [τ0 Hb]]; [ left | right; exists τ0 ];
      (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He _] | Hb'];
       [ exfalso; apply Hne; exact He | exact Hb' ]). }
  assert (Hαb' : a_binds_tvar α (Ξ ++ Θ0))
    by (destruct (a_flex_tvar_weaken_app Ξ Hfα') as [h | [τ h]];
        [ right; left; exact h | right; right; exists τ; exact h ]).

  destruct (@a_inc_strip_flex_mid Ξ β Θ0 κ Θ HdeclsΞ Hinc)
    as [κ1 [τβ [κ2 [Heqκ [Hlen [Hdomκ1 [Hincih [Hwfτβ [Hmonoτβ _]]]]]]]]].
  assert (Hlk : forall γ, γ <> β ->
            msubst_lookup κ γ = msubst_lookup (κ1 ++ κ2) γ)
    by (intros γ Hγ; rewrite Heqκ; apply msubst_lookup_mid_drop; exact Hγ).
  assert (HeqP0 : msubst_pskl κ P0 = msubst_pskl (κ1 ++ κ2) P0).
  { apply msubst_pskl_agree. intros γ Hγ. apply Hlk.
    intro Hc; subst γ; contradiction. }
  assert (Heqα : msubst_lookup κ α = msubst_lookup (κ1 ++ κ2) α)
    by (apply Hlk; exact Hne).
  rewrite Heqα in Hslack. rewrite HeqP0 in Hrs.

  destruct (IH Ξ α P0 R' Ψ Θ (κ1 ++ κ2) Q ltac:(lia)
              HdeclsΞ HdomΞ Hwf' Hwfth HwfP0'
              Hfα' HmodSK HmodTY Hincih Hslack HD Hrs HwfQ)
    as [P1 [Θ1 [Hrun Hopt]]].
  destruct (@a_sub_flex_optimal_fresh NM M P0 Θ0 Ξ α P1 Θ1 _ _ _ β
    Hrun HdeclsΞ Hwf' HwfP0' Hαb' HmodSK HmodTY HβΞΘ0 Hnin Hopt)
    as [P2 [Θ2 [Hrun2 [HwfΘ1 [Hβout [HβP2 Hopt2]]]]]].
  clear Hrun Hopt. rename Hrun2 into Hrun. rename Hopt2 into Hopt.
  clear P1 Θ1. rename P2 into P1. rename Θ2 into Θ1.
  exists P1, ((β ~ abind_flex_mono) ++ Θ1).
  split.
  { apply a_sub_flex__skip; eassumption. }

  intros κf Hidf Hincf.
  destruct (@a_inc_strip_flex_mid Ξ β Θ0 κf
              ((β ~ abind_flex_mono) ++ Θ1) HdeclsΞ Hincf)
    as [κf1 [τf [κf2 [Heqκf [Hlenf [_ [Hincfih [_ [_ _]]]]]]]]].
  assert (Hidfih : is_id_msubst (κf1 ++ κf2)).
  { unfold is_id_msubst in *. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [h1 h2].
    inversion h2; subst. apply Forall_app; split; assumption. }
  assert (Heqτf : τf = ptyp_var_f β).
  { unfold is_id_msubst in Hidf. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [_ h2].
    inversion h2 as [| e κl he hl]; subst.
    unfold is_id_entry in he; simpl in he. exact he. }
  destruct (a_sub_flex_sound Hrun HdeclsΞ Hwf' HwfP0' Hαb' HmodSK HmodTY)
    as [[[w [Hidw Hincw]] _] _].
  assert (Heqw : w = κf1 ++ κf2)
    by (eapply is_id_inc_unique; eauto).
  subst w.
  destruct (Hopt (κf1 ++ κf2) Hidfih Hincw) as [ζ [Hζ [Hie Hprec]]].
  assert (Hkeysf : forall γ, List.In γ (List.map fst (κf1 ++ κf2)) ->
            γ `in` dom (Ξ ++ Θ0))
    by (intros γ hγ; eapply a_inc_keys_dom; eassumption).
  exists ((β, τβ) :: ζ).
  split.
  {
    apply a_inc__flex; [ | exact Hwfτβ | exact Hmonoτβ ].
    exact Hζ. }
  split.
  {
    rewrite Heqκ, Heqκf, Heqτf.
    assert (Hsplit : msubst_compose ((β, τβ) :: ζ)
                       (κf1 ++ (β, ptyp_var_f β) :: κf2)
                   = msubst_compose ((β, τβ) :: ζ) κf1
                     ++ (β, τβ)
                     :: msubst_compose ((β, τβ) :: ζ) κf2).
    { unfold msubst_compose. rewrite List.map_app. simpl.
      destruct (β == β) as [_ | n0]; [ reflexivity | exfalso; auto ]. }
    rewrite Hsplit.
    assert (Hid1 : is_id_msubst κf1 /\ is_id_msubst κf2).
    { unfold is_id_msubst in Hidfih. apply Forall_app in Hidfih. exact Hidfih. }
    destruct Hid1 as [Hidf1 Hidf2].
    assert (Hk1b : forall γ, List.In γ (List.map fst κf1) -> γ <> β).
    { intros γ Hin ->. apply HβΞΘ0, Hkeysf.
      rewrite List.map_app. apply in_or_app; auto. }
    assert (Hk2b : forall γ, List.In γ (List.map fst κf2) -> γ <> β).
    { intros γ Hin ->. apply HβΞΘ0, Hkeysf.
      rewrite List.map_app. apply in_or_app; auto. }
    rewrite (@msubst_compose_cons_l_id β τβ ζ κf1 Hidf1
               (@notin_dom_of_keys_neq _ _ Hk1b)).
    rewrite (@msubst_compose_cons_l_id β τβ ζ κf2 Hidf2
               (@notin_dom_of_keys_neq _ _ Hk2b)).
    apply a_inc_equiv_insert_flex_mid;
      [ exact HdeclsΞ | exact Hlen
      | unfold msubst_compose in *; rewrite <- List.map_app; exact Hie
      | unfold msubst_compose; rewrite List.map_length; exact Hlenf
      | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmonoτβ ]. }
  { rewrite msubst_bskl_head_notin; [exact Hprec |].
    rewrite ftvar_in_bskl_syn. exact HβP2. }
Qed.

Lemma msubst_pskl_tyequiv_pointwise : forall Θs1 ζ Θ Θs2 σ P,
  ζ ∷ Θs1 ⊑ Θ ->
  σ ∷ Θs2 ⊑ Θ ->
  lc_pskl P ->
  (forall γ, {{ Θ ⊢ (msubst_lookup ζ γ) ≡ᵗ (msubst_lookup σ γ) }}a) ->
  {{ Θ ⊢ (msubst_pskl ζ P) ≡ˢ (msubst_pskl σ P) }}a.
Proof.
  intros Θs1 ζ Θ Θs2 σ P Hζ Hσ Hlc; induction Hlc; intros Hag; simpl.
  -  apply a_pskl_tyequiv__refl; constructor.
  -  apply a_tyequiv_pskl; apply Hag.
  -  apply a_pskl_tyequiv__arrow; auto.
  -
    apply a_pskl_tyequiv__all with (L := dom ζ `union` dom σ).
    intros α Hα.
    assert (Hnζ : α `notin` dom ζ) by (clear - Hα; fsetdec).
    assert (Hnσ : α `notin` dom σ) by (clear - Hα; fsetdec).
    rewrite <- (@msubst_pskl_open Θs1 ζ Θ P1 α Hζ Hnζ).
    rewrite <- (@msubst_pskl_open Θs2 σ Θ P1 α Hσ Hnσ).
    exact (H0 α Hag).
  -  apply a_pskl_tyequiv__refl; constructor.
  -  apply a_pskl_tyequiv__univ_ghost; auto.
Qed.

Lemma msubst_ptyp_tyequiv_two_msubst : forall Θs1 ζ Θ Θs2 σ A,
  ζ ∷ Θs1 ⊑ Θ ->
  σ ∷ Θs2 ⊑ Θ ->
  lc_ptyp A ->
  (forall γ, γ `in` ftvar_in_ptyp A ->
     {{ Θ ⊢ (msubst_lookup ζ γ) ≡ᵗ (msubst_lookup σ γ) }}a) ->
  {{ Θ ⊢ (msubst_ptyp ζ A) ≡ᵗ (msubst_ptyp σ A) }}a.
Proof.
  intros Θs1 ζ Θ Θs2 σ A Hζ Hσ Hlc; induction Hlc; intros Hag; simpl.
  - apply a_tyequiv__refl; constructor.
  - apply Hag; simpl; clear; fsetdec.
  - apply a_tyequiv__arrow;
      [ apply IHHlc1 | apply IHHlc2 ];
      intros γ Hγ; apply Hag; simpl; clear - Hγ; fsetdec.
  - apply a_tyequiv__all with (L := dom ζ `union` dom σ).
    intros γ Hγ.
    assert (Hnζ : γ `notin` dom ζ) by (clear - Hγ; fsetdec).
    assert (Hnσ : γ `notin` dom σ) by (clear - Hγ; fsetdec).
    rewrite <- (@msubst_ptyp_open Θs1 ζ Θ A γ Hζ Hnζ).
    rewrite <- (@msubst_ptyp_open Θs2 σ Θ A γ Hσ Hnσ).
    apply H0.
    { intros δ Hδ.
      destruct (δ == γ) as [-> | Hne].
      -
        rewrite (msubst_lookup_notin _ Hnζ), (msubst_lookup_notin _ Hnσ).
        apply a_tyequiv__refl; constructor.
      - apply Hag.
        pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A (ptyp_var_f γ))
          as Hup.
        simpl in Hup. clear - Hδ Hup Hne. fsetdec. }
Qed.

Lemma a_inc_equiv_insert_flex_def_mid :
  forall Ξ κ1 κ2 σ1 σ2 β τ τ0 Θ0 Θ,
  a_decls Ξ ->
  length κ1 = length Ξ ->
  a_inc_equiv (Ξ ++ Θ0) (κ1 ++ κ2) (σ1 ++ σ2) Θ ->
  length σ1 = length Ξ ->
  {{ Θ ⊢ τ ≡ᵗ τ }}a ->
  {{ Θ ⊢ τ ≡ᵗ (msubst_ptyp κ2 τ0) }}a ->
  a_inc_equiv (Ξ ++ (β ~ abind_flex_mono_def τ0) ++ Θ0)
              (κ1 ++ (β, τ) :: κ2) (σ1 ++ (β, τ) :: σ2) Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH];
    intros κ1 κ2 σ1 σ2 β τ τ0 Θ0 Θ Hd Hlk He Hls Hτ Hτ0.
  - destruct κ1; [ | discriminate ]. destruct σ1; [ | discriminate ].
    simpl in *. apply a_inc_equiv__flex_def; assumption.
  - inversion Hd as [ | ? ? Hd' ]; subst.
    destruct κ1 as [| [k1a k1b] κ1']; [ discriminate | ].
    destruct σ1 as [| [s1a s1b] σ1']; [ discriminate | ].
    simpl in He.
    inversion He as [ | Θa κa σa Θb αa τ1 τ2 Hie Heq | | | | ]; subst.
    simpl. apply a_inc_equiv__flex; [ | exact Heq ].
    apply IH; [ exact Hd' | simpl in Hlk; lia | exact Hie
              | simpl in Hls; lia | exact Hτ | exact Hτ0 ].
Qed.

Lemma a_sub_flex_complete_assign :
  forall n NM M Θ0 Ξ α β τ P0 R' Ψ Θ κ Q,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     length Θ0' <= length Ξ + length Θ0 ->
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  sub_flex_complete_concl n NM M
    ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α P0 R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β τ P0 R' Ψ Θ κ Q IH.
  unfold sub_flex_complete_concl, sub_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.

  assert (Huq : uniq (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; eassumption).
  assert (Hwfcons : {{ ⊢ ((β ~ abind_flex_mono_def τ) ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_prefix; exact Hwf).
  inversion Hwfcons as [ | | βz τz Θz HβΘ0 HwfτΘ0 Hmτ HwfΘ0 | | | ]; subst.
  assert (Hftvτ : ftvar_in_ptyp τ [<=] dom Θ0)
    by (apply a_wf_ptyp_ftv_dom; exact HwfτΘ0).
  assert (Hβτ : β `notin` ftvar_in_ptyp τ) by (clear - Hftvτ HβΘ0; fsetdec).

  destruct (@a_inc_strip_flex_def_mid Ξ β τ Θ0 κ Θ HdeclsΞ Hinc)
    as [κ1 [τβ [κ2 [Heqκ [Hlen [Hdomκ1 [Hincih [Heqβ [Hwfτβ [Hmτβ _]]]]]]]]]].
  assert (Hlk : forall γ, γ <> β ->
            msubst_lookup κ γ = msubst_lookup (κ1 ++ κ2) γ)
    by (intros γ Hγ; rewrite Heqκ; apply msubst_lookup_mid_drop; exact Hγ).

  assert (Hτ12 : msubst_ptyp (κ1 ++ κ2) τ = msubst_ptyp κ2 τ).
  { apply msubst_ptyp_agree. intros γ Hγ.
    apply msubst_lookup_app_notin.
    assert (HγΘ0 : γ `in` dom Θ0) by (clear - Hγ Hftvτ; fsetdec).
    rewrite Hdomκ1.
    assert (Huq' : uniq (Ξ ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf').
    clear - Huq' HγΘ0. destruct_uniq. unfold disjoint in *. fsetdec. }
  assert (Heqβ' : {{ Θ ⊢ τβ ≡ᵗ (msubst_ptyp (κ1 ++ κ2) τ) }}a)
    by (rewrite Hτ12; exact Heqβ).

  assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
            subst_pskl_in_pskl (ptyp_to_pskl τ) β P0 }}a).
  { eapply a_wf_pskl_subst_mid_def; eassumption. }
  assert (Hαb : a_binds_tvar α (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
    by (destruct (a_flex_tvar_weaken_app Ξ Hfα) as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (HwfS : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
            subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α) }}a).
  { eapply a_wf_pskl_subst_mid_def; [ exact Hwf | apply a_wf_pskl__var; exact Hαb ]. }

  assert (Hincβ : ((β, τβ) :: (κ1 ++ κ2))
                    ∷ ((β ~ abind_flex_mono_def τ) ++ (Ξ ++ Θ0)) ⊑ Θ)
    by (apply a_inc__flex_def; eassumption).
  assert (HwfX : a_wf_ptyp Θ (msubst_ptyp (κ1 ++ κ2) τ)).
  { eapply a_wf_ptyp_msubst;
      [ eapply a_wf_ptyp_weaken;
        [ intros x b0 Hb0; unfold binds in *; apply in_or_app; right; exact Hb0
        | exact HwfτΘ0 ]
      | exact Hwf' | exact Hincih ]. }
  assert (HmX : mono_ptyp (msubst_ptyp (κ1 ++ κ2) τ))
    by (eapply mono_ptyp_msubst; eassumption).
  assert (HincX : ((β, msubst_ptyp (κ1 ++ κ2) τ) :: (κ1 ++ κ2))
                    ∷ ((β ~ abind_flex_mono_def τ) ++ (Ξ ++ Θ0)) ⊑ Θ)
    by (apply a_inc__flex_def;
        [ exact Hincih | exact HwfX | exact HmX
        | apply a_tyequiv__refl; apply mono_ptyp_lc; exact HmX ]).
  assert (Hagree : forall γ,
            {{ Θ ⊢ (msubst_lookup ((β, τβ) :: (κ1 ++ κ2)) γ)
              ≡ᵗ (msubst_lookup ((β, msubst_ptyp (κ1 ++ κ2) τ)
                                   :: (κ1 ++ κ2)) γ) }}a).
  { intros γ. simpl. destruct (γ == β) as [-> | Hne];
      [ exact Heqβ'
      | apply a_tyequiv__refl; eapply a_inc_msubst_lc; exact Hincih ]. }

  assert (HlcP0 : lc_pskl P0) by (eapply a_wf_pskl_lc; exact HwfP0).
  assert (Hβdomκ1 : β `notin` dom κ1)
    by (rewrite Hdomκ1; clear - HβΞΘ0; simpl_env in HβΞΘ0; fsetdec).
  assert (HeqP0κ : msubst_pskl κ P0
                 = msubst_pskl ((β, τβ) :: (κ1 ++ κ2)) P0).
  { apply msubst_pskl_agree. intros γ _. rewrite Heqκ. simpl.
    destruct (γ == β) as [-> | Hne].
    - rewrite (@msubst_lookup_app_notin κ1 ((β, τβ) :: κ2) β Hβdomκ1).
      simpl.
      match goal with
      | |- (if ?t then _ else _) = _ => destruct t as [_ | n0]
      end; [ reflexivity | exfalso; apply n0; reflexivity ].
    - apply msubst_lookup_mid_drop; exact Hne. }
  assert (Heqs : {{ Θ ⊢ (msubst_pskl κ P0)
                   ≡ˢ (msubst_pskl (κ1 ++ κ2)
                         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)) }}a).
  { rewrite HeqP0κ, msubst_pskl_subst.
    eapply msubst_pskl_tyequiv_pointwise; eassumption. }
  assert (Hrs' : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl (κ1 ++ κ2)
               (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0))) ⊳ Q }}ad).
  { destruct (skl_tyequiv_refine_syn_transport Heqs Hwfth
                (fun x b0 (h : binds x b0 Θ) => h)) as [Hfwd _].
    apply Hfwd. exact Hrs. }
  assert (HeqR : ⌊ pskl_to_uskl
                    (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ⌋ˢ
                 = subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
    by apply uskl_to_pskl_pskl_to_uskl.
  assert (Hslack' : {{ Θ ⊢ R' ≡ᵘ (msubst_uskl_syn (κ1 ++ κ2)
            (pskl_to_uskl
               (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) }}a).
  { rewrite msubst_uskl_syn_pskl_to_uskl, msubst_pskl_subst.
    cbn [msubst_pskl]. rewrite pskl_to_uskl_ptyp.
    eapply a_uskl_tyequiv_trans; [ exact Hslack | ].
    assert (HwfXctx : {{ ⊢ ((β ~ abind_flex_mono_def τ) ++ (Ξ ++ Θ0)) }}a).
    { simpl_env. apply a_wf_aenv__flex_def;
        [ exact HβΞΘ0
        | eapply a_wf_ptyp_weaken;
          [ intros x b0 Hb0; unfold binds in *; apply in_or_app; right;
            exact Hb0 | exact HwfτΘ0 ]
        | exact Hmτ | exact Hwf' ]. }
    assert (HαbX : a_binds_tvar α ((β ~ abind_flex_mono_def τ) ++ (Ξ ++ Θ0))).
    { assert (Hmove : forall (x : atom) (b0 : abind),
                binds x b0 (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0) ->
                binds x b0 ((β ~ abind_flex_mono_def τ) ++ (Ξ ++ Θ0))).
      { intros x b0 Hb. unfold binds in *. simpl in *.
        apply in_app_or in Hb. destruct Hb as [h | h];
          [ right; apply in_or_app; left; exact h
          | destruct h as [h | h];
            [ left; exact h
            | right; apply in_or_app; right; exact h ] ]. }
      destruct Hαb as [Hb | [Hb | [τ0 Hb]]];
        [ left | right; left | right; right; exists τ0 ];
        apply Hmove; exact Hb. }
    assert (Heqlk : {{ Θ ⊢ (msubst_lookup κ α)
              ≡ᵗ (msubst_lookup ((β, msubst_ptyp (κ1 ++ κ2) τ)
                                   :: (κ1 ++ κ2)) α) }}a).
    { simpl. destruct (α == β) as [-> | Hne].
      - rewrite Heqκ.
        rewrite (@msubst_lookup_app_notin κ1 ((β, τβ) :: κ2) β Hβdomκ1).
        simpl.
        match goal with
        | |- context [if ?t then _ else _] => destruct t as [_ | n0]
        end; [ exact Heqβ' | exfalso; apply n0; reflexivity ].
      - rewrite (Hlk α Hne).
        apply a_tyequiv__refl; eapply a_inc_msubst_lc; exact Hincih. }
    apply a_uskl_tyequiv__mono.
    - eapply a_inc_lookup_mono; exact Hinc.
    - eapply a_inc_lookup_mono; exact HincX.
    - eapply a_inc_lookup_wf; eassumption.
    - eapply a_inc_lookup_wf; eassumption.
    - exact Heqlk. }
  assert (Hgf' : NM = a_sub_mode_ty -> uskl_ghost_free R').
  { intros _. eapply tyequiv_mono_paint_ghost_free;
      [ exact Hslack
      | eapply a_inc_lookup_mono; exact Hinc
      | eapply a_inc_lookup_wf; eassumption ]. }
  destruct (IH NM (mode_fn M) (Ξ ++ Θ0)
              (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
              (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
              (pskl_to_uskl
                 (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))
              R' Ψ Θ (κ1 ++ κ2) Q
              ltac:(rewrite length_app; lia)
              Hwf' Hwfth HwfP0' HwfS
              ltac:(intros HSK; apply a_sk_mode_compat_subst_mono;
                    [ apply HmodSK; exact HSK | exact Hmτ ])
              ltac:(intros HTY; apply a_ty_mode_compat_subst_mono;
                    [ apply HmodTY; exact HTY | exact Hmτ ])
              HeqR Hincih Hslack' HD Hrs' HwfQ Hgf')
    as [P1 [Θ1 [Hrun Hopt]]].

  assert (HmodSK' : NM = a_sub_mode_sk ->
            a_sk_mode_compat (mode_fn M)
              (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0))
    by (intros HSK; apply a_sk_mode_compat_subst_mono;
        [ apply HmodSK; exact HSK | exact Hmτ ]).
  assert (HmodTY' : NM = a_sub_mode_ty ->
            a_ty_mode_compat (mode_fn M)
              (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0))
    by (intros HTY; apply a_ty_mode_compat_subst_mono;
        [ apply HmodTY; exact HTY | exact Hmτ ]).
  destruct (a_sub_sound Hrun Hwf' HwfP0' HwfS HmodSK' HmodTY')
    as [[[w [Hidw Hincw]] Hdefs] [HwfΘ1 [Qt [HeqQt [Hjoin1 _]]]]].
  assert (HwfP1o : {{ Θ1 ⨟ empty ⊢ₚₛ P1 }}a)
    by (exact (a_sub_output_wf Hrun Hwf' HwfP0' HwfS)).
  assert (HβflexΘ1 : forall bd, binds β bd Θ1 ->
            bd = abind_flex_mono \/ exists τ0, bd = abind_flex_mono_def τ0).
  { intros bd Hb.
    assert (Hprov : a_suffix_binding bd \/ β `in` dom (Ξ ++ Θ0))
      by (eapply a_inc_binds_provenance; eassumption).
    destruct Hprov as [h | h];
      [ inversion h; subst;
        [ left; reflexivity | right; eexists; reflexivity ]
      | exfalso; clear - h HβΞΘ0; fsetdec ]. }

  assert (HβΞΘ0f : β `notin` ftvar_in_aenv (Ξ ++ Θ0)).
  { pose proof (a_wf_aenv_ftv_dom Hwf') as h. clear - h HβΞΘ0. fsetdec. }
  assert (HβP0' : β `notin` ftvar_in_pskl
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P0
                  (ptyp_to_pskl τ) β) as h.
    pose proof (ftvar_ptyp_to_pskl τ) as h2.
    clear - h h2 Hβτ. fsetdec. }
  assert (HβS : β `notin` ftvar_in_pskl
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))).
  { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper (pskl_var_f α)
                  (ptyp_to_pskl τ) β) as h.
    pose proof (ftvar_ptyp_to_pskl τ) as h2.
    clear - h h2 Hβτ. fsetdec. }
  destruct (atom_fresh (dom Θ1 `union` ftvar_in_aenv Θ1
                        `union` ftvar_in_pskl P1
                        `union` ftvar_in_aenv (Ξ ++ Θ0) `union` dom (Ξ ++ Θ0)
                        `union` ftvar_in_pskl
                            (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
                        `union` ftvar_in_pskl
                            (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                               (pskl_var_f α))
                        `union` ftvar_in_ptyp τ `union` singleton β))
    as [β1 Fr].
  assert (Hrunsw : a_sub NM (mode_fn M)
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) (Ξ ++ Θ0)
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
            (swap_pskl β β1 P1) (swap_aenv β β1 Θ1)).
  { apply (a_sub_swap_junk β β1 NM (mode_fn M)
             (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) (Ξ ++ Θ0)
             (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
             P1 Θ1 Hrun);
      [ clear - HβΞΘ0f HβP0' HβS; fsetdec | clear - Fr; solve_notin_auto ]. }
  exists (swap_pskl β β1 P1),
         ((β ~ abind_flex_mono_def τ) ++ swap_aenv β β1 Θ1).
  split.
  { apply a_sub_flex__assign;
      [ apply swap_junk_dom_out; clear - Fr; solve_notin_auto | exact Hrunsw ]. }

  intros κf Hidf Hincf.
  destruct (@a_inc_strip_flex_def_mid Ξ β τ Θ0 κf
              ((β ~ abind_flex_mono_def τ) ++ swap_aenv β β1 Θ1)
              HdeclsΞ Hincf)
    as [κf1 [τf [κf2 [Heqκf [Hlenf [_ [Hincfih [_ [_ [_ _]]]]]]]]]].
  assert (Hidfih : is_id_msubst (κf1 ++ κf2)).
  { unfold is_id_msubst in *. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [h1 h2].
    inversion h2; subst. apply Forall_app; split; assumption. }
  assert (Heqτf : τf = ptyp_var_f β).
  { unfold is_id_msubst in Hidf. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [_ h2].
    inversion h2 as [| e κl he hl]; subst.
    unfold is_id_entry in he; simpl in he. exact he. }
  assert (Heqw : w = κf1 ++ κf2)
    by (eapply is_id_inc_unique; eassumption).
  subst w.
  destruct (Hopt (κf1 ++ κf2) Hidfih Hincw) as [ζ [Hζ [Hie Hprec]]].
  assert (Hkeysζ : forall γ, List.In γ (List.map fst ζ) -> γ `in` dom Θ1)
    by (intros γ hγ; eapply a_inc_keys_dom; eassumption).
  assert (Hkeysf : forall γ, List.In γ (List.map fst (κf1 ++ κf2)) ->
            γ `in` dom (Ξ ++ Θ0))
    by (intros γ hγ; eapply a_inc_keys_dom; eassumption).

  assert (Hζτ : {{ Θ ⊢ (msubst_ptyp (κ1 ++ κ2) τ) ≡ᵗ (msubst_ptyp ζ τ) }}a).
  { assert (Hwfτ : a_wf_ptyp (Ξ ++ Θ0) τ).
    { eapply a_wf_ptyp_weaken; [ | exact HwfτΘ0 ].
      intros α0 bd Hb. apply binds_app_3; exact Hb. }
    rewrite <- (msubst_compose_id_ptyp Hwf' HwfΘ1 Hidfih Hincw Hζ Hwfτ).
    eapply a_inc_equiv_msubst_ptyp; eauto using a_inc_msubst_lc.
    apply msubst_lc_compose; [eapply a_inc_msubst_lc; exact Hζ |].
    intros α0 A Hin. eapply is_id_msubst_values_lc; eauto. }

  exists ((β, τβ) :: kswap_msubst β β1 ζ).
  split.
  { apply a_inc__flex_def;
      [ apply (a_inc_kswap β β1 ζ Θ1 Θ Hζ);
        [ clear - Fr; solve_notin_auto | exact HwfΘ1 | clear - Fr; solve_notin_auto
        | exact HβflexΘ1 ]
      | exact Hwfτβ | exact Hmτβ | ].
    assert (Hkτ : msubst_ptyp (kswap_msubst β β1 ζ) τ = msubst_ptyp ζ τ).
    { rewrite <- (swap_ptyp_fresh_id β β1 τ) at 1;
        [ | clear - Hβτ; fsetdec | clear - Fr; solve_notin_auto ].
      apply msubst_ptyp_kswap;
        [ clear - Fr; solve_notin_auto
        | intro hc; pose proof (Hkeysζ β1 hc) as h; clear - h Fr; fsetdec
        | clear - Fr; solve_notin_auto
        | left; exact Hβτ ]. }
    rewrite Hkτ.
    eapply a_tyequiv__trans; eassumption. }
  split.
  {
    rewrite Heqκ, Heqκf, Heqτf.
    assert (Hsplit : msubst_compose ((β, τβ) :: kswap_msubst β β1 ζ)
                       (κf1 ++ (β, ptyp_var_f β) :: κf2)
                   = msubst_compose ((β, τβ) :: kswap_msubst β β1 ζ) κf1
                     ++ (β, τβ)
                     :: msubst_compose ((β, τβ) :: kswap_msubst β β1 ζ) κf2).
    { unfold msubst_compose. rewrite List.map_app. simpl.
      destruct (β == β) as [_ | n0]; [ reflexivity | exfalso; auto ]. }
    rewrite Hsplit.
    assert (Hid1 : is_id_msubst κf1 /\ is_id_msubst κf2)
      by (unfold is_id_msubst in Hidfih; apply Forall_app in Hidfih;
          exact Hidfih).
    destruct Hid1 as [Hidf1 Hidf2].
    assert (Hkey1 : forall γ, List.In γ (List.map fst κf1) ->
              γ <> β /\ γ <> β1).
    { intros γ hγ.
      assert (hd : γ `in` dom (Ξ ++ Θ0))
        by (apply Hkeysf; rewrite List.map_app; apply in_or_app; left; exact hγ).
      split; [ intro Hc; subst; clear - hd HβΞΘ0; fsetdec
             | intro Hc; subst; clear - hd Fr; fsetdec ]. }
    assert (Hkey2 : forall γ, List.In γ (List.map fst κf2) ->
              γ <> β /\ γ <> β1).
    { intros γ hγ.
      assert (hd : γ `in` dom (Ξ ++ Θ0))
        by (apply Hkeysf; rewrite List.map_app; apply in_or_app; right; exact hγ).
      split; [ intro Hc; subst; clear - hd HβΞΘ0; fsetdec
             | intro Hc; subst; clear - hd Fr; fsetdec ]. }
    assert (Hk1b : forall γ, List.In γ (List.map fst κf1) -> γ <> β)
      by (intros γ hγ; exact (proj1 (Hkey1 γ hγ))).
    assert (Hk2b : forall γ, List.In γ (List.map fst κf2) -> γ <> β)
      by (intros γ hγ; exact (proj1 (Hkey2 γ hγ))).
    rewrite (@msubst_compose_cons_l_id β τβ (kswap_msubst β β1 ζ) κf1 Hidf1
               (@notin_dom_of_keys_neq _ _ Hk1b)).
    rewrite (@msubst_compose_cons_l_id β τβ (kswap_msubst β β1 ζ) κf2 Hidf2
               (@notin_dom_of_keys_neq _ _ Hk2b)).
    rewrite (msubst_compose_kswap_id β β1 ζ κf1 Hidf1 Hkey1).
    rewrite (msubst_compose_kswap_id β β1 ζ κf2 Hidf2 Hkey2).
    apply a_inc_equiv_insert_flex_def_mid;
      [ exact HdeclsΞ | exact Hlen
      | unfold msubst_compose in *; rewrite <- List.map_app; exact Hie
      | unfold msubst_compose; rewrite List.map_length; exact Hlenf
      | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτβ
      | exact Heqβ ]. }
  {
    assert (Hnbsw : β `notin` ftvar_in_pskl (swap_pskl β β1 P1)).
    { intro Hc.
      assert (h : β1 `in` ftvar_in_pskl P1).
      { pose proof (swap_pskl_ftv_in_rev β β1 P1 β Hc) as h0.
        rewrite swap_atom_l in h0. exact h0. }
      clear - h Fr. solve_notin_auto. }
    rewrite (msubst_bskl_head_notin β τβ (kswap_msubst β β1 ζ)
               (pskl_to_bskl_syn (swap_pskl β β1 P1))
               ltac:(rewrite ftvar_in_bskl_syn; exact Hnbsw)).
    rewrite (@a_inc_kswap_paint β β1 ζ Θ1 _ P1 Hζ HwfP1o HβflexΘ1)
      by (clear - Fr; solve_notin_auto).
    exact Hprec.
  }
Qed.

Lemma ad_pat_sub_fuel_mono_fn_arrow_inv : forall n NM Mf Ψ Θ R Q,
  ad_pat_sub_fuel n NM Mf Ψ Θ R Q ->
  {{ ⊢ Θ }}a ->
  forall M τ, Mf = mode_fn M -> R = ptyp_to_uskl_syn τ ->
  mono_ptyp τ -> a_wf_ptyp Θ τ ->
  exists τ1 τ2,
    {{ Θ ⊢ τ ≡ᵗ (ptyp_arrow τ1 τ2) }}a /\
    mono_ptyp τ1 /\ mono_ptyp τ2 /\
    a_wf_ptyp Θ τ1 /\ a_wf_ptyp Θ τ2 /\
    ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ
      (ptyp_to_uskl_syn (ptyp_arrow τ1 τ2)) Q.
Proof.
  intros n NM Mf Ψ Θ R Q H Hwfth; induction H;
    intros M0 τ0 HeqM HeqR Hm Hwf;
    try discriminate HeqM;
    try (destruct τ0; cbn in HeqR; try discriminate HeqR;
         try solve [ inversion Hm ]).
  -
    inversion HeqM; subst. inversion HeqR; subst.
    assert (Hrefl : {{ Θ ⊢ (ptyp_arrow τ0_1 τ0_2) ≡ᵗ (ptyp_arrow τ0_1 τ0_2) }}a)
      by (apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hm).
    inversion Hm; subst. inversion Hwf; subst.
    exists τ0_1, τ0_2.
    split; [ exact Hrefl | ].
    split; [ assumption | ]. split; [ assumption | ].
    split; [ assumption | ]. split; [ assumption | ].
    cbn. eapply ad_pat_sub_fuel__arrow; eassumption.
  -
    injection HeqR; intros He; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfth | eassumption ]).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwfth | eassumption ]).
    destruct (IHad_pat_sub_fuel Hwfth M0 τ HeqM eq_refl Hmτ Hwfτ)
      as [τ1 [τ2 [Heq [Hm1 [Hm2 [Hwf1 [Hwf2 Hjoin]]]]]]].
    exists τ1, τ2.
    split.
    { eapply a_tyequiv__trans; [ | exact Heq ].
      apply a_tyequiv__flex_def; eassumption. }
    split; [ exact Hm1 | ]. split; [ exact Hm2 | ].
    split; [ exact Hwf1 | ]. split; [ exact Hwf2 | ]. exact Hjoin.
Qed.

Lemma a_inc_attach_decls_prefix : forall Ξ κ1 Θa κa Θb κb Θ,
  a_decls Ξ ->
  (κ1 ++ κa) ∷ (Ξ ++ Θa) ⊑ Θ ->
  length κ1 = length Ξ ->
  κb ∷ Θb ⊑ Θ ->
  (κ1 ++ κb) ∷ (Ξ ++ Θb) ⊑ Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH];
    intros κ1 Θa κa Θb κb Θ Hd Hinc Hlen Hincb.
  - destruct κ1; [ | discriminate ]. simpl. exact Hincb.
  - inversion Hd as [ | ? ? Hd' ]; subst.
    destruct κ1 as [| [k1a k1b] κ1']; [ discriminate | ].
    simpl in Hinc.
    inversion Hinc as [ | Θz κz Θy αz τz Hi Hw Hm | | | | ]; subst.
    simpl. apply a_inc__flex; [ | exact Hw | exact Hm ].
    eapply IH; [ exact Hd' | exact Hi | simpl in Hlen; lia | exact Hincb ].
Qed.

Lemma a_wf_aenv_replace_decls_tail : forall Ξ Θa Θb,
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ Θa) }}a ->
  {{ ⊢ Θb }}a ->
  (forall x, x `in` dom Ξ -> x `notin` dom Θb) ->
  {{ ⊢ (Ξ ++ Θb) }}a.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH]; intros Θa Θb Hd Hwf Hwfb Hdisj.
  - simpl. exact Hwfb.
  - inversion Hd as [ | ? ? Hd' ]; subst.
    simpl in Hwf. inversion Hwf as [ | αz Θz Hn Hwf' | | | | ]; subst.
    simpl. apply a_wf_aenv__flex.
    + rewrite dom_app.
      assert (h1 : x `notin` dom Ξ')
        by (rewrite dom_app in Hn; clear - Hn; fsetdec).
      assert (h2 : x `notin` dom Θb)
        by (apply Hdisj; simpl; clear; fsetdec).
      clear - h1 h2; fsetdec.
    + eapply IH; [ exact Hd' | exact Hwf' | exact Hwfb | ].
      intros y Hy. apply Hdisj. simpl. clear - Hy; fsetdec.
Qed.

Lemma msubst_lookup_insert2 : forall κ1 α0 τ β τ2 α τ1 κ2 γ,
  γ <> α -> γ <> β ->
  msubst_lookup (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) γ
  = msubst_lookup (κ1 ++ (α0, τ) :: κ2) γ.
Proof.
  intros κ1; induction κ1 as [| [x tx] κ1'];
    intros α0 τ β τ2 α τ1 κ2 γ Hα Hβ; simpl.
  - destruct (γ == α0) as [_ | _]; [ reflexivity | ].
    destruct (γ == β) as [e | _]; [ exfalso; auto | ].
    destruct (γ == α) as [e | _]; [ exfalso; auto | reflexivity ].
  - destruct (γ == x) as [_ | _]; [ reflexivity | apply IHκ1'; assumption ].
Qed.

Lemma a_inc_equiv_collapse_solve :
  forall Ξ κ1 κ2 σ1 σ2 α0 τ β τ2 α τ1 X Xb Xa Θ0 Θ,
  a_decls Ξ ->
  length κ1 = length Ξ -> length σ1 = length Ξ ->
  a_inc_equiv
    (Ξ ++ (α0 ~ abind_flex_mono_def
                 (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
        ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
    (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2)
    (σ1 ++ (α0, X) :: (β, Xb) :: (α, Xa) :: σ2) Θ ->
  a_inc_equiv (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0)
              (κ1 ++ (α0, τ) :: κ2) (σ1 ++ (α0, X) :: σ2) Θ.
Proof.
  intros Ξ; induction Ξ as [| [x b] Ξ' IH];
    intros κ1 κ2 σ1 σ2 α0 τ β τ2 α τ1 X Xb Xa Θ0 Θ Hd Hlk Hls He.
  - destruct κ1; [ | discriminate ]. destruct σ1; [ | discriminate ].
    simpl in *.
    inversion He as [ | | Θz κz σz Θy αz τz τz1 τz2 Hie Heq Heqd | | | ];
      subst.
    inversion Hie as [ | Θa κa σa Θb αa τa1 τa2 Hie2 Heq2 | | | | ]; subst.
    inversion Hie2 as [ | Θc κc σc Θe αc τc1 τc2 Hie3 Heq3 | | | | ]; subst.
    apply a_inc_equiv__flex; eassumption.
  - inversion Hd as [ | ? ? Hd' ]; subst.
    destruct κ1 as [| [k1a k1b] κ1']; [ discriminate | ].
    destruct σ1 as [| [s1a s1b] σ1']; [ discriminate | ].
    simpl in He.
    inversion He as [ | Θa κa σa Θb αa τa1 τa2 Hie Heq | | | | ]; subst.
    simpl. apply a_inc_equiv__flex; [ | exact Heq ].
    eapply IH; [ exact Hd' | simpl in Hlk; lia | simpl in Hls; lia | exact Hie ].
Qed.

Lemma app_split_by_head_length : forall (A : Type) (l1 l2 m1 m2 : list A),
  l1 ++ l2 = m1 ++ m2 -> length l1 = length m1 -> l1 = m1 /\ l2 = m2.
Proof.
  intros A l1 l2 m1 m2 Heq Hlen.
  apply app_inj_tail_length; [ exact Heq | ].
  assert (h : length (l1 ++ l2) = length (m1 ++ m2))
    by (rewrite Heq; reflexivity).
  repeat rewrite List.app_length in h. lia.
Qed.

Lemma binds_insert_two_mid : forall (γ : atom) (b : abind) Ξ α0 b0 b1 e1 e2 Θ0,
  binds γ b (Ξ ++ (α0 ~ b0) ++ Θ0) -> γ <> α0 ->
  binds γ b (Ξ ++ (α0 ~ b1) ++ e1 ++ e2 ++ Θ0).
Proof.
  intros γ b Ξ α0 b0 b1 e1 e2 Θ0 Hb Hne.
  unfold binds in *. apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [h | h]; [ left; exact h | right ].
  simpl in h. destruct h as [h | h];
    [ exfalso; inversion h; subst; apply Hne; reflexivity | ].
  simpl. right. apply in_or_app. right. apply in_or_app. right. exact h.
Qed.

Lemma a_sub_flex_complete_solve : forall n NM M Θ0 Ξ α0 P0 R' Ψ Θ κ Q,
  (forall NM' M' Θ0' P0' P' Ra Rb T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' (uskl_arrow Ra Rb) T''
       Ψ' Θ' κ' Q') ->
  sub_flex_complete_concl n NM M ((α0 ~ abind_flex_mono) ++ Θ0) Ξ α0 P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α0 P0 R' Ψ Θ κ Q IH.
  unfold sub_flex_complete_concl, sub_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.

  assert (Huq : uniq (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Hα0ΞΘ0 : α0 `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; eassumption).
  assert (HwfΘ0 : {{ ⊢ Θ0 }}a) by (eapply a_wf_aenv_strip_prefix; exact Hwf').

  destruct (@a_inc_strip_flex_mid Ξ α0 Θ0 κ Θ HdeclsΞ Hinc)
    as [κ1 [τ [κ2 [Heqκ [Hlen [Hdomκ1 [Hincih [Hwfτ [Hmτ Hincκ2]]]]]]]]].
  assert (Hα0κ1 : α0 `notin` dom κ1)
    by (rewrite Hdomκ1; clear - Hα0ΞΘ0; simpl_env in Hα0ΞΘ0; fsetdec).
  assert (Hlkα0 : msubst_lookup κ α0 = τ).
  { rewrite Heqκ.
    rewrite (@msubst_lookup_app_notin κ1 ((α0, τ) :: κ2) α0 Hα0κ1). simpl.
    match goal with
    | |- (if ?t then _ else _) = _ => destruct t as [_ | n0]
    end; [ reflexivity | exfalso; apply n0; reflexivity ]. }
  rewrite Hlkα0 in Hslack.

  destruct (a_uskl_tyequiv_mono_r_inv Hslack (eq_refl (ptyp_to_uskl_syn τ)) Hmτ Hwfτ)
    as [τ' [HeqR' [Hmτ' [Hwfτ' Heqττ']]]].
  subst R'.

  destruct (ad_pat_sub_fuel_mono_fn_arrow_inv HD Hwfth
              (eq_refl (mode_fn M)) (eq_refl (ptyp_to_uskl_syn τ'))
              Hmτ' Hwfτ')
    as [τ1 [τ2 [Heqarr [Hm1 [Hm2 [Hwf1 [Hwf2 _]]]]]]].
  assert (Hτarr : {{ Θ ⊢ τ ≡ᵗ (ptyp_arrow τ1 τ2) }}a).
  { eapply a_tyequiv__trans;
      [ apply a_tyequiv__sym; exact Heqττ' | exact Heqarr ]. }

  simpl_env in Hα0ΞΘ0.
  destruct (atom_fresh (dom Ξ `union` dom Θ0 `union` singleton α0
                        `union` ftvar_in_pskl P0)) as [α Frα].
  destruct (atom_fresh (dom Ξ `union` dom Θ0 `union` singleton α0
                        `union` singleton α `union` ftvar_in_pskl P0))
    as [β Frβ].
  assert (Hαβ : α <> β) by (clear - Frβ; fsetdec).
  assert (HαΞ : α `notin` dom Ξ) by (clear - Frα; fsetdec).
  assert (HαΘ0 : α `notin` dom Θ0) by (clear - Frα; fsetdec).
  assert (Hαα0 : α <> α0) by (clear - Frα; fsetdec).
  assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - Frα; fsetdec).
  assert (HβΞ : β `notin` dom Ξ) by (clear - Frβ; fsetdec).
  assert (HβΘ0 : β `notin` dom Θ0) by (clear - Frβ; fsetdec).
  assert (Hβα0 : β <> α0) by (clear - Frβ; fsetdec).
  assert (HβP0 : β `notin` ftvar_in_pskl P0) by (clear - Frβ; fsetdec).
  assert (Hα0Ξ : α0 `notin` dom Ξ) by (clear - Hα0ΞΘ0; fsetdec).
  assert (Hα0Θ0 : α0 `notin` dom Θ0) by (clear - Hα0ΞΘ0; fsetdec).
  clear Frα Frβ.

  assert (Hincα : ((α, τ1) :: κ2) ∷ ((α ~ abind_flex_mono) ++ Θ0) ⊑ Θ)
    by (apply a_inc__flex; eassumption).
  assert (Hincβ : ((β, τ2) :: (α, τ1) :: κ2)
            ∷ ((β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ⊑ Θ)
    by (apply a_inc__flex; eassumption).
  assert (Hincα0 : ((α0, τ) :: (β, τ2) :: (α, τ1) :: κ2)
            ∷ ((α0 ~ abind_flex_mono_def
                       (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
               ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ⊑ Θ).
  { apply a_inc__flex_def; [ exact Hincβ | exact Hwfτ | exact Hmτ | ].
    cbn.
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [e | _]
    end; [ exfalso; apply Hαβ; exact e | ].
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [_ | n0]
    end; [ | exfalso; apply n0; reflexivity ].
    match goal with
    | |- context [if ?t then _ else _] => destruct t as [_ | n0]
    end; [ exact Hτarr | exfalso; apply n0; reflexivity ]. }
  assert (Hincθs : (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2)
            ∷ (Ξ ++ (α0 ~ abind_flex_mono_def
                          (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) ⊑ Θ).
  { eapply a_inc_attach_decls_prefix;
      [ exact HdeclsΞ | rewrite <- Heqκ; exact Hinc | exact Hlen
      | exact Hincα0 ]. }

  assert (HwfΘb : {{ ⊢ ((α0 ~ abind_flex_mono_def
                     (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
             ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) }}a).
  { assert (Hα0b : α0 `notin` dom ((β ~ abind_flex_mono)
                                   ++ (α ~ abind_flex_mono) ++ Θ0)).
    { simpl_env. clear - Hβα0 Hαα0 Hα0Θ0. fsetdec. }
    apply a_wf_aenv__flex_def; [ exact Hα0b | | | ].
    - apply a_wf_ptyp__arrow; apply a_wf_ptyp__var; right; left;
        unfold binds; simpl; auto.
    - apply mono_ptyp__arrow; apply mono_ptyp__var.
    - apply a_wf_aenv__flex;
        [ simpl_env; clear - Hαβ HβΘ0; fsetdec | ].
      apply a_wf_aenv__flex;
        [ clear - HαΘ0; fsetdec | exact HwfΘ0 ]. }
  assert (HwfΘsrc : {{ ⊢ (Ξ ++ (α0 ~ abind_flex_mono_def
                          (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
               ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0) }}a).
  { eapply a_wf_aenv_replace_decls_tail;
      [ exact HdeclsΞ | exact Hwf | exact HwfΘb | ].
    intros x Hx. simpl_env.
    assert (hx0 : x `notin` dom ((α0 ~ abind_flex_mono) ++ Θ0)).
    { clear - Huq Hx. simpl_env in Huq. destruct_uniq.
      unfold disjoint in *. simpl_env in *. fsetdec. }
    simpl_env in hx0.
    assert (hxα : x <> α) by (intro Hc; subst; clear - HαΞ Hx; fsetdec).
    assert (hxβ : x <> β) by (intro Hc; subst; clear - HβΞ Hx; fsetdec).
    clear - hx0 hxα hxβ. fsetdec. }

  assert (Hmoveb : forall γ,
            a_binds_tvar γ (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0) ->
            a_binds_tvar γ
              (Ξ ++ (α0 ~ abind_flex_mono_def
                            (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)).
  { intros γ Hb. destruct (γ == α0) as [-> | Hne].
    - right; right.
      exists (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)).
      unfold binds; apply in_or_app; right; simpl; left; reflexivity.
    - destruct Hb as [hb | [hb | [τz hb]]];
        [ left | right; left | right; right; exists τz ];
        (eapply binds_insert_two_mid; eassumption). }
  assert (HwfP0src : {{ (Ξ ++ (α0 ~ abind_flex_mono_def
                                  (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                        ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                        ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
    by (eapply a_wf_pskl_tvar_mono; eassumption).

  assert (HwfSsrc : {{ (Ξ ++ (α0 ~ abind_flex_mono_def
                                 (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                       ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                       ++ Θ0) ⨟ empty ⊢ₚₛ
                      (pskl_arrow (pskl_var_f α) (pskl_var_f β)) }}a).
  { apply a_wf_pskl__arrow; apply a_wf_pskl__var; right; left;
      unfold binds; apply in_or_app; right; simpl;
      [ right; right; left; reflexivity | right; left; reflexivity ]. }
  assert (HeqR : ⌊ uskl_arrow (uskl_var_f α) (uskl_var_f β) ⌋ˢ
                 = pskl_arrow (pskl_var_f α) (pskl_var_f β)) by reflexivity.

  assert (Hlkα : msubst_lookup
            (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) α = τ1).
  { assert (hn : α `notin` dom κ1) by (rewrite Hdomκ1; exact HαΞ).
    rewrite (@msubst_lookup_app_notin κ1 _ α hn). simpl.
    destruct (α == α0) as [e | _]; [ exfalso; apply Hαα0; exact e | ].
    destruct (α == β) as [e | _]; [ exfalso; apply Hαβ; exact e | ].
    destruct (α == α) as [_ | n0]; [ reflexivity | exfalso; apply n0; auto ]. }
  assert (Hlkβ : msubst_lookup
            (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) β = τ2).
  { assert (hn : β `notin` dom κ1) by (rewrite Hdomκ1; exact HβΞ).
    rewrite (@msubst_lookup_app_notin κ1 _ β hn). simpl.
    destruct (β == α0) as [e | _]; [ exfalso; apply Hβα0; exact e | ].
    destruct (β == β) as [_ | n0]; [ reflexivity | exfalso; apply n0; auto ]. }
  assert (Hslack' : {{ Θ ⊢ (ptyp_to_uskl_syn τ')
            ≡ᵘ (msubst_uskl_syn (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2)
                  (uskl_arrow (uskl_var_f α) (uskl_var_f β))) }}a).
  { cbn [msubst_uskl_syn]. rewrite Hlkα, Hlkβ.
    change (uskl_arrow (ptyp_to_uskl_syn τ1) (ptyp_to_uskl_syn τ2))
      with (ptyp_to_uskl_syn (ptyp_arrow τ1 τ2)).
    apply a_uskl_tyequiv__mono;
      [ exact Hmτ' | apply mono_ptyp__arrow; assumption
      | exact Hwfτ' | apply a_wf_ptyp__arrow; assumption
      | exact Heqarr ]. }
  assert (Hrs' : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl
               (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) P0)) ⊳ Q }}ad).
  { assert (Heq : msubst_pskl (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) P0
                = msubst_pskl κ P0).
    { rewrite Heqκ. apply msubst_pskl_agree. intros γ Hγ.
      apply msubst_lookup_insert2;
        [ intro Hc; subst; contradiction | intro Hc; subst; contradiction ]. }
    rewrite Heq. exact Hrs. }
  assert (Hgf' : NM = a_sub_mode_ty -> uskl_ghost_free (ptyp_to_uskl_syn τ'))
    by (intros _; apply mono_ptyp_to_uskl_syn_ghost_free; exact Hmτ').
  destruct (IH NM (mode_fn M)
              (Ξ ++ (α0 ~ abind_flex_mono_def
                            (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
              P0 (pskl_arrow (pskl_var_f α) (pskl_var_f β))
              (uskl_var_f α) (uskl_var_f β)
              (ptyp_to_uskl_syn τ') Ψ Θ
              (κ1 ++ (α0, τ) :: (β, τ2) :: (α, τ1) :: κ2) Q
              HwfΘsrc Hwfth HwfP0src HwfSsrc HmodSK HmodTY HeqR Hincθs
              Hslack' HD Hrs' HwfQ Hgf')
    as [P1 [Θ1 [Hrun Hopt]]].

  exists P1, Θ1. split.
  { apply a_sub_flex__solve with (α := α) (β := β);
      [ exact Hαβ
      | simpl_env; clear - HαΞ HαΘ0 Hαα0; fsetdec
      | simpl_env; clear - HβΞ HβΘ0 Hβα0; fsetdec
      | exact Hrun ]. }

  intros κf Hidf Hincf.
  destruct (a_sub_sound Hrun HwfΘsrc HwfP0src HwfSsrc HmodSK HmodTY)
    as [[[w [Hidw Hincw]] _] [HwfΘ1 _]].
  destruct (Hopt w Hidw Hincw) as [ζ [Hζ [Hie Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ | exact Hprec ].

  destruct (@a_inc_strip_flex_def_mid Ξ α0
              (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β))
              ((β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
              w Θ1 HdeclsΞ Hincw)
    as [w1 [τw [w2 [Heqw [Hlenw [_ [Hw12 [_ [_ [_ _]]]]]]]]]].
  destruct (@a_inc_strip_flex_mid Ξ β ((α ~ abind_flex_mono) ++ Θ0)
              (w1 ++ w2) Θ1 HdeclsΞ Hw12)
    as [wa [τwb [wb [Heqwab [Hlenwa [_ [Hwab [_ [_ _]]]]]]]]].
  assert (Hl1 : length w1 = length wa) by (rewrite Hlenw, Hlenwa; reflexivity).
  destruct (app_split_by_head_length w1 w2 wa ((β, τwb) :: wb) Heqwab Hl1)
    as [Heqw1 Heqw2].
  subst wa. subst w2.
  destruct (@a_inc_strip_flex_mid Ξ α Θ0 (w1 ++ wb) Θ1 HdeclsΞ Hwab)
    as [wc [τwa [wd [Heqwcd [Hlenwc [_ [Hwcd [_ [_ _]]]]]]]]].
  assert (Hl2 : length w1 = length wc) by (rewrite Hlenw, Hlenwc; reflexivity).
  destruct (app_split_by_head_length w1 wb wc ((α, τwa) :: wd) Heqwcd Hl2)
    as [Heqw1' Heqwb].
  subst wc. subst wb.

  destruct (@a_inc_strip_flex_mid Ξ α0 Θ0 κf Θ1 HdeclsΞ Hincf)
    as [κf1 [τf [κf2 [Heqκf [Hlenf [_ [Hκf12 [_ [_ _]]]]]]]]].
  assert (Hidw' : is_id_msubst (w1 ++ wd)).
  { unfold is_id_msubst in *. rewrite Heqw in Hidw.
    apply Forall_app in Hidw. destruct Hidw as [h1 h2].
    inversion h2 as [| e0 l0 he0 hl0]; subst.
    inversion hl0 as [| e1 l1 he1 hl1]; subst.
    inversion hl1 as [| e2 l2 he2 hl2]; subst.
    apply Forall_app; split; assumption. }
  assert (Hidf' : is_id_msubst (κf1 ++ κf2)).
  { unfold is_id_msubst in *. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [h1 h2].
    inversion h2; subst. apply Forall_app; split; assumption. }
  assert (Heqid : w1 ++ wd = κf1 ++ κf2)
    by (eapply is_id_inc_unique; eassumption).
  assert (Hl3 : length w1 = length κf1) by (rewrite Hlenw, Hlenf; reflexivity).
  destruct (app_split_by_head_length w1 wd κf1 κf2 Heqid Hl3)
    as [Heqf1 Heqf2].
  subst κf1. subst κf2.

  assert (Heqτw : τw = ptyp_var_f α0 /\ τwb = ptyp_var_f β
                  /\ τwa = ptyp_var_f α).
  { unfold is_id_msubst in Hidw. rewrite Heqw in Hidw.
    apply Forall_app in Hidw. destruct Hidw as [_ h2].
    inversion h2 as [| e0 l0 he0 hl0]; subst.
    inversion hl0 as [| e1 l1 he1 hl1]; subst.
    inversion hl1 as [| e2 l2 he2 hl2]; subst.
    unfold is_id_entry in he0, he1, he2; simpl in he0, he1, he2.
    repeat split; assumption. }
  destruct Heqτw as [-> [-> ->]].
  assert (Heqτf : τf = ptyp_var_f α0).
  { unfold is_id_msubst in Hidf. rewrite Heqκf in Hidf.
    apply Forall_app in Hidf. destruct Hidf as [_ h2].
    inversion h2 as [| e0 l0 he0 hl0]; subst.
    unfold is_id_entry in he0; simpl in he0. exact he0. }
  subst τf.

  assert (Hsplitw : msubst_compose ζ
            (w1 ++ (α0, ptyp_var_f α0) :: (β, ptyp_var_f β)
                :: (α, ptyp_var_f α) :: wd)
          = msubst_compose ζ w1
            ++ (α0, msubst_ptyp ζ (ptyp_var_f α0))
            :: (β, msubst_ptyp ζ (ptyp_var_f β))
            :: (α, msubst_ptyp ζ (ptyp_var_f α))
            :: msubst_compose ζ wd)
    by (unfold msubst_compose; rewrite List.map_app; reflexivity).
  assert (Hsplitf : msubst_compose ζ (w1 ++ (α0, ptyp_var_f α0) :: wd)
          = msubst_compose ζ w1
            ++ (α0, msubst_ptyp ζ (ptyp_var_f α0)) :: msubst_compose ζ wd)
    by (unfold msubst_compose; rewrite List.map_app; reflexivity).
  rewrite Heqκ, Heqκf, Hsplitf.
  rewrite Heqw, Hsplitw in Hie.
  eapply a_inc_equiv_collapse_solve;
    [ exact HdeclsΞ | exact Hlen
    | unfold msubst_compose; rewrite List.map_length; exact Hlenw
    | exact Hie ].
Qed.

Notation "⇓ᵇ[ Θ ] Q" := (msubst_bskl (aenv_msubst Θ) Q)
  (at level 5, Θ at level 0) : type_scope.

Lemma msubst_bskl_ptyp_to_bskl_syn : forall κ A,
  msubst_bskl κ (ptyp_to_bskl_syn A) = ptyp_to_bskl_syn (msubst_ptyp κ A).
Proof.
  intros κ A. unfold ptyp_to_bskl_syn.
  induction A; simpl; try reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - rewrite IHA. reflexivity.
Qed.

Lemma consis_bskl_downarrow_mono_scoped : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall A D,
    R = ptyp_to_uskl_syn A -> mono_ptyp A ->
    ftvar_in_ptyp (⇓ᵗ[ Θ ] A) [<=] D ->
    ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] D.
Proof.
  intros Ψ Θ R Q Hc Hwf; induction Hc; intros A0 D HeqR HmA HAD;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
    simpl. clear; fsetdec.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
    inversion HeqR; subst. simpl.
    rewrite ftvar_in_bskl_syn. rewrite ftvar_ptyp_to_pskl.
    simpl in HAD. exact HAD.
  -
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR; try solve [ inversion HmA ].
    inversion HeqR; subst. inversion HmA; subst.
    simpl in HAD |- *. intros γ Hγ. apply union_1 in Hγ.
    destruct Hγ as [h | h].
    + refine (IHHc1 Hwf A1 D eq_refl _ _ γ h);
        [ assumption | clear - HAD; fsetdec ].
    + refine (IHHc2 Hwf A2 D eq_refl _ _ γ h);
        [ assumption | clear - HAD; fsetdec ].
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
    inversion HeqR; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    simpl in HAD.
    match goal with
    | Hb : binds ?g (abind_flex_mono_def τ) Θ |- _ =>
        assert (Hlk : msubst_lookup (aenv_msubst Θ) g = ⇓ᵗ[ Θ ] τ)
          by (apply aenv_msubst_lookup_def; assumption)
    end.
    rewrite Hlk in HAD.
    exact (IHHc Hwf τ D eq_refl Hmτ HAD).
  -
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk.
    pose proof (IHHc Hwf A0 D HeqR HmA HAD) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    rewrite ftvar_ptyp_to_bskl_syn in IH.
    rewrite ftvar_in_bskl_syn. rewrite ftvar_ptyp_to_pskl.
    exact IH.
Qed.

Lemma msubst_bskl_open_rec_ftv_lower : forall κ B B' k,
  ftvar_in_bskl (msubst_bskl κ B)
    [<=] ftvar_in_bskl (msubst_bskl κ (open_bskl_wrt_bskl_rec k B' B)).
Proof.
  intros κ B; induction B; intros B' k; simpl.
  -  clear; fsetdec.
  -
    destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; simpl; clear; fsetdec.
  -  clear; fsetdec.
  -
    specialize (IHB1 B' k). specialize (IHB2 B' k).
    clear - IHB1 IHB2; fsetdec.
  -  apply (IHB B' (S k)).
  -  apply (IHB B' (S k)).
  -  clear; fsetdec.
  -  apply (IHB B' k).
Qed.

Corollary msubst_bskl_open_ftv_lower : forall κ B B',
  ftvar_in_bskl (msubst_bskl κ B)
    [<=] ftvar_in_bskl (msubst_bskl κ (open_bskl_wrt_bskl B B')).
Proof. intros. apply msubst_bskl_open_rec_ftv_lower. Qed.

Lemma msubst_bskl_ftv_fresh : forall (Θ : aenv) κ Q β,
  (forall α, ftvar_in_ptyp (msubst_lookup κ α) [<=] add α (dom Θ)) ->
  β `notin` ftvar_in_bskl Q ->
  β `notin` dom Θ ->
  β `notin` ftvar_in_bskl (msubst_bskl κ Q).
Proof.
  intros Θ κ Q β Hsc; revert Q;
    induction Q; intros HβQ HβΘ; cbn in *; try solve [ clear; fsetdec ].
  -
    rewrite ftvar_in_bskl_syn. rewrite ftvar_ptyp_to_pskl.
    specialize (Hsc α). clear - Hsc HβQ HβΘ; fsetdec.
  -
    specialize (IHQ1 ltac:(clear - HβQ; solve_notin_auto) HβΘ).
    specialize (IHQ2 ltac:(clear - HβQ; solve_notin_auto) HβΘ).
    clear - IHQ1 IHQ2; fsetdec.
  - apply IHQ; assumption.
  - apply IHQ; assumption.
  - apply IHQ; assumption.
Qed.

Lemma consis_downarrow_mono : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall A, R = ptyp_to_uskl_syn A -> mono_ptyp A -> a_wf_ptyp Θ A ->
  {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] A)) ∼ (⇓ᵇ[ Θ ] Q) }}ad.
Proof.
  intros Ψ Θ R Q Hc Hwf; induction Hc; intros A0 HeqR HmA HwfA;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
    simpl. apply ad_pat_consis__unit; assumption.
  -
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR.
    inversion HeqR as [Heqv]. subst γ0.
    assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f α)))
      by (apply mono_downarrow; eassumption).
    assert (Hwfd : a_wf_ptyp Θ (⇓ᵗ[ Θ ] (ptyp_var_f α)))
      by (apply a_wf_ptyp_downarrow_mono; eassumption).
    assert (Hvis : forall γ, γ `in` ftvar_in_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f α)) ->
                     a_binds_tvar γ Θ)
      by (intros γ Hγ; eapply a_wf_ptyp_ftv_tvarish; eassumption).
    change (⇓ᵇ[ Θ ] (bskl_var_f α))
      with (ptyp_to_bskl_syn (⇓ᵗ[ Θ ] (ptyp_var_f α))).
    eapply ad_pat_consis_psi_cong;
      [ apply consis_mono_refl; eassumption | fsetdec ].
  -
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR; try solve [ inversion HmA ].
    inversion HeqR; subst. inversion HmA; subst. inversion HwfA; subst.
    simpl. apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ apply (IHHc1 Hwf A1 eq_refl ltac:(assumption) ltac:(assumption))
      | apply (IHHc2 Hwf A2 eq_refl ltac:(assumption) ltac:(assumption))
      | exact H ].
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -  destruct A0; cbn in HeqR; try discriminate HeqR.
  -  destruct A0; cbn in HeqR; try discriminate HeqR.
  -  destruct A0; cbn in HeqR; try discriminate HeqR.
  -  destruct A0; cbn in HeqR; try discriminate HeqR.
  -  destruct A0; cbn in HeqR; try discriminate HeqR.
  -  destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR.
    inversion HeqR as [Heqv]. subst γ0.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; eauto).
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    replace (⇓ᵗ[ Θ ] (ptyp_var_f α)) with (⇓ᵗ[ Θ ] τ)
      by (symmetry; exact Hlk).
    exact (IHHc Hwf τ eq_refl Hmτ Hwfτ).
  -
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk.
    pose proof (IHHc Hwf A0 HeqR HmA HwfA) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    exact IH.
Qed.

Lemma refine_pskl_downarrow_mono : forall Θ Δ P Q,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall A, P = ptyp_to_pskl A -> mono_ptyp A -> a_wf_ptyp Θ A ->
  {{ Θ ⨟ Δ ⊢ᵣₚ (⇓ˢ[ Θ ] P) ⊳ (⇓ˢ[ Θ ] Q) }}ad.
Proof.
  intros Θ Δ P Q Hr Hwf; induction Hr; intros A0 HeqP HmA HwfA.
  -
    destruct A0; cbn in HeqP; try discriminate HeqP.
    simpl. apply ad_refine_pskl__unit.
  -
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqP; try discriminate HeqP.
    inversion HeqP as [Heqv]. subst γ0.
    assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] (ptyp_var_f α)))
      by (apply mono_downarrow; eassumption).
    assert (Hwfd : a_wf_ptyp Θ (⇓ᵗ[ Θ ] (ptyp_var_f α)))
      by (apply a_wf_ptyp_downarrow_mono; eassumption).
    change (⇓ˢ[ Θ ] (pskl_var_f α))
      with (ptyp_to_pskl (⇓ᵗ[ Θ ] (ptyp_var_f α))).
    eapply ad_refine_pskl_mono_refl; eassumption.
  -
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqP; try discriminate HeqP; try solve [ inversion HmA ].
    inversion HeqP; subst. inversion HmA; subst. inversion HwfA; subst.
    simpl. apply ad_refine_pskl__arrow;
      [ apply (IHHr1 Hwf A1 eq_refl ltac:(assumption) ltac:(assumption))
      | apply (IHHr2 Hwf A2 eq_refl ltac:(assumption) ltac:(assumption)) ].
  -
    destruct A0; cbn in HeqP; try discriminate HeqP; inversion HmA.
  -
    destruct A0; cbn in HeqP; try discriminate HeqP.
  -
    destruct A0; cbn in HeqP; try discriminate HeqP.
  -
    destruct A0; cbn in HeqP; try discriminate HeqP.
  -
    destruct A0; cbn in HeqP; try discriminate HeqP.
  -
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqP; try discriminate HeqP.
    inversion HeqP as [Heqv]. subst γ0.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; eauto).
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    change (⇓ˢ[ Θ ] (pskl_var_f α))
      with (ptyp_to_pskl (msubst_lookup (aenv_msubst Θ) α)).
    rewrite Hlk. rewrite <- msubst_pskl_embed_ptyp.
    exact (IHHr Hwf τ eq_refl Hmτ Hwfτ).
  -
    simpl.
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    rewrite Hlk. rewrite <- msubst_pskl_embed_ptyp.
    exact (IHHr Hwf A0 HeqP HmA HwfA).
Qed.

Lemma msubst_bskl_open_rec_lc : forall κ,
  msubst_lc κ ->
  forall B B' k,
  msubst_bskl κ (open_bskl_wrt_bskl_rec k B' B)
  = open_bskl_wrt_bskl_rec k (msubst_bskl κ B') (msubst_bskl κ B).
Proof.
  intros κ Hlc B; induction B; intros B' k; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - symmetry.
    apply open_bskl_wrt_bskl_rec_degree_bskl_wrt_bskl.
    apply degree_bskl_wrt_bskl_O.
    apply degree_bskl_wrt_bskl_of_lc_bskl.
    apply lc_pskl_to_bskl_syn. apply ptyp_to_pskl_lc. apply Hlc.
Qed.

Lemma msubst_bskl_open_lc : forall κ B (α : atom),
  msubst_lc κ ->
  α `notin` dom κ ->
  msubst_bskl κ (open_bskl_wrt_bskl B (bskl_var_f α))
  = open_bskl_wrt_bskl (msubst_bskl κ B) (bskl_var_f α).
Proof.
  intros κ B α Hlc Hα. unfold open_bskl_wrt_bskl.
  rewrite (msubst_bskl_open_rec_lc Hlc B (bskl_var_f α) 0).
  cbn [msubst_bskl]. rewrite msubst_lookup_notin by exact Hα.
  reflexivity.
Qed.

Lemma is_sskl_msubst_bskl : forall κ Q,
  msubst_lc κ ->
  (forall α, mono_ptyp (msubst_lookup κ α)) ->
  is_sskl Q -> is_sskl (msubst_bskl κ Q).
Proof.
  intros κ Q Hlc Hmono H; induction H; simpl.
  - apply is_sskl__unit.
  - change (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))
      with (ptyp_to_bskl_syn (msubst_lookup κ α)).
    apply mono_ptyp_to_bskl_syn_is_sskl. apply Hmono.
  - apply is_sskl__arrow; assumption.
  - apply is_sskl__all with (L := L `union` dom κ). intros α Hα.
    assert (Heq : msubst_bskl κ (open_bskl_wrt_bskl A (bskl_var_f α))
                  = open_bskl_wrt_bskl (msubst_bskl κ A) (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ exact Hlc | clear - Hα; fsetdec ]).
    rewrite <- Heq. apply H0. clear - Hα; fsetdec.
  - apply is_sskl__ghost.
  - apply is_sskl__univ_ghost; assumption.
Qed.

Lemma msubst_bskl_pskl_to_bskl_inh : forall κ P,
  (forall α, mono_ptyp (msubst_lookup κ α)) ->
  msubst_bskl κ (pskl_to_bskl_inh P) = pskl_to_bskl_inh (msubst_pskl κ P).
Proof.
  intros κ P Hmono; induction P; simpl; try reflexivity.
  - symmetry. apply ptyp_to_bskl_inh_syn_eq. apply Hmono.
  - rewrite IHP1, IHP2. reflexivity.
  - rewrite IHP. reflexivity.
  - rewrite IHP. reflexivity.
Qed.

Lemma msubst_pskl_lc_of_msubst_lc : forall κ P,
  msubst_lc κ -> lc_pskl P -> lc_pskl (msubst_pskl κ P).
Proof.
  intros κ P Hlc H; induction H; simpl; try solve [ constructor; auto ].
  - apply ptyp_to_pskl_lc. apply Hlc.
  - pick fresh α for (dom κ).
    apply lc_pskl_all_syn_exists with (α1 := α).
    match goal with
    | |- lc_pskl (open_pskl_wrt_pskl (msubst_pskl _ ?B) _) =>
        assert (Heq : msubst_pskl κ (open_pskl_wrt_pskl B (pskl_var_f α))
                      = open_pskl_wrt_pskl (msubst_pskl κ B) (pskl_var_f α))
          by (apply msubst_pskl_open_lc; [ exact Hlc | clear - Fr; solve_notin_auto ])
    end.
    rewrite <- Heq. apply H0.
Qed.

Lemma guarded_pskl_msubst_mono : forall κ P,
  msubst_lc κ ->
  (forall α, mono_ptyp (msubst_lookup κ α)) ->
  guarded_pskl P -> guarded_pskl (msubst_pskl κ P).
Proof.
  intros κ P Hlc Hmono Hg; inversion Hg; subst; simpl.
  - apply guarded_pskl__unit.
  - apply mono_ptyp_to_pskl_guarded. apply Hmono.
  - apply guarded_pskl__arrow;
      apply msubst_pskl_lc_of_msubst_lc; assumption.
Qed.

Lemma msubst_bskl_lc_of_msubst_lc : forall κ Q,
  msubst_lc κ -> lc_bskl Q -> lc_bskl (msubst_bskl κ Q).
Proof.
  intros κ Q Hlc H; induction H; simpl; try solve [ constructor; auto ].
  - apply lc_pskl_to_bskl_syn. apply ptyp_to_pskl_lc. apply Hlc.
  - pick fresh α for (dom κ).
    apply lc_bskl_all_syn_exists with (α1 := α).
    match goal with
    | |- lc_bskl (open_bskl_wrt_bskl (msubst_bskl _ ?B) _) =>
        assert (Heq : msubst_bskl κ (open_bskl_wrt_bskl B (bskl_var_f α))
                      = open_bskl_wrt_bskl (msubst_bskl κ B) (bskl_var_f α))
          by (apply msubst_bskl_open_lc; [ exact Hlc | clear - Fr; solve_notin_auto ])
    end.
    rewrite <- Heq. apply H0.
  - pick fresh α for (dom κ).
    apply lc_bskl_all_inh_exists with (α1 := α).
    match goal with
    | |- lc_bskl (open_bskl_wrt_bskl (msubst_bskl _ ?B) _) =>
        assert (Heq : msubst_bskl κ (open_bskl_wrt_bskl B (bskl_var_f α))
                      = open_bskl_wrt_bskl (msubst_bskl κ B) (bskl_var_f α))
          by (apply msubst_bskl_open_lc; [ exact Hlc | clear - Fr; solve_notin_auto ])
    end.
    rewrite <- Heq. apply H0.
Qed.

Lemma guarded_bskl_msubst_mono : forall κ Q,
  msubst_lc κ ->
  (forall α, mono_ptyp (msubst_lookup κ α)) ->
  guarded_bskl Q -> guarded_bskl (msubst_bskl κ Q).
Proof.
  intros κ Q Hlc Hmono Hg; inversion Hg; subst; simpl.
  - apply guarded_bskl__unit.
  - change (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))
      with (ptyp_to_bskl_syn (msubst_lookup κ α)).
    pose proof (Hmono α) as Hm. destruct Hm; simpl;
      [ apply guarded_bskl__unit | apply guarded_bskl__var
      | apply guarded_bskl__arrow;
        apply lc_pskl_to_bskl_syn; apply ptyp_to_pskl_lc;
        apply mono_ptyp_lc; assumption ].
  - apply guarded_bskl__arrow;
      apply msubst_bskl_lc_of_msubst_lc; assumption.
Qed.

Lemma ptyp_to_uskl_syn_arrow : forall A1 A2,
  ptyp_to_uskl_syn (ptyp_arrow A1 A2)
  = uskl_arrow (ptyp_to_uskl_syn A1) (ptyp_to_uskl_syn A2).
Proof. reflexivity. Qed.

Lemma sub_gv_downarrow_mono : forall n NM M Ψ Θ R Q,
  ad_pat_sub_fuel n NM M Ψ Θ R Q ->
  {{ ⊢ Θ }}a ->
  forall A, R = ptyp_to_uskl_syn A -> mono_ptyp A -> a_wf_ptyp Θ A ->
  ad_pat_sub_fuel n NM M Ψ Θ (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] A)) (⇓ᵇ[ Θ ] Q).
Proof.
  intros n NM M Ψ Θ R Q H; induction H; destr_join;
    intros Hwf A0 HeqR HmA HwfA.
  -
    assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] A0))
      by (apply mono_downarrow; eassumption).
    apply ad_pat_sub_fuel__infer;
      [ assumption
      |
      | apply is_sskl_msubst_bskl;
          [ apply aenv_msubst_lc; exact Hwf
          | intros; apply aenv_msubst_image_mono; exact Hwf
          | assumption ]
      ].
    split.
    + eapply consis_downarrow_mono;
        [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HwfA ].
    + rewrite uskl_to_pskl_ptyp_to_uskl_syn.
      rewrite bskl_to_pskl_msubst_bskl.
      rewrite <- msubst_pskl_embed_ptyp.
      eapply refine_pskl_downarrow_mono;
        [ | exact Hwf | | exact HmA | exact HwfA ];
        [ rewrite <- uskl_to_pskl_ptyp_to_uskl_syn; rewrite <- HeqR;
          eassumption
        | reflexivity ].
  -
    assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] A0))
      by (apply mono_downarrow; eassumption).
    rewrite (msubst_bskl_pskl_to_bskl_inh (aenv_msubst Θ) B
               ltac:(intros; apply aenv_msubst_image_mono; exact Hwf)).
    apply ad_pat_sub_fuel__check;
      [ apply mono_ptyp_to_uskl_syn_guarded; exact Hmd
      | apply guarded_pskl_msubst_mono;
          [ apply aenv_msubst_lc; exact Hwf
          | intros; apply aenv_msubst_image_mono; exact Hwf
          | assumption ]
      |].
    apply ad_consis_join_inh_intro.
    + rewrite <- (msubst_bskl_pskl_to_bskl_inh (aenv_msubst Θ) B
                    ltac:(intros; apply aenv_msubst_image_mono; exact Hwf)).
      eapply consis_downarrow_mono;
        [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HwfA ].
    + rewrite uskl_to_pskl_ptyp_to_uskl_syn.
      rewrite <- msubst_pskl_embed_ptyp.
      eapply refine_pskl_downarrow_mono;
        [ | exact Hwf | | exact HmA | exact HwfA ];
        [ rewrite <- uskl_to_pskl_ptyp_to_uskl_syn; rewrite <- HeqR;
          eassumption
        | reflexivity ].
  -
    simpl.
    apply ad_pat_sub_fuel__forall_r
      with (L := L `union` dom Θ `union` dom (aenv_msubst Θ)).
    intros α Hα.
    assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]).
    assert (HwfA' : a_wf_ptyp ((α ~ abind_tvar) ++ Θ) A0)
      by (eapply a_wf_ptyp_weaken;
          [ intros x b Hb; apply binds_cons_3; exact Hb | exact HwfA ]).
    pose proof (H0 α ltac:(clear - Hα; solve_notin_auto) Hwf' A0 HeqR HmA HwfA') as IH.
    rewrite aenv_msubst_tvar in IH.
    assert (Heq : msubst_bskl (aenv_msubst Θ)
                    (open_bskl_wrt_bskl B (bskl_var_f α))
                  = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) B)
                      (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Hα; fsetdec ]).
    rewrite Heq in IH. exact IH.
  -
    assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] A0))
      by (apply mono_downarrow; eassumption).
    simpl. apply ad_pat_sub_fuel__univ_ghost_r;
      [ assumption
      | apply mono_ptyp_to_uskl_syn_guarded; exact Hmd
      | apply guarded_bskl_msubst_mono;
          [ apply aenv_msubst_lc; exact Hwf
          | intros; apply aenv_msubst_image_mono; exact Hwf
          | assumption ]
      | apply is_sskl_msubst_bskl;
          [ apply aenv_msubst_lc; exact Hwf
          | intros; apply aenv_msubst_image_mono; exact Hwf
          | assumption ]
      | ].
    split.
    + eapply consis_downarrow_mono;
        [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HwfA ].
    + rewrite uskl_to_pskl_ptyp_to_uskl_syn.
      rewrite bskl_to_pskl_msubst_bskl.
      rewrite <- msubst_pskl_embed_ptyp.
      eapply refine_pskl_downarrow_mono;
        [ | exact Hwf | | exact HmA | exact HwfA ];
        [ rewrite <- uskl_to_pskl_ptyp_to_uskl_syn; rewrite <- HeqR;
          eassumption
        | reflexivity ].
  -
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      try solve [ cbn in HeqR; discriminate HeqR ].
    assert (HR : uskl_arrow R1 R2
                 = uskl_arrow (ptyp_to_uskl_syn A1) (ptyp_to_uskl_syn A2))
      by (rewrite HeqR; reflexivity).
    injection HR as HR1 HR2. subst R1. subst R2.
    inversion HmA; subst. inversion HwfA; subst.
    replace (⇓ᵗ[ Θ ] (ptyp_arrow A1 A2))
      with (ptyp_arrow (⇓ᵗ[ Θ ] A1) (⇓ᵗ[ Θ ] A2)) by reflexivity.
    rewrite ptyp_to_uskl_syn_arrow.
    change (⇓ᵇ[ Θ ] (bskl_arrow Q1 Q2))
      with (bskl_arrow (⇓ᵇ[ Θ ] Q1) (⇓ᵇ[ Θ ] Q2)).
    apply ad_pat_sub_fuel__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [| | assumption ].
    split.
    + eapply consis_downarrow_mono;
        [ eassumption | exact Hwf | reflexivity | assumption | assumption ].
    + rewrite uskl_to_pskl_ptyp_to_uskl_syn.
      rewrite bskl_to_pskl_msubst_bskl.
      rewrite <- msubst_pskl_embed_ptyp.
      eapply refine_pskl_downarrow_mono;
        [ | exact Hwf | reflexivity | assumption | assumption ].
      rewrite <- uskl_to_pskl_ptyp_to_uskl_syn. eassumption.
    + apply (IHad_pat_sub_fuel Hwf A2 eq_refl ltac:(assumption)
               ltac:(assumption)).
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -  destruct A0; cbn in HeqR; try discriminate HeqR.
  -  destruct A0; cbn in HeqR; try discriminate HeqR.
  -  destruct A0; cbn in HeqR; try discriminate HeqR.
  -  destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR.
    inversion HeqR as [Heqv]. subst γ0.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; eauto).
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    replace (⇓ᵗ[ Θ ] (ptyp_var_f α)) with (⇓ᵗ[ Θ ] τ)
      by (symmetry; exact Hlk).
    exact (IHad_pat_sub_fuel Hwf τ eq_refl Hmτ Hwfτ).
Qed.

Lemma sub_gv_bskl_downarrow_mono_scoped : forall n NM M Ψ Θ R Q,
  ad_pat_sub_fuel n NM M Ψ Θ R Q ->
  {{ ⊢ Θ }}a ->
  forall A D,
    R = ptyp_to_uskl_syn A -> mono_ptyp A ->
    ftvar_in_ptyp (⇓ᵗ[ Θ ] A) [<=] D ->
    ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] D.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; destr_join;
    intros Hwf A0 D HeqR HmA HAD.
  -
    eapply consis_bskl_downarrow_mono_scoped;
      [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HAD ].
  -
    eapply consis_bskl_downarrow_mono_scoped;
      [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HAD ].
  -
    simpl.
    pick fresh α for (L `union` D `union` dom Θ `union` ftvar_in_bskl B
                      `union` ftvar_in_aenv Θ).
    assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Fr; solve_notin_auto | exact Hwf ]).
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto) Hwf' A0 (add α D) HeqR HmA
                  ltac:(rewrite aenv_msubst_tvar;
                        clear - HAD; solve_notin_auto)) as IH.
    rewrite aenv_msubst_tvar in IH.
    pose proof (msubst_bskl_open_ftv_lower (aenv_msubst Θ) B (bskl_var_f α))
      as Hlow.
    assert (Hfr : α `notin` ftvar_in_bskl (msubst_bskl (aenv_msubst Θ) B)).
    { eapply msubst_bskl_ftv_fresh with (Θ := Θ);
        [ apply aenv_msubst_image_ftv; exact Hwf
        | clear - Fr; solve_notin_auto | clear - Fr; solve_notin_auto ]. }
    clear - IH Hlow Hfr. fsetdec.
  -
    simpl.
    eapply consis_bskl_downarrow_mono_scoped;
      [ eassumption | exact Hwf | exact HeqR | exact HmA | exact HAD ].
  -
    destruct A0 as [ | nb | γ0 | A1 A2 | A0' ];
      cbn in HeqR; try discriminate HeqR; try solve [ inversion HmA ].
    inversion HeqR; subst. inversion HmA; subst.
    simpl in HAD |- *. intros γ Hγ. apply union_1 in Hγ.
    destruct Hγ as [h | h].
    + assert (h1 : ftvar_in_bskl (⇓ᵇ[ Θ ] Q1) [<=] D).
      { eapply consis_bskl_downarrow_mono_scoped with (A := A1);
          [ eassumption | exact Hwf | reflexivity | assumption
          | clear - HAD; fsetdec ]. }
      clear - h1 h; fsetdec.
    + refine (IHad_pat_sub_fuel Hwf A2 D eq_refl _ _ γ h);
        [ assumption | clear - HAD; fsetdec ].
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR; inversion HmA.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
  -
    destruct A0; cbn in HeqR; try discriminate HeqR.
    inversion HeqR; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    simpl in HAD.
    match goal with
    | Hb : binds ?g (abind_flex_mono_def τ) Θ |- _ =>
        assert (Hlk : msubst_lookup (aenv_msubst Θ) g = ⇓ᵗ[ Θ ] τ)
          by (apply aenv_msubst_lookup_def; assumption)
    end.
    rewrite Hlk in HAD.
    exact (IHad_pat_sub_fuel Hwf τ D eq_refl Hmτ HAD).
Qed.

Lemma ad_refine_pskl_strengthen_gen : forall Θ Δ P Q,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad ->
  forall Θ', uniq Θ -> {{ ⊢ Θ' }}a ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall x τ, x `in` Δ -> ~ binds x (abind_flex_mono_def τ) Θ) ->
  (forall γ, γ `in` ftvar_in_pskl P -> γ `in` Δ \/ γ `in` dom Θ') ->
  (forall γ, γ `in` ftvar_in_pskl Q -> γ `in` Δ \/ γ `in` dom Θ') ->
  {{ Θ' ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad.
Proof.
  intros Θ Δ P Q H; induction H;
    intros Θ' Hu Hwf' Hsub Hflex HscP HscQ; simpl in *.
  - apply ad_refine_pskl__unit.
  - apply ad_refine_pskl__var.
  -
    apply ad_refine_pskl__arrow;
      [ apply IHad_refine_pskl1 | apply IHad_refine_pskl2 ];
      auto; intros γ Hγ;
      solve [ apply HscP; clear - Hγ; fsetdec
            | apply HscQ; clear - Hγ; fsetdec ].
  -
    apply ad_refine_pskl__all
      with (L := L `union` dom Θ `union` dom Θ' `union` Δ).
    intros α Hα.
    apply H0; [ clear - Hα; fsetdec | | | | | | ].
    + simpl_env. apply uniq_cons_3; [ exact Hu | clear - Hα; fsetdec ].
    + apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ].
    + intros x b0 Hb0. analyze_binds Hb0.
    + intros x τ Hx Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | ].
      destruct (x == α) as [-> | Hne].
      * apply binds_In in Hb'. clear - Hb' Hα. fsetdec.
      * apply (Hflex x τ); [ clear - Hx Hne; fsetdec | exact Hb' ].
    + intros γ Hγ.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α))
        as Hup. simpl in Hup.
      destruct (γ == α) as [-> | Hne]; [ left; clear; fsetdec | ].
      destruct (HscP γ ltac:(clear - Hγ Hup Hne; solve_notin_auto)) as [h | h];
        [ left; clear - h; fsetdec | right; simpl_env; clear - h; fsetdec ].
    + intros γ Hγ.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f α))
        as Hup. simpl in Hup.
      destruct (γ == α) as [-> | Hne]; [ left; clear; fsetdec | ].
      destruct (HscQ γ ltac:(clear - Hγ Hup Hne; solve_notin_auto)) as [h | h];
        [ left; clear - h; fsetdec | right; simpl_env; clear - h; fsetdec ].
  -
    apply ad_refine_pskl__ghost. exact H.
  -
    apply ad_refine_pskl__univ_ghost_remove. apply IHad_refine_pskl; auto.
  -
    apply ad_refine_pskl__univ_ghost_fill
      with (L := L `union` dom Θ `union` dom Θ' `union` Δ).
    intros α Hα.
    apply H0; [ clear - Hα; fsetdec | | | | | | ].
    + simpl_env. apply uniq_cons_3; [ exact Hu | clear - Hα; fsetdec ].
    + apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ].
    + intros x b0 Hb0. analyze_binds Hb0.
    + intros x τ Hx Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | ].
      exact (Hflex x τ Hx Hb').
    + intros γ Hγ.
      destruct (HscP γ ltac:(clear - Hγ; solve_notin_auto)) as [h | h];
        [ left; exact h | right; simpl_env; clear - h; fsetdec ].
    + intros γ Hγ.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f α))
        as Hup. simpl in Hup.
      destruct (γ == α) as [-> | Hne];
        [ right; simpl_env; clear; fsetdec | ].
      destruct (HscQ γ ltac:(clear - Hγ Hup Hne; solve_notin_auto)) as [h | h];
        [ left; exact h | right; simpl_env; clear - h; fsetdec ].
  -
    apply ad_refine_pskl__univ_ghost_keep.
    apply IHad_refine_pskl; auto.
  -
    assert (hd : α `in` dom Θ').
    { destruct (HscP α ltac:(clear; solve_notin_auto)) as [h | h];
        [ exfalso; exact (Hflex α τ h H) | exact h ]. }
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (eapply binds_strengthen; eassumption).
    eapply ad_refine_pskl__flex_l; [ exact Hb' | ].
    apply IHad_refine_pskl; auto.
    intros γ Hγ. right.
    assert (hw : a_wf_ptyp Θ' τ)
      by (eapply a_wf_aenv_binds_def_wf; eassumption).
    apply a_wf_ptyp_ftv_dom in hw.
    rewrite ftvar_ptyp_to_pskl in Hγ. clear - hw Hγ. fsetdec.
  -
    assert (hd : α `in` dom Θ').
    { destruct (HscQ α ltac:(clear; solve_notin_auto)) as [h | h];
        [ exfalso; exact (Hflex α τ h H) | exact h ]. }
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (eapply binds_strengthen; eassumption).
    eapply ad_refine_pskl__flex_r; [ exact Hb' | ].
    apply IHad_refine_pskl; auto.
    intros γ Hγ. right.
    assert (hw : a_wf_ptyp Θ' τ)
      by (eapply a_wf_aenv_binds_def_wf; eassumption).
    apply a_wf_ptyp_ftv_dom in hw.
    rewrite ftvar_ptyp_to_pskl in Hγ. clear - hw Hγ. fsetdec.
Qed.

Lemma ad_refine_pskl_strengthen : forall Θ Δ P Q,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad ->
  forall Θ', uniq Θ -> {{ ⊢ Θ' }}a ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall x, x `in` Δ -> x `notin` dom Θ) ->
  (forall γ, γ `in` ftvar_in_pskl P -> γ `in` Δ \/ γ `in` dom Θ') ->
  (forall γ, γ `in` ftvar_in_pskl Q -> γ `in` Δ \/ γ `in` dom Θ') ->
  {{ Θ' ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad.
Proof.
  intros Θ Δ P Q H Θ' Hu Hwf' Hsub Hdisj HscP HscQ.
  eapply ad_refine_pskl_strengthen_gen;
    [ exact H | exact Hu | exact Hwf' | exact Hsub | | exact HscP | exact HscQ ].
  intros x τ Hx Hb. apply (Hdisj x Hx). eapply binds_In; exact Hb.
Qed.

Lemma ad_pat_sub_fuel_mono_strengthen : forall n NM M Ψ Θ R Q,
  ad_pat_sub_fuel n NM M Ψ Θ R Q ->
  forall τ, R = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  forall Θ', uniq Θ -> {{ ⊢ Θ' }}a ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall γ, γ `in` ftvar_in_ptyp τ -> γ `in` dom Θ') ->
  (forall γ, γ `in` ftvar_in_bskl Q -> γ `in` dom Θ') ->
  ad_pat_sub_fuel n NM M Ψ Θ' R Q.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; destr_join;
    intros τ0 HeqR Hm Θ' Hu Hwf' Hsub HscR HscQ;
    pose proof (ftvar_ptyp_to_uskl_syn τ0) as HftvR;
    rewrite <- HeqR in HftvR.
  -
    apply ad_pat_sub_fuel__infer; try assumption.
    split.
    + eapply ad_pat_consis_strengthen; try eassumption;
        intros γ Hγ;
        solve [ apply HscR; clear - Hγ HftvR; fsetdec
              | apply HscQ; clear - Hγ; fsetdec ].
    + eapply ad_refine_pskl_strengthen;
        [ eassumption | exact Hu | exact Hwf' | exact Hsub
        | intros x Hx; exfalso; clear - Hx; fsetdec | | ];
        intros γ Hγ; right;
        solve [ apply HscR; rewrite ftvar_in_pskl_uskl_to_pskl in Hγ;
                clear - Hγ HftvR; fsetdec
              | apply HscQ; rewrite ftvar_bskl_to_pskl in Hγ;
                clear - Hγ; fsetdec ].
  -
    apply ad_pat_sub_fuel__check; try assumption.
    apply ad_consis_join_inh_intro.
    + eapply ad_pat_consis_strengthen; try eassumption;
        intros γ Hγ;
        solve [ apply HscR; clear - Hγ HftvR; fsetdec
              | apply HscQ; rewrite ftvar_in_bskl_inh; clear - Hγ; fsetdec ].
    + eapply ad_refine_pskl_strengthen;
        [ eassumption | exact Hu | exact Hwf' | exact Hsub
        | intros x Hx; exfalso; clear - Hx; fsetdec | | ];
        intros γ Hγ; right;
        solve [ apply HscR; rewrite ftvar_in_pskl_uskl_to_pskl in Hγ;
                clear - Hγ HftvR; fsetdec
              | apply HscQ; rewrite ftvar_in_bskl_inh; clear - Hγ; fsetdec ].
  -
    apply ad_pat_sub_fuel__forall_r with (L := L `union` dom Θ `union` dom Θ').
    intros α Hα.
    eapply H0;
      [ clear - Hα; fsetdec | exact HeqR | exact Hm
      | simpl_env; apply uniq_cons_3; [ exact Hu | clear - Hα; fsetdec ]
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]
      | intros x b0 Hb0; analyze_binds Hb0
      | intros γ Hγ; simpl_env; assert (h := HscR γ Hγ); clear - h; fsetdec
      | ].
    intros γ Hγ. simpl_env.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper B (bskl_var_f α))
      as Hup. simpl in Hup.
    destruct (γ == α) as [-> | Hne]; [ clear; fsetdec | ].
    assert (h : γ `in` dom Θ')
      by (apply HscQ; simpl; clear - Hγ Hup Hne; fsetdec).
    clear - h; fsetdec.
  -
    apply ad_pat_sub_fuel__univ_ghost_r; try assumption.
    split.
    + eapply ad_pat_consis_strengthen; try eassumption;
        intros γ Hγ;
        solve [ apply HscR; clear - Hγ HftvR; fsetdec
              | apply HscQ; simpl; clear - Hγ; fsetdec ].
    + eapply ad_refine_pskl_strengthen;
        [ eassumption | exact Hu | exact Hwf' | exact Hsub
        | intros x Hx; exfalso; clear - Hx; fsetdec | | ];
        intros γ Hγ; right;
        solve [ apply HscR; rewrite ftvar_in_pskl_uskl_to_pskl in Hγ;
                clear - Hγ HftvR; fsetdec
              | apply HscQ; simpl;
                rewrite ftvar_bskl_to_pskl in Hγ;
                clear - Hγ; fsetdec ].
  -
    destruct τ0; cbn in HeqR; try discriminate HeqR.
    inversion HeqR; subst. inversion Hm; subst.
    eapply ad_pat_sub_fuel__arrow; [ | | eassumption ].
    + split.
      * eapply ad_pat_consis_strengthen; try eassumption.
        -- intros γ Hγ. apply HscR. simpl. simpl in HftvR.
           clear - Hγ HftvR. fsetdec.
        -- intros γ Hγ. apply HscQ. simpl. clear - Hγ. fsetdec.
      * eapply ad_refine_pskl_strengthen;
          [ eassumption | exact Hu | exact Hwf' | exact Hsub
          | intros x Hx; exfalso; clear - Hx; fsetdec | | ].
        -- intros γ Hγ. right. apply HscR. simpl.
           rewrite ftvar_in_pskl_uskl_to_pskl in Hγ.
           simpl in HftvR. clear - Hγ HftvR. fsetdec.
        -- intros γ Hγ. right. apply HscQ. simpl.
           rewrite ftvar_bskl_to_pskl in Hγ. clear - Hγ. fsetdec.
    + eapply IHad_pat_sub_fuel;
        [ reflexivity | assumption | exact Hu | exact Hwf' | exact Hsub | | ].
      * intros γ Hγ. apply HscR. simpl. simpl in HftvR.
        clear - Hγ HftvR. fsetdec.
      * intros γ Hγ. apply HscQ. simpl. clear - Hγ. fsetdec.
  -
    destruct τ0; cbn in HeqR; discriminate HeqR.
  -
    destruct τ0; cbn in HeqR; try discriminate HeqR. inversion Hm.
  -
    destruct τ0; cbn in HeqR; discriminate HeqR.
  -
    destruct τ0; cbn in HeqR; discriminate HeqR.
  -
    destruct τ0; cbn in HeqR; discriminate HeqR.
  -
    destruct τ0; cbn in HeqR; discriminate HeqR.
  -
    assert (Hτ0 : τ0 = ptyp_var_f α)
      by (destruct τ0; cbn in HeqR; try discriminate HeqR;
          injection HeqR; intros ->; reflexivity).
    subst τ0.
    assert (HαΘ' : α `in` dom Θ')
      by (apply HscR; simpl; clear; fsetdec).
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (eapply binds_strengthen; [ eassumption | exact Hu | exact Hsub
                                   | exact HαΘ' ]).
    eapply ad_pat_sub_fuel__flex_mono; [ exact Hb' | ].
    eapply IHad_pat_sub_fuel;
      [ reflexivity
      | eapply a_wf_aenv_binds_def_mono; eassumption
      | exact Hu | exact Hwf' | exact Hsub | | exact HscQ ].
    intros γ Hγ.
    assert (hw : a_wf_ptyp Θ' τ)
      by (eapply a_wf_aenv_binds_def_wf; eassumption).
    apply a_wf_ptyp_ftv_dom in hw. clear - hw Hγ. fsetdec.
Qed.

Lemma ad_refine_syn_strengthen_gen : forall Θ Δ Q P,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad ->
  forall Θ', uniq Θ -> {{ ⊢ Θ' }}a ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall x τ, x `in` Δ -> ~ binds x (abind_flex_mono_def τ) Θ) ->
  (forall γ, γ `in` ftvar_in_bskl Q -> γ `in` Δ \/ γ `in` dom Θ') ->
  (forall γ, γ `in` ftvar_in_bskl P -> γ `in` Δ \/ γ `in` dom Θ') ->
  {{ Θ' ⨟ Δ ⊢ᵣ Q ⊳ P }}ad.
Proof.
  intros Θ Δ Q P H; induction H;
    intros Θ' Hu Hwf' Hsub Hflex HscQ HscP; simpl in *.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
  - apply ad_refine_syn_arrow_intro;
      [ apply IHad_refine_syn1 | apply IHad_refine_syn2 ];
      auto; intros γ Hγ;
      solve [ apply HscQ; clear - Hγ; fsetdec
            | apply HscP; clear - Hγ; fsetdec ].
  -
    apply ad_refine_syn_all_intro
      with (L := L `union` dom Θ `union` dom Θ' `union` Δ).
    intros α Hα.
    apply H1; [ clear - Hα; fsetdec | | | | | | ].
    + simpl_env. apply uniq_cons_3; [ exact Hu | clear - Hα; fsetdec ].
    + apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ].
    + intros x b0 Hb0. analyze_binds Hb0.
    + intros x τ Hx Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | ].
      destruct (x == α) as [-> | Hne].
      * apply binds_In in Hb'. clear - Hb' Hα. fsetdec.
      * apply (Hflex x τ); [ clear - Hx Hne; fsetdec | exact Hb' ].
    + intros γ Hγ.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f α))
        as Hup. simpl in Hup.
      destruct (γ == α) as [-> | Hne]; [ left; clear; fsetdec | ].
      destruct (HscQ γ ltac:(clear - Hγ Hup Hne; solve_notin_auto)) as [h | h];
        [ left; clear - h; fsetdec | right; simpl_env; clear - h; fsetdec ].
    + intros γ Hγ.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f α))
        as Hup. simpl in Hup.
      destruct (γ == α) as [-> | Hne]; [ left; clear; fsetdec | ].
      destruct (HscP γ ltac:(clear - Hγ Hup Hne; solve_notin_auto)) as [h | h];
        [ left; clear - h; fsetdec | right; simpl_env; clear - h; fsetdec ].
  -
    apply ad_refine_syn__ghost; assumption.
  - apply ad_refine_syn_univ_ghost_remove_intro. apply IHad_refine_syn; auto.
  -
    apply ad_refine_syn_univ_ghost_fill_intro
      with (L := L `union` dom Θ `union` dom Θ' `union` Δ).
    intros α Hα.
    apply H1; [ clear - Hα; fsetdec | | | | | | ].
    + simpl_env. apply uniq_cons_3; [ exact Hu | clear - Hα; fsetdec ].
    + apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ].
    + intros x b0 Hb0. analyze_binds Hb0.
    + intros x τ Hx Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | ].
      exact (Hflex x τ Hx Hb').
    + intros γ Hγ.
      destruct (HscQ γ ltac:(clear - Hγ; solve_notin_auto)) as [h | h];
        [ left; exact h | right; simpl_env; clear - h; fsetdec ].
    + intros γ Hγ.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f α))
        as Hup. simpl in Hup.
      destruct (γ == α) as [-> | Hne];
        [ right; simpl_env; clear; fsetdec | ].
      destruct (HscP γ ltac:(clear - Hγ Hup Hne; solve_notin_auto)) as [h | h];
        [ left; exact h | right; simpl_env; clear - h; fsetdec ].
  - apply ad_refine_syn_univ_ghost_keep_intro.
    apply IHad_refine_syn; auto.
  -
    assert (hd : α `in` dom Θ').
    { destruct (HscQ α ltac:(clear; solve_notin_auto)) as [h | h];
        [ exfalso; exact (Hflex α τ h H) | exact h ]. }
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (eapply binds_strengthen; eassumption).
    eapply ad_refine_syn__flex_l; [ exact Hb' | ].
    apply IHad_refine_syn; auto.
    intros γ Hγ. right.
    assert (hw : a_wf_ptyp Θ' τ)
      by (eapply a_wf_aenv_binds_def_wf; eassumption).
    apply a_wf_ptyp_ftv_dom in hw.
    unfold ptyp_to_bskl_syn in Hγ. rewrite ftvar_in_bskl_syn in Hγ.
    rewrite ftvar_ptyp_to_pskl in Hγ. clear - hw Hγ. fsetdec.
  -
    assert (hd : α `in` dom Θ').
    { destruct (HscP α ltac:(clear; solve_notin_auto)) as [h | h];
        [ exfalso; exact (Hflex α τ h H) | exact h ]. }
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ')
      by (eapply binds_strengthen; eassumption).
    eapply ad_refine_syn__flex_r; [ exact Hb' | ].
    apply IHad_refine_syn; auto.
    intros γ Hγ. right.
    assert (hw : a_wf_ptyp Θ' τ)
      by (eapply a_wf_aenv_binds_def_wf; eassumption).
    apply a_wf_ptyp_ftv_dom in hw.
    unfold ptyp_to_bskl_syn in Hγ. rewrite ftvar_in_bskl_syn in Hγ.
    rewrite ftvar_ptyp_to_pskl in Hγ. clear - hw Hγ. fsetdec.
Qed.

Lemma ad_refine_syn_strengthen : forall Θ Δ Q P,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad ->
  forall Θ', uniq Θ -> {{ ⊢ Θ' }}a ->
  (forall x b, binds x b Θ' -> binds x b Θ) ->
  (forall x, x `in` Δ -> x `notin` dom Θ) ->
  (forall γ, γ `in` ftvar_in_bskl Q -> γ `in` Δ \/ γ `in` dom Θ') ->
  (forall γ, γ `in` ftvar_in_bskl P -> γ `in` Δ \/ γ `in` dom Θ') ->
  {{ Θ' ⨟ Δ ⊢ᵣ Q ⊳ P }}ad.
Proof.
  intros Θ Δ Q P H Θ' Hu Hwf' Hsub Hdisj HscQ HscP.
  eapply ad_refine_syn_strengthen_gen;
    [ exact H | exact Hu | exact Hwf' | exact Hsub | | exact HscQ | exact HscP ].
  intros x τ Hx Hb. apply (Hdisj x Hx). eapply binds_In; exact Hb.
Qed.

Lemma a_wf_pskl_msubst_mono_images : forall Θs Δ P,
  {{ Θs ⨟ Δ ⊢ₚₛ P }}a ->
  forall σ,
  msubst_lc σ ->
  (forall α, mono_ptyp (msubst_lookup σ α)) ->
  (forall α, α `in` Δ -> α `notin` dom σ) ->
  (forall β γ, a_binds_tvar β Θs -> γ `in` ftvar_in_ptyp (msubst_lookup σ β) ->
     a_binds_tvar γ Θs /\ (β `notin` Δ -> γ `notin` Δ)) ->
  {{ Θs ⨟ Δ ⊢ₚₛ (msubst_pskl σ P) }}a.
Proof.
  intros Θs Δ P H; induction H; intros σ Hlc Hmono HΔ Himg; simpl.
  - apply a_wf_pskl__unit.
  -
    apply a_wf_pskl_of_ptyp_vis; [ apply Hlc | ].
    intros γ Hγ. exact (proj1 (Himg α γ H Hγ)).
  - apply a_wf_pskl__arrow; [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ]; assumption.
  -
    apply a_wf_pskl__all with (L := L `union` dom σ `union` dom Θ).
    intros α Hα.
    assert (Hασ : α `notin` dom σ) by (clear - Hα; fsetdec).
    rewrite <- (msubst_pskl_open_lc P Hlc Hασ).
    apply H0; [ clear - Hα; fsetdec | exact Hlc | exact Hmono | | ].
    + intros β Hβ. destruct (β == α) as [-> | Hne]; [ exact Hασ | ].
      apply HΔ. clear - Hβ Hne; fsetdec.
    + intros β γ Hβ Hγ.
      destruct (a_binds_tvar_cons_tvar_inv Hβ) as [-> | Hβ'].
      * rewrite (@msubst_lookup_notin σ α Hασ) in Hγ. simpl in Hγ.
        assert (Heq : γ = α) by (clear - Hγ; fsetdec). subst γ.
        split; [ apply a_binds_tvar_cons_tvar; left; reflexivity | ].
        intros Hn. exfalso. clear - Hn; fsetdec.
      * destruct (Himg β γ Hβ' Hγ) as [Hγb Hγn].
        split; [ apply a_binds_tvar_cons_tvar; right; exact Hγb | ].
        intros Hn.
        assert (HγΘ : γ `in` dom Θ)
          by (destruct Hγb as [Hb | [Hb | [τ Hb]]]; eapply binds_In; exact Hb).
        assert (Hne : γ <> α) by (intro Hc; subst; clear - Hα HγΘ; fsetdec).
        assert (Hn' : β `notin` Δ) by (clear - Hn; fsetdec).
        specialize (Hγn Hn'). clear - Hγn Hne. fsetdec.
  - apply a_wf_pskl__ghost.
  -
    apply a_wf_pskl__univ_ghost.
    + apply guarded_pskl_msubst_mono; assumption.
    + apply IHa_wf_pskl; [ exact Hlc | exact Hmono | | ].
      * intros β Hβ. exfalso. clear - Hβ. fsetdec.
      * intros β γ Hβ Hγ.
        apply a_binds_tvar_aenv_minus in Hβ as [Hβ HβΔ].
        destruct (Himg β γ Hβ Hγ) as [Hγb Hγn].
        split; [ | intros _; clear; fsetdec ].
        apply a_binds_tvar_aenv_minus. split; [ exact Hγb | exact (Hγn HβΔ) ].
Qed.

Lemma a_wf_pskl_downarrow : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (⇓ˢ[ Θ ] P) }}a.
Proof.
  intros Θ Δ P H Hwf HΔ.
  apply a_wf_pskl_msubst_mono_images;
    [ exact H | apply aenv_msubst_lc; exact Hwf
    | apply aenv_msubst_image_mono; exact Hwf | | ].
  - intros α Hα. pose proof (dom_aenv_msubst Θ) as h.
    pose proof (HΔ α Hα) as h2. clear - h h2. fsetdec.
  - intros β γ Hβ Hγ.
    assert (Hγb : a_binds_tvar γ Θ)
      by (eapply a_wf_ptyp_ftv_tvarish;
          [ apply aenv_msubst_image_wf; eassumption | exact Hγ ]).
    split; [ exact Hγb | intros _ Hc ].
    apply (HΔ γ Hc).
    destruct Hγb as [Hb | [Hb | [τ Hb]]]; eapply binds_In; exact Hb.
Qed.

Lemma downarrow_images_avoid_cons : forall Θ Δ α,
  {{ ⊢ Θ }}a -> α `notin` dom Θ ->
  (forall β γ, β `in` dom (aenv_msubst Θ) ->
     γ `in` ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) β) -> γ `notin` Δ) ->
  (forall β γ, β `in` dom (aenv_msubst Θ) ->
     γ `in` ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) β) ->
     γ `notin` add α Δ).
Proof.
  intros Θ Δ α Hwf HαΘ HΔ β γ Hβ Hγ.
  assert (Hbt : a_binds_tvar β Θ)
    by (destruct (@aenv_msubst_dom_inv _ _ Hβ) as [Hb | Hb];
        [ right; left; exact Hb | right; right; exact Hb ]).
  pose proof (a_wf_ptyp_ftv_dom (@aenv_msubst_image_wf _ Hwf _ Hbt)) as Hsc.
  pose proof (HΔ β γ Hβ Hγ) as h.
  assert (Hne : γ <> α) by (intro Hc; subst; clear - Hsc Hγ HαΘ; fsetdec).
  clear - h Hne. fsetdec.
Qed.

Lemma refine_syn_downarrow_gen : forall Θ Δ Q P,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad ->
  {{ ⊢ Θ }}a ->
  (forall β γ, β `in` dom (aenv_msubst Θ) ->
     γ `in` ftvar_in_ptyp (msubst_lookup (aenv_msubst Θ) β) -> γ `notin` Δ) ->
  {{ Θ ⨟ Δ ⊢ᵣ (⇓ᵇ[ Θ ] Q) ⊳ (⇓ᵇ[ Θ ] P) }}ad.
Proof.
  intros Θ Δ Q Q' H; induction H; intros Hwf HΔ.
  -  apply ad_refine_syn__unit.
  -
    destruct (AtomSetProperties.In_dec α (dom (aenv_msubst Θ))) as [Hin | Hn].
    2: { simpl. rewrite msubst_lookup_notin by exact Hn. simpl.
         apply ad_refine_syn__var. }
    assert (Hbt : a_binds_tvar α Θ)
      by (destruct (@aenv_msubst_dom_inv _ _ Hin) as [Hb | Hb];
          [ right; left; exact Hb | right; right; exact Hb ]).
    +
      simpl.
      change (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup (aenv_msubst Θ) α)))
        with (ptyp_to_bskl_syn (msubst_lookup (aenv_msubst Θ) α)).
      apply ad_refine_syn_mono_refl.
      apply aenv_msubst_image_mono; exact Hwf.
  -
    simpl. apply ad_refine_syn_arrow_intro;
      [ apply IHad_refine_syn1 | apply IHad_refine_syn2 ];
      solve [ exact Hwf | exact HΔ ].
  -
    simpl.
    apply ad_refine_syn_all_intro
      with (L := L `union` dom Θ `union` Δ `union` dom (aenv_msubst Θ)).
    intros α Hα.
    assert (HeqQ : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl Q (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) Q)
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Hα; fsetdec ]).
    assert (HeqP : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl Q' (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) Q')
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Hα; fsetdec ]).
    rewrite <- HeqQ, <- HeqP.
    rewrite <- (aenv_msubst_tvar α Θ).
    apply H1; [ clear - Hα; fsetdec
              | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ] | ].
    rewrite aenv_msubst_tvar.
    assert (HαΘ : α `notin` dom Θ) by (clear - Hα; fsetdec).
    exact (@downarrow_images_avoid_cons Θ Δ α Hwf HαΘ HΔ).
  -
    simpl. rewrite msubst_bskl_pskl_to_bskl_syn.
    apply ad_refine_syn__ghost.
    apply inter_empty_pointwise. intros γ HγΔ Hγ.
    destruct (msubst_pskl_ftv_ex _ _ Hγ) as [β [Hβ Hγβ]].
    destruct (AtomSetProperties.In_dec β (dom (aenv_msubst Θ))) as [Hin | Hn].
    + exact (HΔ β γ Hin Hγβ HγΔ).
    + rewrite (@msubst_lookup_notin _ β Hn) in Hγβ. simpl in Hγβ.
      assert (Heq : γ = β) by (clear - Hγβ; fsetdec). subst γ.
      clear - H Hβ HγΔ. fsetdec.
  -
    simpl. apply ad_refine_syn_univ_ghost_remove_intro.
    apply IHad_refine_syn; eassumption.
  -
    simpl.
    apply ad_refine_syn_univ_ghost_fill_intro
      with (L := L `union` dom Θ `union` Δ `union` dom (aenv_msubst Θ)).
    intros α Hα.
    assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]).
    pose proof (H1 α ltac:(clear - Hα; solve_notin_auto) Hwf' HΔ) as IH.
    rewrite aenv_msubst_tvar in IH.
    assert (HeqP : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl Q' (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) Q')
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Hα; fsetdec ]).
    rewrite HeqP in IH. simpl in IH. exact IH.
  -
    simpl. apply ad_refine_syn_univ_ghost_keep_intro.
    apply IHad_refine_syn; eassumption.
  -
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    simpl. rewrite Hlk.
    pose proof (IHad_refine_syn Hwf HΔ) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    exact IH.
  -
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    simpl. rewrite Hlk.
    pose proof (IHad_refine_syn Hwf HΔ) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    exact IH.
Qed.

Lemma refine_syn_downarrow : forall Θ Δ Q P,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad ->
  {{ ⊢ Θ }}a ->
  (forall x, x `in` Δ -> x `notin` dom Θ) ->
  {{ Θ ⨟ Δ ⊢ᵣ (⇓ᵇ[ Θ ] Q) ⊳ (⇓ᵇ[ Θ ] P) }}ad.
Proof.
  intros Θ Δ Q P H Hwf HΔ.
  apply (refine_syn_downarrow_gen H Hwf).
  intros β γ Hβ Hγ Hc.
  assert (Hbt : a_binds_tvar β Θ)
    by (destruct (@aenv_msubst_dom_inv _ _ Hβ) as [Hb | Hb];
        [ right; left; exact Hb | right; right; exact Hb ]).
  pose proof (a_wf_ptyp_ftv_dom (@aenv_msubst_image_wf _ Hwf _ Hbt)) as Hsc.
  apply (HΔ γ Hc). clear - Hsc Hγ. fsetdec.
Qed.

Lemma refine_syn_downarrow_source_ftv : forall Θ Δ Q P,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad ->
  {{ ⊢ Θ }}a ->
  ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] Δ ∪ ftvar_in_bskl (⇓ᵇ[ Θ ] P).
Proof.
  intros Θ Δ Q Q' H Hwf. revert Hwf.
  induction H; intros Hwf.
  -  simpl. clear; fsetdec.
  -  clear; fsetdec.
  -
    pose proof (IHad_refine_syn1 Hwf) as h1.
    pose proof (IHad_refine_syn2 Hwf) as h2.
    simpl. clear - h1 h2; fsetdec.
  -
    simpl.
    pick fresh α for (L `union` Δ `union` dom Θ `union` ftvar_in_bskl Q
                      `union` ftvar_in_bskl Q' `union` dom (aenv_msubst Θ)).
    assert (HeqQ : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl Q (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) Q)
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Fr; solve_notin_auto ]).
    assert (HeqP : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl Q' (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) Q')
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Fr; solve_notin_auto ]).
    assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Fr; solve_notin_auto | exact Hwf ]).
    pose proof (H1 α ltac:(clear - Fr; solve_notin_auto) Hwf') as IH.
    rewrite aenv_msubst_tvar in IH.
    rewrite HeqQ, HeqP in IH.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower
                  (msubst_bskl (aenv_msubst Θ) Q) (bskl_var_f α)) as Hlow.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                  (msubst_bskl (aenv_msubst Θ) Q') (bskl_var_f α)) as Hup.
    simpl in Hup.
    assert (Hfr : α `notin` ftvar_in_bskl (msubst_bskl (aenv_msubst Θ) Q)).
    { eapply msubst_bskl_ftv_fresh with (Θ := Θ);
        [ apply aenv_msubst_image_ftv; exact Hwf
        | clear - Fr; solve_notin_auto | clear - Fr; solve_notin_auto ]. }
    clear - IH Hlow Hup Hfr. fsetdec.
  -  simpl. clear; fsetdec.
  -
    pose proof (IHad_refine_syn Hwf) as IH. simpl. clear - IH; fsetdec.
  -
    simpl.
    pick fresh α for (L `union` Δ `union` dom Θ `union` ftvar_in_bskl Q
                      `union` ftvar_in_bskl Q' `union` dom (aenv_msubst Θ)).
    assert (Hwf' : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Fr; solve_notin_auto | exact Hwf ]).
    assert (HeqP : msubst_bskl (aenv_msubst Θ)
                     (open_bskl_wrt_bskl Q' (bskl_var_f α))
                   = open_bskl_wrt_bskl (msubst_bskl (aenv_msubst Θ) Q')
                       (bskl_var_f α))
      by (apply msubst_bskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Fr; solve_notin_auto ]).
    pose proof (H1 α ltac:(clear - Fr; solve_notin_auto) Hwf') as IH.
    rewrite aenv_msubst_tvar in IH.
    rewrite HeqP in IH. simpl in IH.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                  (msubst_bskl (aenv_msubst Θ) Q') (bskl_var_f α)) as Hup.
    simpl in Hup.
    assert (Hfr : α `notin` ftvar_in_bskl (msubst_bskl (aenv_msubst Θ) Q)).
    { eapply msubst_bskl_ftv_fresh with (Θ := Θ);
        [ apply aenv_msubst_image_ftv; exact Hwf
        | clear - Fr; solve_notin_auto | clear - Fr; solve_notin_auto ]. }
    clear - IH Hup Hfr. fsetdec.
  -
    pose proof (IHad_refine_syn Hwf) as IH. simpl. clear - IH; fsetdec.
  -
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    pose proof (IHad_refine_syn Hwf) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    simpl. rewrite Hlk. exact IH.
  -
    assert (Hlk : msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[ Θ ] τ)
      by (apply aenv_msubst_lookup_def; assumption).
    pose proof (IHad_refine_syn Hwf) as IH.
    rewrite msubst_bskl_ptyp_to_bskl_syn in IH.
    simpl. rewrite Hlk. exact IH.
Qed.

Lemma ad_precise_downarrow_gen : forall Θs Δs P,
  {{ Θs ⨟ Δs ⊢ₚₛ P }}a ->
  forall Θ Δ,
  {{ ⊢ Θ }}a ->
  (forall α, a_binds_tvar α Θs -> a_binds_tvar α Θ) ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (⇓ˢ[ Θ ] P) ⊑ P }}ad.
Proof.
  unfold ad_precise.
  intros Θs Δs P H; induction H; intros Θ' Δ' Hwf Hmap; simpl.
  - apply ad_refine_syn__unit.
  -
    apply Hmap in H. rename H into Hbt.
    assert (Hwfv : a_wf_ptyp Θ' (ptyp_var_f α))
      by (apply a_wf_ptyp__var; exact Hbt).
    assert (Hmv : mono_ptyp (ptyp_var_f α)) by (apply mono_ptyp__var).
    assert (Hmd : mono_ptyp (⇓ᵗ[ Θ' ] (ptyp_var_f α)))
      by (apply mono_downarrow; eassumption).
    assert (Hwfd : a_wf_ptyp Θ' (⇓ᵗ[ Θ' ] (ptyp_var_f α)))
      by (apply a_wf_ptyp_downarrow_mono; eassumption).
    assert (Heq : {{ Θ' ⊢ (ptyp_var_f α) ≡ᵗ (⇓ᵗ[ Θ' ] (ptyp_var_f α)) }}a)
      by (apply a_tyequiv_to_downarrow_mono; eassumption).
    change (pskl_to_bskl_inh (ptyp_to_pskl (msubst_lookup (aenv_msubst Θ') α)))
      with (pskl_to_bskl_inh (ptyp_to_pskl (⇓ᵗ[ Θ' ] (ptyp_var_f α)))).
    rewrite (ptyp_to_bskl_inh_syn_eq Hmd).
    change (bskl_var_f α) with (ptyp_to_bskl_syn (ptyp_var_f α)).
    eapply tyequiv_mono_refine_syn;
      [ exact Hwf | exact Hmd | exact Hmv
      | apply a_tyequiv__sym; exact Heq
      | intros γ Hγ; eapply a_wf_ptyp_ftv_tvarish; eassumption ].
  -
    apply ad_refine_syn_arrow_intro;
      [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ]; assumption.
  -
    apply ad_refine_syn_all_intro
      with (L := L `union` dom Θ' `union` dom (aenv_msubst Θ')).
    intros α Hα.
    assert (Heq : msubst_pskl (aenv_msubst Θ')
                    (open_pskl_wrt_pskl P (pskl_var_f α))
                  = open_pskl_wrt_pskl (msubst_pskl (aenv_msubst Θ') P)
                      (pskl_var_f α))
      by (apply msubst_pskl_open_lc;
          [ apply aenv_msubst_lc; exact Hwf | clear - Hα; fsetdec ]).
    repeat rewrite <- pskl_to_bskl_inh_open.
    rewrite <- Heq.
    rewrite <- (aenv_msubst_tvar α Θ').
    apply H0; [ clear - Hα; fsetdec
              | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ] | ].
    intros β Hβ. apply a_binds_tvar_cons_tvar.
    destruct (a_binds_tvar_cons_tvar_inv Hβ) as [-> | Hβ']; auto.
  -
    replace (pskl_to_bskl_inh pskl_ghost)
      with (pskl_to_bskl_syn pskl_ghost) at 2 by reflexivity.
    apply ad_refine_syn__ghost. cbn. clear; fsetdec.
  -
    apply ad_refine_syn_univ_ghost_keep_intro.
    apply IHa_wf_pskl; [ exact Hwf | ].
    intros β Hβ. apply Hmap.
    apply a_binds_tvar_aenv_minus in Hβ. apply Hβ.
Qed.

Lemma ad_precise_downarrow : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (⇓ˢ[ Θ ] P) ⊑ P }}ad.
Proof.
  intros Θ Δ P H Hwf.
  apply (@ad_precise_downarrow_gen Θ Δ P H Θ Δ Hwf). intros α Hα; exact Hα.
Qed.

Lemma ad_precise_downarrow_restore : forall Θ0 Θ P Q,
  {{ Θ0 ⨟ empty ⊢ₚᵣ P ⊑ (bskl_to_pskl (⇓ᵇ[ Θ ] Q)) }}ad ->
  (forall α bd, binds α bd Θ0 -> binds α bd Θ) ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ empty ⊢ₚᵣ P ⊑ (bskl_to_pskl Q) }}ad.
Proof.
  intros Θ0 Θ P Q Hprec Hsub HwfQ Hwf.
  assert (HprecΘ : {{ Θ ⨟ empty ⊢ₚᵣ P ⊑ (bskl_to_pskl (⇓ᵇ[ Θ ] Q)) }}ad).
  { unfold ad_precise in *. eapply ad_refine_syn_weaken; eauto. }
  unfold ad_precise in *.
  rewrite (bskl_to_pskl_msubst_bskl (aenv_msubst Θ) Q) in HprecΘ.
  eapply ad_refine_syn_trans;
    [ apply ad_precise_downarrow; assumption
    | exact Hwf
    | intros α Hα; clear - Hα; fsetdec
    | rewrite bskl_to_pskl_pskl_to_bskl_inh; exact HwfQ
    | exact HprecΘ ].
Qed.

Local Lemma sub_flex_skip_normalize :
  forall n NM M Θ0 Ξ α β bd P0 R' Ψ Θ κ Q κa κb Θpre Θ',
  a_decls Ξ -> dom Ξ [<=] ftvar_in_pskl P0 ->
  {{ ⊢ (Ξ ++ (β ~ bd) ++ Θ0) }}a -> {{ ⊢ Θ }}a ->
  {{ (Ξ ++ (β ~ bd) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_flex_tvar Θ0 α ->
  κ ∷ (Ξ ++ (β ~ bd) ++ Θ0) ⊑ Θ ->
  {{ Θ ⊢ R' ≡ᵘ (ptyp_to_uskl_syn (msubst_lookup κ α)) }}a ->
  ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ R' Q ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  κ = κa ++ κb -> dom κa [=] dom Ξ -> κb ∷ Θ0 ⊑ Θ' ->
  Θpre ++ Θ' = Θ -> {{ ⊢ Θ' }}a ->
  msubst_compose (aenv_msubst Θ) κ ∷ (Ξ ++ Θ0) ⊑ Θ' /\
  {{ Θ' ⊢ ptyp_to_uskl_syn (⇓ᵗ[ Θ ] (msubst_lookup κ α))
      ≡ᵘ ptyp_to_uskl_syn
        (msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α) }}a /\
  ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ'
    (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] (msubst_lookup κ α))) (⇓ᵇ[ Θ ] Q) /\
  {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh
      (msubst_pskl (msubst_compose (aenv_msubst Θ) κ) P0)) ⊳ (⇓ᵇ[ Θ ] Q) }}ad /\
  {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl (⇓ᵇ[ Θ ] Q)) }}a.
Proof.
  intros n NM M Θ0 Ξ α β bd P0 R' Ψ Θ κ Q κa κb Θpre Θ'
    HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα0 Hinc Hslack HD Hrs HwfQ
    Heqκ Hdκa Hincb HeqW HwfΘ'.
  assert (Huq : uniq (Ξ ++ (β ~ bd) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
  assert (HwfΘ0 : {{ ⊢ Θ0 }}a).
  { eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (β ~ bd)).
    simpl_env. exact Hwf. }
  assert (HαΘ0 : α `in` dom Θ0)
    by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
  assert (Hαb0 : a_binds_tvar α Θ0)
    by (destruct Hfα0 as [Hb | [τ Hb]];
        [right; left | right; right; exists τ]; exact Hb).
  assert (Hαbfull : a_binds_tvar α (Ξ ++ (β ~ bd) ++ Θ0)).
  { destruct (a_flex_tvar_weaken_app (Ξ ++ (β ~ bd)) Hfα0)
      as [Hb | [τ Hb]];
      [right; left | right; right; exists τ]; simpl_env in Hb; exact Hb. }
  assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
  { intros y c Hb. rewrite <- HeqW. apply binds_app_3. exact Hb. }
  assert (Hincb_n : msubst_compose (aenv_msubst Θ) κb ∷ Θ0 ⊑ Θ').
  { pose proof (a_inc_self_downarrow Hincb Θpre) as Hs.
    rewrite HeqW in Hs.
    apply Hs; eassumption. }

  assert (Hmκα : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact Hinc).
  assert (Hwfκα : a_wf_ptyp Θ (msubst_lookup κ α))
    by (eapply a_inc_lookup_wf; eassumption).
  destruct (a_uskl_tyequiv_mono_r_inv Hslack
              (eq_refl (ptyp_to_uskl_syn (msubst_lookup κ α))) Hmκα Hwfκα)
    as [τ' [HeqR' [Hmτ' [Hwfτ' Heqττ']]]].
  subst R'.
  assert (Hddτ' : ⇓ᵗ[ Θ ] τ' = ⇓ᵗ[ Θ ] (msubst_lookup κ α))
    by (apply a_tyequiv_downarrow; eassumption).

  assert (Hακa : α `notin` dom κa).
  { rewrite Hdκa. clear - Huq HαΘ0. simpl_env in Huq. solve_uniq. }
  assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup κ α)).
  { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb Hακa).
    eapply a_inc_lookup_wf; eassumption. }
  assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ')
    by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
  assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup κ α) = ⇓ᵗ[ Θ' ] (msubst_lookup κ α)).
  { rewrite <- HeqW.
    apply downarrow_app_agree_ptyp; [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
  assert (HO1 : ftvar_in_ptyp (⇓ᵗ[ Θ ] τ') [<=] dom Θ').
  { rewrite Hddτ'. rewrite Hddα. apply a_wf_ptyp_ftv_dom.
    apply a_wf_ptyp_downarrow_mono; eassumption. }

  assert (Hmono_img : forall γ, mono_ptyp (msubst_lookup (aenv_msubst Θ) γ))
    by (intros; apply aenv_msubst_image_mono; exact Hwfth).
  assert (HO2 : ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] dom Θ').
  { eapply sub_gv_bskl_downarrow_mono_scoped;
      [ exact HD | exact Hwfth | reflexivity | exact Hmτ' | exact HO1 ]. }
  assert (Heqinh : ⇓ᵇ[ Θ ] (pskl_to_bskl_inh (msubst_pskl κ P0))
                   = pskl_to_bskl_inh (⇓ˢ[ Θ ] (msubst_pskl κ P0)))
    by (apply msubst_bskl_pskl_to_bskl_inh; exact Hmono_img).
  assert (HO3 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P0)) [<=] dom Θ').
  { pose proof (refine_syn_downarrow_source_ftv Hrs Hwfth) as h.
    rewrite Heqinh in h. rewrite ftvar_in_bskl_inh in h.
    clear - h HO2. fsetdec. }

  assert (Hside : forall γ, γ `in` ftvar_in_pskl P0 ->
            γ `in` dom κ \/ γ `notin` dom (aenv_msubst Θ))
    by (intros x Hx; eapply a_inc_downarrow_vis;
        [exact Hinc | exact Hwf | exact Hwfth
        | eapply a_wf_pskl_ftv_binds; eassumption]).
  assert (Hgr : forall γ, γ `in` dom κa ->
            ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup κa γ)) [<=] dom Θ').
  { intros γ Hγ.
    assert (HXP : γ `in` ftvar_in_pskl P0)
      by (apply HdomΞ; rewrite <- Hdκa; exact Hγ).
    assert (Hγκ : γ `in` dom κ)
      by (rewrite Heqκ; rewrite dom_app; clear - Hγ; fsetdec).
    assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup κa γ)
                   = msubst_lookup (msubst_compose (aenv_msubst Θ) κ) γ).
    { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hγκ)).
      f_equal. rewrite Heqκ. symmetry. apply msubst_lookup_app_in; exact Hγ. }
    rewrite Heqlk.
    eapply AtomSetProperties.subset_trans;
      [ apply (msubst_pskl_ftv_lower
                 (msubst_compose (aenv_msubst Θ) κ) P0 HXP) | ].
    rewrite msubst_pskl_compose; eassumption. }
  assert (Hinc_sub : msubst_compose (aenv_msubst Θ) κ ∷ (Ξ ++ Θ0) ⊑ Θ').
  { assert (HincR : κa ++ κb ∷ (Ξ ++ (β ~ bd) ++ Θ0) ⊑ Θ)
      by (rewrite <- Heqκ; exact Hinc).
    rewrite Heqκ. rewrite msubst_compose_app.
    eapply a_inc_downarrow_prefix; eassumption. }

  assert (Hmd : mono_ptyp (⇓ᵗ[ Θ ] τ'))
    by (apply mono_downarrow; eassumption).
  assert (Hwfd' : a_wf_ptyp Θ' (⇓ᵗ[ Θ ] τ')).
  { rewrite Hddτ'. rewrite Hddα.
    apply a_wf_ptyp_downarrow_mono; eassumption. }
  assert (Hjoin' : ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ'
                     (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] τ')) (⇓ᵇ[ Θ ] Q)).
  { eapply ad_pat_sub_fuel_mono_strengthen;
      [ eapply sub_gv_downarrow_mono;
          [ exact HD | exact Hwfth | reflexivity | exact Hmτ' | exact Hwfτ' ]
      | reflexivity | exact Hmd | exact HuqΘ | exact HwfΘ' | exact Hsub'
      | intros γ Hγ; clear - HO1 Hγ; fsetdec
      | intros γ Hγ; clear - HO2 Hγ; fsetdec ]. }

  assert (Hrs' : {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh
                      (msubst_pskl (msubst_compose (aenv_msubst Θ) κ) P0)) ⊳ (⇓ᵇ[ Θ ] Q) }}ad).
  { rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P0 Hside).
    pose proof (refine_syn_downarrow Hrs Hwfth
                  ltac:(intros x Hx; exfalso; clear - Hx; solve_notin_auto)) as h.
    rewrite Heqinh in h.
    eapply ad_refine_syn_strengthen;
      [ exact h | exact HuqΘ | exact HwfΘ' | exact Hsub'
      | intros x Hx; exfalso; clear - Hx; fsetdec
      | intros γ Hγ; right; rewrite ftvar_in_bskl_inh in Hγ;
        clear - HO3 Hγ; fsetdec
      | intros γ Hγ; right; clear - HO2 Hγ; fsetdec ]. }

  assert (HwfQ' : {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl (⇓ᵇ[ Θ ] Q)) }}a).
  { rewrite bskl_to_pskl_msubst_bskl.
    eapply a_wf_pskl_strengthen;
      [ apply a_wf_pskl_downarrow;
          [ exact HwfQ | exact Hwfth
          | intros x Hx; exfalso; clear - Hx; fsetdec ]
      | exact HuqΘ | exact Hsub'
      | intros γ Hγ;
        rewrite <- bskl_to_pskl_msubst_bskl in Hγ;
        rewrite ftvar_bskl_to_pskl in Hγ;
        clear - HO2 Hγ; fsetdec ]. }

  assert (Hακdom : α `in` dom κ).
  { rewrite Heqκ. rewrite dom_app.
    assert (Hαd : α `in` dom κb)
      by (eapply a_inc_flex_dom; eassumption).
    clear - Hαd. fsetdec. }
  assert (Hslack' : {{ Θ' ⊢ (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] τ'))
              ≡ᵘ (ptyp_to_uskl_syn
                    (msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α)) }}a).
  { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hακdom)).
    rewrite <- Hddτ'.
    apply a_uskl_tyequiv__mono;
      [ exact Hmd | exact Hmd | exact Hwfd' | exact Hwfd'
      | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmd ]. }
  rewrite Hddτ' in Hslack', Hjoin'.
  repeat apply conj; assumption.
Qed.

Lemma a_sub_flex_complete_skip_rigid : forall n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q,

  (forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
     length Ξ' <= S (length Ξ) ->
     sub_flex_complete_concl n NM M Θ0 Ξ' α' P0' R'' Ψ' Θ'' κ' Q') ->
  α <> β ->
  β `notin` ftvar_in_pskl P0 ->
  sub_flex_complete_concl n NM M ((β ~ abind_tvar) ++ Θ0) Ξ α P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q IH Hne Hnin.
  unfold sub_flex_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.

  assert (Huq : uniq (Ξ ++ (β ~ abind_tvar) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; eassumption).
  assert (Huq' : uniq (Ξ ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf').
  assert (HwfΘ0 : {{ ⊢ Θ0 }}a) by (eapply a_wf_aenv_strip_prefix; exact Hwf').
  assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
    by (eapply a_wf_pskl_strip_mid; eassumption).

  assert (Hfα0 : a_flex_tvar Θ0 α).
  { destruct Hfα as [Hb | [τ0 Hb]]; [ left | right; exists τ0 ];
      (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He _] | Hb'];
       [ exfalso; apply Hne; exact He | exact Hb' ]). }
  assert (Hαb' : a_binds_tvar α (Ξ ++ Θ0))
    by (destruct (a_flex_tvar_weaken_app Ξ Hfα0) as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).

  destruct (@a_inc_strip_decls_prefix Ξ ((β ~ abind_tvar) ++ Θ0) κ Θ HdeclsΞ
              Hinc)
    as [κa [κb [Heqκ [Hdκa Hincxb]]]].
  destruct (a_inc_tvar_inv Hincxb) as [Ξv [Θ' [HeqΘ [HsufΞv Hincb]]]].
  assert (HwfΘ' : {{ ⊢ Θ' }}a).
  { rewrite HeqΘ in Hwfth.
    eapply a_wf_aenv_strip_prefix with (Ξ := Ξv ++ (β ~ abind_tvar)).
    simpl_env. simpl_env in Hwfth. exact Hwfth. }
  assert (HeqW : (Ξv ++ (β ~ abind_tvar)) ++ Θ' = Θ)
    by (rewrite HeqΘ; simpl_env; reflexivity).
  assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
  { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
    exact Hb. }
  destruct (@sub_flex_skip_normalize n NM M Θ0 Ξ α β (abind_tvar) P0 R' Ψ Θ κ Q
              κa κb (Ξv ++ (β ~ abind_tvar)) Θ'
              HdeclsΞ HdomΞ Hwf Hwfth HwfP0
              Hfα0 Hinc Hslack HD Hrs HwfQ Heqκ Hdκa Hincb HeqW HwfΘ')
    as (Hinc_sub & Hslack' & Hjoin' & Hrs' & HwfQ').

  destruct (IH Ξ α P0 (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] (msubst_lookup κ α))) Ψ Θ'
              (msubst_compose (aenv_msubst Θ) κ) (⇓ᵇ[ Θ ] Q) ltac:(lia)
              HdeclsΞ HdomΞ Hwf' HwfΘ' HwfP0' Hfα0 HmodSK HmodTY
              Hinc_sub Hslack' Hjoin' Hrs' HwfQ')
    as [P1 [Θ1 [Hrun Hopt]]].
  destruct (@a_sub_flex_optimal_fresh NM M P0 Θ0 Ξ α P1 Θ1 _ _ _ β
    Hrun HdeclsΞ Hwf' HwfP0' Hαb' HmodSK HmodTY HβΞΘ0 Hnin Hopt)
    as [P2 [Θ2 [Hrun2 [HwfΘ1 [Hβout [HβP2 Hopt2]]]]]].
  clear Hrun Hopt. rename Hrun2 into Hrun. rename Hopt2 into Hopt.
  clear P1 Θ1. rename P2 into P1. rename Θ2 into Θ1.
  exists P1, ((β ~ abind_tvar) ++ Θ1).
  split.
  { apply a_sub_flex__skip_rigid; eassumption. }

  intros κf Hidf Hincf.
  assert (Hincf' : κf ∷ (Ξ ++ Θ0) ⊑ Θ1)
    by (eapply a_inc_tvar_mid_strip_id; eassumption).
  destruct (Hopt κf Hidf Hincf') as [ζ [Hζ [Hie Hprec]]].
  exists ζ.
  split.
  {
    rewrite HeqΘ. apply a_inc__tvar; [ | exact HsufΞv ].
    exact Hζ. }
  split.
  {
    destruct (@a_inc_strip_decls_prefix Ξ Θ0 κf Θ1
                HdeclsΞ Hincf')
      as [κf1 [κf2 [Heqκf [Hdκf1 _]]]].
    assert (Hmi : a_inc_equiv (Ξ ++ (β ~ abind_tvar) ++ Θ0)
                    (msubst_compose (aenv_msubst Θ) κ)
                    (msubst_compose ζ κf)
                    (Ξv ++ (β ~ abind_tvar) ++ Θ')).
    { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb).
      rewrite Heqκf. rewrite (msubst_compose_app ζ κf1 κf2).
      apply a_inc_equiv_mid_insert_tvar;
        [ exact HdeclsΞ | exact Huq'
        | rewrite dom_msubst_compose; exact Hdκa
        | rewrite dom_msubst_compose; exact Hdκf1
        | exact HsufΞv | ].
      rewrite Heqκ in Hie.
      rewrite (msubst_compose_app (aenv_msubst Θ) κa κb) in Hie.
      rewrite Heqκf in Hie.
      rewrite (msubst_compose_app ζ κf1 κf2) in Hie.
      exact Hie. }
    rewrite <- HeqΘ in Hmi.
    eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
    pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
      as Hself.
    simpl in Hself. apply Hself; eassumption. }
  {
    eapply ad_precise_downarrow_restore; eauto. }
Qed.

Lemma a_sub_flex_complete_skip_tm_var :
  forall n NM M Θ0 Ξ α β Qv P0 R' Ψ Θ κ Q,

  (forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
     length Ξ' <= S (length Ξ) ->
     sub_flex_complete_concl n NM M Θ0 Ξ' α' P0' R'' Ψ' Θ'' κ' Q') ->
  sub_flex_complete_concl n NM M ((β ~ abind_var_typ Qv) ++ Θ0) Ξ α P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β Qv P0 R' Ψ Θ κ Q IH.
  unfold sub_flex_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.

  assert (Huq : uniq (Ξ ++ (β ~ abind_var_typ Qv) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }

  assert (Hfα0 : a_flex_tvar Θ0 α).
  { apply a_flex_tvar_cons_nonflex in Hfα;
      [exact Hfα | apply abind_is_tm_nonflex; simpl; exact I]. }
  assert (HαΘ0 : α `in` dom Θ0)
    by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
  assert (Hne : α <> β).
  { intro Hc; subst. clear - HαΘ0 HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }

  assert (Hnin : β `notin` ftvar_in_pskl P0)
    by (eapply a_wf_pskl_tm_entry_fresh;
        [exact Hwf | simpl; exact I | exact HwfP0]).
  assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; eassumption).
  assert (Huq' : uniq (Ξ ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf').
  assert (HwfΘ0 : {{ ⊢ Θ0 }}a) by (eapply a_wf_aenv_strip_prefix; exact Hwf').
  assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
    by (eapply a_wf_pskl_strip_mid; eassumption).

  assert (HwfaΘ0x : {{ ⊢ ((β ~ abind_var_typ Qv) ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_prefix; exact Hwf).
  destruct (a_wf_aenv_var_typ_inv HwfaΘ0x) as [_ [HwfQv0 _]].
  assert (HwfQv : a_wf_ptyp (Ξ ++ Θ0) Qv)
    by (eapply a_wf_ptyp_weaken;
        [ intros ? ? Hb; apply binds_app_3; exact Hb | exact HwfQv0 ]).
  assert (HlcQv : lc_ptyp Qv) by (eapply a_wf_ptyp_lc; exact HwfQv0).
  assert (HftvQv : ftvar_in_ptyp Qv [<=] dom Θ0)
    by (apply a_wf_ptyp_ftv_dom; exact HwfQv0).
  assert (Hαb' : a_binds_tvar α (Ξ ++ Θ0))
    by (destruct (a_flex_tvar_weaken_app Ξ Hfα0) as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).

  destruct (@a_inc_strip_decls_prefix Ξ ((β ~ abind_var_typ Qv) ++ Θ0) κ Θ
              HdeclsΞ Hinc)
    as [κa [κb [Heqκ [Hdκa Hincxb]]]].
  destruct (a_inc_var_inv Hincxb)
    as [Ξv [A' [Θ' [HeqΘ [HeqA' [HsufΞv Hincb]]]]]].
  assert (HwfΘ' : {{ ⊢ Θ' }}a).
  { rewrite HeqΘ in Hwfth.
    eapply a_wf_aenv_strip_prefix with (Ξ := Ξv ++ (β ~ abind_var_typ A')).
    simpl_env. simpl_env in Hwfth. exact Hwfth. }
  assert (HeqW : (Ξv ++ (β ~ abind_var_typ A')) ++ Θ' = Θ)
    by (rewrite HeqΘ; simpl_env; reflexivity).
  assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
  { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
    exact Hb. }
  destruct (@sub_flex_skip_normalize n NM M Θ0 Ξ α β (abind_var_typ Qv) P0 R' Ψ Θ κ Q
              κa κb (Ξv ++ (β ~ abind_var_typ A')) Θ'
              HdeclsΞ HdomΞ Hwf Hwfth HwfP0
              Hfα0 Hinc Hslack HD Hrs HwfQ Heqκ Hdκa Hincb HeqW HwfΘ')
    as (Hinc_sub & Hslack' & Hjoin' & Hrs' & HwfQ').

  destruct (IH Ξ α P0 (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] (msubst_lookup κ α))) Ψ Θ'
              (msubst_compose (aenv_msubst Θ) κ) (⇓ᵇ[ Θ ] Q) ltac:(lia)
              HdeclsΞ HdomΞ Hwf' HwfΘ' HwfP0' Hfα0 HmodSK HmodTY
              Hinc_sub Hslack' Hjoin' Hrs' HwfQ')
    as [P1 [Θ1 [Hrun Hopt]]].
  destruct (@a_sub_flex_optimal_fresh NM M P0 Θ0 Ξ α P1 Θ1 _ _ _ β
    Hrun HdeclsΞ Hwf' HwfP0' Hαb' HmodSK HmodTY HβΞΘ0 Hnin Hopt)
    as [P2 [Θ2 [Hrun2 [HwfΘ1 [Hβout [HβP2 Hopt2]]]]]].
  clear Hrun Hopt. rename Hrun2 into Hrun. rename Hopt2 into Hopt.
  clear P1 Θ1. rename P2 into P1. rename Θ2 into Θ1.
  exists P1,
         ((β ~ abind_var_typ Qv) ++ Θ1).
  split.
  { apply a_sub_flex__skip_tm_var; eassumption. }

  intros κf Hidf Hincf.
  assert (Hincf' : κf ∷ (Ξ ++ Θ0) ⊑ Θ1)
    by (eapply a_inc_var_mid_strip_id; eassumption).
  destruct (Hopt κf Hidf Hincf') as [ζ [Hζ [Hie Hprec]]].
  assert (Hmiddle : {{ Θ' ⊢ A' ≡ᵗ
            msubst_ptyp (msubst_compose (aenv_msubst Θ) κb) Qv }}a).
  { eapply a_tyequiv__trans; [ exact HeqA' | ].
    apply a_tyequiv__sym.
    eapply msubst_compose_downarrow_tyequiv
      with (Θpre := Ξv ++ (β ~ abind_var_typ A'));
      [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth | exact HwfΘ'
      | eapply a_inc_msubst_lc; exact Hincb
      | intros α0 HXd;
        destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
        (eapply a_inc_lookup_wf; [ exact Hincb | exact HwfΘ0 | ]);
        [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
      | exact HlcQv ]. }

  assert (Hag : msubst_ptyp (msubst_compose (aenv_msubst Θ) κ) Qv
              = msubst_ptyp (msubst_compose (aenv_msubst Θ) κb) Qv).
  { apply msubst_ptyp_agree. intros α0 HXQ.
    rewrite Heqκ. rewrite msubst_compose_app.
    apply msubst_lookup_app_notin.
    rewrite dom_msubst_compose. rewrite Hdκa.
    assert (Hα0Θ0 : α0 `in` dom Θ0) by (clear - HftvQv HXQ; fsetdec).
    clear - Huq Hα0Θ0. simpl_env in Huq. solve_uniq. }
  exists ζ.
  split.
  {
    rewrite HeqΘ. apply a_inc__var; [ | | exact HsufΞv ].
    - exact Hζ.
    -
      assert (Hlc1 : msubst_lc (msubst_compose (aenv_msubst Θ) κ))
        by (eapply a_inc_msubst_lc; exact Hinc_sub).
      assert (Hlc2 : msubst_lc (msubst_compose ζ κf)).
      { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ | ].
        intros a t Hin. eapply is_id_msubst_values_lc; eassumption. }
      pose proof (a_inc_equiv_msubst_ptyp HwfQv Hie Hwf' Hlc1 Hlc2) as Hmid.
      rewrite (msubst_compose_id_ptyp Hwf' HwfΘ1 Hidf Hincf' Hζ HwfQv)
        in Hmid.
      rewrite Hag in Hmid.
      eapply a_tyequiv__trans; eassumption. }
  split.
  {
    destruct (@a_inc_strip_decls_prefix Ξ Θ0 κf Θ1
                HdeclsΞ Hincf')
      as [κf1 [κf2 [Heqκf [Hdκf1 _]]]].
    assert (Hmi : a_inc_equiv (Ξ ++ (β ~ abind_var_typ Qv) ++ Θ0)
                    (msubst_compose (aenv_msubst Θ) κ)
                    (msubst_compose ζ κf)
                    (Ξv ++ (β ~ abind_var_typ A') ++ Θ')).
    { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb).
      rewrite Heqκf. rewrite (msubst_compose_app ζ κf1 κf2).
      apply a_inc_equiv_mid_insert_var;
        [ exact HdeclsΞ | exact Huq'
        | rewrite dom_msubst_compose; exact Hdκa
        | rewrite dom_msubst_compose; exact Hdκf1
        | exact Hmiddle | exact HsufΞv | ].
      rewrite Heqκ in Hie.
      rewrite (msubst_compose_app (aenv_msubst Θ) κa κb) in Hie.
      rewrite Heqκf in Hie.
      rewrite (msubst_compose_app ζ κf1 κf2) in Hie.
      exact Hie. }
    rewrite <- HeqΘ in Hmi.
    eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
    pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
      as Hself.
    simpl in Hself. apply Hself; eassumption. }
  {
    eapply ad_precise_downarrow_restore; eauto. }
Qed.

Lemma a_sub_flex_complete_skip_tm_skl :
  forall n NM M Θ0 Ξ α β Qv P0 R' Ψ Θ κ Q,

  (forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
     length Ξ' <= S (length Ξ) ->
     sub_flex_complete_concl n NM M Θ0 Ξ' α' P0' R'' Ψ' Θ'' κ' Q') ->
  sub_flex_complete_concl n NM M ((β ~ abind_var_skl Qv) ++ Θ0) Ξ α P0
    R' Ψ Θ κ Q.
Proof.
  intros n NM M Θ0 Ξ α β Qv P0 R' Ψ Θ κ Q IH.
  unfold sub_flex_complete_concl in *.
  intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
         HwfQ.

  assert (Huq : uniq (Ξ ++ (β ~ abind_var_skl Qv) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HβΞΘ0 : β `notin` dom (Ξ ++ Θ0)).
  { clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }

  assert (Hfα0 : a_flex_tvar Θ0 α).
  { apply a_flex_tvar_cons_nonflex in Hfα;
      [exact Hfα | apply abind_is_tm_nonflex; simpl; exact I]. }
  assert (HαΘ0 : α `in` dom Θ0)
    by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
  assert (Hne : α <> β).
  { intro Hc; subst. clear - HαΘ0 HβΞΘ0. simpl_env in HβΞΘ0. fsetdec. }

  assert (Hnin : β `notin` ftvar_in_pskl P0)
    by (eapply a_wf_pskl_tm_entry_fresh;
        [exact Hwf | simpl; exact I | exact HwfP0]).
  assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; eassumption).
  assert (Huq' : uniq (Ξ ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf').
  assert (HwfΘ0 : {{ ⊢ Θ0 }}a) by (eapply a_wf_aenv_strip_prefix; exact Hwf').
  assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
    by (eapply a_wf_pskl_strip_mid; eassumption).

  assert (HwfaΘ0x : {{ ⊢ ((β ~ abind_var_skl Qv) ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_prefix; exact Hwf).
  destruct (a_wf_aenv_var_skl_inv HwfaΘ0x) as [_ [HwfQv0 _]].
  assert (HwfQv : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ Qv }}a)
    by (eapply a_wf_pskl_weaken;
        [ intros ? ? Hb; apply binds_app_3; exact Hb | exact HwfQv0 ]).
  assert (HlcQv : lc_pskl Qv) by (eapply a_wf_pskl_lc; eauto).
  assert (HftvQv : ftvar_in_pskl Qv [<=] dom Θ0)
    by (apply a_scope_pskl_ftv_dom; exact (a_scope_pskl_of_wf HwfQv0)).
  assert (Hαb' : a_binds_tvar α (Ξ ++ Θ0))
    by (destruct (a_flex_tvar_weaken_app Ξ Hfα0) as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).

  destruct (@a_inc_strip_decls_prefix Ξ ((β ~ abind_var_skl Qv) ++ Θ0) κ Θ
              HdeclsΞ Hinc)
    as [κa [κb [Heqκ [Hdκa Hincxb]]]].
  destruct (a_inc_var_skl_inv Hincxb)
    as [Ξv [Qv' [Θ' [HeqΘ [HeqQv' [HsufΞv Hincb]]]]]].
  assert (HwfΘ' : {{ ⊢ Θ' }}a).
  { rewrite HeqΘ in Hwfth.
    eapply a_wf_aenv_strip_prefix with (Ξ := Ξv ++ (β ~ abind_var_skl Qv')).
    simpl_env. simpl_env in Hwfth. exact Hwfth. }
  assert (HeqW : (Ξv ++ (β ~ abind_var_skl Qv')) ++ Θ' = Θ)
    by (rewrite HeqΘ; simpl_env; reflexivity).
  assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
  { intros y c Hb. rewrite HeqΘ. apply binds_app_3. apply binds_app_3.
    exact Hb. }
  destruct (@sub_flex_skip_normalize n NM M Θ0 Ξ α β (abind_var_skl Qv) P0 R' Ψ Θ κ Q
              κa κb (Ξv ++ (β ~ abind_var_skl Qv')) Θ'
              HdeclsΞ HdomΞ Hwf Hwfth HwfP0
              Hfα0 Hinc Hslack HD Hrs HwfQ Heqκ Hdκa Hincb HeqW HwfΘ')
    as (Hinc_sub & Hslack' & Hjoin' & Hrs' & HwfQ').

  destruct (IH Ξ α P0 (ptyp_to_uskl_syn (⇓ᵗ[ Θ ] (msubst_lookup κ α))) Ψ Θ'
              (msubst_compose (aenv_msubst Θ) κ) (⇓ᵇ[ Θ ] Q) ltac:(lia)
              HdeclsΞ HdomΞ Hwf' HwfΘ' HwfP0' Hfα0 HmodSK HmodTY
              Hinc_sub Hslack' Hjoin' Hrs' HwfQ')
    as [P1 [Θ1 [Hrun Hopt]]].
  destruct (@a_sub_flex_optimal_fresh NM M P0 Θ0 Ξ α P1 Θ1 _ _ _ β
    Hrun HdeclsΞ Hwf' HwfP0' Hαb' HmodSK HmodTY HβΞΘ0 Hnin Hopt)
    as [P2 [Θ2 [Hrun2 [HwfΘ1 [Hβout [HβP2 Hopt2]]]]]].
  clear Hrun Hopt. rename Hrun2 into Hrun. rename Hopt2 into Hopt.
  clear P1 Θ1. rename P2 into P1. rename Θ2 into Θ1.
  exists P1,
         ((β ~ abind_var_skl Qv) ++ Θ1).
  split.
  { apply a_sub_flex__skip_tm_skl; eassumption. }

  intros κf Hidf Hincf.
  assert (Hincf' : κf ∷ (Ξ ++ Θ0) ⊑ Θ1)
    by (eapply a_inc_var_skl_mid_strip_id; eassumption).
  destruct (Hopt κf Hidf Hincf') as [ζ [Hζ [Hie Hprec]]].
  assert (Hmiddle : {{ Θ' ⊢ Qv' ≡ˢ
            msubst_pskl (msubst_compose (aenv_msubst Θ) κb) Qv }}a).
  { eapply a_pskl_tyequiv__trans; [ exact HeqQv' | ].
    apply a_pskl_tyequiv__sym.
    eapply msubst_pskl_compose_downarrow_tyequiv
      with (Θpre := Ξv ++ (β ~ abind_var_skl Qv'));
      [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth | exact HwfΘ'
      | eapply a_inc_msubst_lc; exact Hincb
      | intros α0 HXd;
        destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
        (eapply a_inc_lookup_wf; [ exact Hincb | exact HwfΘ0 | ]);
        [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
      | exact HlcQv ]. }

  assert (Hag : msubst_pskl (msubst_compose (aenv_msubst Θ) κ) Qv
              = msubst_pskl (msubst_compose (aenv_msubst Θ) κb) Qv).
  { apply msubst_pskl_agree. intros α0 HXQ.
    rewrite Heqκ. rewrite msubst_compose_app.
    apply msubst_lookup_app_notin.
    rewrite dom_msubst_compose. rewrite Hdκa.
    assert (Hα0Θ0 : α0 `in` dom Θ0) by (clear - HftvQv HXQ; fsetdec).
    clear - Huq Hα0Θ0. simpl_env in Huq. solve_uniq. }
  exists ζ.
  split.
  {
    rewrite HeqΘ. apply a_inc__var_skl; [ | | exact HsufΞv ].
    - exact Hζ.
    -
      assert (Hlc1 : msubst_lc (msubst_compose (aenv_msubst Θ) κ))
        by (eapply a_inc_msubst_lc; exact Hinc_sub).
      assert (Hlc2 : msubst_lc (msubst_compose ζ κf)).
      { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ | ].
        intros a t Hin. eapply is_id_msubst_values_lc; eassumption. }
      pose proof (a_inc_equiv_msubst_pskl (a_scope_pskl_of_wf HwfQv) Hie Hwf'
                   Hlc1 Hlc2) as Hmid.
      rewrite (msubst_compose_id_pskl Hwf' HwfΘ1 Hidf Hincf' Hζ
                 (a_scope_pskl_of_wf HwfQv))
        in Hmid.
      rewrite Hag in Hmid.
      eapply a_pskl_tyequiv__trans; eassumption. }
  split.
  {
    destruct (@a_inc_strip_decls_prefix Ξ Θ0 κf Θ1
                HdeclsΞ Hincf')
      as [κf1 [κf2 [Heqκf [Hdκf1 _]]]].
    assert (Hmi : a_inc_equiv (Ξ ++ (β ~ abind_var_skl Qv) ++ Θ0)
                    (msubst_compose (aenv_msubst Θ) κ)
                    (msubst_compose ζ κf)
                    (Ξv ++ (β ~ abind_var_skl Qv') ++ Θ')).
    { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb).
      rewrite Heqκf. rewrite (msubst_compose_app ζ κf1 κf2).
      apply a_inc_equiv_mid_insert_var_skl;
        [ exact HdeclsΞ | exact Huq'
        | rewrite dom_msubst_compose; exact Hdκa
        | rewrite dom_msubst_compose; exact Hdκf1
        | exact Hmiddle | exact HsufΞv | ].
      rewrite Heqκ in Hie.
      rewrite (msubst_compose_app (aenv_msubst Θ) κa κb) in Hie.
      rewrite Heqκf in Hie.
      rewrite (msubst_compose_app ζ κf1 κf2) in Hie.
      exact Hie. }
    rewrite <- HeqΘ in Hmi.
    eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
    pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
      as Hself.
    simpl in Hself. apply Hself; eassumption. }
  {
    eapply ad_precise_downarrow_restore; eauto. }
Qed.
