Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo_decl.prop_precision.

Set Implicit Arguments.

Lemma tyequiv_mono_refine_syn : forall Θ Δ A A',
  {{ ⊢ Θ }}a ->
  mono_ptyp A -> mono_ptyp A' ->
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  {{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn A) ⊳ (ptyp_to_bskl_syn A') }}ad.
Proof.
  intros Θ Δ A A' Hwf HmA HmB Heq Hvis.
  assert (Hc : {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ (ptyp_to_bskl_syn A') }}ad)
    by (apply tyequiv_mono_consis; auto).
  apply ad_refine_syn_ghost_free_delta with (Δ0 := empty).
  2:{ unfold ptyp_to_bskl_syn. apply pskl_to_bskl_syn_ghost_free.
      apply ptyp_to_pskl_ghost_free. }
  replace (ptyp_to_bskl_syn A)
    with (pskl_to_bskl_inh (uskl_to_pskl (ptyp_to_uskl_syn A))).
  2:{ rewrite uskl_to_pskl_ptyp. apply ptyp_to_bskl_inh_syn_eq; auto. }
  eapply ad_pat_consis_refine_syn_mono;
    [ exact Hc | exact Hwf | apply mono_ptyp_to_bskl_syn; auto | | ].
  - clear. fsetdec.
  - intros β τ Hb. clear. fsetdec.
Qed.

Lemma consis_precise_core : forall Θ Δ ζ α Qb A,
  {{ ⊢ Θ }}a ->
  mono_ptyp (msubst_lookup ζ α) ->
  (forall α0, α0 `in` ftvar_in_ptyp (msubst_lookup ζ α) -> a_binds_tvar α0 Θ) ->
  mono_ptyp A ->
  Qb = ptyp_to_bskl_syn A ->
  {{ Θ ⊢ (msubst_lookup ζ α) ≡ᵗ A }}a ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb) }}ad.
Proof.
  intros Θ Δ ζ α Qb A Hwf HmA Hvis HmC HQb Heq.
  unfold ad_precise.

  replace (bskl_to_pskl (msubst_bskl ζ (bskl_var_f α)))
    with (ptyp_to_pskl (msubst_lookup ζ α)).
  2:{ change (msubst_bskl ζ (bskl_var_f α))
        with (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ζ α))).
      rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity. }
  rewrite (ptyp_to_bskl_inh_syn_eq HmA).

  subst Qb.
  rewrite (bskl_to_pskl_ptyp_to_bskl_syn A).
  rewrite (ptyp_to_bskl_inh_syn_eq HmC).
  apply tyequiv_mono_refine_syn; auto.
Qed.

Lemma a_inc_equiv_lookup_flex : forall Θ0 κ1 κ2 Θ,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  forall α, a_flex_tvar Θ0 α ->
  {{ Θ ⊢ (msubst_lookup κ1 α) ≡ᵗ (msubst_lookup κ2 α) }}a.
Proof.
  intros Θ0 κ1 κ2 Θ H; induction H; intros α0 Hflex.
  -
    destruct Hflex as [Hb | [τ Hb]]; inversion Hb.
  -
    simpl. destruct (α0 == α) as [->|Hne]; [ exact H0 | ].
    exact (IHa_inc_equiv α0 (proj1 (a_flex_tvar_cons_other _ _ Hne) Hflex)).
  -
    simpl. destruct (α0 == α) as [->|Hne]; [ exact H0 | ].
    exact (IHa_inc_equiv α0 (proj1 (a_flex_tvar_cons_other _ _ Hne) Hflex)).
  -
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds; apply in_or_app; right; simpl; right; exact Hby | ].
    exact (IHa_inc_equiv α0 (a_flex_tvar_cons_tm Hflex I)).
  -
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds; apply in_or_app; right; simpl; right; exact Hby | ].
    exact (IHa_inc_equiv α0 (a_flex_tvar_cons_tm Hflex I)).
  -
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds; apply in_or_app; right; simpl; right; exact Hby | ].
    exact (IHa_inc_equiv α0 (a_flex_tvar_strip_tvar Hflex)).
Qed.

Lemma a_inc_equiv_compose_id_at : forall Θ0 κ κ1 ζ Θ α,
  a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ ->
  a_flex_tvar Θ0 α ->
  α `in` dom κ1 ->
  msubst_lookup κ1 α = ptyp_var_f α ->
  {{ Θ ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup ζ α) }}a.
Proof.
  intros Θ0 κ κ1 ζ Θ α Hie Hflex Hdom Hid.
  pose proof (a_inc_equiv_lookup_flex Hie Hflex) as He.
  rewrite (msubst_lookup_compose ζ κ1 (or_introl Hdom)) in He.
  rewrite Hid in He. simpl in He.
  exact He.
Qed.

Lemma consis_precise_close : forall Θ0 Θ1 Θ Δ κ κ1 ζ α Qb A,
  {{ ⊢ Θ }}a ->
  a_flex_tvar Θ0 α ->
  a_binds_tvar α Θ1 ->
  ζ ∷ Θ1 ⊑ Θ ->
  {{ ⊢ Θ1 }}a ->
  a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ ->
  α `in` dom κ1 ->
  msubst_lookup κ1 α = ptyp_var_f α ->
  mono_ptyp A ->
  Qb = ptyp_to_bskl_syn A ->
  {{ Θ ⊢ (msubst_lookup κ α) ≡ᵗ A }}a ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb) }}ad.
Proof.
  intros Θ0 Θ1 Θ Δ κ κ1 ζ α Qb A
         Hwf Hflex HbΘ1 HζΘ Hwf1 Hie Hdom Hid HmC HQb HeqκαC.
  assert (Hζκ : {{ Θ ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup ζ α) }}a)
    by (eapply a_inc_equiv_compose_id_at; eauto).
  assert (HmζA : mono_ptyp (msubst_lookup ζ α))
    by (eapply a_inc_lookup_mono; exact HζΘ).
  assert (HvisζA : forall α0,
             α0 `in` ftvar_in_ptyp (msubst_lookup ζ α) -> a_binds_tvar α0 Θ).
  { intros α0 Hα0. eapply a_wf_ptyp_ftv_tvarish;
      [ eapply a_inc_lookup_wf; eauto | exact Hα0 ]. }
  eapply consis_precise_core with (A := A); eauto.
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact Hζκ | exact HeqκαC ].
Qed.

Lemma consis_precise_via_join : forall Θ0 Θ1 Θ Δ κ κ1 ζ α Qb,
  {{ ⊢ Θ }}a ->
  a_flex_tvar Θ0 α ->
  κ ∷ Θ0 ⊑ Θ ->
  a_binds_tvar α Θ1 ->
  ζ ∷ Θ1 ⊑ Θ ->
  {{ ⊢ Θ1 }}a ->
  a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ ->
  α `in` dom κ1 ->
  msubst_lookup κ1 α = ptyp_var_f α ->
  {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ (pskl_var_f α))) ∼ Qb }}ad ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb) }}ad.
Proof.
  intros Θ0 Θ1 Θ Δ κ κ1 ζ α Qb
         Hwf Hflex HκΘ HbΘ1 HζΘ Hwf1 Hie Hdom Hid Hjoin.
  assert (Hmκα : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact HκΘ).
  replace (msubst_pskl κ (pskl_var_f α))
    with (ptyp_to_pskl (msubst_lookup κ α)) in Hjoin by reflexivity.
  rewrite pskl_to_uskl_ptyp in Hjoin.
  destruct (consis_mono_join Hjoin Hwf (A := msubst_lookup κ α) eq_refl Hmκα)
    as [C [HmC [HQb HeqκαC]]].
  eapply consis_precise_close; eauto.
Qed.

Lemma consis_precise_via_refine : forall Θ0 Θ1 Θ Δ Δ1 κ κ1 ζ α Qb,
  {{ ⊢ Θ }}a ->
  a_flex_tvar Θ0 α ->
  κ ∷ Θ0 ⊑ Θ ->
  a_binds_tvar α Θ1 ->
  ζ ∷ Θ1 ⊑ Θ ->
  {{ ⊢ Θ1 }}a ->
  a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ ->
  α `in` dom κ1 ->
  msubst_lookup κ1 α = ptyp_var_f α ->
  {{ Θ ⨟ Δ1 ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f α))) ⊳ Qb }}ad ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb) }}ad.
Proof.
  intros Θ0 Θ1 Θ Δ Δ1 κ κ1 ζ α Qb
         Hwf Hflex HκΘ HbΘ1 HζΘ Hwf1 Hie Hdom Hid Hrs.
  assert (Hmκα : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact HκΘ).
  replace (msubst_pskl κ (pskl_var_f α))
    with (ptyp_to_pskl (msubst_lookup κ α)) in Hrs by reflexivity.
  rewrite (ptyp_to_bskl_inh_syn_eq Hmκα) in Hrs.
  destruct (refine_mono_join Hrs Hwf (A := msubst_lookup κ α) eq_refl Hmκα)
    as [C [HmC [HQb HeqκαC]]].
  eapply consis_precise_close; eauto.
Qed.
