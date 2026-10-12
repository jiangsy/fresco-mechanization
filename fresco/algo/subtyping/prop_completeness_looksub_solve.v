Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.prop_tag.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_mod_compat.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.consistency.prop_consis_precise.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_precise.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.subtyping.prop_rigid_substitution.
Require Import src.fresco.algo.subtyping.prop_solve_extension.
Require Import src.fresco.algo.subtyping.prop_completeness_solve_eq_var.

Set Implicit Arguments.

Require Import src.fresco.algo.subtyping.prop_completeness_lookeq_solve.
Require Import src.fresco.algo.subtyping.prop_completeness_solve_sub_var.

Lemma ftag_in_uskl_subst_lower : forall ψ α R,
  α `in` ftvar_in_uskl R ->
  ftag_in_uskl ψ [<=] ftag_in_uskl (subst_uskl_in_uskl ψ α R).
Proof.
  intros ψ α R; induction R;
    cbn [ftvar_in_uskl subst_uskl_in_uskl ftag_in_uskl]; intros Hin;
    try solve [ clear - Hin; exfalso; fsetdec
              | specialize (IHR Hin); clear - IHR; fsetdec ].
  -
    match goal with |- context [if ?c then _ else _] => destruct c end;
      [ clear; fsetdec | exfalso; clear - Hin n; fsetdec ].
  -
    destruct (AtomSetProperties.In_dec α (ftvar_in_uskl R1)) as [H1 | H1];
      [ specialize (IHR1 H1); clear - IHR1; fsetdec
      | assert (H2 : α `in` ftvar_in_uskl R2) by (clear - Hin H1; fsetdec);
        specialize (IHR2 H2); clear - IHR2; fsetdec ].
Qed.

Lemma msubst_uskl_syn_ftv_keep : forall κ α R,
  α `notin` dom κ ->
  α `in` ftvar_in_uskl R ->
  α `in` ftvar_in_uskl (msubst_uskl_syn κ R).
Proof.
  intros κ α R Hκ; induction R;
    cbn [ftvar_in_uskl msubst_uskl_syn]; intros Hin;
    try solve [ clear - Hin; exfalso; fsetdec
              | specialize (IHR Hin); clear - IHR; fsetdec ].
  -
    assert (Heq : α0 = α) by (clear - Hin; fsetdec); subst α0.
    rewrite (msubst_lookup_notin _ Hκ). rewrite ptyp_to_uskl_syn_var.
    cbn [ftvar_in_uskl]; clear; fsetdec.
  -
    destruct (AtomSetProperties.In_dec α (ftvar_in_uskl R1)) as [H1 | H1];
      [ specialize (IHR1 H1); clear - IHR1; fsetdec
      | assert (H2 : α `in` ftvar_in_uskl R2) by (clear - Hin H1; fsetdec);
        specialize (IHR2 H2); clear - IHR2; fsetdec ].
Qed.

Lemma a_looksub_all_flex_mono : forall Θ α m P P0 Ξ 𝒞,
  {{ Θ ⊢ P ≼[ α , m ] P0 ⤳ Ξ ⨾ 𝒞 }}a -> all_flex_mono Ξ.
Proof.
  intros Θ α m P P0 Ξ 𝒞 H; unfold all_flex_mono; induction H.
  - constructor.
  - constructor.
  - constructor.
  - eapply a_lookeq_all_flex_mono; eassumption.
  - assumption.
  - apply Forall_app; split;
      [ eapply a_lookeq_all_flex_mono; eassumption | assumption ].
  - assumption.
  - assumption.
Qed.

Inductive alpha_stack (α : atom) : pskl -> Prop :=
| ast_var : alpha_stack α (pskl_var_f α)
| ast_all : forall L P,
    (forall β, β `notin` L ->
       alpha_stack α (open_pskl_wrt_pskl P (pskl_var_f β))) ->
    alpha_stack α (pskl_all_syn P)
| ast_univ_ghost : forall P,
    alpha_stack α P -> alpha_stack α (pskl_univ_ghost P).

Lemma alpha_stack_subst_var : forall α P β γ,
  alpha_stack α P -> β <> α ->
  alpha_stack α (subst_pskl_in_pskl (pskl_var_f γ) β P).
Proof.
  intros α P β γ H; induction H; intros Hne; cbn.
  - destruct_if; [ exfalso; congruence | apply ast_var ].
  - apply ast_all with (L := L `union` singleton β).
    intros β1 Hβ1.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ1; fsetdec | apply lc_pskl_var_f ].
    apply H0; [ clear - Hβ1; solve_notin | exact Hne ].
  - apply ast_univ_ghost; apply IHalpha_stack; exact Hne.
Qed.

Lemma alpha_stack_all_of_one : forall α P β,
  alpha_stack α (open_pskl_wrt_pskl P (pskl_var_f β)) ->
  β <> α -> β `notin` ftvar_in_pskl P ->
  alpha_stack α (pskl_all_syn P).
Proof.
  intros α P β Hst Hne Hfr.
  apply ast_all with (L := add β (add α (ftvar_in_pskl P))).
  intros β1 Hβ1.

  rewrite (subst_pskl_in_pskl_intro β P (pskl_var_f β1)) by exact Hfr.
  apply alpha_stack_subst_var; assumption.
Qed.

Lemma alpha_stack_ftv : forall α P,
  alpha_stack α P -> α `in` ftvar_in_pskl P.
Proof.
  intros α P H; induction H; simpl.
  - clear; fsetdec.
  - pick fresh β for (L `union` singleton α).
    specialize (H0 β ltac:(clear - Fr; fsetdec)).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
    simpl in Hup.
    assert (Hne : α <> β) by (clear - Fr; fsetdec).
    clear - H0 Hup Hne; fsetdec.
  - exact IHalpha_stack.
Qed.

Definition looksub_solve_result
    (Θ0 Θ Θw : aenv) (κ : metasubst) (Δ Δρ Ψi Ψa : atoms)
    (ψa : uskl) (α : atom) (M : mode) (P P0 Pi : pskl) (L : atoms) : Prop :=
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
    {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
    all_flex_mono Ξs /\
    uniq Ξs /\
    keys κs = keys Ξs /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
    {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξc ++ Θ0) }}a /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
    (M = mode_tc ->
       ftvar_in_a_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                             `union` dom κ `union` def_ftv Θ
       \/ (alpha_stack α P /\ Ξc = nil /\ κc = nil
           /\ exists T, 𝒞 = a_cstr_sub M T :: nil)) /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞).

Lemma looksub_solve_identity :
  forall Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi L,
  {{ Θ0 ⊢ P ≼[ α , M ] P0 ⤳ nil ⨾ nil }}a ->
  {{ ⊢ Θ0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad ->
  @looksub_solve_result Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi L.
Proof.
  intros Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi L HLK HwfΘ0 HwfPi Hκ Hprec.
  exists nil, nil, nil, Pi, (@nil (atom * ptyp)), (@nil (atom * ptyp)).
  repeat split.
  - exact HLK.
  - simpl. apply a_solve_cstr__empty.
  - apply Forall_nil.
  - apply uniq_nil.
  - intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec.
  - apply Forall_nil.
  - simpl. exact HwfPi.
  - simpl. exact HwfΘ0.
  - simpl; clear; fsetdec.
  - apply Forall_nil.
  - simpl. exact Hκ.
  - simpl. apply a_inc_equiv_refl; exact Hκ.
  - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
  - simpl. exact Hprec.
  -  intros _; left; simpl; clear; fsetdec.
  -
    intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec.
Qed.

Lemma looksub_solve_single :
  forall Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi L T Ξs Pa κs,
  {{ Θ0 ⊢ P ≼[ α , M ] P0 ⤳ nil ⨾ (a_cstr_sub M T :: nil) }}a ->
  {{ Θ0 ⊩ (a_cstr_sub M T :: nil) ⨾ Pi ⤳ Ξs ⨾ Pa }}a ->
  all_flex_mono Ξs -> uniq Ξs -> keys κs = keys Ξs ->
  (forall α0, α0 `in` dom Ξs -> α0 `notin` L) ->
  Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  {{ (Ξs ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a ->
  {{ ⊢ Θ0 }}a -> κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad ->
  alpha_stack α P ->
  (forall α0, α0 `in` dom Ξs ->
     α0 `notin` ftvar_in_a_cstrs (a_cstr_sub M T :: nil)) ->
  @looksub_solve_result Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi L.
Proof.
  intros Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi L T Ξs Pa κs
    HLK HSolve Hfms Hus Hks Hfrs HFs Hmon HwfPa HwfΘ0 Hκ Hprec Hstk Hapart.
  exists (a_cstr_sub M T :: nil), nil, Ξs, Pa, (@nil (atom * ptyp)), κs.
  repeat split.
  - exact HLK.
  - exact HSolve.
  - exact Hfms.
  - exact Hus.
  - exact Hks.
  - exact Hfrs.
  - exact HFs.
  - exact HwfPa.
  - exact HwfΘ0.
  - cbn; clear; fsetdec.
  - apply Forall_nil.
  -
    apply a_inc_flex_prefix_build;
      [ exact Hfms | exact Hks
      | eapply forall_wf_mono_weaken; [ exact Hmon | exact HFs ]
      | exact Hκ ].
  - apply a_inc_equiv_refl; exact Hκ.
  - intros α0 Hα0; cbn in Hα0; clear - Hα0; fsetdec.
  - exact Hprec.
  -
    intros _; right.
    exact (conj Hstk (conj eq_refl (conj eq_refl (ex_intro _ T eq_refl)))).
  - exact Hapart.
Qed.

Lemma a_looksub_solve_complete_leaf :
  forall n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' Rsub α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  (forall α0, a_flex_tvar Θ0 α0 ->
     ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw) ->
  ftvar_in_uskl ψa [<=] dom Θw ->
  Δρ ∩ dom Θw [=] empty ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->
  Ψi `union` Ψa [=] Ψ' ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  ad_pat_sub_fuel n NM M Ψsub Θs Rsub Q ->
  {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl Rsub) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->

  uskl_rsubst NM Θ Δρ Ψρ Rsub
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ->
  Ψρ ∩ Ψ' [=] empty ->
  rsubst_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  (α `notin` ftvar_in_pskl P \/ P = pskl_var_f α) ->
  (forall x b, binds x b Θs -> binds x b Θ) ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
    {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
    all_flex_mono Ξs /\
    uniq Ξs /\
    keys κs = keys Ξs /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
    {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξc ++ Θ0) }}a /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
    (M = mode_tc ->
       ftvar_in_a_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                             `union` dom κ `union` def_ftv Θ
       \/ (alpha_stack α P /\ Ξc = nil /\ κc = nil
           /\ exists T, 𝒞 = a_cstr_sub M T :: nil)) /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞).
Proof.
  intros n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' Rsub α.
  intros HwfΘ HwfΘ0 HwfΘw Hmon Hnr Hκw Hψaw HΔρw
         HwfP0 HwfPi HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR
         HscopeR HlcR Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2
         Hsubty HwfSubj Hrefine Hrho HΨρ Hrfr HΔρΔ HΔρPi Hspecial Hext L HL.
  destruct Hspecial as [Hnin | Heqα].
  -
  { assert (Hκav : forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)).
      { intros p Hp. pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb.
        clear - HαΘ Hb; fsetdec. }
      assert (HαMS : α `notin` ftvar_in_uskl (msubst_uskl_syn κ R')).
      { rewrite <- ftvar_in_pskl_uskl_to_pskl.
        rewrite uskl_to_pskl_msubst_uskl_syn. rewrite HeraseR.
        apply msubst_pskl_ftv_avoid; [ exact Hκav | exact Hnin ]. }
      rewrite (subst_uskl_in_uskl_fresh_eq (msubst_uskl_syn κ R') ψa α HαMS)
        in Hrho.
      assert (HΨsR : Ψsub [<=] ftag_in_uskl Rsub)
        by (apply (ad_pat_sub_fuel_ftag_sub Hsubty)).
      pose proof (uskl_rsubst_ftag_sub Hrho) as Hftr.
      rewrite ftag_in_uskl_msubst_uskl_syn in Hftr.
      assert (HΨa0 : Ψa [=] empty)
        by (clear - HΨs2 HΨsR Hftr Hdisj Hsub HΨρ; fsetdec).

      apply (looksub_solve_identity Θw Δρ L).
      - apply a_looksub__absent; exact Hnin.
      - exact HwfΘ0.
      - exact HwfPi.
      - exact Hκ.
      - eapply ad_partial_precise_psi_cong;
          [ exact Hpre | clear - HΨa0; fsetdec ]. }
  -
    rewrite Heqα in HeraseR |- *.
  { assert (Hlk : msubst_lookup κ α = ptyp_var_f α).
    { apply msubst_lookup_notin.
      intro Hc. apply (a_inc_dom_sub Hκ) in Hc. contradiction. }
    assert (HR : R' = uskl_var_f α).
    { destruct R'; simpl in HeraseR; try discriminate HeraseR.
      injection HeraseR as ->. reflexivity. }
    subst R'.
    assert (Hms : msubst_uskl_syn κ (uskl_var_f α) = uskl_var_f α)
      by (cbn; rewrite Hlk; apply ptyp_to_uskl_syn_var).
    rewrite Hms in Hrho.
    assert (Hsubj : subst_uskl_in_uskl ψa α (uskl_var_f α) = ψa).
    { cbn. match goal with |- context [if ?c then _ else _] => destruct c end;
        [ reflexivity | contradiction ]. }
    rewrite Hsubj in Hrho.
    cbn in HΨs1.
    assert (Hsv : solve_sub_ext Θ0 Θw M Pi P0 L
                    (fun κ' Pa =>
                       {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa)
                         ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad)).
    { eapply a_solve_sub_complete_var
        with (Δρ := Δρ) (Ψρ := Ψρ) (ψsub := Rsub) (Ψsub := Ψsub)
             (Θs := Θs);
      [ exact HwfΘ | exact HwfΘ0
      | exact HwfΘw | exact Hmon | exact Hnr | exact Hκw | exact HΔρw
      | exact HwfPi | exact HwfP0
      | exact HmodSK | exact HmodTY | exact Hκ
      | exact Hrho
      | exact Htags | exact HwfSubj | exact Hsub | exact HΨρ
      | exact Hrfr
      | exact HΔρΔ
      | exact HΔρPi
      | exact Hdfresh | exact Hpre
      | clear - HΨs1; fsetdec | exact HΨs2
      | exact Hext | exact Hsubty | exact Hrefine | exact HL ]. }
    destruct Hsv as (Ξs & Pa & κs & Hsolve & Hfms & Hus & Hks & Hfrs & HFs
                     & HwfPa & Hprec).
    eapply (looksub_solve_single Δρ).
    - apply a_looksub__var.
    - apply a_solve_cstr__sub; exact Hsolve.
    - exact Hfms.
    - exact Hus.
    - exact Hks.
    - exact Hfrs.
    - exact HFs.
    - exact Hmon.
    -
      exact HwfPa.
    - exact HwfΘ0.
    - exact Hκ.
    - exact Hprec.
    -
      apply ast_var.
    -
      intros α0 Hα0. simpl.
      pose proof (a_wf_pskl_ftv_dom HwfP0) as Hfd. simpl in Hfd.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      pose proof (Hfrs α0 Hα0) as Hf.
      clear - Hfd Hds HL Hf. fsetdec. }
Qed.

Lemma looksub_solve_forall_l_close :
  forall Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi Lav R0 β,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  pskl_all_syn (uskl_to_pskl R0) = P ->
  β `notin` dom Θ -> β `notin` dom Θ0 -> β `notin` dom Θw ->
  β `notin` ftvar_in_uskl ψa -> β <> α ->
  β `notin` add α (ftvar_in_aenv Θ0 `union` ftvar_in_pskl (uskl_to_pskl R0)
                     `union` ftvar_in_pskl P0) ->
  @looksub_solve_result ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ)
    Θw κ (add β Δ) (add β Δρ) Ψi Ψa ψa α M
    (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) P0 Pi (add β Lav) ->
  @looksub_solve_result Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi Lav.
Proof.
  intros Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi Lav R0 β
    HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HeraseR HβΘ HβΘ0 HβΘw Hβψa Hβα Fr REC.
  unfold looksub_solve_result in REC |- *.
  assert (HPnα : P <> pskl_var_f α) by (rewrite <- HeraseR; discriminate).
  pose proof (uskl_to_pskl_open R0 β) as HeraseRβ.
    destruct REC as (𝒞 & Ξc & Ξs & Pa & κc & κs
                     & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
                     & HwfPa & HwfΞ & HαΞ
                     & Hmapfst & Himg & Hinc & Hinceq & Hκfresh
                     & Hprec & HftvC & HapartR).

    pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
    assert (HβΞc : β `notin` dom Ξc).
    { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
      apply Hκfresh. simpl; clear; fsetdec. }
    assert (HβC : β `notin` ftvar_in_a_cstrs 𝒞).
    {
      pose proof (a_wf_pskl_ftv_dom HwfP0) as Hpf.
      eapply a_looksub_ftv_ctx;
        [ exact HLK | simpl; clear; fsetdec
        | clear - Hpf HβΘ0; fsetdec | exact HβΞc ]. }
    assert (HβΞs : β `notin` dom Ξs)
      by (intro Hc; pose proof (Hfrs β Hc) as Hf; clear - Hf; fsetdec).
    assert (HβPa : β `notin` ftvar_in_pskl Pa).
    { intro Hin0.
      destruct (a_solve_cstr_ftv HSolve Hin0) as [Hl | Hr];
        [ pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi;
          clear - Hl Hfi HβC HβΘ0 HβΞs; fsetdec
        | apply Hr; repeat rewrite dom_app; simpl; clear; fsetdec ]. }
    assert (Hfmc : all_flex_mono Ξc)
      by (eapply a_looksub_all_flex_mono; exact HLK).
    destruct (solve_outputs_strip_tvar Hfms Hfmc Hks Hmapfst HFs Himg
                HβΘw Hβψa HβΘ HβPa HwfPa HwfΞ Hinc)
      as (HwfPa' & HwfΞ' & Hinc').
    destruct (pskl_ghost_dec P0) as [HP0h | HP0nh].
    {
      subst P0.
      destruct (a_looksub_ghost_target HLK) as [HΞc HC].
      assert (HSid : Ξs = nil /\ Pa = Pi).
      { destruct HC as [HCn | [_ HCv]]; rewrite HCn in HSolve || rewrite HCv in HSolve;
        inversion HSolve; subst;
          [ split; reflexivity
          | match goal with
            | Hs : {{ _ ⊢ₛ _ ≼[ _ ] pskl_ghost ⤳ _ ⨾ _ }}a |- _ =>
                destruct (a_solve_sub_ghost_target_inv Hs) as [Hn1 Hn2]
            end; split; assumption ]. }
      destruct HSid as [HΞs HPa].
      assert (Hκcn : κc = nil) by
        (rewrite HΞc in Hmapfst; destruct κc as [ | pc κc' ];
           [ reflexivity | cbn in Hmapfst; discriminate Hmapfst ]).
      assert (Hκsn : κs = nil) by
        (rewrite HΞs in Hks; destruct κs as [ | ps κs' ];
           [ reflexivity | cbn in Hks; discriminate Hks ]).
      subst Ξc Ξs Pa κc κs.
      apply (looksub_solve_identity Θw Δρ Lav).
      --
         apply a_looksub__vacuous; exact HPnα.
      -- exact HwfΘ0.
      -- exact HwfPi.
      -- exact Hκ.
      --
         simpl in Hprec.
         eapply ad_partial_precise_delta_shrink with (Δ := Δ);
           [ eapply ad_partial_precise_strengthen_tvar; exact Hprec
           | clear; fsetdec ]. }
    rewrite HeraseRβ in HLK.
    assert (HSolve0 : {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a)
      by (eapply a_solve_cstr_strip_tvar_mid; exact HSolve).
    assert (HPaSc : ftvar_in_pskl Pa
                      [<=] dom Ξs `union` ftvar_in_aenv (Ξc ++ Θ0)).
    { pose proof (a_wf_pskl_ftv_dom HwfPa) as Hd.
      pose proof (dom_subset_ftvar_in_aenv Ξc) as Hdc.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
      rewrite ftvar_in_aenv_app.
      rewrite ! dom_app in Hd. simpl in Hd.
      clear - Hd Hdc Hd0 HβPa; fsetdec. }
    edestruct a_looksub_solve_forall_l_mode
      as [𝒞r [HLKr [HSolver [Hd𝒞 Hapr]]]];
      [ exact HLK | exact HSolve0 | exact HP0nh
      | clear - Fr; solve_notin | exact Hfms | exact HPaSc
      | exact HapartR | ].
    exists 𝒞r, Ξc, Ξs, Pa, κc, κs.
    repeat split.
    --
       rewrite <- HeraseR. exact HLKr.
    --  exact HSolver.
    --  exact Hfms.
    --  exact Hus.
    --  exact Hks.
    --
       intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
    --  exact HFs.
    --  exact HwfPa'.
    --  exact HwfΞ'.
    --  exact HαΞ.
    --  exact Hmapfst.
    --  exact Himg.
    --  exact Hinc'.
    --  apply a_inc_equiv_refl; exact Hκ.
    --
       intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
       clear - Hκfresh; fsetdec.
    --
       eapply ad_partial_precise_delta_shrink with (Δ := Δ);
         [ eapply ad_partial_precise_strengthen_tvar; exact Hprec
         | clear; fsetdec ].
    --
       intros HMtc.
       destruct Hd𝒞 as [ -> | (HQvar & HΞn & T & T' & HT & HT') ].
       ++
          destruct (HftvC HMtc) as [Hleft | (Hstk & -> & -> & (Tc & ->))].
          ** left. cbn [def_ftv] in Hleft. exact Hleft.
          ** right. repeat split; try reflexivity.
             --- rewrite <- HeraseR. cbn [uskl_to_pskl].
                 rewrite HeraseRβ in Hstk.
                 eapply alpha_stack_all_of_one;
                   [ exact Hstk | clear - Hβα; auto | clear - Fr; solve_notin ].
             --- exists Tc; reflexivity.
       ++
          right. repeat split.
          ** rewrite <- HeraseR. cbn [uskl_to_pskl]. rewrite HQvar.
             apply ast_all with (L := empty). intros β1 _.
             unfold open_pskl_wrt_pskl; cbn. apply ast_var.
          ** exact HΞn.
          ** rewrite HΞn in Hmapfst.
             destruct κc as [ | pc κc' ];
               [ reflexivity | cbn in Hmapfst; discriminate Hmapfst ].
          ** exists T'; exact HT'.
    --
       exact Hapr.
Qed.

Lemma looksub_solve_univ_ghost_l_close :
  forall Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P Pbody P0 Pi Lav,
  pskl_univ_ghost Pbody = P ->
  @looksub_solve_result Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M Pbody P0 Pi Lav ->
  @looksub_solve_result Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi Lav.
Proof.
  intros Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P Pbody P0 Pi Lav HeraseR REC.
  unfold looksub_solve_result in REC |- *.
  assert (HPnα : P <> pskl_var_f α) by (rewrite <- HeraseR; discriminate).
  destruct REC as (𝒞 & Ξc & Ξs & Pa & κc & κs
                     & Hlook & Hsolve0 & Hfms0 & Hus0 & Hks0 & Hfrs0 & HFs0
                     & HwfPa0 & HwfΞ0
                     & HαΞ0 & Hkeys0 & Himg0 & Hinc0 & Hinceq0
                     & Hκf0 & Hprec0 & HftvC0 & HapartR).
  destruct (pskl_ghost_dec P0) as [HP0h | HP0nh].
  { subst P0.
    destruct (a_looksub_ghost_target Hlook) as [HΞn HCn].
    assert (HSid : Ξs = nil /\ Pa = Pi).
    { destruct HCn as [HCe | [_ HCe]]; rewrite HCe in Hsolve0;
      inversion Hsolve0; subst;
        [ split; reflexivity
        | match goal with
          | Hs : {{ _ ⊢ₛ _ ≼[ _ ] pskl_ghost ⤳ _ ⨾ _ }}a |- _ =>
              destruct (a_solve_sub_ghost_target_inv Hs) as [Hn1 Hn2]
          end; split; assumption ]. }
    destruct HSid as [HΞs HPa].
    assert (Hκcn : κc = nil) by
      (rewrite HΞn in Hkeys0; destruct κc as [ | pc κc' ];
         [ reflexivity | cbn in Hkeys0; discriminate Hkeys0 ]).
    assert (Hκsn : κs = nil) by
      (rewrite HΞs in Hks0; destruct κs as [ | ps κs' ];
         [ reflexivity | cbn in Hks0; discriminate Hks0 ]).
    subst Ξc Ξs Pa κc κs.
    apply (looksub_solve_identity Θw Δρ Lav).
    - apply a_looksub__vacuous; exact HPnα.
    - exact HwfΞ0.
    - exact HwfPa0.
    - exact Hinc0.
    - exact Hprec0. }
  assert (HPaSc : ftvar_in_pskl Pa
                    [<=] dom Ξs `union` ftvar_in_aenv (Ξc ++ Θ0)).
  { pose proof (a_wf_pskl_ftv_dom HwfPa0) as Hd.
    pose proof (dom_subset_ftvar_in_aenv Ξc) as Hdc.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
    rewrite ftvar_in_aenv_app.
    rewrite ! dom_app in Hd.
    clear - Hd Hdc Hd0; fsetdec. }
  edestruct a_looksub_solve_univ_ghost_l_mode
    as [𝒞r [Hlookr [Hsolver [Hd𝒞 Hapr]]]];
    [ exact Hlook | exact Hsolve0 | exact HP0nh
    | exact Hfms0 | exact HPaSc | exact HapartR | ].
  exists 𝒞r, Ξc, Ξs, Pa, κc, κs.
  repeat split; try assumption;
    [ rewrite <- HeraseR; exact Hlookr
    | intros HMtc;
      destruct Hd𝒞 as [ -> | (HQvar & HΞn & T & T' & HT & HT') ];
        [ destruct (HftvC0 HMtc) as [Hleft | (Hstk & -> & -> & (Tc & ->))];
            [ left; exact Hleft
            | right; repeat split; try reflexivity;
              [ rewrite <- HeraseR; cbn [uskl_to_pskl];
                apply ast_univ_ghost; exact Hstk
              | exists Tc; reflexivity ] ]
        | right; repeat split;
            [ rewrite <- HeraseR; rewrite HQvar;
              apply ast_univ_ghost; apply ast_var
            | exact HΞn
            | rewrite HΞn in Hkeys0;
              destruct κc as [ | pc κc' ];
                [ reflexivity | cbn in Hkeys0; discriminate Hkeys0 ]
            | exists T'; exact HT' ] ] ].
Qed.

Definition looksub_solve_motive (Θw : aenv) (Ψ' : atoms) (ψa : uskl) (α : atom)
    (NM : a_sub_mode) (M : mode) (Ψsub : atoms) (Θs : aenv) (Rsub : uskl)
    (Q : bskl) : Prop :=
  forall Θ Θ0 κ Δ Δρ Ψρ R' P P0 Pi Ψi Ψa,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  (forall α0, a_flex_tvar Θ0 α0 ->
     ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw) ->
  Δρ ∩ dom Θw [=] empty ->
  α `notin` dom Θ0 -> κ ∷ Θ0 ⊑ Θ -> α `notin` dom κ ->
  (forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)) ->
  ⌊ R' ⌋ˢ = P ->
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  α `notin` dom Θ ->
  Ψi `union` Ψa [=] Ψ' ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  lc_bskl Q ->
  uskl_rsubst NM Θ Δρ Ψρ Rsub
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ->
  Ψρ ∩ Ψ' [=] empty ->
  rsubst_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi) ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  (forall x b, binds x b Θs -> binds x b Θ) ->
  {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl Rsub) }}a ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  @looksub_solve_result Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi L.

Inductive uskl_forall_of : uskl -> uskl -> Prop :=
| uskl_forall_of__syn : forall R, uskl_forall_of (uskl_all_syn R) R
| uskl_forall_of__tag : forall ε R, uskl_forall_of (uskl_all_tag ε R) R.

Lemma uskl_forall_of_erase : forall S R,
  uskl_forall_of S R -> ⌊ S ⌋ˢ = pskl_all_syn ⌊ R ⌋ˢ.
Proof. intros S R H; destruct H; reflexivity. Qed.

Lemma uskl_forall_of_ftag : forall S R,
  uskl_forall_of S R -> ftag_in_uskl R [<=] ftag_in_uskl S.
Proof. intros S R H; destruct H; cbn [ftag_in_uskl]; fsetdec. Qed.

Lemma uskl_forall_of_ftv : forall S R,
  uskl_forall_of S R -> ftvar_in_uskl S [=] ftvar_in_uskl R.
Proof. intros S R H; destruct H; cbn [ftvar_in_uskl]; fsetdec. Qed.

Lemma uskl_forall_of_lc_body : forall S R β,
  uskl_forall_of S R -> lc_uskl S ->
  lc_uskl (open_uskl_wrt_uskl R (uskl_var_f β)).
Proof. intros S R β H Hlc; destruct H; inversion Hlc; auto. Qed.

Lemma uskl_forall_of_subst_msubst : forall ψ α κ S R,
  uskl_forall_of S R ->
  uskl_forall_of (subst_uskl_in_uskl ψ α (msubst_uskl_syn κ S))
                 (subst_uskl_in_uskl ψ α (msubst_uskl_syn κ R)).
Proof. intros ψ α κ S R H; destruct H; constructor. Qed.

Lemma uskl_rsubst_forall_of_r_inv : forall NM Θ Δρ Ψρ S T Tb,
  uskl_rsubst NM Θ Δρ Ψρ S T ->
  uskl_forall_of T Tb ->
  exists L Sb, uskl_forall_of S Sb /\
    forall α, α `notin` L ->
      uskl_rsubst NM Θ Δρ Ψρ (open_uskl_wrt_uskl Sb (uskl_var_f α))
                          (open_uskl_wrt_uskl Tb (uskl_var_f α)).
Proof.
  intros NM Θ Δρ Ψρ S T Tb H HT; destruct HT.
  - destruct (uskl_rsubst_all_syn_r_inv H) as (L & Sb & -> & Hfam).
    exists L, Sb; split; [ constructor | exact Hfam ].
  - destruct (uskl_rsubst_all_tag_r_inv H) as (L & Sb & -> & Hfam).
    exists L, Sb; split; [ constructor | exact Hfam ].
Qed.

Lemma uskl_forall_of_body_eq : forall S R R0,
  uskl_forall_of S R -> uskl_forall_of S R0 -> R = R0.
Proof. intros S R R0 H H0; destruct H; inversion H0; reflexivity. Qed.

Lemma looksub_solve_forall_l_step :
  forall Θw Ψ' ψa α NM M n Ψ Ψg Θs ψ Q Rall R,
  {{ ⊢ Θw }}a -> ftvar_in_uskl ψa [<=] dom Θw ->
  a_tags_sort NM Ψ' ψa ->
  ad_pat_sub_fuel (S n) NM M Ψ Θs Rall Q ->
  ad_pat_sub_fuel n NM M (Ψ `union` Ψg) Θs (open_uskl_wrt_uskl R ψ) Q ->
  looksub_solve_motive Θw Ψ' ψa α NM M (Ψ `union` Ψg) Θs
    (open_uskl_wrt_uskl R ψ) Q ->
  Ψg ∩ ftag_in_uskl Rall [=] empty ->
  a_tags_sort NM Ψg ψ ->
  {{ Θs ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a ->
  uskl_forall_of Rall R ->
  looksub_solve_motive Θw Ψ' ψa α NM M Ψ Θs Rall Q.
Proof.
  intros Θw Ψ' ψa α NM M n Ψ Ψ'0 Θsm ψ Q S R
         HwfΘw Hψaw Htags Hderiv Hsubty IH H1 H2 H3 HS
         Θ Θ0 κ Δ Δρ Ψρ R' P P0 Pi Ψi Ψa
         HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw HαΘ0 Hκ Hακdom Hκav HeraseR HscopeR
         HlcR Hdisj HwfP0 HwfPi HmodSK HmodTY HαΘ Hsub HΨs1 HΨs2 Hdfresh Hpre
         Hrefine HlcQ Hrho HΨρ Hrfr HΔρΔ HΔρftv HΔρPi Hext HwfSubj Hψaap
         Lav HLav.

  assert (Hleaf : α `notin` ftvar_in_pskl P \/ P = pskl_var_f α ->
            @looksub_solve_result Θ0 Θ Θw κ Δ Δρ Ψi Ψa ψa α M P P0 Pi Lav).
  { intros Hcase. eapply a_looksub_solve_complete_leaf; eassumption. }
  destruct (pskl_eq_var_dec P α) as [Heqα | HPnα].
  { exact (Hleaf (or_intror Heqα)). }
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P)) as [Hin | Hnin].
  - assert (HαR : α `in` ftvar_in_uskl R')
      by (rewrite <- HeraseR, ftvar_in_pskl_uskl_to_pskl in Hin; exact Hin).
    assert (HRnv : forall β, R' <> uskl_var_f β).
    { intros β Heq; subst R'; cbn in HαR.
      assert (Heqβ : β = α) by (clear - HαR; fsetdec); subst β.
      cbn in HeraseR; contradiction (HPnα (eq_sym HeraseR)). }
    assert (HR'all : exists R0, uskl_forall_of R' R0).
    { destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
        cbn in Hrho, HαR;
        try solve [ contradiction (HRnv _ eq_refl) | clear - HαR; fsetdec
                  | destruct HS; inversion Hrho ];
        eexists; constructor. }
    destruct HR'all as (R0 & HR').
    destruct (uskl_rsubst_forall_of_r_inv Hrho
                (uskl_forall_of_subst_msubst ψa α κ HR'))
      as (Lρ & Rb0 & HSb & Hfam).
    rewrite <- (uskl_forall_of_body_eq HS HSb) in Hfam.
    rewrite (uskl_forall_of_erase HR') in HeraseR.
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
    assert (HΨ'sub : Ψ' [<=] ftag_in_uskl S).
    { pose proof (uskl_rsubst_ftag_target_sub Hrho) as Ht.
      pose proof (@ftag_in_uskl_subst_lower ψa α (msubst_uskl_syn κ R')
                    (@msubst_uskl_syn_ftv_keep κ α R' Hακdom HαR)) as Hl.
      clear - Ht Hl Hψatag; fsetdec. }
    assert (HΨgfresh : Ψ'0 ∩ Ψ' [=] empty) by (clear - H1 HΨ'sub; fsetdec).

    assert (Hwfψ : {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a)
      by (eapply a_wf_pskl_weaken; [ exact Hext | exact H3 ]).
    assert (Hlcψ : lc_uskl ψ)
      by (apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact Hwfψ).
    assert (Hlcψa : lc_uskl ψa)
      by (apply is_dskl_lc; inversion Htags; assumption).
    pick fresh β for
      (Lρ `union` dom Θ `union` dom Θ0 `union` dom κ `union` Δ `union` Δρ
         `union` def_ftv Θ `union` singleton α `union` ftvar_in_uskl R
         `union` ftvar_in_uskl R0 `union` ftvar_in_uskl ψ
         `union` ftvar_in_uskl ψa `union` ftvar_in_pskl P0
         `union` ftvar_in_pskl Pi `union` ftvar_in_pskl (uskl_to_pskl R0)

         `union` ftvar_in_aenv Θ0).
    assert (HβΘ : β `notin` dom Θ) by (clear - Fr; solve_notin).
    assert (HβΘ0 : β `notin` dom Θ0) by (clear - Fr; solve_notin).
    assert (Hβκ : β `notin` dom κ) by (clear - Fr; solve_notin).
    assert (HβΔ : β `notin` Δ) by (clear - Fr; solve_notin).
    assert (HβΔρ : β `notin` Δρ) by (clear - Fr; solve_notin).
    assert (HβR : β `notin` ftvar_in_uskl R) by (clear - Fr; solve_notin).
    assert (Hβψa : β `notin` ftvar_in_uskl ψa) by (clear - Fr; solve_notin).
    assert (Hβα : β <> α) by (clear - Fr; solve_notin).
    assert (HβL : β `notin` Lρ) by (clear - Fr; solve_notin).
    destruct (@uskl_rsubst_subst NM Θ Δρ Ψρ
                (open_uskl_wrt_uskl R (uskl_var_f β))
                (open_uskl_wrt_uskl
                   (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R0))
                   (uskl_var_f β))
                (Hfam β HβL)
                β ψ Ψ'0 H2 Hwfψ Hlcψ HβΘ HβΔρ)
      as (Ψρ' & HΨρ'sub & HΨρ'mono & _ & Hrho').
    rewrite <- (@subst_uskl_in_uskl_intro β R ψ) in Hrho'; [ | exact HβR ].
    rewrite <- (@subst_msubst_uskl_syn_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa)
      in Hrho'.

    destruct (solve_context_open_tvar
                HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 Hβα HβΘ HβΘ0)
      as (Hweak0 & Hweak & Hwfβ & Hwfβ0 & HαΘβ & HαΘ0β & Hκβ
          & HwfP0β & HwfPiβ).
    assert (HscopeRβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
              [<=] add α (dom ((β ~ abind_tvar) ++ Θ0)
                            `union` dom ((β ~ abind_tvar) ++ Θ))).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β))
        as Hup.
      pose proof (uskl_forall_of_ftv HR') as Hftv.
      simpl in Hup |- *. clear - Hup Hftv HscopeR; fsetdec. }
    assert (HlcR0β : lc_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
      by (eapply uskl_forall_of_lc_body; eassumption).
    assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
              ∩ Ψ' [=] empty).
    { rewrite ftag_in_uskl_open_var.
      pose proof (uskl_forall_of_ftag HR') as Hftag. clear - Hdisj Hftag; fsetdec. }
    assert (HΨs1β : (Ψ `union` Ψ'0)
              [<=] union (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                     (union Ψρ' Ψa)).
    {
      rewrite ftag_in_uskl_open_var.
      pose proof (ad_pat_sub_fuel_ftag_sub Hsubty) as Hs.
      pose proof (uskl_rsubst_ftag_sub Hrho') as Hr.
      pose proof (@ftag_in_uskl_subst_uskl_in_uskl ψa α
                    (msubst_uskl_syn κ
                       (open_uskl_wrt_uskl R0 (uskl_var_f β)))) as Hb.
      pose proof (ftag_in_uskl_msubst_uskl_syn κ
                    (open_uskl_wrt_uskl R0 (uskl_var_f β))) as Hm.
      pose proof (ftag_in_uskl_open_var R0 β) as Hop.
      clear - Hs Hr Hb Hm Hop HΨs1 Hdisj Hψatag HΨgfresh HΨρ'mono; fsetdec. }
    assert (HΨs2β : Ψa [<=] Ψ `union` Ψ'0) by (clear - HΨs2; fsetdec).
    assert (Hdfreshβ : delta_def_fresh (add β Δ) ((β ~ abind_tvar) ++ Θ))
      by (eapply delta_def_fresh_open_tvar; eassumption).
    assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ)
              ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad)
      by (eapply ad_partial_precise_open_tvar_fresh; eassumption).
    assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad)
      by (eapply ad_refine_syn_weaken; [ exact Hrefine | exact Hweak ]).
    assert (Hrhoβ : uskl_rsubst NM ((β ~ abind_tvar) ++ Θ) (add β Δρ) Ψρ'
              (open_uskl_wrt_uskl R ψ)
              (subst_uskl_in_uskl ψa α
                 (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β)))))
      by (eapply uskl_rsubst_weaken; [ exact Hrho' | exact Hweak ]).
    assert (HΨρβ : Ψρ' ∩ Ψ' [=] empty)
      by (clear - HΨρ'sub HΨρ HΨgfresh; fsetdec).
    assert (Hrfrβ : rsubst_fresh (add β Δρ) ((β ~ abind_tvar) ++ Θ) κ)
      by (eapply rsubst_fresh_open_tvar; eassumption).
    assert (HΔρΔβ : add β Δρ [<=] add β Δ) by (clear - HΔρΔ; fsetdec).
    assert (HΔρftvβ : forall α0, α0 `in` (add β Δρ) ->
              α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi).
    { intros α0 Hα0.
      destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin1 | Hni1];
        [ exact (HΔρftv α0 Hin1) | ].
      assert (Heqβ : α0 = β) by (clear - Hα0 Hni1; fsetdec); subst α0.
      clear - Fr; solve_notin. }
    assert (HΔρPiβ : forall α0, α0 `in` (add β Δρ) ->
              α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)).
    { intros α0 Hα0.
      destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin1 | Hni1];
        [ exact (HΔρPi α0 Hin1) | ].
      assert (Heqβ : α0 = β) by (clear - Hα0 Hni1; fsetdec); subst α0.
      pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi)) as Hsh.
      enough (Hne : β `notin` ftvar_in_pskl (msubst_pskl κ Pi))
        by (clear - Hsh Hne; fsetdec).
      apply msubst_pskl_ftv_avoid;
        [ intros pp Hpp;
          pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb;
          clear - Hb HβΘ; fsetdec
        | clear - Fr; solve_notin ]. }
    assert (Hextβ : forall (x : atom) (b : abind),
              binds x b Θsm -> binds x b ((β ~ abind_tvar) ++ Θ))
      by (intros x b Hb; apply binds_app_3; apply Hext; exact Hb).

    assert (HwfSubjβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty
              ⊢ₚₛ ⌊ open_uskl_wrt_uskl R ψ ⌋ˢ }}a).
    { rewrite (uskl_forall_of_erase HS) in HwfSubj. inversion HwfSubj; subst.
      rewrite uskl_to_pskl_open_gen.
      eapply a_wf_pskl_weaken; [ exact Hweak | ].
      eapply a_wf_pskl_open; [ eassumption | exact Hwfψ ]. }
    destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HβΘ)
      as (HβΘw & Hmonβ & Hnrβ & Hκwβ).
    assert (HΔρwβ : (add β Δρ) ∩ dom Θw [=] empty)
      by (clear - HΔρw HβΘw; fsetdec).
    assert (HLavβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β Lav)
      by (rewrite ftvar_in_aenv_cons_tvar; clear - HLav; fsetdec).
    assert (Hψaapβ : (ftvar_in_uskl ψa) ∩ (add β Δρ) [=] empty)
      by (clear - Hψaap Hβψa; solve_notin_auto).
    eapply looksub_solve_forall_l_close with (Δρ := Δρ);
      [ exact HwfΘ | exact HwfΘ0 | exact HwfP0 | exact HwfPi | exact Hκ
      | exact HeraseR | exact HβΘ | exact HβΘ0 | exact HβΘw | exact Hβψa
      | exact Hβα | clear - Fr; solve_notin | ].
    exact (IH ((β ~ abind_tvar) ++ Θ) ((β ~ abind_tvar) ++ Θ0) κ (add β Δ)
              (add β Δρ) Ψρ' (open_uskl_wrt_uskl R0 (uskl_var_f β))
              ⌊ open_uskl_wrt_uskl R0 (uskl_var_f β) ⌋ˢ P0 Pi Ψi Ψa
              Hwfβ Hwfβ0 Hmonβ Hnrβ Hκwβ HΔρwβ
              HαΘ0β Hκβ Hακdom Hκav eq_refl HscopeRβ
              HlcR0β Hdisjβ HwfP0β HwfPiβ HmodSK HmodTY HαΘβ Hsub
              HΨs1β HΨs2β Hdfreshβ Hpreβ Hrefβ HlcQ Hrhoβ HΨρβ
              Hrfrβ HΔρΔβ HΔρftvβ HΔρPiβ Hextβ HwfSubjβ

              Hψaapβ (add β Lav) HLavβ).
  - exact (Hleaf (or_introl Hnin)).
Qed.

Theorem a_looksub_solve_complete_gen :
  forall n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' Rsub α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  (forall α0, a_flex_tvar Θ0 α0 ->
     ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw) ->
  ftvar_in_uskl ψa [<=] dom Θw ->
  Δρ ∩ dom Θw [=] empty ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->
  Ψi `union` Ψa [=] Ψ' ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  ad_pat_sub_fuel n NM M Ψsub Θs Rsub Q ->
  {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl Rsub) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  lc_bskl Q ->

  uskl_rsubst NM Θ Δρ Ψρ Rsub
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ->
  Ψρ ∩ Ψ' [=] empty ->
  rsubst_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi) ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  (forall x b, binds x b Θs -> binds x b Θ) ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
    {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
    all_flex_mono Ξs /\
    uniq Ξs /\
    keys κs = keys Ξs /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
    {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξc ++ Θ0) }}a /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
    (M = mode_tc ->
       ftvar_in_a_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                             `union` dom κ `union` def_ftv Θ
       \/ (alpha_stack α P /\ Ξc = nil /\ κc = nil
           /\ exists T, 𝒞 = a_cstr_sub M T :: nil)) /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞).
Proof.
  intros n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' Rsub α.
  intros HwfΘ HwfΘ0 HwfΘw Hmon Hnr Hκw Hψaw HΔρw
         HwfP0 HwfPi HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR
         HscopeR HlcR Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2
         Hsubty HwfSubj Hrefine HlcQ Hrho HΨρ Hrfr HΔρΔ HΔρftv HΔρPi Hext Hψaap
         L HL.
  pose proof Hsubty as Hderiv.
  assert (Hακdom : α `notin` dom κ)
    by (intro Hc; apply (a_inc_dom_sub Hκ) in Hc; contradiction).
  assert (Hκav : forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)).
  { intros p Hp. pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb.
    clear - HαΘ Hb; fsetdec. }
  revert Θ Θ0 κ Δ Δρ Ψρ R' P P0 Pi Ψi Ψa
         HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
         HαΘ0 Hκ Hακdom Hκav HeraseR HscopeR HlcR Hdisj
         HwfP0 HwfPi HmodSK HmodTY HαΘ Hsub HΨs1 HΨs2 Hdfresh Hpre
         Hrefine HlcQ Hrho HΨρ Hrfr HΔρΔ HΔρftv HΔρPi Hext
         HwfSubj Hψaap L HL.
  revert Hderiv.
  induction Hsubty; intros Hderiv
    Θe Θ0 κ Δ Δρ Ψρ R' P'' P0 Pi Ψi Ψa
    HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
    HαΘ0 Hκ Hακdom Hκav HeraseR HscopeR HlcR Hdisj
    HwfP0 HwfPi HmodSK HmodTY HαΘ Hsub HΨs1 HΨs2 Hdfresh Hpre
    Hrefine HlcQ Hrho HΨρ Hrfr HΔρΔ HΔρftv HΔρPi Hext
    HwfSubj Hψaap Lav HLav;
    rename Θ into Θsm; rename Θe into Θ.
  all: destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P'')) as [Hin | Hnin];
    [ | eapply a_looksub_solve_complete_leaf;
        solve [ eassumption | left; exact Hnin ] ].
  all: destruct (pskl_eq_var_dec P'' α) as [Heqα | HPnα];
    [ eapply a_looksub_solve_complete_leaf;
        solve [ eassumption | right; exact Heqα ] | ].
  all: assert (HαR : α `in` ftvar_in_uskl R')
    by (rewrite <- HeraseR in Hin;
        rewrite ftvar_in_pskl_uskl_to_pskl in Hin; exact Hin).
  all: match goal with
       | Hx : forall x b, binds x b ?S -> binds x b _ |- _ =>
         repeat match goal with
         | H : {{ _ ⨟ S ⊢ˢ _ ∼ᵣ _ }}ad |- _ =>
             let H' := fresh "Hw" in
             pose proof (ad_consis_join_weaken H _ Hx) as H';
             clear H; rename H' into H
         | H : {{ _ ⨟ S ⊢ˢ _ ∼ _ }}ad |- _ =>
             let H' := fresh "Hw" in
             pose proof (ad_pat_consis_weaken H _ Hx) as H';
             clear H; rename H' into H
         | H : {{ S ⨟ _ ⊢ₚₛ _ }}a |- _ =>
             let H' := fresh "Hw" in
             pose proof (a_wf_pskl_weaken Hx H) as H';
             clear H; rename H' into H
         | H : binds _ _ S |- _ => apply Hx in H
         end
       end.
  all: assert (HRnv : forall β, R' <> uskl_var_f β);
    [ intros β Heq; subst R'; cbn in HαR;
      assert (Heqβ : β = α) by (clear - HαR; fsetdec); subst β;
      cbn in HeraseR; contradiction (HPnα (eq_sym HeraseR)) | ].
  -
    assert (HP0 : P0 = pskl_ghost).
    { destruct NM;
        [ pose proof (HmodTY eq_refl) as Hm
        | pose proof (HmodSK eq_refl) as Hm ];
        inversion Hm; reflexivity. }
    subst P0.
    apply (looksub_solve_identity Θw Δρ Lav).
    +
      apply a_looksub__vacuous; assumption.
    + exact HwfΘ0.
    + exact HwfPi.
    + exact Hκ.
    + assert (HΨae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
      eapply ad_partial_precise_psi_cong; [ exact Hpre | clear - HΨae; fsetdec ].
  -

    assert (HgfP0 : pskl_ghost_free P0)
      by (apply a_ty_mode_compat_tc_ghost_free; exact (HmodTY eq_refl)).
    assert (HgP0 : guarded_pskl P0).
    { pose proof (HmodTY eq_refl) as Hmod.
      inversion Hmod as [ | A HeqA | ]; subst.
      destruct A as [ | nA | αA | A1 A2 | A0 ]; cbn [ptyp_to_pskl] in *.
      - apply guarded_pskl__unit.
      - inversion HwfP0.
      - apply guarded_pskl__var.
      - exact (a_wf_pskl_arrow_guarded HwfP0).
      -
        exfalso.
        assert (HgQ : guarded_bskl (pskl_to_bskl_inh B))
          by (apply guarded_pskl_to_bskl_inh; exact H0).
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        destruct B; cbn [pskl_to_bskl_inh] in Hrefine, HgQ;
          try solve [ inversion HgQ ];
          inversion Hrefine; subst;
          solve [ eapply ad_refine_allinh_lhs_mono_absurd;
                    [ exact HwfΘ | eassumption | reflexivity | reflexivity
                    | eapply a_wf_aenv_binds_def_mono;
                        [ exact HwfΘ | eassumption ] ] ]. }
    assert (HgP : guarded_pskl P'').
    { rewrite <- HeraseR.
      destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
        cbn in Hrho |- *;
        try solve [ contradiction (HRnv _ eq_refl) | inversion HlcR
                  | inversion Hrho; subst; inversion H ].
      - apply guarded_pskl__unit.
      - inversion HlcR; subst.
        apply guarded_pskl__arrow; apply lc_uskl_to_pskl; assumption. }
    assert (Hsub' : Ψi `union` Ψa [<=] Ψ') by (clear - Hsub; fsetdec).
    destruct (@a_lookeq_solve_complete_gen
                (size_uskl R' + size_pskl P0)
                a_sub_mode_ty Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψ ψa (pskl_to_bskl_inh B)
                P'' P0 Pi R' α Θ Δρ Ψρ T
                (le_n _) HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0 HwfPi Hκ Hκw Hψaw
                HαΘ HαΘ0 HeraseR HscopeR HlcR Htags Hdisj Hsub' Hdfresh Hpre
                HΨs1 HΨs2 (ad_consis_join_consis H1) HlcQ HwfSubj Hrefine
                Hrho (fun x b Hb => Hb) HΨρ Hrfr HΔρΔ HΔρw HΔρftv HΔρPi
                Hψaap Lav HLav)
      as (𝒞 & Ξc & Ξs & Pa & κc & κs
          & Hlook & Hsolve & Hfms & Hus & Hks & Hfrs & HFs
          & HwfPa & HwfΞ & HαΞ & Hkeys
          & HFor & Hftv & Hinc & Heqv & Hκcfresh0 & Hprec & Hapart0).
    rename Hκcfresh0 into Hκcfresh.
    exists 𝒞, Ξc, Ξs, Pa, κc, κs.
    split;
      [ apply a_looksub__check;
          [ exact HgfP0 | exact HPnα | exact HgP | exact HgP0
          | exact Hlook ] | ].
    repeat split; try assumption.
    intros _; left; exact Hftv.
  -
    pose proof (HmodTY eq_refl) as Hmod.
    inversion Hmod as [ | A HeqA | ]; subst.
    destruct A as [ | nA | αA | A1 A2 | A0 ];
      cbn [ptyp_to_pskl] in HwfP0, Hrefine, Hpre, HΔρftv |- *.
    +
      exfalso; exact (proj1 (ad_refine_syn_msubst_guarded_not_all
                               HwfΘ Hκ guarded_pskl__unit Hrefine B) eq_refl).
    +  inversion HwfP0.
    +
      exfalso; exact (proj1 (ad_refine_syn_msubst_guarded_not_all
                               HwfΘ Hκ (guarded_pskl__var _) Hrefine B) eq_refl).
    +
      exfalso; exact (proj1 (ad_refine_syn_msubst_guarded_not_all HwfΘ Hκ
                               (a_wf_pskl_arrow_guarded HwfP0) Hrefine B) eq_refl).
    +
      cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
      inversion Hrefine; subst.
      match goal with Hr : forall α, α `notin` ?Lr -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
        rename Hr into Hrbody; remember Lr as Lr0 eqn:HeqLr; clear HeqLr end.
      inversion HwfP0; subst.
      match goal with Hw : forall α, α `notin` ?Lw -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
        rename Hw into Hw0body; remember Lw as Lw0 eqn:HeqLw; clear HeqLw end.
      pick fresh β for
        (L `union` Lr0 `union` Lw0 `union` dom Θ `union` dom Θ0
           `union` dom Θsm `union` dom κ `union` ftvar_in_uskl ψa
           `union` ftvar_in_uskl T `union` ftvar_in_pskl Pi
           `union` ftvar_in_uskl R' `union` ftvar_in_pskl ⌊ R' ⌋ˢ
           `union` ftvar_in_pskl (ptyp_to_pskl A0) `union` def_ftv Θ

           `union` ftvar_in_aenv Θ0
           `union` Δ `union` Δρ `union` singleton α).
      assert (HβΘ : β `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (HβΘ0 : β `notin` dom Θ0) by (clear - Fr; solve_notin).
      assert (Hβκ : β `notin` dom κ) by (clear - Fr; solve_notin).
      assert (Hβψa : β `notin` ftvar_in_uskl ψa) by (clear - Fr; solve_notin).
      assert (Hβα : β <> α) by (clear - Fr; solve_notin).
      assert (HβΔρ : β `notin` Δρ) by (clear - Fr; solve_notin).
      destruct (solve_context_open_tvar
                  HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 Hβα HβΘ HβΘ0)
        as (Hweak0 & Hweak & Hwfβ & Hwfβ0 & HαΘβ & HαΘ0β & Hκβ & _ & HwfPiβ).

      assert (HwfP0β : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                ⊢ₚₛ (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f β)) }}a).
      { eapply a_wf_pskl_delta_mono;
          [ apply (Hw0body β ltac:(clear - Fr; solve_notin))
          | intros ? _ Hine; clear - Hine; fsetdec ]. }
      assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ))
        by (eapply delta_def_fresh_weaken_tvar; eassumption).
      assert (Hrfrβ : rsubst_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ)
        by (apply rsubst_fresh_weaken_tvar; exact Hrfr).
      assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad)
        by (eapply ad_partial_precise_weaken; [ exact Hpre | exact Hweak ]).
      assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                (pskl_to_bskl_inh
                   (msubst_pskl κ (open_pskl_wrt_pskl (ptyp_to_pskl A0)
                                     (pskl_var_f β))))
                ⊳ (open_bskl_wrt_bskl B (bskl_var_f β)) }}ad).
      { rewrite (@msubst_pskl_open Θ0 κ Θ (ptyp_to_pskl A0) β Hκ Hβκ).
        rewrite pskl_to_bskl_inh_open.
        eapply ad_refine_syn_delta_mono;
          [ apply (Hrbody β ltac:(clear - Fr; solve_notin))
          | clear; fsetdec ]. }

      assert (Hrhoβ : uskl_rsubst a_sub_mode_ty ((β ~ abind_tvar) ++ Θ) Δρ Ψρ T
                (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')))
        by (eapply uskl_rsubst_weaken; [ exact Hrho | exact Hweak ]).
      assert (HΔρftvβ : forall α0, α0 `in` Δρ ->
                α0 `notin` ftvar_in_pskl
                     (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f β))
                   `union` ftvar_in_pskl Pi).
      { intros α0 Hα0. pose proof (HΔρftv α0 Hα0) as Hd0.
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                      (ptyp_to_pskl A0) (pskl_var_f β)) as Hup.
        cbn [ftvar_in_pskl] in Hd0, Hup.
        assert (Hβ0 : α0 <> β) by (intro Hc; subst; contradiction).
        clear - Hd0 Hup Hβ0; fsetdec. }
      assert (HscopeRβ : ftvar_in_uskl R'
                [<=] add α (dom ((β ~ abind_tvar) ++ Θ0)
                              `union` dom ((β ~ abind_tvar) ++ Θ)))
        by (simpl; clear - HscopeR; fsetdec).
      assert (HwfSubjβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ ⌊ T ⌋ˢ }}a)
        by (eapply a_wf_pskl_weaken; [ exact Hweak | exact HwfSubj ]).
      assert (Hextβ : forall (x : atom) (b : abind),
                binds x b ((β ~ abind_tvar) ++ Θsm) ->
                binds x b ((β ~ abind_tvar) ++ Θ)).
      { intros x b Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> ->] | Hb'];
          [ simpl; auto | apply binds_app_3; apply Hext; exact Hb' ]. }

      destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HβΘ)
        as (HβΘw & Hmonβ & Hnrβ & Hκwβ).
      assert (HLavβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β Lav)
        by (rewrite ftvar_in_aenv_cons_tvar; clear - HLav; fsetdec).
      assert (HβL : β `notin` L) by (clear - Fr; solve_notin).
      edestruct (H0 β HβL Htags (H β HβL)
                   ((β ~ abind_tvar) ++ Θ) ((β ~ abind_tvar) ++ Θ0) κ Δ Δρ Ψρ
                   R' ⌊ R' ⌋ˢ (open_pskl_wrt_pskl (ptyp_to_pskl A0)
                             (pskl_var_f β)) Pi Ψi Ψa
                   Hwfβ Hwfβ0 Hmonβ Hnrβ Hκwβ HΔρw
                   HαΘ0β Hκβ Hακdom Hκav eq_refl HscopeRβ HlcR
                   Hdisj HwfP0β HwfPiβ
                   ltac:(intro Hc; discriminate Hc)
                   ltac:(intros _; rewrite <- ptyp_to_pskl_open;
                         apply a_ty_mode_compat__tc)
                   HαΘβ Hsub HΨs1 HΨs2 Hdfreshβ Hpreβ Hrefβ ltac:(lc_tgt)
                   Hrhoβ HΨρ Hrfrβ HΔρΔ HΔρftvβ HΔρPi Hextβ
                   HwfSubjβ Hψaap (add β Lav) HLavβ)
        as (𝒞 & Ξc & Ξs & Pa & κc & κs
            & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
            & HwfPa & HwfΞ & HαΞ
            & Hmapfst & Himg & Hinc & Hinceq & Hκfresh
            & Hprec & HftvC & HapartR).
      assert (HβΞs : β `notin` dom Ξs)
        by (intro Hc; pose proof (Hfrs β Hc) as Hf; clear - Hf; fsetdec).
      pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
      assert (HβΞc : β `notin` dom Ξc).
      { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
        apply Hκfresh. simpl; clear; fsetdec. }
      assert (Hfmc : all_flex_mono Ξc)
        by (eapply a_looksub_all_flex_mono; exact HLK).

      destruct (HftvC eq_refl) as [Hleft | (Hstk & -> & -> & (Tc & ->))].
      *
        assert (HβC : β `notin` ftvar_in_a_cstrs 𝒞).
        { cbn [def_ftv] in Hleft. pose proof (def_ftv_dom HwfΘ) as Hdf.
          clear - Hleft HβΞc Hβκ Hβψa HβΘ Hdf; fsetdec. }
        assert (HβPa : β `notin` ftvar_in_pskl Pa).
        {
          intro Hin0.
          destruct (a_solve_cstr_ftv HSolve Hin0) as [Hl | Hr];
            [ pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi;
              clear - Hl Hfi HβC HβΘ0 HβΞs; fsetdec
            | apply Hr; repeat rewrite dom_app; simpl; clear; fsetdec ]. }
        destruct (solve_outputs_strip_tvar Hfms Hfmc Hks Hmapfst HFs Himg
                    HβΘw Hβψa HβΘ HβPa HwfPa HwfΞ Hinc)
          as (HwfPa' & HwfΞ' & Hinc').
        exists 𝒞, Ξc, Ξs, Pa, κc, κs.
        repeat split.
        --

           apply a_looksub_forall_r_adm with (β := β);
             [ exact (ptyp_to_pskl_ghost_free (ptyp_all A0))
             |
               assumption
             | clear - Fr; solve_notin | exact HLK ].
        --  eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
        --  exact Hfms.
        --  exact Hus.
        --  exact Hks.
        --
           intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
        --  exact HFs.
        --  exact HwfPa'.
        --  exact HwfΞ'.
        --  exact HαΞ.
        --  exact Hmapfst.
        --  exact Himg.
        --  exact Hinc'.
        --  apply a_inc_equiv_refl; exact Hκ.
        --
           intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
           clear - Hκfresh; fsetdec.
        --
           eapply ad_partial_precise_strengthen_tvar; exact Hprec.
        --
           intros _; left. cbn [def_ftv] in Hleft. exact Hleft.
        --
           exact HapartR.
      *
        cbn [ftvar_in_a_cstrs] in *.
        cbn [app] in Hprec.
        assert (Hdκs : dom κs [=] dom Ξs) by (apply keys_eq_dom; exact Hks).
        assert (HβPaκ0 : β `notin`
                  ftvar_in_pskl (msubst_pskl (κs ++ κ) Pa)).
        { eapply ad_partial_precise_src_ftv_avoid;
            [ exact Hprec | exact Hβψa | clear - Fr; solve_notin
            | intros τ0 Hb;
              destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                [ discriminate Habs
                | apply HβΘ; eapply binds_In; exact Hb' ]
            | cbn [def_ftv]; clear - Fr; solve_notin ]. }
        assert (HβPa : β `notin` ftvar_in_pskl Pa).
        { pose proof (msubst_pskl_ftv_dom_lower (κs ++ κ) Pa) as Hlo.
          repeat rewrite dom_app in Hlo.
          clear - HβPaκ0 Hlo Hβκ HβΞs Hdκs; fsetdec. }
        eapply (looksub_solve_single Δρ).
        -- apply a_looksub__forall_r with (β := β);
             [ exact (ptyp_to_pskl_ghost_free (ptyp_all A0))
             | clear - Fr; solve_notin
             | exact (alpha_stack_ftv Hstk)
             | exact HPnα
             | exact HLK ].
        -- exact (@a_solve_cstr_strip_tvar_mid nil β Θ0 _ _ _ _ HSolve).
        -- exact Hfms.
        -- exact Hus.
        -- exact Hks.
        -- intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
        -- exact HFs.
        -- exact Hmon.
        -- cbn [app] in HwfPa; exact (@a_wf_pskl_strip_tvar Ξs β Θ0 _ _ HwfPa HβPa).
        -- exact HwfΘ0.
        -- exact Hκ.
        -- eapply ad_partial_precise_strengthen_tvar; exact Hprec.
        -- exact Hstk.
        -- exact HapartR.
  -
    assert (HP0 : P0 = pskl_ghost)
      by (pose proof (HmodSK eq_refl) as Hm; inversion Hm; reflexivity).
    subst P0.
    apply (looksub_solve_identity Θw Δρ Lav).
    +
      apply a_looksub__vacuous; assumption.
    + exact HwfΘ0.
    + exact HwfPi.
    + exact Hκ.
    + assert (HΨae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
      eapply ad_partial_precise_psi_cong; [ exact Hpre | clear - HΨae; fsetdec ].
  -
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR, HeraseR;
      try solve [ contradiction (HRnv _ eq_refl) | inversion Hrho
                | clear - HαR; fsetdec ].
    destruct (uskl_rsubst_arrow_r_inv Hrho)
      as (R1' & R2' & Ψρ1 & Ψρ2 & HRs & Hrhoa & Hrhob & HΨρeq).
    injection HRs as HRsA HRsB.
    rewrite <- HRsA in Hrhoa. rewrite <- HRsB in Hrhob. clear HRsA HRsB.

    assert (HP0arr : exists P01 P02, P0 = pskl_arrow P01 P02 /\
              (NM = a_sub_mode_sk -> a_sk_mode_compat M P02) /\
              (NM = a_sub_mode_ty -> a_ty_mode_compat M P02)).
    { destruct NM.
      - specialize (HmodTY eq_refl); inversion HmodTY; subst.
        match goal with |- exists _ _, pskl_arrow ?A ?B = _ /\ _ =>
          exists A, B end.
        repeat split; [ intros Habs; discriminate Habs | intros _; assumption ].
      - specialize (HmodSK eq_refl); inversion HmodSK; subst.
        match goal with |- exists _ _, pskl_arrow ?A ?B = _ /\ _ =>
          exists A, B end.
        repeat split; [ intros _; assumption | intros Habs; discriminate Habs ]. }
    destruct HP0arr as (P01 & P02 & HP0eq & HmodSK2 & HmodTY2).
    subst P0.
    destruct (a_wf_pskl_arrow_inv HwfP0) as [HwfP01 HwfP02].

    cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
    destruct (ad_refine_arrow_arrow_inv Hrefine) as [Href1 Href2].

    cbn [uskl_to_pskl] in HwfSubj.
    destruct (a_wf_pskl_arrow_inv HwfSubj) as [HwfSubjA HwfSubjB].
    destruct (lc_uskl_arrow_inv HlcR) as [HlcRa HlcRb].

    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
    assert (HΨa : Ψa [=] union (Ψ1 ∩ Ψ') (Ψ2 ∩ Ψ'))
      by (clear - HΨs1 HΨs2 Hsub H0 Hdisj HΨρ; fsetdec).

    pose proof (rsubst_component_tags
                  (ad_pat_consis_ftag_sub (ad_consis_join_consis H)) Hrhoa Hψatag)
      as HΨs1L.
    pose proof (rsubst_component_tags (ad_pat_sub_fuel_ftag_sub Hsubty) Hrhob Hψatag)
      as HΨs1R.
    assert (HΨρ1e : Ψρ1 ∩ Ψ' [=] empty) by (clear - HΨρ HΨρeq; fsetdec).
    assert (HΨρ2e : Ψρ2 ∩ Ψ' [=] empty) by (clear - HΨρ HΨρeq; fsetdec).

    assert (HsubL : Ψi `union` (Ψ1 ∩ Ψ') [<=] Ψ') by (clear - Hsub; fsetdec).
    assert (HΨs2L : Ψ1 ∩ Ψ' [<=] Ψ1) by (clear; fsetdec).
    assert (HΔρftvL : forall α0, α0 `in` Δρ ->
              α0 `notin` ftvar_in_pskl P01 `union` ftvar_in_pskl Pi)
      by (intros α0 Hα0; pose proof (HΔρftv α0 Hα0) as Hd0;
          cbn [ftvar_in_pskl] in Hd0; clear - Hd0; fsetdec).
    assert (HLav1 : ftvar_in_aenv Θ0 [<=] add α (union Lav (dom Θ)))
      by (clear - HLav; fsetdec).
    assert (HscopeRa : ftvar_in_uskl Ra [<=] add α (dom Θ0 `union` dom Θ))
      by (clear - HscopeR; cbn in HscopeR; fsetdec).
    assert (HdisjRa : (ftag_in_uskl Ra) ∩ Ψ' [=] empty)
      by (clear - Hdisj; cbn in Hdisj; fsetdec).
    assert (HlcQ1 : lc_bskl Q1) by lc_tgt.
    destruct (@a_lookeq_solve_complete_gen
                (size_uskl Ra + size_pskl P01)
                NM Θ0 Θ Θw κ Δ Ψ' Ψi (Ψ1 ∩ Ψ') Ψ1 ψa Q1
                (uskl_to_pskl Ra) P01 Pi Ra α Θ Δρ Ψρ1 R1
                (le_n _) HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP01 HwfPi Hκ Hκw Hψaw
                HαΘ HαΘ0 eq_refl HscopeRa HlcRa Htags HdisjRa HsubL Hdfresh Hpre
                HΨs1L HΨs2L (ad_consis_join_consis H) HlcQ1 HwfSubjA Href1
                Hrhoa (fun x b Hb => Hb) HΨρ1e Hrfr HΔρΔ HΔρw HΔρftvL HΔρPi
                Hψaap _ HLav1)
      as (C1 & Ξc1 & Ξs1 & Pa1 & κc1 & κs1
          & HLK1 & HSolve1 & Hfms1 & Hus1 & Hks1 & Hfrs1 & HFs1
          & HwfPa1 & HwfΞ1 & HαΞ1
          & Hmap1 & Himg1 & HftvC1 & Hinc1 & Hinceq1 & Hκf1 & Hpre1
          & Hapart1).
    pose proof (@keys_eq_dom _ _ κc1 Ξc1 Hmap1) as Hd1.
    assert (Hd_s1 : dom κs1 [=] dom Ξs1) by (apply keys_eq_dom; exact Hks1).
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdf0.
    assert (HαΞs1 : α `notin` dom Ξs1)
      by (intro Hc; pose proof (Hfrs1 α Hc) as Hf; clear - Hf; fsetdec).
    assert (HΞs1L : forall x, x `in` dom Ξs1 -> x `notin` Lav)
      by (intros x Hx; pose proof (Hfrs1 x Hx) as Hf; clear - Hf; fsetdec).
    pose proof (a_wf_aenv_solve_block HwfΞ1 HSolve1 Hfms1 Hus1) as HwfΞs1.
    assert (Hαr : α `notin` dom (Ξs1 ++ Ξc1 ++ Θ0))
      by (repeat rewrite dom_app; clear - HαΞs1 HαΞ1 HαΘ0; fsetdec).
    assert (Hinc1' : (κs1 ++ κc1 ++ κ) ∷ (Ξs1 ++ Ξc1 ++ Θ0) ⊑ Θ) by exact Hinc1.
    assert (Hακdom' : α `notin` dom (κs1 ++ κc1 ++ κ)).
    { intro Hc. apply (a_inc_dom_sub Hinc1') in Hc. contradiction. }
    assert (Hκav' : forall p, In p (κs1 ++ κc1 ++ κ) ->
              α `notin` ftvar_in_ptyp (snd p)).
    { intros p Hp. pose proof (a_inc_image_ftv_dom Hinc1' p Hp) as Hb.
      clear - HαΘ Hb; fsetdec. }
    destruct (solve_scope_arrow_prefix (conj Hmon (conj Hnr Hκw)) Hψaw
                Hmap1 Himg1 Hks1 HFs1) as (_ & _ & Hκw1).
    assert (HscopeRb : ftvar_in_uskl Rb
              [<=] add α (dom (Ξs1 ++ Ξc1 ++ Θ0) `union` dom Θ))
      by (repeat rewrite dom_app; clear - HscopeR; cbn in HscopeR; fsetdec).
    assert (HwfP02R : {{ (Ξs1 ++ Ξc1 ++ Θ0) ⨟ empty ⊢ₚₛ P02 }}a)
      by (eapply a_wf_pskl_weaken;
            [ intros x b Hb; apply binds_app_3; apply binds_app_3; exact Hb
            | exact HwfP02 ]).
    pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd02.
    assert (Htr_c : msubst_uskl_syn (κs1 ++ κc1 ++ κ) Rb
                    = msubst_uskl_syn κ Rb).
    { cbn in HscopeR.
      apply msubst_uskl_syn_prepend_fresh2; intros α0 Hα0.
      - assert (Hin1 : α0 `in` dom Ξs1) by (clear - Hα0 Hd_s1; fsetdec).
        pose proof (Hfrs1 α0 Hin1) as Hf.
        clear - Hf HscopeR HLav Hdf0; fsetdec.
      - specialize (Hκf1 α0 Hα0). clear - Hκf1 HscopeR; fsetdec. }
    assert (Htr_r : msubst_pskl (κs1 ++ κc1 ++ κ) P02 = msubst_pskl κ P02).
    { apply msubst_pskl_prepend_fresh2; intros α0 Hα0.
      - assert (Hin1 : α0 `in` dom Ξs1) by (clear - Hα0 Hd_s1; fsetdec).
        pose proof (Hfrs1 α0 Hin1) as Hf.
        clear - Hf Hfd02 HLav Hdf0; fsetdec.
      - specialize (Hκf1 α0 Hα0). clear - Hκf1 Hfd02; fsetdec. }
    rewrite <- Htr_c in Hrhob.
    assert (Href2' : {{ Θ ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh (msubst_pskl (κs1 ++ κc1 ++ κ) P02)) ⊳ Q2 }}ad)
      by (rewrite Htr_r; exact Href2).

    assert (HfrΞ1 : (ftvar_in_pskl P02) ∩ (dom Ξc1) [=] empty).
    { apply inter_dom_empty_of_forall. intros x Hx. rewrite <- Hd1 in Hx.
      specialize (Hκf1 x Hx). clear - Hκf1 Hfd02; fsetdec. }
    assert (HfrΞs1 : (ftvar_in_pskl P02) ∩ (dom Ξs1) [=] empty).
    { apply inter_dom_empty_of_forall. intros x Hx.
      pose proof (Hfrs1 x Hx) as Hf. clear - Hf Hfd02 HLav Hdf0; fsetdec. }
    assert (HsubR : (Ψi `union` (Ψ1 ∩ Ψ')) `union` (Ψ2 ∩ Ψ') [=] Ψ')
      by (clear - Hsub HΨa; fsetdec).
    assert (HΨs2R : Ψ2 ∩ Ψ' [<=] Ψ2) by (clear; fsetdec).
    assert (HdisjRb : (ftag_in_uskl Rb) ∩ Ψ' [=] empty)
      by (clear - Hdisj; cbn in Hdisj; fsetdec).
    assert (HΔρΘ0 : Δρ [<=] dom Θ0).
    { intros α0 Hα0. destruct (Hrfr α0 Hα0) as (Hb & _ & _).
      apply binds_In with (a := abind_tvar).
      eapply a_inc_binds_tvar_rev; [ exact Hκ | exact Hb ]. }
    assert (HΔρΞc1 : forall α0, α0 `in` Δρ -> α0 `notin` dom Ξc1).
    { intros α0 Hα0 Hc. rewrite <- Hd1 in Hc. specialize (Hκf1 α0 Hc).
      destruct (Hrfr α0 Hα0) as (Hb & _ & _). apply binds_In in Hb.
      clear - Hκf1 Hb; fsetdec. }
    assert (HΔρΞs1 : forall α0, α0 `in` Δρ -> α0 `notin` dom Ξs1).
    { intros α0 Hα0 Hc. pose proof (Hfrs1 α0 Hc) as Hf.
      pose proof (HΔρΘ0 α0 Hα0) as Hd00.
      clear - Hf Hd00 HLav Hdf0; fsetdec. }
    assert (HΔρPa1ftv : forall α0, α0 `in` Δρ ->
              α0 `notin` ftvar_in_pskl Pa1).
    { intros α0 Hα0.
      pose proof (a_solve_cstr_ftv_eq HSolve1 (a_lookeq_cstr_eq HLK1))
        as Hs1.
      pose proof (HΔρftv α0 Hα0) as Hd0. cbn [ftvar_in_pskl] in Hd0.
      pose proof (HΔρΞc1 α0 Hα0) as HΞ.
      pose proof (HΔρΞs1 α0 Hα0) as HΞs.
      assert (Hα0Θ0 : α0 `in` dom Θ0) by (apply HΔρΘ0; exact Hα0).
      assert (Hc1 : α0 `notin` ftvar_in_a_cstrs C1)
        by (eapply a_lookeq_ftv_ctx;
              [ exact HLK1 | exact Hα0Θ0 | clear - Hd0; fsetdec | exact HΞ ]).
      clear - Hs1 Hc1 Hd0 HΞ HΞs; fsetdec. }
    assert (HΔρftvR : forall α0, α0 `in` Δρ ->
              α0 `notin` ftvar_in_pskl P02 `union` ftvar_in_pskl Pa1).
    { intros α0 Hα0. pose proof (HΔρftv α0 Hα0) as Hd0.
      cbn [ftvar_in_pskl] in Hd0.
      pose proof (HΔρPa1ftv α0 Hα0) as Hp1. clear - Hd0 Hp1; fsetdec. }
    pose proof (rsubst_fresh_arrow_prefix Hrfr HΔρw Hψaap HFs1 Himg1)
      as HrfrR.
    pose proof (rsubst_fresh_shielded HrfrR HΔρPa1ftv) as HΔρPa1.
    assert (HLavR : ftvar_in_aenv (Ξs1 ++ Ξc1 ++ Θ0)
              [<=] add α (union (union Lav (union (dom Ξs1) (dom Ξc1)))
                                (ftvar_in_a_cstrs C1))).
    { repeat rewrite ftvar_in_aenv_app.
      pose proof (all_flex_mono_ftvar_in_aenv Hfms1) as Hs1f.
      pose proof (all_flex_mono_ftvar_in_aenv
                    (a_lookeq_all_flex_mono HLK1)) as Hc1f.
      clear - Hs1f Hc1f HLav; fsetdec. }

    destruct (IHHsubty Htags Hsubty Θ (Ξs1 ++ Ξc1 ++ Θ0) (κs1 ++ κc1 ++ κ)
                    Δ Δρ Ψρ2
                    Rb (uskl_to_pskl Rb) P02 Pa1
                    (Ψi `union` (Ψ1 ∩ Ψ')) (Ψ2 ∩ Ψ')
                    HwfΘ HwfΞs1 Hmon Hnr Hκw1 HΔρw
                    Hαr Hinc1' Hακdom' Hκav'
                    eq_refl HscopeRb HlcRb HdisjRb HwfP02R HwfPa1
                    HmodSK2 HmodTY2 HαΘ HsubR HΨs1R HΨs2R Hdfresh
                    Hpre1 Href2' ltac:(lc_tgt) Hrhob HΨρ2e HrfrR HΔρΔ HΔρftvR HΔρPa1 Hext
                    HwfSubjB Hψaap
                    (add α (union (union Lav (union (dom Ξs1) (dom Ξc1)))
                                  (ftvar_in_a_cstrs C1))) HLavR) as (C2 & Ξc2 & Ξs2 & Pa2 & κc2 & κs2
                     & HLK2 & HSolve2 & Hfms2 & Hus2 & Hks2 & Hfrs2 & HFs2
                     & HwfPa2 & HwfΞ2
                     & HαΞ2 & Hmap2 & Himg2 & Hinc2 & Hinceq2
                     & Hκf2 & Hpre2 & HftvC2 & Hapart2).
    pose proof (a_lookeq_all_flex_mono HLK1) as HfmΞ1.
    pose proof (a_looksub_all_flex_mono HLK2) as HfmΞ2.
    pose proof (@keys_eq_dom _ _ κc2 Ξc2 Hmap2) as Hd2.
    assert (Hmapc : keys (κc1 ++ κc2) = keys (Ξc1 ++ Ξc2))
      by (rewrite !keys_app; rewrite Hmap1, Hmap2; reflexivity).
    assert (Hmaps : keys (κs2 ++ κs1) = keys (Ξs2 ++ Ξs1))
      by (rewrite !keys_app; rewrite Hks1, Hks2; reflexivity).
    assert (HΞ2disj : forall x, x `in` dom Ξc2 ->
              x `notin` dom (Ξs1 ++ Ξc1 ++ Θ0)).
    { intros x Hx. rewrite <- Hd2 in Hx. pose proof (Hκf2 x Hx) as Hf.
      clear - Hf; fsetdec. }
    assert (HΞ2Ξc1Θ0 : forall x, x `in` dom Ξc2 ->
              x `notin` dom (Ξc1 ++ Θ0))
      by (intros x Hx; pose proof (HΞ2disj x Hx) as Hf;
          repeat rewrite dom_app in Hf; rewrite dom_app; clear - Hf; fsetdec).
    assert (Hdisj12 : forall β0, β0 `in` dom κc1 -> β0 `notin` dom κc2).
    { intros β0 Hβ0 Hin2. pose proof (Hκf2 β0 Hin2) as Hf2.
      repeat rewrite dom_app in Hf2. rewrite Hd1 in Hβ0.
      clear - Hf2 Hβ0; fsetdec. }
    assert (Hdisj2s1 : forall β0, β0 `in` dom κc2 -> β0 `notin` dom κs1).
    { intros β0 Hβ0. pose proof (Hκf2 β0 Hβ0) as Hf2.
      repeat rewrite dom_app in Hf2. clear - Hf2 Hd_s1; fsetdec. }
    assert (HΞ2C1 : forall x, x `in` dom Ξc2 ->
              x `notin` ftvar_in_a_cstrs C1).
    {
      intros x Hx. rewrite <- Hd2 in Hx.
      pose proof (Hκf2 x Hx) as Hf. repeat rewrite dom_app in Hf.
      apply (a_cstrs_bound_fresh HwfΘ Hκ HftvC1). clear - Hf; fsetdec. }
    assert (HC2s1 : forall x, x `in` dom Ξs1 ->
              x `notin` ftvar_in_a_cstrs C2).
    { intros x Hx. eapply a_looksub_ftv_ctx;
        [ exact HLK2
        | repeat rewrite dom_app; clear - Hx; fsetdec
        | pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd;
          pose proof (HΞs1L x Hx) as Hf;
          clear - Hfd Hf Hdf0 HLav; fsetdec
        | intro Hc; pose proof (HΞ2disj x Hc) as Hf2;
          repeat rewrite dom_app in Hf2; clear - Hf2 Hx; fsetdec ]. }
    assert (HΞs2 : forall x, x `in` dom Ξs2 ->
              x `notin` dom Ξs1 `union` ftvar_in_a_cstrs C1)
      by (intros x Hx; pose proof (Hfrs2 x Hx) as Hf; clear - Hf; fsetdec).
    destruct (arrow_merge_scopes Hus1 Hus2 HfmΞ1 HfmΞ2 HwfΘ0 HΞs2 Hapart2 Hapart1
                HC2s1 HwfΞ2 HwfPa2) as (Hus & HwfPa & HwfΞ & Hapart).
    exists (C1 ++ C2), (Ξc1 ++ Ξc2), (Ξs2 ++ Ξs1), Pa2,
           (κc1 ++ κc2), (κs2 ++ κs1).
    repeat split.
    --
        assert (Hgc1 : ftvar_in_a_cstrs C1 ∩ dom Ξc2 [=] empty)
          by (apply inter_dom_empty_of_forall; exact HΞ2C1).
        assert (Hgc2 : ftvar_in_a_cstrs C2 ∩ dom Ξc1 [=] empty).
        { apply inter_dom_empty_of_forall. intros x Hx2 Hx1.
          assert (Hxin : x `in` ftvar_in_aenv (Ξs1 ++ Ξc1 ++ Θ0)).
          { pose proof (dom_subset_ftvar_in_aenv (Ξs1 ++ Ξc1 ++ Θ0)) as Hds.
            repeat rewrite dom_app in Hds. clear - Hds Hx2; fsetdec. }
          destruct ((proj1 a_looksub_lookeq_ftv) _ _ _ _ _ _ _ HLK2 x Hx1)
            as [Hlft | Hrgt]; [ | clear - Hrgt Hxin; contradiction ].
          assert (HxΞ2 : x `notin` dom Ξc2).
          { intro Hc. pose proof (HΞ2Ξc1Θ0 x Hc) as Hn.
            rewrite dom_app in Hn. clear - Hn Hx2; fsetdec. }
          clear - Hlft HxΞ2 HfrΞ1 Hx2; fsetdec. }
        rewrite <- HeraseR. apply a_looksub__arrow;
          [ exact Hgc1 | exact Hgc2
          | exact HLK1
          | eapply a_looksub_ctx_ftv_mono with (Θ := (Ξs1 ++ Ξc1 ++ Θ0));
              [ exact HLK2
              | repeat rewrite ftvar_in_aenv_app; clear; fsetdec
              |
                intros β0 Hβ0;
                assert (Hns : β0 `notin` dom Ξs1)
                  by (clear - HfrΞs1 Hβ0; fsetdec);
                assert (Hnc : β0 `notin` dom Ξc1)
                  by (clear - HfrΞ1 Hβ0; fsetdec);
                rewrite (@a_flex_tvar_app_notin Ξs1 (Ξc1 ++ Θ0) β0 Hns);
                rewrite (@a_flex_tvar_app_notin Ξc1 Θ0 β0 Hnc);
                reflexivity ] ].
    --
       exact (a_solve_cstr_arrow_merge (a_lookeq_cstr_eq HLK1) HSolve1
                HSolve2 HwfPi HfmΞ2 HΞ2disj HΞ2C1).
    --  apply all_flex_mono_app; assumption.
    --  exact Hus.
    --  exact Hmaps.
    --
       intros α0 Hα0. rewrite dom_app in Hα0.
       apply union_1 in Hα0; destruct Hα0 as [Hα0 | Hα0];
         [ pose proof (Hfrs2 α0 Hα0) as Hf | pose proof (Hfrs1 α0 Hα0) as Hf ];
         clear - Hf; fsetdec.
    --  apply Forall_app; split; assumption.
    --  exact HwfPa.
    --  exact HwfΞ.
    --
       rewrite dom_app; clear - HαΞ1 HαΞ2; fsetdec.
    --  exact Hmapc.
    --  apply Forall_app; split; assumption.
    --
       exact (a_inc_arrow_merge Hfms1 HfmΞ1 Hfms2 HfmΞ2 Hks1 Hmap1 Hks2 Hmap2
                Hκ Hinc1 Hinc2).
    --  apply a_inc_equiv_refl; exact Hκ.
    --
       intros α0 Hα0. rewrite dom_app in Hα0.
       apply union_1 in Hα0; destruct Hα0 as [Hα0 | Hα0].
       ++ apply Hκf1; exact Hα0.
       ++ pose proof (Hκf2 α0 Hα0) as Hf. repeat rewrite dom_app in Hf.
          clear - Hf; fsetdec.
    --
       rewrite (@msubst_pskl_arrow_merge κs1 κc1 κs2 κc2 κ Pa2
                  Hdisj12 Hdisj2s1).
       eapply ad_partial_precise_psi_cong;
         [ exact Hpre2 | clear - HΨa; fsetdec ].
    --
       intros Habs; discriminate Habs.
    --
       exact Hapart.
  -

    exact (looksub_solve_forall_l_step HwfΘw Hψaw Htags Hderiv Hsubty
             (IHHsubty Htags Hsubty) H1 H2 H3 (uskl_forall_of__tag ε R)
             HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw HαΘ0 Hκ Hακdom Hκav HeraseR HscopeR
             HlcR Hdisj HwfP0 HwfPi HmodSK HmodTY HαΘ Hsub HΨs1 HΨs2 Hdfresh
             Hpre Hrefine HlcQ Hrho HΨρ Hrfr HΔρΔ HΔρftv HΔρPi Hext HwfSubj
             Hψaap HLav).
  -

    exact (looksub_solve_forall_l_step HwfΘw Hψaw Htags Hderiv Hsubty
             (IHHsubty Htags Hsubty) H1 H2 H3 (uskl_forall_of__syn R)
             HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw HαΘ0 Hκ Hακdom Hκav HeraseR HscopeR
             HlcR Hdisj HwfP0 HwfPi HmodSK HmodTY HαΘ Hsub HΨs1 HΨs2 Hdfresh
             Hpre Hrefine HlcQ Hrho HΨρ Hrfr HΔρΔ HΔρftv HΔρPi Hext HwfSubj
             Hψaap HLav).

  -
    exfalso.
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR;
      solve [ contradiction (HRnv _ eq_refl)
            | clear - HαR; fsetdec
            | inversion Hrho ].
  -
    exfalso.
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR;
      solve [ contradiction (HRnv _ eq_refl)
            | clear - HαR; fsetdec
            | inversion Hrho ].
  -
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR, HeraseR;
      try solve [ contradiction (HRnv _ eq_refl) | inversion Hrho
                | clear - HαR; fsetdec ].
    destruct (uskl_rsubst_univ_ghost_r_inv Hrho) as (Rb0 & HeqRs & Hrho0).
    injection HeqRs as HeqRs. rewrite <- HeqRs in Hrho0. clear HeqRs.

    assert (HlcR0 : lc_uskl R0) by (inversion HlcR; assumption).

    assert (HwfSubj0 : {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl R) }}a)
      by (cbn [uskl_to_pskl] in HwfSubj;
          eapply a_wf_pskl_univ_ghost_inv; exact HwfSubj).
    assert (HscopeR0 : ftvar_in_uskl R0 [<=] add α (dom Θ0 `union` dom Θ))
      by (clear - HscopeR; cbn in HscopeR; fsetdec).
    assert (HdisjR0 : (ftag_in_uskl R0) ∩ Ψ' [=] empty)
      by (clear - Hdisj; cbn in Hdisj; fsetdec).
    assert (HΨs1R0 : Ψ [<=] ftag_in_uskl R0 `union` Ψρ `union` Ψa)
      by (clear - HΨs1; cbn in HΨs1; fsetdec).
    eapply looksub_solve_univ_ghost_l_close with (Δρ := Δρ);
      [ exact HeraseR | ].
    exact (IHHsubty Htags Hsubty Θ Θ0 κ Δ Δρ Ψρ R0 (uskl_to_pskl R0) P0 Pi Ψi Ψa
      HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw HαΘ0 Hκ Hακdom Hκav
      eq_refl HscopeR0 HlcR0 HdisjR0 HwfP0 HwfPi HmodSK HmodTY HαΘ
      Hsub HΨs1R0 HΨs2 Hdfresh Hpre Hrefine HlcQ Hrho0 HΨρ Hrfr HΔρΔ
      HΔρftv HΔρPi Hext HwfSubj0 Hψaap Lav HLav).
  -
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR, HeraseR;
      try solve [ contradiction (HRnv _ eq_refl) | inversion Hrho
                | clear - HαR; fsetdec ].
    destruct (uskl_rsubst_dot_univ_ghost_r_inv Hrho) as (Rb0 & HeqRs & Hrho0).
    injection HeqRs as HeqRs. rewrite <- HeqRs in Hrho0. clear HeqRs.

    assert (HlcR0 : lc_uskl R0) by (inversion HlcR; assumption).

    assert (HwfSubj0 : {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl R) }}a)
      by (cbn [uskl_to_pskl] in HwfSubj;
          eapply a_wf_pskl_univ_ghost_inv; exact HwfSubj).
    assert (HscopeR0 : ftvar_in_uskl R0 [<=] add α (dom Θ0 `union` dom Θ))
      by (clear - HscopeR; cbn in HscopeR; fsetdec).
    assert (HdisjR0 : (ftag_in_uskl R0) ∩ Ψ' [=] empty)
      by (clear - Hdisj; cbn in Hdisj; fsetdec).
    assert (HΨs1R0 : Ψ [<=] ftag_in_uskl R0 `union` Ψρ `union` Ψa)
      by (clear - HΨs1; cbn in HΨs1; fsetdec).
    eapply looksub_solve_univ_ghost_l_close with (Δρ := Δρ);
      [ exact HeraseR | ].
    exact (IHHsubty Htags Hsubty Θ Θ0 κ Δ Δρ Ψρ R0 (uskl_to_pskl R0) P0 Pi Ψi Ψa
      HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw HαΘ0 Hκ Hακdom Hκav
      eq_refl HscopeR0 HlcR0 HdisjR0 HwfP0 HwfPi HmodSK HmodTY HαΘ
      Hsub HΨs1R0 HΨs2 Hdfresh Hpre Hrefine HlcQ Hrho0 HΨρ Hrfr HΔρΔ
      HΔρftv HΔρPi Hext HwfSubj0 Hψaap Lav HLav).
  -
    exfalso.
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in Hrho, HαR;
      solve [ contradiction (HRnv _ eq_refl)
            | clear - HαR; fsetdec
            | inversion Hrho ].
Qed.

Theorem a_looksub_solve_complete :
  forall n NM M Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->
  Ψi `union` Ψa [=] Ψ' ->
  ftvar_in_uskl ψa [<=] dom Θ ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψa ->
  Ψa [<=] Ψsub ->

  ad_pat_sub_fuel n NM M Ψsub Θ
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) Q ->
  {{ Θ ⨟ empty ⊢ₚₛ
    (uskl_to_pskl (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R'))) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
    {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
    all_flex_mono Ξs /\
    uniq Ξs /\
    keys κs = keys Ξs /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κs /\
    {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξc ++ Θ0) }}a /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
    (M = mode_tc ->
       ftvar_in_a_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc
                             `union` dom κ `union` def_ftv Θ
       \/ (alpha_stack α P /\ Ξc = nil /\ κc = nil
           /\ exists T, 𝒞 = a_cstr_sub M T :: nil)) /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞).
Proof.
  intros n NM M Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α.
  intros HwfΘ HwfΘ0 HwfP0 HwfPi HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR
         HscopeR HlcR Htags Hdisj Hsub Hψaw Hdfresh Hpre HΨs1 HΨs2
         Hsubty HwfSubj Hrefine HwfQ L HL.
  edestruct (@a_looksub_solve_complete_gen n NM M Θ0 Θ Θ Θ κ Δ empty empty Ψ'
               Ψi Ψa Ψsub ψa Q P P0 Pi R'
               (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) α)
    as (𝒞 & Ξc & Ξs & Pa & κc & κs
        & Hlook & Hsolve & Hfms & Hus & Hks & Hfrs & HFs
        & HwfPa & HwfΞ & HαΞ & Hkeys
        & HFor & Hinc & Heqv & Hκcfresh & Hprec & HftvC & HapartC);
    [ exact HwfΘ | exact HwfΘ0
    | exact HwfΘ | intros x b Hb; exact Hb | intros x b Hb; left; exact Hb
    | intros α0 Hf; eapply a_inc_lookup_flex_ftv_dom; [ exact Hκ | exact Hf ]
    | exact Hψaw | clear; fsetdec
    | exact HwfP0 | exact HwfPi
    | exact HmodSK | exact HmodTY | exact Hκ | exact HαΘ | exact HαΘ0
    | exact HeraseR | exact HscopeR | exact HlcR | exact Htags | exact Hdisj
    | exact Hsub | exact Hdfresh | exact Hpre
    | clear - HΨs1; fsetdec | exact HΨs2
    | exact Hsubty | exact HwfSubj | exact Hrefine
    | apply lc_bskl_of_bskl_to_pskl; exact (a_wf_pskl_lc HwfQ)
    | apply ursubst__refl;
        [ apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact HwfSubj
        | clear; fsetdec ]
    | clear; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | clear; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | intros x b Hb; exact Hb
    | clear; fsetdec
    | exact HL
    | ].
  exists 𝒞, Ξc, Ξs, Pa, κc, κs.
  repeat split; assumption.
Qed.
