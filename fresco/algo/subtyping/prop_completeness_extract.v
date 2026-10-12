Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_precise.
Require Import src.fresco.algo.subtyping.prop_rigid_substitution.
Require Import src.fresco.algo.subtyping.prop_solve_extension.
Require Import src.fresco.algo.subtyping.prop_completeness_solve_eq_var.
Require Import src.fresco.algo.subtyping.prop_completeness_lookeq_solve.
Require Import src.fresco.algo.subtyping.prop_completeness_looksub_solve.

Set Implicit Arguments.

Inductive pskl_all_free : pskl -> Prop :=
| paf_unit   : pskl_all_free pskl_unit
| paf_var_b  : forall n, pskl_all_free (pskl_var_b n)
| paf_var_f  : forall α, pskl_all_free (pskl_var_f α)
| paf_arrow  : forall P1 P2,
    pskl_all_free P1 -> pskl_all_free P2 -> pskl_all_free (pskl_arrow P1 P2)
| paf_ghost   : pskl_all_free pskl_ghost
| paf_univ_ghost : forall P, pskl_all_free P -> pskl_all_free (pskl_univ_ghost P).

#[export] Hint Constructors pskl_all_free : fresco.

Lemma pskl_inh_eq_syn_inv : forall P Q,
  pskl_to_bskl_inh P = pskl_to_bskl_syn Q ->
  P = Q /\ pskl_all_free P.
Proof.
  induction P; intros Q Heq; destruct Q; cbn in Heq; try discriminate Heq.
  - split; [ reflexivity | apply paf_unit ].
  - injection Heq as ->. split; [ reflexivity | apply paf_var_b ].
  - injection Heq as ->. split; [ reflexivity | apply paf_var_f ].
  - injection Heq as Heq1 Heq2.
    destruct (IHP1 _ Heq1) as [-> Hf1]. destruct (IHP2 _ Heq2) as [-> Hf2].
    split; [ reflexivity | apply paf_arrow; assumption ].
  - split; [ reflexivity | apply paf_ghost ].
  - injection Heq as Heq0. destruct (IHP _ Heq0) as [-> Hf].
    split; [ reflexivity | apply paf_univ_ghost; assumption ].
Qed.

Lemma pskl_all_ghost_free_mono : forall P,
  pskl_all_free P -> pskl_ghost_free P -> lc_pskl P ->
  exists τ, ptyp_to_pskl τ = P /\ mono_ptyp τ.
Proof.
  intros P Ha; induction Ha; intros Hg Hlc; cbn in Hg;
    try solve [ contradiction ].
  - exists ptyp_unit; split; [ reflexivity | apply mono_ptyp__unit ].
  -
    inversion Hlc.
  - exists (ptyp_var_f α); split; [ reflexivity | apply mono_ptyp__var ].
  - destruct Hg as [Hg1 Hg2]. inversion Hlc; subst.
    destruct (IHHa1 Hg1 ltac:(assumption)) as [τ1 [Heq1 Hm1]].
    destruct (IHHa2 Hg2 ltac:(assumption)) as [τ2 [Heq2 Hm2]].
    exists (ptyp_arrow τ1 τ2); cbn; rewrite Heq1, Heq2.
    split; [ reflexivity | apply mono_ptyp__arrow; assumption ].
Qed.

Lemma ad_refine_syn_ghost_l_inv : forall Θ Δ Y,
  {{ Θ ⨟ Δ ⊢ᵣ bskl_ghost ⊳ Y }}ad ->
  (exists P, Δ ∩ ftvar_in_pskl P [=] empty /\ Y = pskl_to_bskl_syn P)
  \/ (exists α τ, binds α (abind_flex_mono_def τ) Θ /\ Y = bskl_var_f α).
Proof.
  intros Θ Δ Y H; inversion H; subst;
    [ left; eexists; split; [ eassumption | reflexivity ]
    | right; do 2 eexists; split; [ eassumption | reflexivity ] ].
Qed.

Lemma ad_precise_ghost_inv_mono : forall Θ Δ X,
  {{ Θ ⨟ Δ ⊢ₚᵣ pskl_ghost ⊑ X }}ad ->
  pskl_ghost_free X -> lc_pskl X ->
  (forall γ, γ `in` ftvar_in_pskl X -> γ `notin` Δ -> a_binds_tvar γ Θ) ->
  exists τ, ptyp_to_pskl τ = X /\ mono_ptyp τ /\ {{ Θ ⨟ empty ⊢ₚₛ X }}a.
Proof.
  intros Θ Δ X Hp Hgf Hlc HscX. unfold ad_precise in Hp. cbn in Hp.
  destruct (ad_refine_syn_ghost_l_inv Hp) as [[P [HΔP Heq]] | [α [τ0 [Hb Heq]]]].
  -
    destruct (@pskl_inh_eq_syn_inv _ _ Heq) as [-> Haf].
    destruct (@pskl_all_ghost_free_mono _ Haf Hgf Hlc) as [τ [Heqτ Hmτ]].
    exists τ; repeat split; [ exact Heqτ | exact Hmτ | ].
    subst. apply a_wf_pskl_of_ptyp_vis;
      [ apply mono_ptyp_lc; exact Hmτ | ].
    rewrite ftvar_ptyp_to_pskl in HΔP.
    intros γ Hγ. apply HscX;
      [ rewrite ftvar_ptyp_to_pskl; exact Hγ | clear - Hγ HΔP; fsetdec ].
  -
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in Heq;
      try discriminate Heq.

    assert (Hαe : α0 = α) by congruence; subst α0.
    exists (ptyp_var_f α); split; [ reflexivity | split ];
      [ apply mono_ptyp__var
      |
        apply a_wf_pskl__var; right; right; exists τ0; exact Hb ].
Qed.

Lemma ad_refine_syn_all_l_not_mono : forall Θ Δ Y τ,
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_all_inh Y) ⊳ (ptyp_to_bskl_syn τ) }}ad ->
  {{ ⊢ Θ }}a -> mono_ptyp τ -> False.
Proof.
  intros Θ Δ Y τ H. remember (bskl_all_inh Y) as Src eqn:HeqS.
  remember (ptyp_to_bskl_syn τ) as Tgt eqn:HeqT.
  revert Y τ HeqS HeqT.
  induction H; intros Y0 τ0 HeqS HeqT HwfΘ Hmτ; subst;
    try discriminate HeqS.
  -
    destruct τ0; cbn in HeqT; discriminate HeqT.
  -
    destruct τ0; cbn in HeqT; try discriminate HeqT.
    assert (Hαe : α = α0) by congruence; subst α0.
    eapply IHad_refine_syn;
      [ reflexivity | reflexivity | exact HwfΘ
      | eapply a_wf_aenv_binds_def_mono; eassumption ].
Qed.

Lemma a_wf_ptyp_of_wf_pskl_mono : forall Θ τ,
  mono_ptyp τ ->
  {{ Θ ⨟ empty ⊢ₚₛ (ptyp_to_pskl τ) }}a ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ τ Hm; induction Hm; intros Hwf; cbn in Hwf.
  - apply a_wf_ptyp__unit.
  - inversion Hwf; subst.
    apply a_wf_ptyp__var.
    assumption.
  - inversion Hwf; subst. apply a_wf_ptyp__arrow; auto.
Qed.

Lemma ad_refine_syn_rename_delta_remove : forall Θ Δ Q Q' β α0,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  {{ ⊢ Θ }}a ->
  β `notin` dom Θ -> β `in` Δ ->
  α0 `notin` dom Θ -> α0 `notin` ftvar_in_bskl Q' ->
  {{ Θ ⨟ (add α0 (remove β Δ)) ⊢ᵣ
    (subst_bskl_in_bskl (bskl_var_f α0) β Q) ⊳
    (subst_bskl_in_bskl (bskl_var_f α0) β Q') }}ad.
Proof.
  intros Θ Δ Q Q' β α0 H HwfΘ Hβ HβΔ Hα0 Hα0Q.
  eapply ad_refine_syn_delta_mono;
    [ apply ad_refine_syn_rename;
        [ exact H | exact HβΔ | exact Hβ
        | eapply a_wf_aenv_def_ftv_notin; eassumption
        | exact Hα0Q
        | eapply a_wf_aenv_def_ftv_notin; eassumption ]
    | clear; fsetdec ].
Qed.

Lemma ad_precise_rename_delta : forall Θ Δ P X β α0,
  {{ Θ ⨟ Δ ⊢ₚᵣ P ⊑ X }}ad ->
  {{ ⊢ Θ }}a ->
  β `notin` dom Θ -> β `in` Δ ->
  α0 `notin` dom Θ -> α0 `notin` ftvar_in_pskl X ->
  {{ Θ ⨟ (add α0 (remove β Δ)) ⊢ₚᵣ
    (subst_pskl_in_pskl (pskl_var_f α0) β P) ⊑
    (subst_pskl_in_pskl (pskl_var_f α0) β X) }}ad.
Proof.
  intros Θ Δ P X β α0 H HwfΘ Hβ HβΔ Hα0 Hα0X. unfold ad_precise in *.
  rewrite <- ! subst_var_bskl_inh.
  apply ad_refine_syn_rename_delta_remove; try assumption.
  rewrite ftvar_in_bskl_inh; exact Hα0X.
Qed.

Lemma a_flex_def_counterpart : forall Θ Δ α τ,
  {{ ⊢ Θ }}a -> binds α (abind_flex_mono_def τ) Θ ->
  ptyp_to_bskl_syn τ = pskl_to_bskl_inh (ptyp_to_pskl τ) /\
  pskl_ghost_free (ptyp_to_pskl τ) /\ lc_pskl (ptyp_to_pskl τ) /\
  (forall γ, γ `in` ftvar_in_pskl (ptyp_to_pskl τ) -> γ `notin` Δ ->
     a_binds_tvar γ Θ).
Proof.
  intros Θ Δ α τ HwfΘ Hb.
  assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eassumption).
  assert (Hwfτ : a_wf_ptyp Θ τ) by (eapply a_wf_aenv_binds_def_wf; eassumption).
  refine (conj _ (conj (ptyp_to_pskl_ghost_free _) (conj _ _))).
  - symmetry; apply ptyp_to_bskl_inh_syn_eq; exact Hmτ.
  - apply ptyp_to_pskl_lc; eapply a_wf_ptyp_lc; exact Hwfτ.
  - intros γ Hγ _; eapply a_wf_pskl_ftv_binds;
      [ apply a_wf_ptyp_to_wf_pskl with (Δ := empty); exact Hwfτ | exact Hγ ].
Qed.

Lemma ad_precise_arrow_l_inv : forall Θ Δ Src Tgt,
  {{ Θ ⨟ Δ ⊢ᵣ Src ⊳ Tgt }}ad ->
  forall S1 S2 X,
  Src = bskl_arrow (pskl_to_bskl_inh S1) (pskl_to_bskl_inh S2) ->
  Tgt = pskl_to_bskl_inh X ->
  {{ ⊢ Θ }}a -> pskl_ghost_free X -> lc_pskl X ->
  (forall γ, γ `in` ftvar_in_pskl X -> γ `notin` Δ -> a_binds_tvar γ Θ) ->
  exists X1 X2,
    pskl_ghost_free X1 /\ pskl_ghost_free X2 /\ lc_pskl X1 /\ lc_pskl X2 /\
    (forall γ, γ `in` ftvar_in_pskl X1 -> γ `notin` Δ -> a_binds_tvar γ Θ) /\
    (forall γ, γ `in` ftvar_in_pskl X2 -> γ `notin` Δ -> a_binds_tvar γ Θ) /\
    {{ Θ ⨟ Δ ⊢ₚᵣ S1 ⊑ X1 }}ad /\ {{ Θ ⨟ Δ ⊢ₚᵣ S2 ⊑ X2 }}ad /\
    (forall Y1 Y2,
       {{ Θ ⨟ Δ ⊢ₚᵣ Y1 ⊑ X1 }}ad -> {{ Θ ⨟ Δ ⊢ₚᵣ Y2 ⊑ X2 }}ad ->
       {{ Θ ⨟ Δ ⊢ₚᵣ (pskl_arrow Y1 Y2) ⊑ X }}ad).
Proof.
  intros Θ Δ Src Tgt H; induction H;
    intros S1 S2 X HeqS HeqT HwfΘ Hgf Hlc HscX;
    try discriminate HeqS.
  -
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    inversion HeqS; inversion HeqT; subst.
    cbn in Hgf; destruct Hgf as [Hgf1 Hgf2]. inversion Hlc; subst.
    exists X1, X2. unfold ad_precise.
    split; [ assumption | ]. split; [ assumption | ].
    split; [ assumption | ]. split; [ assumption | ].
    split; [ intros γ Hγ; apply HscX; cbn; clear - Hγ; fsetdec | ].
    split; [ intros γ Hγ; apply HscX; cbn; clear - Hγ; fsetdec | ].
    split; [ assumption | ]. split; [ assumption | ].
    intros Y1 Y2 HY1 HY2. cbn.
    apply ad_refine_syn_arrow_intro; assumption.
  -
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    assert (Hαe : α0 = α) by congruence; subst α0.
    destruct (@a_flex_def_counterpart Θ Δ α τ HwfΘ H)
      as (Hpaint & Hgτ & Hlτ & Hsτ).
    destruct (IHad_refine_syn S1 S2 (ptyp_to_pskl τ) HeqS Hpaint HwfΘ
                Hgτ Hlτ Hsτ)
      as (X1 & X2 & Hg1 & Hg2 & Hl1 & Hl2 & Hs1 & Hs2 & Hp1 & Hp2 & Hreplay).
    exists X1, X2.
    split; [ exact Hg1 | ]. split; [ exact Hg2 | ].
    split; [ exact Hl1 | ]. split; [ exact Hl2 | ].
    split; [ exact Hs1 | ]. split; [ exact Hs2 | ].
    split; [ exact Hp1 | ]. split; [ exact Hp2 | ].
    intros Y1 Y2 HY1 HY2. unfold ad_precise; cbn.
    apply ad_refine_syn__flex_r with (τ := τ); [ assumption | ].
    rewrite Hpaint. exact (Hreplay Y1 Y2 HY1 HY2).
Qed.

Lemma ad_precise_univ_ghost_l_inv : forall Θ Δ Src Tgt,
  {{ Θ ⨟ Δ ⊢ᵣ Src ⊳ Tgt }}ad ->
  forall S0 X,
  Src = bskl_univ_ghost (pskl_to_bskl_inh S0) ->
  Tgt = pskl_to_bskl_inh X ->
  {{ ⊢ Θ }}a -> pskl_ghost_free X -> lc_pskl X ->
  (forall γ, γ `in` ftvar_in_pskl X -> γ `notin` Δ -> a_binds_tvar γ Θ) ->
  exists X',
    pskl_ghost_free X' /\ lc_pskl X' /\
    (forall γ, γ `in` ftvar_in_pskl X' -> γ `notin` Δ -> a_binds_tvar γ Θ) /\
    {{ Θ ⨟ Δ ⊢ₚᵣ S0 ⊑ X' }}ad /\
    (forall Y, {{ Θ ⨟ Δ ⊢ₚᵣ Y ⊑ X' }}ad -> {{ Θ ⨟ Δ ⊢ₚᵣ Y ⊑ X }}ad).
Proof.
  intros Θ Δ Src Tgt H; induction H;
    intros S0 X HeqS HeqT HwfΘ Hgf Hlc HscX;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    exists X.
    split; [ exact Hgf | ]. split; [ exact Hlc | ]. split; [ exact HscX | ].
    split; [ unfold ad_precise; try rewrite <- HeqT; assumption | ].
    intros Y HY; exact HY.
  -
    exfalso.
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      discriminate HeqT.
  -
    exfalso.
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    cbn in Hgf; contradiction.
  -
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    assert (Hαe : α0 = α) by congruence; subst α0.
    destruct (@a_flex_def_counterpart Θ Δ α τ HwfΘ H)
      as (Hpaint & Hgτ & Hlτ & Hsτ).
    destruct (IHad_refine_syn S0 (ptyp_to_pskl τ) HeqS Hpaint HwfΘ
                Hgτ Hlτ Hsτ)
      as (X' & Hg' & Hl' & Hs' & Hp' & Hreplay).
    exists X'.
    split; [ exact Hg' | ]. split; [ exact Hl' | ]. split; [ exact Hs' | ].
    split; [ exact Hp' | ].
    intros Y HY. unfold ad_precise; cbn.
    apply ad_refine_syn__flex_r with (τ := τ); [ assumption | ].
    rewrite Hpaint. exact (Hreplay Y HY).
Qed.

Lemma ad_precise_all_l_inv : forall Θ Δ Src Tgt,
  {{ Θ ⨟ Δ ⊢ᵣ Src ⊳ Tgt }}ad ->
  forall S0 X,
  Src = bskl_all_inh (pskl_to_bskl_inh S0) ->
  Tgt = pskl_to_bskl_inh X ->
  {{ ⊢ Θ }}a -> pskl_ghost_free X -> lc_pskl X ->
  exists X0 L,
    X = pskl_all_syn X0 /\
    (forall β, β `notin` L ->
       {{ Θ ⨟ (add β Δ) ⊢ₚᵣ (open_pskl_wrt_pskl S0 (pskl_var_f β))
                       ⊑ (open_pskl_wrt_pskl X0 (pskl_var_f β)) }}ad).
Proof.
  intros Θ Δ Src Tgt H; induction H;
    intros S0 X HeqS HeqT HwfΘ Hgf Hlc;
    try discriminate HeqS.
  -
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    inversion HeqS; inversion HeqT; subst.
    exists X0, L. split; [ reflexivity | ].
    intros β Hβ. unfold ad_precise.
    rewrite ! pskl_to_bskl_inh_open.

    eapply ad_refine_syn_defs_mono; [ apply H0; exact Hβ | ].
    intros γ τ Hb. apply binds_app_iff in Hb as [Hb | Hb];
      [ apply binds_one_iff in Hb; destruct Hb as [_ Hc]; discriminate Hc
      | exact Hb ].
  -
    exfalso.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eassumption).
    subst.
    eapply ad_refine_syn_all_l_not_mono; eassumption.
Qed.

Lemma a_inc_lookup_ftv : forall Θ0 κ Θ α,
  κ ∷ Θ0 ⊑ Θ ->
  ftvar_in_ptyp (msubst_lookup κ α) [<=] add α (dom Θ).
Proof.
  intros Θ0 κ Θ α H; revert α; induction H; intros α0; cbn.
  - clear; fsetdec.
  - destruct (α0 == α) as [-> | Hne].
    + assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ')
        by (eapply a_wf_ptyp_ftv_dom; eassumption).
      clear - Hsc; fsetdec.
    + apply IHa_inc.
  - destruct (α0 == α) as [-> | Hne].
    + assert (Hsc : ftvar_in_ptyp τ' [<=] dom Θ')
        by (eapply a_wf_ptyp_ftv_dom; eassumption).
      clear - Hsc; fsetdec.
    + apply IHa_inc.
  - specialize (IHa_inc α0); simpl_env; clear - IHa_inc; fsetdec.
  - specialize (IHa_inc α0); simpl_env; clear - IHa_inc; fsetdec.
  - specialize (IHa_inc α0); simpl_env; clear - IHa_inc; fsetdec.
Qed.

Lemma msubst_ftv_app_wf : forall Θ κa κb,
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa ->
  (forall α, ftvar_in_ptyp (msubst_lookup κb α) [<=] add α (dom Θ)) ->
  forall α, ftvar_in_ptyp (msubst_lookup (κa ++ κb) α) [<=] add α (dom Θ).
Proof.
  intros Θ κa κb Hall Hsc α.
  induction κa as [ | [α1 τ1] κa' IH ]; cbn; [ apply Hsc | ].
  inversion Hall as [ | ph pt [Hwf1 Hm1] Hall' ]; subst; cbn in Hwf1.
  destruct (α == α1) as [-> | Hne].
  - assert (Hs1 : ftvar_in_ptyp τ1 [<=] dom Θ)
      by (eapply a_wf_ptyp_ftv_dom; exact Hwf1).
    clear - Hs1; fsetdec.
  - apply IH; exact Hall'.
Qed.

Lemma msubst_pskl_ftv_fresh : forall (Θ : aenv) κ P β,
  (forall α, ftvar_in_ptyp (msubst_lookup κ α) [<=] add α (dom Θ)) ->
  β `notin` ftvar_in_pskl P ->
  β `notin` dom Θ ->
  β `notin` ftvar_in_pskl (msubst_pskl κ P).
Proof.
  intros Θ κ P β Hsc; revert P;
    induction P as [ | n | α | P1 IH1 P2 IH2 | P0 IH0 | | P0 IH0 ];
    intros HβP HβΘ; cbn in *; try solve [ clear; fsetdec ].
  - assert (Hb : ftvar_in_pskl (ptyp_to_pskl (msubst_lookup κ α))
                 [<=] ftvar_in_ptyp (msubst_lookup κ α))
      by (apply ptyp_to_pskl_ftv).
    specialize (Hsc α). clear - Hb Hsc HβP HβΘ; fsetdec.
  - specialize (IH1 ltac:(clear - HβP; solve_notin_auto) HβΘ).
    specialize (IH2 ltac:(clear - HβP; solve_notin_auto) HβΘ).
    clear - IH1 IH2; fsetdec.
  - apply IH0; assumption.
  - apply IH0; assumption.
Qed.

Lemma ad_precise_all_of_one : forall Θ Δ S0 X0 β,
  {{ Θ ⨟ (add β Δ) ⊢ₚᵣ (open_pskl_wrt_pskl S0 (pskl_var_f β))
                  ⊑ (open_pskl_wrt_pskl X0 (pskl_var_f β)) }}ad ->
  {{ ⊢ Θ }}a ->
  β `notin` dom Θ -> β `notin` Δ ->
  β `notin` ftvar_in_pskl S0 -> β `notin` ftvar_in_pskl X0 ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (pskl_all_syn S0) ⊑ (pskl_all_syn X0) }}ad.
Proof.
  intros Θ Δ S0 X0 β Hpre HwfΘ HβΘ HβΔ HβS HβX.
  unfold ad_precise; cbn [pskl_to_bskl_inh].
  apply ad_refine_syn_all_intro
    with (L := add β (Δ `union` dom Θ `union` ftvar_in_pskl S0
                        `union` ftvar_in_pskl X0)).
  intros α0 Hα0.
  rewrite <- ! pskl_to_bskl_inh_open.
  eapply ad_refine_syn_defs_mono;
    [ | intros γ τ Hb; apply binds_app_iff; right; exact Hb ].
  change (ad_refine_syn Θ (add α0 Δ)
            (pskl_to_bskl_inh (open_pskl_wrt_pskl S0 (pskl_var_f α0)))
            (pskl_to_bskl_inh (open_pskl_wrt_pskl X0 (pskl_var_f α0)))).
  assert (Hsub : add α0 Δ [<=] add α0 (remove β (add β Δ)))
    by (clear - HβΔ; fsetdec).

  eapply ad_refine_syn_delta_mono; [ | exact Hsub ].
  rewrite (subst_pskl_in_pskl_intro β S0 (pskl_var_f α0)) by exact HβS.
  rewrite (subst_pskl_in_pskl_intro β X0 (pskl_var_f α0)) by exact HβX.
  apply ad_precise_rename_delta;
    [ exact Hpre | exact HwfΘ | exact HβΘ | clear; fsetdec
    | clear - Hα0; fsetdec | ].
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper X0 (pskl_var_f β)) as Hup.
  cbn in Hup. clear - Hup Hα0; fsetdec.
Qed.

Lemma a_binds_tvar_app_minus : forall (Ξ Θ : aenv) Δ γ,
  a_binds_tvar γ (Ξ ++ aenv_minus Θ Δ) ->
  a_binds_tvar γ (Ξ ++ Θ) /\ (γ `in` dom Ξ \/ γ `notin` Δ).
Proof.
  intros Ξ Θ Δ γ H. unfold a_binds_tvar in *.
  destruct H as [Hb | [Hb | [τ Hb]]]; apply binds_app_iff in Hb;
    destruct Hb as [Hb | Hb];
    [ | apply binds_aenv_minus in Hb; destruct Hb as [Hb HγΔ]
    | | apply binds_aenv_minus in Hb; destruct Hb as [Hb HγΔ]
    | | apply binds_aenv_minus in Hb; destruct Hb as [Hb HγΔ] ];
    (split;
     [ first [ left; apply binds_app_iff; solve [ auto ]
             | right; left; apply binds_app_iff; solve [ auto ]
             | right; right; exists τ; apply binds_app_iff; solve [ auto ] ]
     | first [ right; exact HγΔ | left; eapply binds_In; exact Hb ] ]).
Qed.

Lemma a_guess_ty_witness : forall n Θ0 Θ κs Δ Δ0 Ps X,
  size_pskl Ps <= n ->
  {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ Δ0 ⊢ₚₛ Ps }}a ->
  msubst_lc κs ->
  (forall α, ftvar_in_ptyp (msubst_lookup κs α) [<=] add α (dom Θ)) ->
  pskl_ghost_free X -> lc_pskl X ->
  (forall γ, γ `in` ftvar_in_pskl X -> γ `notin` Δ -> a_binds_tvar γ Θ) ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_pskl κs Ps) ⊑ X }}ad ->
  forall L, exists Ξ' A κ',
    (forall Θg, ftvar_in_aenv Θg [<=] L -> a_guess_mono Θg Ps Ξ' A) /\
    all_flex_mono Ξ' /\
    uniq Ξ' /\
    keys κ' = keys Ξ' /\
    (forall α, α `in` dom Ξ' -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
    {{ (Ξ' ++ Θ0) ⨟ Δ0 ⊢ₚₛ (ptyp_to_pskl A) }}a /\
    {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_pskl (κ' ++ κs) (ptyp_to_pskl A)) ⊑ X }}ad.
Proof.
  intros n; induction n as [ | n IH ];
    intros Θ0 Θ κs Δ Δ0 Ps X Hsz HwfΘ HwfPs Hκlc Hκsc Hgf Hlc HscX Hprec L.
  -
    exfalso. pose proof (size_pskl_min Ps) as Hm.
    clear - Hsz Hm. inversion Hsz; lia.
  - assert (HlcPs : lc_pskl Ps) by (eapply a_wf_pskl_lc; exact HwfPs).
    destruct Ps as [ | m | α | Ps1 Ps2 | Ps0 | | Ps0 ].
    +
      exists nil, ptyp_unit, nil.
      split; [ intros Θg _; apply a_guess_mono__unit | ].
      split; [ apply Forall_nil | ].
      split; [ apply uniq_nil | ].
      split; [ reflexivity | ].
      split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
      split; [ apply Forall_nil | ].
      split; [ cbn; apply a_wf_pskl__unit | ].
      cbn [app ptyp_to_pskl]. exact Hprec.
    +
      exfalso. inversion HlcPs.
    +
      exists nil, (ptyp_var_f α), nil.
      split; [ intros Θg _; apply a_guess_mono__var | ].
      split; [ apply Forall_nil | ].
      split; [ apply uniq_nil | ].
      split; [ reflexivity | ].
      split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
      split; [ apply Forall_nil | ].
      split; [ cbn [app ptyp_to_pskl]; exact HwfPs | ].
      cbn [app ptyp_to_pskl]. exact Hprec.
    +
      cbn in Hsz.
      assert (HwfPs1 : {{ Θ0 ⨟ Δ0 ⊢ₚₛ Ps1 }}a) by (inversion HwfPs; subst; assumption).
      assert (HwfPs2 : {{ Θ0 ⨟ Δ0 ⊢ₚₛ Ps2 }}a) by (inversion HwfPs; subst; assumption).
      assert (Hpre' : {{ Θ ⨟ Δ ⊢ᵣ
                (bskl_arrow (pskl_to_bskl_inh (msubst_pskl κs Ps1))
                            (pskl_to_bskl_inh (msubst_pskl κs Ps2)))
                ⊳ (pskl_to_bskl_inh X) }}ad)
        by (unfold ad_precise in Hprec; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_arrow_l_inv Θ Δ _ _ Hpre'
                  (msubst_pskl κs Ps1) (msubst_pskl κs Ps2) X
                  eq_refl eq_refl HwfΘ Hgf Hlc HscX)
        as (X1 & X2 & Hg1 & Hg2 & Hl1 & Hl2 & Hs1 & Hs2 & Hp1 & Hp2 & Hreplay).
      destruct (IH Θ0 Θ κs Δ Δ0 Ps1 X1 ltac:(clear - Hsz; lia)
                   HwfΘ HwfPs1 Hκlc Hκsc Hg1 Hl1 Hs1 Hp1
                   (L `union` ftvar_in_pskl Ps1 `union` ftvar_in_pskl Ps2))
        as (Ξ1 & A1 & κa & Hgu1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hwf1 & Hpr1).
      destruct (IH Θ0 Θ κs Δ Δ0 Ps2 X2 ltac:(clear - Hsz; lia)
                   HwfΘ HwfPs2 Hκlc Hκsc Hg2 Hl2 Hs2 Hp2
                   (L `union` ftvar_in_pskl Ps1 `union` ftvar_in_pskl Ps2
                      `union` dom Ξ1))
        as (Ξ2 & A2 & κb & Hgu2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hwf2 & Hpr2).
      assert (Hdκa : dom κa [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).
      assert (Hdκb : dom κb [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
      assert (HA1 : ftvar_in_pskl (ptyp_to_pskl A1)
                    [<=] ftvar_in_pskl Ps1 `union` dom Ξ1).
      { assert (Hb : ftvar_in_ptyp A1 [<=] ftvar_in_pskl Ps1 `union` dom Ξ1)
          by (eapply a_guess_mono_ftv; apply (Hgu1 nil); simpl; fsetdec).
        assert (Hc : ftvar_in_pskl (ptyp_to_pskl A1) [<=] ftvar_in_ptyp A1)
          by (apply ptyp_to_pskl_ftv).
        clear - Hb Hc; fsetdec. }
      assert (HA2 : ftvar_in_pskl (ptyp_to_pskl A2)
                    [<=] ftvar_in_pskl Ps2 `union` dom Ξ2).
      { assert (Hb : ftvar_in_ptyp A2 [<=] ftvar_in_pskl Ps2 `union` dom Ξ2)
          by (eapply a_guess_mono_ftv; apply (Hgu2 nil); simpl; fsetdec).
        assert (Hc : ftvar_in_pskl (ptyp_to_pskl A2) [<=] ftvar_in_ptyp A2)
          by (apply ptyp_to_pskl_ftv).
        clear - Hb Hc; fsetdec. }
      assert (Hdisj : disjoint Ξ1 Ξ2).
      { unfold disjoint. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hα0 Hfr2; fsetdec. }
      assert (Heq1 : msubst_pskl (κa ++ κb ++ κs) (ptyp_to_pskl A1)
                     = msubst_pskl (κa ++ κs) (ptyp_to_pskl A1)).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0 Hdκb; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hfr2 HA1; fsetdec. }
      assert (Heq2 : msubst_pskl (nil ++ κa ++ (κb ++ κs)) (ptyp_to_pskl A2)
                     = msubst_pskl (nil ++ (κb ++ κs)) (ptyp_to_pskl A2)).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin1 : α0 `in` dom Ξ1) by (clear - Hα0 Hdκa; fsetdec).
        specialize (Hfr1 α0 Hin1).
        assert (Hne : α0 `notin` dom Ξ2)
          by (clear - Hin1 Hdisj; unfold disjoint in Hdisj; fsetdec).
        clear - Hfr1 Hne HA2; fsetdec. }
      cbn [app] in Heq2.
      exists (Ξ1 ++ Ξ2), (ptyp_arrow A1 A2), (κa ++ κb).
      split; [ intros Θg Hsub; apply a_guess_mono__arrow;
               [ apply Hgu1 | apply Hgu2 ]; clear - Hsub; fsetdec | ].
      split; [ apply all_flex_mono_app; assumption | ].
      split; [ clear - Hu1 Hu2 Hdisj; solve_uniq | ].
      split; [ rewrite ! keys_app; rewrite Hk1, Hk2; reflexivity | ].
      split; [ intros α0 Hα0; rewrite dom_app in Hα0;
               destruct (union_1 Hα0) as [Hin1 | Hin2];
                 [ specialize (Hfr1 α0 Hin1); clear - Hfr1; fsetdec
                 | specialize (Hfr2 α0 Hin2); clear - Hfr2; fsetdec ] | ].
      split; [ apply Forall_app; split; assumption | ].
      split.
      { rewrite app_assoc. cbn [ptyp_to_pskl]. apply a_wf_pskl__arrow.
        - eapply a_wf_pskl_weaken; [ | exact Hwf1 ].
          intros x b Hb. apply binds_weaken. exact Hb.
        - eapply a_wf_pskl_weaken; [ | exact Hwf2 ].
          intros x b Hb. apply binds_app_3. exact Hb. }
      rewrite app_assoc. cbn [ptyp_to_pskl msubst_pskl].
      rewrite Heq1, Heq2.
      apply Hreplay; assumption.
    +
      cbn in Hsz.
      assert (HwfF : exists Lw, forall β, β `notin` Lw ->
                {{ ((β ~ abind_tvar) ++ Θ0) ⨟ (add β Δ0) ⊢ₚₛ
                   (open_pskl_wrt_pskl Ps0 (pskl_var_f β)) }}a)
        by (inversion HwfPs; subst; eexists; eassumption).
      destruct HwfF as [Lw HwfF].
      assert (Hpre' : {{ Θ ⨟ Δ ⊢ᵣ
                (bskl_all_inh (pskl_to_bskl_inh (msubst_pskl κs Ps0)))
                ⊳ (pskl_to_bskl_inh X) }}ad)
        by (unfold ad_precise in Hprec; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_all_l_inv Θ Δ _ _ Hpre' (msubst_pskl κs Ps0) X
                  eq_refl eq_refl HwfΘ Hgf Hlc)
        as (X0 & Lp & HeqX & HprF).
      subst X.
      assert (HgfX0 : pskl_ghost_free X0) by (cbn in Hgf; exact Hgf).
      assert (HlcX0 : forall α0,
                lc_pskl (open_pskl_wrt_pskl X0 (pskl_var_f α0)))
        by (inversion Hlc; subst; assumption).
      pick fresh β for (L `union` Lw `union` Lp `union` Δ `union` Δ0
                          `union` ftvar_in_pskl Ps0 `union` ftvar_in_pskl X0
                          `union` dom Θ `union` dom Θ0 `union` dom κs).
      assert (HwfβPs : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ (add β Δ0) ⊢ₚₛ
                (open_pskl_wrt_pskl Ps0 (pskl_var_f β)) }}a)
        by (apply HwfF; clear - Fr; fsetdec).
      assert (HscβX : forall γ,
                γ `in` ftvar_in_pskl (open_pskl_wrt_pskl X0 (pskl_var_f β)) ->
                γ `notin` add β Δ -> a_binds_tvar γ Θ).
      { intros γ Hγ HγΔ. apply HscX; [ | clear - HγΔ; fsetdec ].
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper X0 (pskl_var_f β))
          as Hup.
        cbn in Hup |- *. clear - Hup Hγ HγΔ; fsetdec. }
      assert (HprβX : {{ Θ ⨟ (add β Δ) ⊢ₚᵣ
                (msubst_pskl κs (open_pskl_wrt_pskl Ps0 (pskl_var_f β)))
                ⊑ (open_pskl_wrt_pskl X0 (pskl_var_f β)) }}ad).
      { rewrite (@msubst_pskl_open_lc κs Ps0 β Hκlc
                   ltac:(clear - Fr; solve_notin_auto)).
        apply HprF; clear - Fr; fsetdec. }
      destruct (IH ((β ~ abind_tvar) ++ Θ0) Θ κs (add β Δ) (add β Δ0)
                   (open_pskl_wrt_pskl Ps0 (pskl_var_f β))
                   (open_pskl_wrt_pskl X0 (pskl_var_f β))
                   ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var;
                         clear - Hsz; lia)
                   HwfΘ HwfβPs Hκlc Hκsc
                   ltac:(unfold open_pskl_wrt_pskl;
                         apply pskl_ghost_free_open_rec; exact HgfX0)
                   ltac:(apply HlcX0)
                   HscβX HprβX
                   (add β (L `union` dom Θ `union` dom Θ0
                             `union` ftvar_in_pskl Ps0
                             `union` ftvar_in_pskl X0)))
        as (Ξ' & A' & κ' & Hgu & Hfm & Hu & Hk & Hfr & HF & Hwf' & Hpr).

      assert (HβΞ : β `notin` dom Ξ')
        by (intro Hc; specialize (Hfr β Hc); clear - Hfr; fsetdec).
      assert (HopenA : open_ptyp_wrt_ptyp (close_ptyp_wrt_ptyp β A')
                         (ptyp_var_f β) = A')
        by (apply open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp).
      assert (HβA : β `notin` ftvar_in_ptyp (close_ptyp_wrt_ptyp β A'))
        by (rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp; clear; fsetdec).
      assert (HβPA : β `notin` ftvar_in_pskl
                       (ptyp_to_pskl (close_ptyp_wrt_ptyp β A'))).
      { assert (Hc : ftvar_in_pskl (ptyp_to_pskl (close_ptyp_wrt_ptyp β A'))
                     [<=] ftvar_in_ptyp (close_ptyp_wrt_ptyp β A'))
          by (apply ptyp_to_pskl_ftv).
        clear - Hc HβA; fsetdec. }
      assert (HopenPA : ptyp_to_pskl A'
                = open_pskl_wrt_pskl
                    (ptyp_to_pskl (close_ptyp_wrt_ptyp β A')) (pskl_var_f β))
        by (rewrite <- ptyp_to_pskl_open; rewrite HopenA; reflexivity).
      exists Ξ', (ptyp_all (close_ptyp_wrt_ptyp β A')), κ'.
      split.
      {
        intros Θg Hsub.
        eapply a_guess_mono_all_of_one with (β := β);
          [ rewrite HopenA; apply Hgu;
            rewrite ftvar_in_aenv_app; rewrite ftvar_in_aenv_one;
            cbn [ftvar_in_abind]; clear - Hsub; fsetdec
          | clear - Hsub Fr; fsetdec
          | clear - Fr; fsetdec
          | exact HβA ]. }
      split; [ exact Hfm | ].
      split; [ exact Hu | ].
      split; [ exact Hk | ].
      split; [ intros α0 Hα0; specialize (Hfr α0 Hα0);
               clear - Hfr; fsetdec | ].
      split; [ exact HF | ].
      split.
      { cbn [ptyp_to_pskl].
        apply a_wf_pskl_all_of_one_at with (β := β); [ | exact HβPA ].
        rewrite <- HopenPA.
        eapply a_wf_pskl_tvar_mono; [ exact Hwf' | ].
        intros γ [Hb | [Hb | [τ Hb]]];
          [ left | right; left | right; right; exists τ ];
          apply binds_mid_to_front; exact Hb. }

      assert (Hβκ : β `notin` ftvar_in_pskl
                (msubst_pskl (κ' ++ κs)
                   (ptyp_to_pskl (close_ptyp_wrt_ptyp β A')))).
      { eapply msubst_pskl_ftv_fresh;
          [ eapply msubst_ftv_app_wf; [ exact HF | exact Hκsc ]
          | exact HβPA
          | clear - Fr; fsetdec ]. }
      cbn [ptyp_to_pskl msubst_pskl].
      eapply ad_precise_all_of_one with (β := β);
        [ | exact HwfΘ | clear - Fr; fsetdec | clear - Fr; fsetdec
        | exact Hβκ | clear - Fr; fsetdec ].
      rewrite <- (@msubst_pskl_open_lc (κ' ++ κs)
                    (ptyp_to_pskl (close_ptyp_wrt_ptyp β A')) β
                    (msubst_lc_app_wf HF Hκlc)
                    ltac:(rewrite dom_app;
                          assert (Hd : dom κ' [=] dom Ξ')
                            by (apply keys_eq_dom; exact Hk);
                          clear - Hd HβΞ Fr; solve_notin_auto)).
      rewrite <- HopenPA. exact Hpr.
    +
      assert (Hpre' : {{ Θ ⨟ Δ ⊢ₚᵣ pskl_ghost ⊑ X }}ad)
        by (unfold ad_precise in Hprec |- *; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_ghost_inv_mono Θ Δ X Hpre' Hgf Hlc HscX)
        as (τ & Heqτ & Hmτ & HwfX).
      assert (Hwfτ : a_wf_ptyp Θ τ)
        by (apply a_wf_ptyp_of_wf_pskl_mono;
            [ exact Hmτ | rewrite Heqτ; exact HwfX ]).
      pick fresh α1 for (L `union` dom Θ `union` dom Θ0 `union` dom κs).
      exists ((α1 ~ abind_flex_mono) ++ nil), (ptyp_var_f α1),
             ((α1, τ) :: nil).
      split; [ intros Θg Hsub; apply a_guess_mono__ghost;
               clear - Hsub Fr; fsetdec | ].
      split; [ unfold all_flex_mono; repeat constructor | ].
      split; [ solve_uniq | ].
      split; [ reflexivity | ].
      split; [ intros α0 Hα0; simpl_env in Hα0;
               assert (Hα1 : α0 = α1) by (clear - Hα0; fsetdec);
               subst α0; clear - Fr; fsetdec | ].
      split; [ constructor; [ split; assumption | apply Forall_nil ] | ].
      split.
      { cbn [app ptyp_to_pskl]. apply a_wf_pskl__var. right. left.
        unfold binds. left. reflexivity. }

      cbn [app ptyp_to_pskl msubst_pskl].
      rewrite msubst_lookup_cons_eq. rewrite Heqτ.
      unfold ad_precise. exact (ad_refine_syn_refl_inh_gen HwfX Θ Δ).
    +
      cbn in Hsz.
      assert (HwfPs0 : {{ (aenv_minus Θ0 Δ0) ⨟ empty ⊢ₚₛ Ps0 }}a)
        by (inversion HwfPs; subst; assumption).
      assert (Hpre' : {{ Θ ⨟ Δ ⊢ᵣ
                (bskl_univ_ghost (pskl_to_bskl_inh (msubst_pskl κs Ps0)))
                ⊳ (pskl_to_bskl_inh X) }}ad)
        by (unfold ad_precise in Hprec; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_univ_ghost_l_inv Θ Δ _ _ Hpre' (msubst_pskl κs Ps0) X
                  eq_refl eq_refl HwfΘ Hgf Hlc HscX)
        as (X' & Hg' & Hl' & Hs' & Hp' & Hreplay).
      destruct (IH (aenv_minus Θ0 Δ0) Θ κs Δ empty Ps0 X'
                   ltac:(clear - Hsz; lia)
                   HwfΘ HwfPs0 Hκlc Hκsc Hg' Hl' Hs' Hp' (L `union` Δ0))
        as (Ξ' & A & κ' & Hgu & Hfm & Hu & Hk & Hfr & HF & Hwf' & Hpr).
      exists Ξ', A, κ'.
      split; [ intros Θg Hsub; apply a_guess_mono__univ_ghost;
               apply Hgu; clear - Hsub; fsetdec | ].
      split; [ exact Hfm | ].
      split; [ exact Hu | ].
      split; [ exact Hk | ].
      split; [ intros α0 Hα0; specialize (Hfr α0 Hα0);
               clear - Hfr; fsetdec | ].
      split; [ exact HF | ].
      split.
      {
        eapply a_wf_pskl_delta_mono.
        - eapply a_wf_pskl_tvar_mono; [ exact Hwf' | ].
          intros γ Hγ. apply (proj1 (@a_binds_tvar_app_minus _ _ _ _ Hγ)).
        - intros γ Hγ HγΔ0. exfalso.
          destruct (proj2 (@a_binds_tvar_app_minus _ _ _ _
                             (a_wf_pskl_ftv_binds Hwf' Hγ))) as [HγΞ | Hγn].
          + specialize (Hfr γ HγΞ). clear - Hfr HγΔ0; fsetdec.
          + exact (Hγn HγΔ0). }
      apply Hreplay; exact Hpr.
Qed.

Theorem a_extract_complete_gen :
  forall n NM M Θ0 Θ κ Ψa Ψsub ψa Q P P0 R' α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψa ψa ->
  (ftag_in_uskl R') ∩ Ψa [=] empty ->
  ftvar_in_uskl ψa [<=] dom Θ ->
  {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψa ⌋ˢ }}a ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψa ->
  Ψa [<=] Ψsub ->

  ad_pat_sub_fuel n NM M Ψsub Θ
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) Q ->
  {{ Θ ⨟ empty ⊢ₚₛ
    (uskl_to_pskl (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R'))) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  exists Ξ Pa κa,
    ({{ Θ0 ⊢ P ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ Pa }}a) /\
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξ ++ Θ0) }}a /\
    a_decls Ξ /\
    keys κa = keys Ξ /\
    (κa ++ κ) ∷ (Ξ ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl (κa ++ κ) Pa) ⊑ ⌊ ψa ⌋ˢ }}ad.
Proof.
  intros n NM M Θ0 Θ κ Ψa Ψsub ψa Q P P0 R' α.
  intros HwfΘ HwfΘ0 HwfP0 HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR HscopeR HlcR
         Htags Hdisj Hψaw Hwfψ HΨsubU HΨsubL Hsubty
         HwfSubj Hrefine HwfQ.

  destruct (@a_looksub_solve_complete n NM M Θ0 Θ κ empty Ψa empty Ψa Ψsub ψa Q
              P P0 pskl_ghost R' α
              HwfΘ HwfΘ0 HwfP0 ltac:(apply a_wf_pskl__ghost)
              HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR HscopeR HlcR Htags Hdisj
              ltac:(clear; solve_notin_auto) Hψaw (delta_def_fresh_empty Θ)
              ltac:(cbn [msubst_pskl];
                    apply ad_ppre__ghost; [ clear; solve_notin_auto | clear; fsetdec ])
              HΨsubU HΨsubL
              Hsubty HwfSubj Hrefine HwfQ
              (ftvar_in_aenv Θ0) ltac:(clear; solve_notin_auto))
    as (𝒞 & Ξc & Ξs & Pa & κc & κs
        & Hlook & Hsolve & Hfms & Hus & Hks & Hfrs & HFs
        & HwfPa & HwfΞc & HαΞc & Hkeysc
        & HForc & Hincc & Heqv & Hκcfresh & Hprec & _ & Hapart).

  assert (Hpre : {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ ⌊ ψa ⌋ˢ }}ad).
  { eapply ad_partial_precise_complete;
      [ exact HwfΘ | exact Htags | exact Hwfψ | ].
    eapply ad_partial_precise_psi_cong; [ exact Hprec | clear; fsetdec ]. }

  assert (HfmΞc : all_flex_mono Ξc)
    by (eapply a_looksub_all_flex_mono; exact Hlook).
  assert (HwmΞc : Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κc).
  { destruct (@a_inc_flex_prefix_split Ξs κs (Ξc ++ Θ0) (κc ++ κ) Θ
                Hfms Hks Hincc) as [_ HincC].
    destruct (@a_inc_flex_prefix_split Ξc κc Θ0 κ Θ HfmΞc Hkeysc HincC)
      as [Hw _]; exact Hw. }
  assert (HfrsC : forall x, x `in` dom Ξs ->
            x `notin` ftvar_in_aenv (Ξc ++ Θ0))
    by (intros x Hx; eapply a_solve_cstr_generated_fresh;
          [ exact Hsolve | exact Hx ]).
  pose proof (a_wf_aenv_solve_block HwfΞc Hsolve Hfms Hus) as HwfΞs.
  assert (HuqΞsc : uniq (Ξs ++ Ξc ++ Θ0)) by (apply a_wf_aenv_uniq; exact HwfΞs).
  assert (Hdcs : forall β0, β0 `in` dom κc -> β0 `notin` dom κs).
  { intros β0 Hβ0 Hc.
    pose proof (@keys_eq_dom _ _ κc Ξc Hkeysc) as Hdc0.
    pose proof (@keys_eq_dom _ _ κs Ξs Hks) as Hds0.
    assert (Hinc : β0 `in` dom Ξc) by (clear - Hβ0 Hdc0; fsetdec).
    assert (Hins : β0 `in` dom Ξs) by (clear - Hc Hds0; fsetdec).
    pose proof (HfrsC β0 Hins) as Hf.
    pose proof (dom_subset_ftvar_in_aenv (Ξc ++ Θ0)) as Hdd.
    rewrite dom_app in Hdd. clear - Hf Hdd Hinc; fsetdec. }

  destruct NM.
  -
    assert (Hgfψ : pskl_ghost_free ⌊ ψa ⌋ˢ)
      by (inversion Htags; subst; apply uskl_ghost_free_to_pskl; assumption).
    assert (Hlcψ : lc_pskl ⌊ ψa ⌋ˢ) by (eapply a_wf_pskl_lc; exact Hwfψ).
    destruct (@a_guess_ty_witness (size_pskl Pa) (Ξs ++ Ξc ++ Θ0) Θ
                (κs ++ κc ++ κ) empty empty Pa ⌊ ψa ⌋ˢ
                (le_n _) HwfΘ HwfPa
                ltac:(unfold msubst_lc; intros α0;
                      eapply a_inc_msubst_lc; exact Hincc)
                ltac:(intros α0; eapply a_inc_lookup_ftv; exact Hincc)
                Hgfψ Hlcψ
                ltac:(intros γ Hγ _; eapply a_wf_pskl_ftv_binds;
                      [ exact Hwfψ | exact Hγ ])
                Hpre
                (add α (ftvar_in_aenv (Ξs ++ Ξc ++ Θ0) `union` dom Θ
                          `union` dom Θ0 `union` dom Ξc `union` dom Ξs
                          `union` dom κ
                          `union` ftvar_in_a_cstrs 𝒞
                          `union` ftvar_in_pskl Pa)))
      as (Ξ' & A & κ' & Hgu & HfmΞ' & HuqΞ' & Hkeys' & Hfr' & HF' & Hwf'
          & Hpr').
    assert (HdomΞ' : dom κ' [=] dom Ξ') by (apply keys_eq_dom; exact Hkeys').
    assert (Hdc : dom κc [=] dom Ξc) by (apply keys_eq_dom; exact Hkeysc).
    assert (Hds : dom κs [=] dom Ξs) by (apply keys_eq_dom; exact Hks).
    assert (HuqAll : uniq (Ξc ++ Ξs ++ Ξ' ++ Θ0)).
    { assert (Hd : disjoint Ξ' (Ξs ++ Ξc ++ Θ0))
        by (unfold disjoint; intros α0 Hα0; rewrite !dom_app in Hα0;
            assert (Hin : α0 `in` dom Ξ') by (clear - Hα0; fsetdec);
            specialize (Hfr' α0 Hin); clear - Hα0 Hfr'; fsetdec).
      clear - HuqΞsc HuqΞ' Hd; solve_uniq. }
    exists (Ξc ++ Ξs ++ Ξ'), (ptyp_to_pskl A), (κc ++ κs ++ κ').
    split.
    { eapply a_extract__solve;
        [ exact Hlook | exact Hsolve
        | apply a_guess__ty; apply Hgu; clear; fsetdec
        | apply inter_dom_empty_of_forall; exact Hapart

        | apply inter_dom_empty_of_forall;
          intros x Hx; specialize (Hfr' x Hx); clear - Hfr'; fsetdec ]. }
    split.
    {
      eapply a_wf_pskl_weaken; [ | exact Hwf' ].
      intros x b Hb. simpl_env. analyze_binds Hb. }
    split.
    { apply (@a_wf_aenv_flex_prefix (Ξc ++ Ξs ++ Ξ') Θ0);
        [ repeat apply all_flex_mono_app; assumption
        | simpl_env; clear - HuqAll; solve_uniq
        | exact HwfΘ0 ]. }
    split.
    { apply all_flex_mono_decls. repeat apply all_flex_mono_app; assumption. }
    split; [ rewrite ! keys_app; rewrite Hkeysc, Hks, Hkeys'; reflexivity | ].
    split.
    { apply (@a_inc_flex_prefix_build (Ξc ++ Ξs ++ Ξ') (κc ++ κs ++ κ') Θ0 κ Θ);
        [ repeat apply all_flex_mono_app; assumption
        | rewrite ! keys_app; rewrite Hkeysc, Hks, Hkeys'; reflexivity
        | repeat (apply Forall_app; split); assumption
        | exact Hκ ]. }
    split; [ exact Heqv | ].
    assert (Hd'c : forall β0, β0 `in` dom κ' -> β0 `notin` dom κc)
      by (intros β0 Hβ0;
          assert (Hin : β0 `in` dom Ξ') by (clear - Hβ0 HdomΞ'; fsetdec);
          specialize (Hfr' β0 Hin); clear - Hfr' Hdc; fsetdec).
    assert (Hd's : forall β0, β0 `in` dom κ' -> β0 `notin` dom κs)
      by (intros β0 Hβ0;
          assert (Hin : β0 `in` dom Ξ') by (clear - Hβ0 HdomΞ'; fsetdec);
          specialize (Hfr' β0 Hin); clear - Hfr' Hds; fsetdec).
    assert (Hdc' : forall β0, β0 `in` dom κc -> β0 `notin` dom κ')
      by (intros β0 Hβ0 Hc; exact (Hd'c β0 Hc Hβ0)).
    assert (Hperm : msubst_pskl ((κc ++ κs ++ κ') ++ κ) (ptyp_to_pskl A)
                  = msubst_pskl (κ' ++ κs ++ κc ++ κ) (ptyp_to_pskl A)).
    { rewrite (list_app_assoc κc (κs ++ κ') κ).
      rewrite (list_app_assoc κs κ' κ).
      apply msubst_pskl_lookup_congr. intro β0.

      rewrite (@msubst_lookup_app_swap κc κs (κ' ++ κ) β0 Hdcs).
      rewrite (@msubst_lookup_app_swap κ' κs (κc ++ κ) β0 Hd's).
      apply msubst_lookup_app_agree.
      apply (@msubst_lookup_app_swap κc κ' κ β0 Hdc'). }
    rewrite Hperm. exact Hpr'.
  -
    exists (Ξc ++ Ξs ++ nil), Pa, (κc ++ κs ++ nil).
    split.
    { eapply a_extract__solve;
        [ exact Hlook | exact Hsolve | apply a_guess__sk
        | apply inter_dom_empty_of_forall; exact Hapart

        | simpl; clear; fsetdec ]. }
    rewrite ! app_nil_r.
    split.
    { eapply a_wf_pskl_weaken; [ | exact HwfPa ].
      intros x b Hb. simpl_env. analyze_binds Hb. }
    split.
    { apply (@a_wf_aenv_flex_prefix (Ξc ++ Ξs) Θ0);
        [ apply all_flex_mono_app; assumption
        | simpl_env; clear - HuqΞsc; solve_uniq
        | exact HwfΘ0 ]. }
    split; [ apply all_flex_mono_decls; apply all_flex_mono_app; assumption | ].
    split; [ rewrite ! keys_app; rewrite Hkeysc, Hks; reflexivity | ].
    split.
    { apply (@a_inc_flex_prefix_build (Ξc ++ Ξs) (κc ++ κs) Θ0 κ Θ);
        [ apply all_flex_mono_app; assumption
        | rewrite ! keys_app; rewrite Hkeysc, Hks; reflexivity
        | apply Forall_app; split; assumption
        | exact Hκ ]. }
    split; [ exact Heqv | ].
    rewrite (list_app_assoc κc κs κ).
    rewrite (@msubst_pskl_app_swap κc κs κ Pa Hdcs).
    exact Hpre.
Qed.

Corollary a_extract_complete :
  forall n NM M Θ0 Θ κ Ψa ψa Q P P0 R' α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψa ψa ->
  (ftag_in_uskl R') ∩ Ψa [=] empty ->
  ftvar_in_uskl ψa [<=] dom Θ ->
  {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψa ⌋ˢ }}a ->
  ad_pat_sub_fuel n NM M Ψa Θ
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) Q ->
  {{ Θ ⨟ empty ⊢ₚₛ
    (uskl_to_pskl (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R'))) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  exists Ξ Pa κa,
    ({{ Θ0 ⊢ P ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ Pa }}a) /\
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξ ++ Θ0) }}a /\
    a_decls Ξ /\
    keys κa = keys Ξ /\
    (κa ++ κ) ∷ (Ξ ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl (κa ++ κ) Pa) ⊑ ⌊ ψa ⌋ˢ }}ad.
Proof.
  intros n NM M Θ0 Θ κ Ψa ψa Q P P0 R' α.
  intros HwfΘ HwfΘ0 HwfP0 HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR HscopeR HlcR
         Htags Hdisj Hψaw Hwfψ Hsubty HwfSubj Hrefine HwfQ.
  eapply a_extract_complete_gen with (Ψsub := Ψa);
    [ exact HwfΘ | exact HwfΘ0 | exact HwfP0 | exact HmodSK | exact HmodTY
    | exact Hκ | exact HαΘ | exact HαΘ0 | exact HeraseR | exact HscopeR
    | exact HlcR | exact Htags | exact Hdisj
    | exact Hψaw
    | exact Hwfψ
    | clear; fsetdec | clear; fsetdec
    | exact Hsubty | exact HwfSubj | exact Hrefine | exact HwfQ ].
Qed.
