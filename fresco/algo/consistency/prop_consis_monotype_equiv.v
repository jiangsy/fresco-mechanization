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

Set Implicit Arguments.

Lemma consis_mono_join : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall A, R = ptyp_to_uskl_syn A -> mono_ptyp A ->
  exists C, mono_ptyp C /\ Qt = ptyp_to_bskl_syn C /\ {{ Θ ⊢ A ≡ᵗ C }}a.
Proof.
  intros Ψ Θ R Qt Hc Hwf; induction Hc; intros A0 HeqS HmA0;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in *.
  -
    destruct HmA0 as [ | α0 | A1 A2 Hm1 Hm2 ]; simpl in HeqS; try discriminate.
    exists ptyp_unit.
    split; [ apply mono_ptyp__unit | ].
    split; [ reflexivity | ].
    apply a_tyequiv__refl; apply lc_ptyp_unit.
  -
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    exists (ptyp_var_f α0).
    split; [ apply mono_ptyp__var | ].
    split; [ reflexivity | ].
    apply a_tyequiv__refl; apply lc_ptyp_var_f.
  -
    destruct HmA0 as [ | | A1 A2 Hm1 Hm2 ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    destruct (IHHc1 Hwf A1 eq_refl Hm1) as [C1 [HmC1 [HeqQ1 He1]]].
    destruct (IHHc2 Hwf A2 eq_refl Hm2) as [C2 [HmC2 [HeqQ2 He2]]].
    exists (ptyp_arrow C1 C2).
    split; [ apply mono_ptyp__arrow; auto | ].
    split; [ simpl; rewrite HeqQ1, HeqQ2; reflexivity | ].
    apply a_tyequiv__arrow; auto.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHc Hwf τ eq_refl Hmτ) as [C [HmC [HeqQ He]]].
    exists C.
    split; [ exact HmC | ].
    split; [ exact HeqQ | ].
    eapply a_tyequiv__trans;
      [ apply a_tyequiv__flex_def; eassumption | exact He ].
  -
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHc Hwf A0 HeqS HmA0) as [C [HmC [HeqQ He]]].
    assert (Hτ : C = τ)
      by (apply ptyp_to_bskl_syn_inj; auto;
          unfold ptyp_to_bskl_syn; rewrite <- HeqQ; reflexivity).
    subst C.
    exists (ptyp_var_f α).
    split; [ apply mono_ptyp__var | ].
    split; [ reflexivity | ].
    eapply a_tyequiv__trans;
      [ exact He
      | apply a_tyequiv__sym; apply a_tyequiv__flex_def; eassumption ].
Qed.

Lemma refine_mono_join : forall Θ Δ Qb Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qb ⊳ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall A, Qb = ptyp_to_bskl_syn A -> mono_ptyp A ->
  exists C, mono_ptyp C /\ Qt = ptyp_to_bskl_syn C /\ {{ Θ ⊢ A ≡ᵗ C }}a.
Proof.
  intros Θ Δ Qb Qt Hr Hwf; induction Hr; intros B0 HeqB HmB0;
    unfold ptyp_to_bskl_syn in *.
  -
    destruct HmB0 as [ | α0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
    exists ptyp_unit.
    split; [ apply mono_ptyp__unit | ].
    split; [ reflexivity | ].
    apply a_tyequiv__refl; apply lc_ptyp_unit.
  -
    destruct HmB0 as [ | α0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
    inversion HeqB; subst.
    exists (ptyp_var_f α0).
    split; [ apply mono_ptyp__var | ].
    split; [ reflexivity | ].
    apply a_tyequiv__refl; apply lc_ptyp_var_f.
  -
    destruct HmB0 as [ | α0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
    inversion HeqB; subst.
    destruct (IHHr1 Hwf B1 eq_refl Hm1) as [C1 [HmC1 [HeqQ1 He1]]].
    destruct (IHHr2 Hwf B2 eq_refl Hm2) as [C2 [HmC2 [HeqQ2 He2]]].
    exists (ptyp_arrow C1 C2).
    split; [ apply mono_ptyp__arrow; auto | ].
    split; [ simpl; rewrite HeqQ1, HeqQ2; reflexivity | ].
    apply a_tyequiv__arrow; auto.
  -  destruct HmB0; simpl in HeqB; discriminate.
  -
    destruct HmB0; simpl in HeqB; discriminate.
  -  destruct HmB0; simpl in HeqB; discriminate.
  -  destruct HmB0; simpl in HeqB; discriminate.
  -  destruct HmB0; simpl in HeqB; discriminate.
  -
    destruct HmB0 as [ | α0 | B1 B2 Hm1 Hm2 ]; simpl in HeqB; try discriminate.
    inversion HeqB; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHr Hwf τ eq_refl Hmτ) as [C [HmC [HeqQ He]]].
    exists C.
    split; [ exact HmC | ].
    split; [ exact HeqQ | ].
    eapply a_tyequiv__trans;
      [ apply a_tyequiv__flex_def; eassumption | exact He ].
  -
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHr Hwf B0 HeqB HmB0) as [C [HmC [HeqQ He]]].
    assert (Hτ : C = τ)
      by (apply ptyp_to_bskl_syn_inj; auto;
          unfold ptyp_to_bskl_syn; rewrite <- HeqQ; reflexivity).
    subst C.
    exists (ptyp_var_f α).
    split; [ apply mono_ptyp__var | ].
    split; [ reflexivity | ].
    eapply a_tyequiv__trans;
      [ exact He
      | apply a_tyequiv__sym; apply a_tyequiv__flex_def; eassumption ].
Qed.

Theorem consis_refine_mono_tyequiv : forall Θ A A' Qt,
  {{ ⊢ Θ }}a ->
  mono_ptyp A ->
  mono_ptyp A' ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ Qt }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (ptyp_to_pskl A')) ⊳ Qt }}ad ->
  {{ Θ ⊢ A ≡ᵗ A' }}a.
Proof.
  intros Θ A A' Qt Hwf HmA HmB Hc Hr.
  rewrite (ptyp_to_bskl_inh_syn_eq HmB) in Hr.
  destruct (consis_mono_join Hc Hwf (A := A) eq_refl HmA) as [C  [HmC  [HeqC  HeA]]].
  destruct (refine_mono_join Hr Hwf (A := A') eq_refl HmB) as [C' [HmC' [HeqC' HeB]]].
  assert (HCC : C = C')
    by (apply ptyp_to_bskl_syn_inj; auto; rewrite <- HeqC, <- HeqC'; reflexivity).
  subst C'.
  eapply a_tyequiv__trans; [ exact HeA | apply a_tyequiv__sym; exact HeB ].
Qed.

Lemma consis_mono_refl : forall A Θ,
  mono_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ (ptyp_to_bskl_syn A) }}ad.
Proof.
  intros A Θ Hm; unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  induction Hm; intros Hvis; simpl.
  - apply ad_pat_consis__unit. fsetdec.
  - apply ad_pat_consis__var; [ fsetdec | apply Hvis; simpl; fsetdec ].
  - apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHm1 | apply IHHm2 | fsetdec ];
      intros α Hα; apply Hvis; simpl; fsetdec.
Qed.

Lemma consis_mono_sym : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall A A', R = ptyp_to_uskl_syn A -> Qt = ptyp_to_bskl_syn A' ->
  mono_ptyp A -> mono_ptyp A' ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A') ∼ (ptyp_to_bskl_syn A) }}ad.
Proof.
  intros Ψ Θ R Qt Hc Hwf; induction Hc; intros A0 B0 HeqS HeqQ HmA0 HmB0;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in *.
  -
    destruct HmA0; simpl in HeqS; try discriminate.
    destruct HmB0; simpl in HeqQ; try discriminate.
    simpl. apply ad_pat_consis__unit. fsetdec.
  -
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    destruct HmB0 as [ | β0 | ]; simpl in HeqQ; try discriminate.
    inversion HeqS; inversion HeqQ; subst.
    simpl. apply ad_pat_consis__var; [ fsetdec | assumption ].
  -
    destruct HmA0 as [ | | A1 A2 Hm1 Hm2 ]; simpl in HeqS; try discriminate.
    destruct HmB0 as [ | | B1 B2 Hn1 Hn2 ]; simpl in HeqQ; try discriminate.
    inversion HeqS; inversion HeqQ; subst.
    simpl. apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ eapply IHHc1 | eapply IHHc2 | fsetdec ]; eauto.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -  destruct HmA0; simpl in HeqS; discriminate.
  -
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
  -
    destruct HmB0 as [ | β0 | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_pat_consis__flex_l; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

Lemma ad_pat_consis_psi_cong : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Ψ', Ψ [=] Ψ' ->
  {{ Ψ' ⨟ Θ ⊢ˢ R ∼ Q }}ad.
Proof.
  intros Ψ Θ R Q H; induction H; intros Ψ' Heq;
    econstructor; eauto; fsetdec.
Qed.

Lemma a_tyequiv_mono_vis : forall Θ A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ ⊢ Θ }}a ->
  ((mono_ptyp A /\ (forall α0, α0 `in` ftvar_in_ptyp A -> a_binds_tvar α0 Θ)) ->
   (mono_ptyp A' /\ (forall α0, α0 `in` ftvar_in_ptyp A' -> a_binds_tvar α0 Θ))) /\
  ((mono_ptyp A' /\ (forall α0, α0 `in` ftvar_in_ptyp A' -> a_binds_tvar α0 Θ)) ->
   (mono_ptyp A /\ (forall α0, α0 `in` ftvar_in_ptyp A -> a_binds_tvar α0 Θ))).
Proof.
  intros * Heq Hwf; induction Heq; split; intros [Hm Hv];
    try solve [ split; assumption ]; try tauto.
  -
    split.
    + eapply a_wf_aenv_binds_def_mono; eauto.
    + intros α0 Hα0.
      eapply a_wf_ptyp_ftv_tvarish;
        [ eapply a_wf_aenv_binds_def_wf; eauto | exact Hα0 ].
  -
    split; [ apply mono_ptyp__var | ].
    intros α0 Hα0. simpl in Hα0.
    assert (α0 = α) by (clear - Hα0; fsetdec). subst.
    right; right; exists τ; assumption.
  -
    inversion Hm as [ | | ? ? Hm1 Hm2 ]; subst; simpl in Hv.
    destruct (IHHeq1 Hwf) as [IH1 _]. destruct (IHHeq2 Hwf) as [IH2 _].
    destruct (IH1 (conj Hm1
        (fun α0 Hα0 => Hv α0 (union_2 _ Hα0)))) as [HmB1 HvB1].
    destruct (IH2 (conj Hm2
        (fun α0 Hα0 => Hv α0 (union_3 _ Hα0)))) as [HmB2 HvB2].
    split; [ apply mono_ptyp__arrow; auto | ].
    intros α0 Hα0; simpl in Hα0.
    destruct (union_1 Hα0); auto.
  -
    inversion Hm as [ | | ? ? Hm1 Hm2 ]; subst; simpl in Hv.
    destruct (IHHeq1 Hwf) as [_ IH1]. destruct (IHHeq2 Hwf) as [_ IH2].
    destruct (IH1 (conj Hm1
        (fun α0 Hα0 => Hv α0 (union_2 _ Hα0)))) as [HmA1 HvA1].
    destruct (IH2 (conj Hm2
        (fun α0 Hα0 => Hv α0 (union_3 _ Hα0)))) as [HmA2 HvA2].
    split; [ apply mono_ptyp__arrow; auto | ].
    intros α0 Hα0; simpl in Hα0.
    destruct (union_1 Hα0); auto.
  -
    inversion Hm.
  -
    inversion Hm.
Qed.

Lemma consis_unfold_def_subject : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall α1 τ, R = uskl_var_f α1 ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn τ) ∼ Qt }}ad.
Proof.
  intros * Hc Hwf; induction Hc; intros α10 τ0 HeqS Hb;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    eapply ad_pat_consis__flex_r; [ exact Hb | ].
    eapply ad_pat_consis_psi_cong;
      [ apply consis_mono_refl | clear - H; fsetdec ].
    + eapply a_wf_aenv_binds_def_mono; eauto.
    + intros β Hβ.
      eapply a_wf_ptyp_ftv_tvarish;
        [ eapply a_wf_aenv_binds_def_wf; eauto | exact Hβ ].
  -
    inversion HeqS; subst.
    assert (Huniq : uniq Θ) by (apply a_wf_aenv_uniq; auto).
    assert (Heqτ : abind_flex_mono_def τ = abind_flex_mono_def τ0)
      by (eapply binds_unique; eauto).
    inversion Heqτ; subst.
    exact Hc.
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

Lemma consis_arrow_subject_transport : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  forall R1 R2 R1' R2',
  R = uskl_arrow R1 R2 ->
  (forall Ψ' Q', {{ Ψ' ⨟ Θ ⊢ˢ R1 ∼ Q' }}ad -> {{ Ψ' ⨟ Θ ⊢ˢ R1' ∼ Q' }}ad) ->
  (forall Ψ' Q', {{ Ψ' ⨟ Θ ⊢ˢ R2 ∼ Q' }}ad -> {{ Ψ' ⨟ Θ ⊢ˢ R2' ∼ Q' }}ad) ->
  {{ Ψ ⨟ Θ ⊢ˢ (uskl_arrow R1' R2') ∼ Qt }}ad.
Proof.
  intros * Hc; induction Hc; intros S1' S2' R1' R2' HeqS Htr1 Htr2;
    try discriminate HeqS.
  -
    inversion HeqS; subst.
    eapply ad_pat_consis__arrow; [ apply Htr1 | apply Htr2 | ]; eauto.
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

Lemma tyequiv_mono_consis_transport : forall Θ A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ ⊢ Θ }}a ->
  mono_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  (forall Ψ Qt, {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A') ∼ Qt }}ad ->
     {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ Qt }}ad) /\
  (forall Ψ Qt, {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ Qt }}ad ->
     {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A') ∼ Qt }}ad).
Proof.
  intros Θ A A' Heq Hwf; induction Heq; intros Hm Hv.
  -
    split; intros Ψ Qt Hc; exact Hc.
  -
    destruct (a_tyequiv_mono_vis Heq Hwf) as [_ Hback].
    destruct (Hback (conj Hm Hv)) as [HmA HvA].
    destruct (IHHeq Hwf HmA HvA) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  -
    destruct (a_tyequiv_mono_vis Heq1 Hwf) as [Hfwd _].
    destruct (Hfwd (conj Hm Hv)) as [HmB HvB].
    destruct (IHHeq1 Hwf Hm Hv) as [H1l H1r].
    destruct (IHHeq2 Hwf HmB HvB) as [H2l H2r].
    split; intros Ψ Qt Hc; [ apply H1l, H2l, Hc | apply H2r, H1r, Hc ].
  -
    split; intros Ψ Qt Hc.
    +
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl.
      eapply ad_pat_consis__flex_l; [ eassumption | exact Hc ].
    +
      eapply consis_unfold_def_subject;
        [ exact Hc | exact Hwf | | eassumption ].
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl; reflexivity.
  -
    inversion Hm as [ | | ? ? Hm1 Hm2 ]; subst; simpl in Hv.
    assert (Hv1 : forall α, α `in` ftvar_in_ptyp A1 -> a_binds_tvar α Θ)
      by (intros α Hα; apply Hv; fsetdec).
    assert (Hv2 : forall α, α `in` ftvar_in_ptyp A2 -> a_binds_tvar α Θ)
      by (intros α Hα; apply Hv; fsetdec).
    destruct (IHHeq1 Hwf Hm1 Hv1) as [H1l H1r].
    destruct (IHHeq2 Hwf Hm2 Hv2) as [H2l H2r].
    split; intros Ψ Qt Hc.
    + eapply consis_arrow_subject_transport with (R1' := ptyp_to_uskl_syn A1);
        [ exact Hc | | exact H1l | exact H2l ].
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl; reflexivity.
    + eapply consis_arrow_subject_transport with (R1' := ptyp_to_uskl_syn B1);
        [ exact Hc | | exact H1r | exact H2r ].
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl; reflexivity.
  -
    inversion Hm.
Qed.

Theorem tyequiv_mono_consis : forall Θ A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ ⊢ Θ }}a ->
  mono_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ (ptyp_to_bskl_syn A') }}ad.
Proof.
  intros * Heq Hwf Hm Hv.
  destruct (a_tyequiv_mono_vis Heq Hwf) as [Hfwd _].
  destruct (Hfwd (conj Hm Hv)) as [HmB HvB].
  destruct (tyequiv_mono_consis_transport Heq Hwf Hm Hv) as [Hd1 _].
  apply Hd1.
  apply consis_mono_refl; auto.
Qed.
