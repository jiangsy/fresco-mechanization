Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.

Set Implicit Arguments.

Lemma a_wf_pskl_delta_mono : forall Θ Δ0 P,
  {{ Θ ⨟ Δ0 ⊢ₚₛ P }}a ->
  forall Δ, (forall α, α `in` ftvar_in_pskl P -> α `in` Δ -> α `in` Δ0) ->
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ0 P H; induction H; intros Δ' Hagree; simpl in Hagree.
  - constructor.
  - constructor. assumption.
  - constructor; [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ];
      intros β Hβ; apply Hagree; fsetdec.
  - apply a_wf_pskl__all with (L := L `union` ftvar_in_pskl P).
    intros α Hα. apply H0; [ fsetdec | ].
    intros β Hβ Hβin.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hup.
    simpl in Hup.
    destruct (β == α) as [-> | Hne]; [ fsetdec | ].
    assert (β `in` Δ) by (apply Hagree; fsetdec). fsetdec.
  - constructor.
  - constructor; [ assumption | ].
    apply (a_wf_pskl_tvar_mono_ftv H0).
    intros β Hβ Hb. apply a_binds_tvar_aenv_minus in Hb.
    apply a_binds_tvar_aenv_minus. destruct Hb as [Hb Hn]. split; [ exact Hb | ].
    intro Hin. apply Hn. apply Hagree; assumption.
Qed.

Lemma lc_pskl_to_bskl_inh : forall P,
  lc_pskl P -> lc_bskl (pskl_to_bskl_inh P).
Proof.
  intros P H; induction H; simpl; auto.
  apply lc_bskl_all_inh. intros α.
  rewrite <- pskl_to_bskl_inh_open; auto.
Qed.

Lemma guarded_pskl_to_bskl_inh : forall P,
  guarded_pskl P -> guarded_bskl (pskl_to_bskl_inh P).
Proof.
  intros P H; inversion H; subst; simpl; constructor;
    auto using lc_pskl_to_bskl_inh.
Qed.

Lemma ad_refine_syn_is_iskl : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  is_iskl Q.
Proof.
  intros * H; induction H; try assumption; constructor.
Qed.

Lemma ad_refine_syn_ghost_empty : forall Θ P,
  {{ Θ ⨟ empty ⊢ᵣ bskl_ghost ⊳ (pskl_to_bskl_syn P) }}ad.
Proof. intros; apply ad_refine_syn__ghost; clear; fsetdec. Qed.

Lemma ad_refine_syn_arrow_intro : forall Θ Δ Q1 Q2 Q3 Q4,
  {{ Θ ⨟ Δ ⊢ᵣ Q1 ⊳ Q3 }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Q2 ⊳ Q4 }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow Q3 Q4) }}ad.
Proof.
  intros * H1 H2. apply ad_refine_syn__arrow; auto.
  constructor; eapply ad_refine_syn_is_iskl; eassumption.
Qed.

Lemma ad_refine_syn_all_intro : forall L Θ Δ Q Q',
  (forall α, α `notin` L ->
     {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ᵣ
       (open_bskl_wrt_bskl Q (bskl_var_f α)) ⊳
       (open_bskl_wrt_bskl Q' (bskl_var_f α)) }}ad) ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_all_inh Q) ⊳ (bskl_all_inh Q') }}ad.
Proof.
  intros * H. apply ad_refine_syn__all with (L := L); auto.
  apply is_iskl__all with (L := L). intros α Hα.
  eapply ad_refine_syn_is_iskl; eauto.
Qed.

Lemma ad_refine_syn_univ_ghost_remove_intro : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q) ⊳ Q' }}ad.
Proof.
  intros * H. apply ad_refine_syn__univ_ghost_remove; auto.
  constructor; eapply ad_refine_syn_is_iskl; eassumption.
Qed.

Lemma ad_refine_syn_univ_ghost_fill_intro : forall L Θ Δ Q Q',
  (forall α, α `notin` L ->
     {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣ
       (bskl_univ_ghost Q) ⊳ (open_bskl_wrt_bskl Q' (bskl_var_f α)) }}ad) ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q) ⊳ (bskl_all_syn Q') }}ad.
Proof.
  intros * H. apply ad_refine_syn__univ_ghost_fill with (L := L); auto.
  pick fresh α for L. eapply ad_refine_syn_is_iskl; eauto.
Qed.

Lemma ad_refine_syn_univ_ghost_keep_intro : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q) ⊳ (bskl_univ_ghost Q') }}ad.
Proof.
  intros * H. apply ad_refine_syn__univ_ghost_keep; auto.
  constructor; eapply ad_refine_syn_is_iskl; eassumption.
Qed.

Lemma ad_refine_syn_weaken : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  {{ Θ' ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros * H Θ' Hle. eapply ad_refine_syn_defs_mono;
    [ exact H | intros; apply Hle; assumption ].
Qed.

Lemma ad_refine_pskl_weaken : forall Θ Δ P P',
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad ->
  forall Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  {{ Θ' ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros * H Θ' Hle. eapply ad_refine_pskl_defs_mono;
    [ exact H | intros; apply Hle; assumption ].
Qed.

Lemma ad_refine_syn_delta_mono : forall Θ Δ0 Q Q',
  {{ Θ ⨟ Δ0 ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Δ, Δ [<=] Δ0 ->
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros Θ Δ0 Q Q' H; induction H; intros Δ' Hsub;
    eauto using ad_refine_syn.
  - apply ad_refine_syn__all with (L := L); [ assumption | ].
    intros α Hα. apply H1; auto. fsetdec.
  - apply ad_refine_syn__ghost. fsetdec.
Qed.

Lemma ad_refine_syn_ghost_free_delta : forall Θ Δ0 Q P,
  {{ Θ ⨟ Δ0 ⊢ᵣ Q ⊳ P }}ad ->
  bskl_ghost_free Q ->
  forall Δ, {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad.
Proof.
  intros Θ Δ0 Q P H; induction H; intros Hg Δ'; simpl in Hg;
    try contradiction; eauto using ad_refine_syn.
  - destruct Hg; eauto using ad_refine_syn.
  - apply ad_refine_syn__all with (L := L); [ assumption | ]. intros α Hα.
    apply H1; auto. apply bskl_ghost_free_open_rec; exact Hg.
  - eapply ad_refine_syn__flex_l; [ exact H | ].
    apply IHad_refine_syn; auto.
    unfold ptyp_to_bskl_syn. apply pskl_to_bskl_syn_ghost_free.
    apply ptyp_to_pskl_ghost_free.
Qed.

Lemma ad_refine_syn_defs_avoid : forall Θ Δ Qs Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  forall S Θ',
  (forall β τ, binds β (abind_flex_mono_def τ) Θ -> β `notin` S ->
     binds β (abind_flex_mono_def τ) Θ' /\ S ∩ ftvar_in_ptyp τ [=] empty) ->
  S ∩ ftvar_in_bskl Qs [=] empty ->
  S ∩ ftvar_in_bskl Qt [=] empty ->
  {{ Θ' ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad.
Proof.
  intros Θ Δ Qs Qt H; induction H; intros S Θ' Hm Hs Ht; simpl in Hs, Ht.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
  - apply ad_refine_syn_arrow_intro;
      [ apply (IHad_refine_syn1 S) | apply (IHad_refine_syn2 S) ];
      try assumption; clear - Hs Ht; fsetdec.
  - apply ad_refine_syn_all_intro with (L := L `union` S). intros β Hβ.
    apply (H1 β ltac:(clear - Hβ; fsetdec) S); [ | | ].
    + intros γ τ Hb Hγ. apply binds_app_1 in Hb as [Hb | Hb];
        [ apply binds_one_iff in Hb as [_ Hb]; discriminate | ].
      destruct (Hm γ τ Hb Hγ) as [Hb' Hd].
      split; [ apply binds_app_3; exact Hb' | exact Hd ].
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
        as Hup; simpl in Hup. clear - Hs Hup Hβ; fsetdec.
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f β))
        as Hup; simpl in Hup. clear - Ht Hup Hβ; fsetdec.
  - apply ad_refine_syn__ghost; assumption.
  - apply ad_refine_syn_univ_ghost_remove_intro; eauto.
  - apply ad_refine_syn_univ_ghost_fill_intro with (L := L `union` S). intros β Hβ.
    apply (H1 β ltac:(clear - Hβ; fsetdec) S); [ | simpl; exact Hs | ].
    + intros γ τ Hb Hγ. apply binds_app_1 in Hb as [Hb | Hb];
        [ apply binds_one_iff in Hb as [_ Hb]; discriminate | ].
      destruct (Hm γ τ Hb Hγ) as [Hb' Hd].
      split; [ apply binds_app_3; exact Hb' | exact Hd ].
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f β))
        as Hup; simpl in Hup. clear - Ht Hup Hβ; fsetdec.
  - apply ad_refine_syn_univ_ghost_keep_intro; eauto.
  - assert (Hα : α `notin` S)
      by (intros Hin; assert (Hx : α `in` S ∩ singleton α)
            by (clear - Hin; fsetdec);
          rewrite Hs in Hx; clear - Hx; fsetdec).
    destruct (Hm α τ H Hα) as [Hb' Hd].
    apply ad_refine_syn__flex_l with (τ := τ); [ exact Hb' | ].
    apply (IHad_refine_syn S); [ exact Hm | | exact Ht ].
    rewrite ftvar_ptyp_to_bskl_syn; exact Hd.
  - assert (Hα : α `notin` S)
      by (intros Hin; assert (Hx : α `in` S ∩ singleton α)
            by (clear - Hin; fsetdec);
          rewrite Ht in Hx; clear - Hx; fsetdec).
    destruct (Hm α τ H Hα) as [Hb' Hd].
    apply ad_refine_syn__flex_r with (τ := τ); [ exact Hb' | ].
    apply (IHad_refine_syn S); [ exact Hm | exact Hs | ].
    rewrite ftvar_ptyp_to_bskl_syn; exact Hd.
Qed.

Lemma ad_refine_pskl_delta_mono : forall Θ Δ0 P P',
  {{ Θ ⨟ Δ0 ⊢ᵣₚ P ⊳ P' }}ad ->
  forall Δ, Δ [<=] Δ0 ->
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros Θ Δ0 P P' H; induction H; intros Δ' Hsub;
    eauto using ad_refine_pskl.
  - apply ad_refine_pskl__all with (L := L).
    intros α Hα. apply H0; auto. fsetdec.
  - apply ad_refine_pskl__ghost. fsetdec.
Qed.

Lemma ad_refine_syn_refl_inh_gen : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ' Δ',
  {{ Θ' ⨟ Δ' ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh P) }}ad.
Proof.
  intros Θ Δ P H.
  assert (Hlc : lc_pskl P) by (clear - H; induction H; eauto using lc_pskl).
  clear H. pose proof Hlc as Hlc0. revert Hlc0.
  induction Hlc; intros Hlc0 Θ' Δ';
    pose proof (is_iskl_pskl_to_bskl_inh _ Hlc0) as Hi;
    simpl in Hi |- *.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
  - apply ad_refine_syn__arrow; auto.
  - apply ad_refine_syn__all with (L := {}); [ exact Hi | ].
    intros α _.
    repeat rewrite <- pskl_to_bskl_inh_open. auto.
  - replace (pskl_to_bskl_inh pskl_ghost)
      with (pskl_to_bskl_syn pskl_ghost) at 2 by reflexivity.
    apply ad_refine_syn__ghost. simpl. fsetdec.
  - apply ad_refine_syn__univ_ghost_keep; auto.
Qed.

Lemma ad_refine_syn_refl_inh : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh P) }}ad.
Proof. intros. eapply ad_refine_syn_refl_inh_gen; eauto. Qed.

Lemma ad_refine_pskl_refl_gen : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ' Δ', {{ Θ' ⨟ Δ' ⊢ᵣₚ P ⊳ P }}ad.
Proof.
  intros Θ Δ P H; induction H; intros Θ' Δ'; simpl.
  - apply ad_refine_pskl__unit.
  - apply ad_refine_pskl__var.
  - apply ad_refine_pskl__arrow; auto.
  - apply ad_refine_pskl__all with (L := L). auto.
  - apply ad_refine_pskl__ghost. simpl. fsetdec.
  - apply ad_refine_pskl__univ_ghost_keep. auto.
Qed.

Lemma ad_refine_pskl_refl : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P }}ad.
Proof. intros. eapply ad_refine_pskl_refl_gen; eauto. Qed.

Lemma ad_refine_syn_mono_refl : forall Θ Δ τ,
  mono_ptyp τ ->
  {{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn τ) ⊳ (ptyp_to_bskl_syn τ) }}ad.
Proof.
  intros Θ Δ τ Hm; induction Hm; simpl.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
  - apply ad_refine_syn_arrow_intro; auto.
Qed.

Lemma ad_pat_consis_refl_erase : forall R' Θ,
  lc_uskl R' ->
  (forall α, α `in` ftvar_in_uskl R' -> a_binds_tvar α Θ) ->
  ad_pat_consis empty Θ R' (pskl_to_bskl_syn ⌊ R' ⌋ˢ).
Proof.
  intros R' Θ Hlc; revert Θ; induction Hlc; intros Θ Hvis; simpl.
  - apply ad_pat_consis__unit. fsetdec.
  - apply ad_pat_consis__var; [ fsetdec | ].
    apply Hvis. simpl. fsetdec.
  - apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHlc1 | apply IHHlc2 | fsetdec ];
      intros α Hα; apply Hvis; simpl; fsetdec.
  -
    apply ad_pat_consis__forall_syn with (L := dom Θ).
    intros α Hα.
    rewrite <- pskl_to_bskl_syn_open.
    replace (open_pskl_wrt_pskl ⌊ R ⌋ˢ (pskl_var_f α))
      with (⌊ open_uskl_wrt_uskl R (uskl_var_f α) ⌋ˢ)
      by (unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl;
          apply uskl_to_pskl_open_rec).
    apply H0.
    intros β Hβ.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                  R (uskl_var_f α)) as Hup.
    simpl in Hup.
    assert (HY' : β `in` (singleton α `union` ftvar_in_uskl R))
      by (clear - Hβ Hup; fsetdec).
    destruct (union_1 HY') as [HYX | HYR].
    + apply singleton_1 in HYX; subst.
      left. unfold binds; left; reflexivity.
    + apply a_binds_tvar_weaken_cons; auto.
  -
    apply ad_pat_consis__forall_syn_tagged with (L := dom Θ).
    intros α Hα.
    rewrite <- pskl_to_bskl_syn_open.
    replace (open_pskl_wrt_pskl ⌊ R ⌋ˢ (pskl_var_f α))
      with (⌊ open_uskl_wrt_uskl R (uskl_var_f α) ⌋ˢ)
      by (unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl;
          apply uskl_to_pskl_open_rec).
    apply H0.
    intros β Hβ.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                  R (uskl_var_f α)) as Hup.
    simpl in Hup.
    assert (HY' : β `in` (singleton α `union` ftvar_in_uskl R))
      by (clear - Hβ Hup; fsetdec).
    destruct (union_1 HY') as [HYX | HYR].
    + apply singleton_1 in HYX; subst.
      left. unfold binds; left; reflexivity.
    + apply a_binds_tvar_weaken_cons; auto.
  -
    replace bskl_ghost with (pskl_to_bskl_inh pskl_ghost) by reflexivity.
    apply ad_pat_consis__ghost; [ fsetdec ].
  -
    apply ad_pat_consis__univ_ghost. auto.
  -
    apply ad_pat_consis__ghostg. fsetdec.
  -
    apply ad_pat_consis__dot_univ_ghost. auto.
Qed.

Lemma bskl_monoish_paint : forall τ,
  mono_ptyp τ -> bskl_monoish (ptyp_to_bskl_syn τ).
Proof. intros τ Hm; induction Hm; simpl; constructor; auto. Qed.

Lemma ad_refine_mono_paint_rhs_monoish : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  bskl_monoish Q.
Proof.
  intros * Hwf Hr τ Heq Hm.
  destruct (refine_mono_join Hr Hwf Heq Hm) as (C & Hmono & -> & _).
  apply bskl_monoish_paint; exact Hmono.
Qed.

Lemma ad_refine_arrow_arrow_inv : forall Θ Δr Q1' Q2' Q1 Q2,
  {{ Θ ⨟ Δr ⊢ᵣ (bskl_arrow Q1' Q2') ⊳ (bskl_arrow Q1 Q2) }}ad ->
  ({{ Θ ⨟ Δr ⊢ᵣ Q1' ⊳ Q1 }}ad) /\ ({{ Θ ⨟ Δr ⊢ᵣ Q2' ⊳ Q2 }}ad).
Proof.
  intros Θ Δr Q1' Q2' Q1 Q2 H; inversion H; subst; split; assumption.
Qed.

Lemma ad_refine_inh_deltar_var_rhs_no_ghost : forall Θr Δr Q' Q,
  {{ Θr ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall α0 P', Q = bskl_var_f α0 -> Q' = pskl_to_bskl_inh P' ->
  α0 `notin` dom Θr ->
  α0 `in` Δr ->
  pskl_no_ghost P'.
Proof.
  intros Θr Δr Q' Q H; induction H; intros α0 P' HeqQ HeqL HX0 HΔ0;
    try discriminate HeqQ.
  -
    destruct P'; simpl in HeqL; try discriminate HeqL.
    simpl; exact I.
  -
    exfalso.
    destruct P; simpl in HeqQ; try discriminate HeqQ.
    inversion HeqQ; subst.
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      simpl in Hint; clear - Hint HΔ0; fsetdec end.
  -
    destruct P'; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    simpl. eapply IHad_refine_syn; eauto.
  -
    destruct P'; simpl in HeqL; try discriminate HeqL.
    simpl; exact I.
  -
    inversion HeqQ; subst.
    exfalso. apply HX0.
    match goal with Hb : binds _ (abind_flex_mono_def _) _ |- _ =>
      eapply binds_In; exact Hb end.
Qed.

Lemma ad_refine_mono_paint_ftv_bound : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall τb S, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  ftvar_in_ptyp τb [<=] S ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     α `in` S /\ ftvar_in_ptyp τ0 [<=] S) ->
  ftvar_in_bskl Q [<=] S.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros τb S HeqL Hmb Hsub Hdefs.
  -  simpl. clear; fsetdec.
  -
    symmetry in HeqL. apply ptyp_to_bskl_syn_var_inv in HeqL; subst τb.
    simpl in *. clear - Hsub; fsetdec.
  -
    symmetry in HeqL.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqL)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    simpl in Hsub.
    assert (Hm1 : mono_ptyp τ1) by (inversion Hmb; assumption).
    assert (Hm2 : mono_ptyp τ2) by (inversion Hmb; assumption).
    assert (Hb1 : ftvar_in_bskl Q3 [<=] S)
      by (eapply IHad_refine_syn1;
            [ exact HwfΘ | exact Heq1 | exact Hm1
            | clear - Hsub; fsetdec | exact Hdefs ]).
    assert (Hb2 : ftvar_in_bskl Q4 [<=] S)
      by (eapply IHad_refine_syn2;
            [ exact HwfΘ | exact Heq2 | exact Hm2
            | clear - Hsub; fsetdec | exact Hdefs ]).
    simpl. clear - Hb1 Hb2; fsetdec.
  -
    destruct τb; simpl in HeqL; discriminate HeqL.
  -
    destruct τb; simpl in HeqL; discriminate HeqL.
  -  destruct τb; simpl in HeqL; discriminate HeqL.
  -  destruct τb; simpl in HeqL; discriminate HeqL.
  -  destruct τb; simpl in HeqL; discriminate HeqL.
  -
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    destruct (Hdefs _ _ H) as [_ Hτ].
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity
      | eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | exact H ]
      | exact Hτ | exact Hdefs ].
  -
    destruct (Hdefs _ _ H) as [Hα _]. simpl. clear - Hα; fsetdec.
Qed.

Lemma ad_refine_mono_paint_allinh_rhs_absurd : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Q0, Q = bskl_all_inh Q0 ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros * Hwf Hr Q0 -> τ -> Hm.
  pose proof (ad_refine_mono_paint_rhs_monoish Hwf Hr eq_refl Hm) as Hshape.
  inversion Hshape.
Qed.

Lemma ad_refine_mono_paint_allsyn_rhs_absurd : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Q0, Q = bskl_all_syn Q0 ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros * Hwf Hr Q0 -> τ -> Hm.
  pose proof (ad_refine_mono_paint_rhs_monoish Hwf Hr eq_refl Hm) as Hshape.
  inversion Hshape.
Qed.
