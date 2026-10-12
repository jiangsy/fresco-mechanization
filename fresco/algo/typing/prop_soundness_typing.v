Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_mod_compat.
Require Import src.fresco.algo.basic.prop_wf_preservation.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.def_typing.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo_decl.prop_renaming.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_gen.
Require Import src.fresco.algo.basic.prop_suffix_erase.
Require Import src.fresco.deco_algo.prop_soundness_sub.

Set Implicit Arguments.

Local Ltac destr_join :=
  repeat match goal with
         | Hj : ad_consis_join _ _ _ _ |- _ =>
             let Hc := fresh "Hjc" in let Hr := fresh "Hjr" in
             destruct Hj as [Hc Hr];
             try rewrite bskl_to_pskl_pskl_to_bskl_inh in Hr
         end.

Lemma btyp_to_bskl_ptyp_to_btyp_inh : forall A,
  btyp_to_bskl (ptyp_to_btyp_inh A) = pskl_to_bskl_inh (ptyp_to_pskl A).
Proof. induction A; simpl; congruence. Qed.

Lemma btyp_syn_painting_inv : forall B P,
  btyp_to_bskl B = pskl_to_bskl_syn P ->
  B = ptyp_to_btyp_syn (btyp_to_ptyp B).
Proof.
  intros B; induction B; intros P Heq; destruct P; simpl in Heq;
    try discriminate; simpl; try reflexivity.
  - inversion Heq. erewrite <- IHB1 by eassumption.
    erewrite <- IHB2 by eassumption. reflexivity.
  - inversion Heq. erewrite <- IHB by eassumption. reflexivity.
Qed.

Lemma ad_refine_syn_inh_tyequiv : forall Θ Δ Qs Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall A B,
  Qs = pskl_to_bskl_inh (ptyp_to_pskl A) ->
  Qt = btyp_to_bskl B ->
  {{ Θ ⊢ A ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros Θ Δ Qs Qt H; induction H; intros Hwf A B HeqS HeqT.
  -
    destruct A; simpl in HeqS; try discriminate.
    destruct B; simpl in HeqT; try discriminate.
    apply a_tyequiv__refl. apply lc_ptyp_unit.
  -
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqS; try discriminate.
    destruct B as [ | n | α2 | B1 B2 | B0 | B0 ]; simpl in HeqT;
      try discriminate.
    assert (Hα1 : α1 = α) by (inversion HeqS; reflexivity).
    assert (Hα2 : α2 = α) by (inversion HeqT; reflexivity).
    subst. apply a_tyequiv__refl. apply lc_ptyp_var_f.
  -
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqS; try discriminate.
    destruct B as [ | n | α2 | B1 B2 | B0 | B0 ]; simpl in HeqT;
      try discriminate.
    inversion HeqS; inversion HeqT; subst.
    apply a_tyequiv__arrow;
      [ apply IHad_refine_syn1 | apply IHad_refine_syn2 ];
      solve [ exact Hwf | reflexivity ].
  -
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqS; try discriminate.
    destruct B as [ | n | α2 | B1 B2 | B0 | B0 ]; simpl in HeqT;
      try discriminate.
    inversion HeqS; inversion HeqT; subst.
    apply a_tyequiv__all with (L := L `union` dom Θ). intros α Hα.
    rewrite <- btyp_to_ptyp_open_var.
    assert (HαL : α `notin` L) by solve_notin.
    assert (HαΘ : α `notin` dom Θ) by solve_notin.
    eapply prop_metasubst.a_tyequiv_strengthen_tvar_cons; [ | reflexivity ].
    apply (H1 α HαL (a_wf_aenv__tvar HαΘ Hwf)
             (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))
             (open_btyp_wrt_btyp B0 (btyp_var_f α)));
      [ rewrite ptyp_to_pskl_open, pskl_to_bskl_inh_open; reflexivity
      | rewrite btyp_to_bskl_open; reflexivity ].
  -
    destruct A; simpl in HeqS; discriminate.
  -
    destruct A; simpl in HeqS; discriminate.
  -
    destruct A; simpl in HeqS; discriminate.
  -
    destruct A; simpl in HeqS; discriminate.
  -
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqS; try discriminate.
    assert (Hα1 : α1 = α) by (inversion HeqS; reflexivity). subst α1.
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    eapply a_tyequiv__trans; [ apply a_tyequiv__flex_def; exact H | ].
    apply IHad_refine_syn;
      [ exact Hwf
      | unfold ptyp_to_bskl_syn in *;
        rewrite (ptyp_to_bskl_inh_syn_eq Hmono); reflexivity
      | exact HeqT ].
  -
    destruct B as [ | n | α2 | B1 B2 | B0 | B0 ]; simpl in HeqT;
      try discriminate.
    assert (Hα2 : α2 = α) by (inversion HeqT; reflexivity). subst α2.
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    assert (IH2 : {{ Θ ⊢ A ≡ᵗ (btyp_to_ptyp (ptyp_to_btyp_inh τ)) }}a).
    { apply (IHad_refine_syn Hwf A (ptyp_to_btyp_inh τ)); [ exact HeqS | ].
      rewrite btyp_to_bskl_ptyp_to_btyp_inh.
      symmetry; apply (ptyp_to_bskl_inh_syn_eq Hmono). }
    rewrite btyp_to_ptyp_ptyp_to_btyp_inh in IH2.
    simpl. eapply a_tyequiv__trans;
      [ exact IH2 | apply a_tyequiv__sym; apply a_tyequiv__flex_def; exact H ].
Qed.

Lemma a_consis_chk_tyequiv : forall Θ0 A B Θ1,
  a_consis_chk Θ0 (ptyp_to_pskl B) (ptyp_to_pskl A) Θ1 ->
  {{ ⊢ Θ0 }}a ->
  a_wf_ptyp Θ0 A ->
  a_wf_ptyp Θ0 B ->
  {{ Θ1 ⊢ B ≡ᵗ A }}a.
Proof.
  intros Θ0 A B Θ1 Hchk Hwf HwfA HwfB.
  destruct (a_consis_chk_annot_refine Hchk Hwf HwfB
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA))
    as [Bt [HeqBt Href]].
  destruct (a_consis_chk_sound Hchk Hwf
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA)
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfB))
    as [Hle [Hwf1 _]].
  apply a_tyequiv__sym.
  rewrite <- HeqBt.
  eapply ad_refine_syn_inh_tyequiv;
    [ exact Href | exact Hwf1 | reflexivity | reflexivity ].
Qed.

Lemma a_typing_tm_ge : forall m Θ0 P0 e A Θ1,
  {{ Θ0 ⊢[ m ; P0 ] e ⦂ A ⊣ Θ1 }}a -> aenv_tm_le Θ1 Θ0.
Proof.
  intros m Θ0 P0 e A Θ1 H; induction H.
  -  eapply a_sub_tm_ge; eassumption.
  -  eapply a_sub_tm_ge; eassumption.
  -
    eapply aenv_tm_le_trans; [ eapply a_sub_tm_ge; eassumption | assumption ].
  -
    eapply aenv_tm_le_trans;
      [ eapply a_consis_chk_tm_ge; eassumption | assumption ].
  -
    intros y b Htm Hb.
    apply a_split_tm_ge in H0.
    pose proof (binds_In _ y b _ Hb) as Hy.
    apply H0; [ exact Htm | ].
    eapply binds_tm_strip_suffix;
      [ apply a_decls_suffix; eapply a_guess_mono_decls; eassumption
      | exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H4 Hy;
        rewrite !dom_app in H4; rewrite !dom_app in Hy; fsetdec
      | exact Hb ].
  -
    intros y b Htm Hb.
    apply a_split_tm_ge in H0. apply a_consis_chk_tm_ge in H1.
    pose proof (binds_In _ y b _ Hb) as Hy.
    apply H0; [ exact Htm | ]. apply H1; [ exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H3 Hy;
        rewrite !dom_app in H3; rewrite !dom_app in Hy; fsetdec
      | exact Hb ].
  -
    intros y b Htm Hb.
    pose proof (binds_In _ y b _ Hb) as Hy.
    eapply aenv_tm_le_via_binder_ge with (x := α);
      [ exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H2 Hy; rewrite !dom_app in H2; fsetdec
      | apply binds_app_3; exact Hb ].
  -
    intros y b Htm Hb.
    apply a_split_tm_ge in H.
    pose proof (binds_In _ y b _ Hb) as Hy.
    apply H; [ exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H3 Hy; rewrite !dom_app in H3; fsetdec
      | apply binds_app_3; exact Hb ].
  -
    intros y b Htm Hb.
    pose proof (binds_In _ y b _ Hb) as Hy.
    eapply aenv_tm_le_via_binder_ge with (x := α);
      [ exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H2 Hy; rewrite !dom_app in H2; fsetdec
      | apply binds_app_3; exact Hb ].
  -
    intros y b Htm Hb.
    apply a_split_tm_ge in H. apply a_consis_chk_tm_ge in H0.
    pose proof (binds_In _ y b _ Hb) as Hy.
    apply H; [ exact Htm | ]. apply H0; [ exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H4 Hy; rewrite !dom_app in H4; fsetdec
      | apply binds_app_3; exact Hb ].
  -
    eapply aenv_tm_le_trans; [ exact IHa_typing2 | ].
    eapply aenv_tm_le_trans;
      [ exact IHa_typing1 | eapply a_pat_tm_ge; eassumption ].
Qed.

Lemma a_tyequiv_isub_le : forall Θ Θ' A A',
  Θ ⊴ Θ' -> {{ Θ ⊢ A ≡ᵗ A' }}a -> {{ Θ' ⊢ A ≡ᵗ A' }}a.
Proof.
  intros Θ Θ' A A' [[κ [Hid Hinc]] _] Heq.
  eapply a_tyequiv_isub; eassumption.
Qed.

Lemma ad_sd_typing_isub_tm : forall M Θ e B,
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  forall Θ', Θ ⊴ Θ' -> aenv_tm_le Θ Θ' ->
  {{ Θ' ⊢ˢᵈ[ M ] e ⦂ B }}ad.
Proof.
  intros M Θ e B H; induction H; intros Θ' Hle Htm.
  -  apply ad_sd_typing__unit. eapply ad_pat_sub_isub; eauto.
  -
    eapply ad_sd_typing__var;
      [ apply Htm; [ exact I | exact H ] | eapply ad_pat_sub_isub; eauto ].
  -
    eapply ad_sd_typing__anno;
      [ eapply a_wf_ptyp_isub; eassumption
      | apply IHad_sd_typing; assumption | eapply ad_pat_sub_isub; eauto ].
  -
    eapply ad_sd_typing__freeze;
      [ apply IHad_sd_typing; assumption | eapply a_tyequiv_isub_le; eauto ].
  -
    apply ad_sd_typing__abs_check_step with (L := L).
    intros α Hα. apply H0;
      [ exact Hα | apply a_isub_cons_tvar; exact Hle
      | apply aenv_tm_le_cons; exact Htm ].
  -
    apply ad_sd_typing__abs_check_base with (L := L);
      [ eapply a_wf_ptyp_isub; eauto | assumption | ].
    intros x Hx. apply H2;
      [ exact Hx
      | apply a_isub_cons_var_typ; [ exact Hle | eapply a_wf_ptyp_lc; eauto ]
      | apply aenv_tm_le_cons; exact Htm ].
  -
    apply ad_sd_typing__abs_anno_check_step with (L := L).
    intros α Hα. apply H0;
      [ exact Hα | apply a_isub_cons_tvar; exact Hle
      | apply aenv_tm_le_cons; exact Htm ].
  -
    apply ad_sd_typing__abs_anno_check_base with (L := L) (A' := A');
      [ eapply a_wf_ptyp_isub; eauto | eapply a_tyequiv_isub_le; eauto
      | assumption | ].
    intros x Hx. apply H3;
      [ exact Hx
      | apply a_isub_cons_var_typ; [ exact Hle | eapply a_wf_ptyp_lc; eauto ]
      | apply aenv_tm_le_cons; exact Htm ].
  -
    apply ad_sd_typing__abs with (L := L);
      [ assumption | eapply a_wf_ptyp_isub; eauto | assumption | ].
    intros x Hx. apply H3;
      [ exact Hx
      | apply a_isub_cons_var_typ; [ exact Hle | eapply a_wf_ptyp_lc; eauto ]
      | apply aenv_tm_le_cons; exact Htm ].
  -
    eapply ad_sd_typing__abs_anno with (L := L) (A' := A');
      [ assumption | eapply a_wf_ptyp_isub; eauto
      | eapply a_tyequiv_isub_le; eauto | eassumption | assumption | ].
    intros x Hx. apply H5;
      [ exact Hx
      | apply a_isub_cons_var_typ; [ exact Hle | eapply a_wf_ptyp_lc; eauto ]
      | apply aenv_tm_le_cons; exact Htm ].
  -
    eapply ad_sd_typing__app;
      [ eapply ad_pat_isub_tm; eauto | eapply ad_refine_syn_isub; eauto
      | apply IHad_sd_typing1; assumption
      | eapply a_tyequiv_isub_le; eauto
      | apply IHad_sd_typing2; assumption ].
Qed.

Lemma ad_sd_typing_subst_tm : forall M Θ' e B,
  {{ Θ' ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  forall Θa x (b : abind) Θ0 y,
  Θ' = Θa ++ (x ~ b) ++ Θ0 ->
  abind_is_tm b ->
  x `notin` dom Θa `union` dom Θ0 ->
  {{ (Θa ++ (y ~ b) ++ Θ0) ⊢ˢᵈ[ M ] (subst_exp_in_exp (exp_var_f y) x e) ⦂ B }}ad.
Proof.
  intros M Θ' e B H; induction H;
    intros Θa x0 b0 Θb y Heq Htm Hx0; subst; simpl;
  assert (Hren : aenv_tbinds_le (Θa ++ (x0 ~ b0) ++ Θb) (Θa ++ (y ~ b0) ++ Θb))
    by (apply aenv_tbinds_le_rename_tm; apply abind_is_tm_not_ty; exact Htm).
  -
    apply ad_sd_typing__unit.
    eapply ad_pat_sub_mono;
      [ eassumption | exact Hren ].
  -
    destruct_if as [Heqx | Hne].
    + subst x.
      assert (Hb0 : abind_var_typ A = b0).
      { apply binds_app_1 in H as [Hb | Hb];
          [ exfalso; apply binds_In in Hb; clear - Hb Hx0; fsetdec | ].
        apply binds_app_1 in Hb as [Hb | Hb];
          [ | exfalso; apply binds_In in Hb; clear - Hb Hx0; fsetdec ].
        destruct Hb as [Hp | []]. inversion Hp; reflexivity. }
      eapply ad_sd_typing__var;
        [ rewrite Hb0; apply binds_app_3;
          unfold binds; simpl; left; reflexivity
        | eapply ad_pat_sub_mono;
            [ eassumption | exact Hren ] ].
    + eapply ad_sd_typing__var;
        [ | eapply ad_pat_sub_mono;
              [ eassumption | exact Hren ] ].
      apply binds_app_1 in H as [Hb | Hb];
        [ apply binds_app_2; exact Hb | ].
      apply binds_app_1 in Hb as [Hb | Hb];
        [ destruct Hb as [Hp | []]; inversion Hp; subst; exfalso; auto | ].
      apply binds_app_3; unfold binds; simpl; right; exact Hb.
  -
    eapply ad_sd_typing__anno;
      [ eapply a_wf_ptyp_mono;
          [ eassumption | exact Hren ]
      | apply IHad_sd_typing; auto
      | eapply ad_pat_sub_mono;
          [ eassumption | exact Hren ] ].
  -
    eapply ad_sd_typing__freeze;
      [ apply IHad_sd_typing; auto
      | eapply a_tyequiv_ctx_mono;
          [ eassumption | exact Hren ] ].
  -
    apply ad_sd_typing__abs_check_step
      with (L := L `union` singleton x0 `union` singleton y).
    intros α Hα.
    apply (H0 α ltac:(clear - Hα; solve_notin_auto)
             ((α ~ abind_tvar) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hα; fsetdec ].
  -
    apply ad_sd_typing__abs_check_base
      with (L := L `union` singleton x0 `union` singleton y);
      [ eapply a_wf_ptyp_mono;
          [ eassumption | exact Hren ]
      | assumption | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H2 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_typ A) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hz; fsetdec ].
  -
    apply ad_sd_typing__abs_anno_check_step
      with (L := L `union` singleton x0 `union` singleton y).
    intros α Hα.
    apply (H0 α ltac:(clear - Hα; solve_notin_auto)
             ((α ~ abind_tvar) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hα; fsetdec ].
  -
    apply ad_sd_typing__abs_anno_check_base
      with (L := L `union` singleton x0 `union` singleton y) (A' := A');
      [ eapply a_wf_ptyp_mono;
          [ eassumption | exact Hren ]
      | eapply a_tyequiv_ctx_mono;
          [ eassumption | exact Hren ]
      | assumption | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H3 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_typ A) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hz; fsetdec ].
  -
    apply ad_sd_typing__abs
      with (L := L `union` singleton x0 `union` singleton y);
      [ assumption
      | eapply a_wf_ptyp_mono;
          [ eassumption | exact Hren ]
      | assumption | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H3 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_typ A) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hz; fsetdec ].
  -
    eapply ad_sd_typing__abs_anno
      with (L := L `union` singleton x0 `union` singleton y);
      try assumption; try reflexivity;
      try (eapply a_wf_ptyp_mono;
           [ eassumption | exact Hren ]);
      try (eapply a_tyequiv_ctx_mono;
           [ eassumption | exact Hren ]).
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H5 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_typ A) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hz; fsetdec ].
  -
    eapply ad_sd_typing__app;
      [ eapply ad_pat_subst_tm; [ eassumption | reflexivity | exact Htm
                                | exact Hx0 ]
      | eapply ad_refine_syn_mono;
          [ eassumption | exact Hren ]
      | apply IHad_sd_typing1; auto
      | eapply a_tyequiv_ctx_mono;
          [ eassumption | exact Hren ]
      | apply IHad_sd_typing2; auto ].
Qed.

Corollary ad_sd_typing_rename_tm : forall M x (b : abind) Θ0 e B y,
  {{ ((x ~ b) ++ Θ0) ⊢ˢᵈ[ M ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}ad ->
  abind_is_tm b ->
  x `notin` dom Θ0 `union` fvar_in_exp e ->
  {{ ((y ~ b) ++ Θ0) ⊢ˢᵈ[ M ] (open_exp_wrt_exp e (exp_var_f y)) ⦂ B }}ad.
Proof.
  intros * Hd Htm Hx.
  rewrite (subst_exp_in_exp_intro x); [ | clear - Hx; fsetdec ].
  change ((y ~ b) ++ Θ0) with (nil ++ (y ~ b) ++ Θ0).
  eapply ad_sd_typing_subst_tm;
    [ exact Hd | reflexivity | exact Htm | simpl; clear - Hx; fsetdec ].
Qed.

Lemma btyp_inh_painting_inv : forall B,
  is_ityp B -> B = ptyp_to_btyp_inh (btyp_to_ptyp B).
Proof.
  intros B H; induction H; simpl; try reflexivity.
  - f_equal; assumption.
  - f_equal.
    destruct (atom_fresh (L `union` ftvar_in_btyp A
                            `union` ftvar_in_btyp
                                      (ptyp_to_btyp_inh (btyp_to_ptyp A))))
      as [α Hα].
    apply (open_btyp_wrt_btyp_inj _ _ α);
      [ clear - Hα; fsetdec | clear - Hα; fsetdec | ].
    rewrite <- ptyp_to_btyp_inh_open_var, <- btyp_to_ptyp_open_var.
    apply H0. clear - Hα; fsetdec.
Qed.

Corollary btyp_check_colouring : forall B A,
  is_ityp B -> btyp_to_ptyp B = A -> B = ptyp_to_btyp_inh A.
Proof. intros B A Hi Heq. subst A. apply btyp_inh_painting_inv; exact Hi. Qed.

Lemma btyp_syn_colouring_inv : forall B,
  is_styp B -> B = ptyp_to_btyp_syn (btyp_to_ptyp B).
Proof.
  intros B H; induction H; simpl; try reflexivity.
  - f_equal; assumption.
  - f_equal.
    destruct (atom_fresh (L `union` ftvar_in_btyp B
                            `union` ftvar_in_btyp
                                      (ptyp_to_btyp_syn (btyp_to_ptyp B))))
      as [α Hα].
    apply (open_btyp_wrt_btyp_inj _ _ α);
      [ clear - Hα; fsetdec | clear - Hα; fsetdec | ].
    rewrite <- ptyp_to_btyp_syn_open_var, <- btyp_to_ptyp_open_var.
    apply H0. clear - Hα; fsetdec.
Qed.

Lemma degree_btyp_of_degree_bskl_erase : forall B k,
  degree_bskl_wrt_bskl k (btyp_to_bskl B) -> degree_btyp_wrt_btyp k B.
Proof.
  induction B; intros k H; simpl in H; inversion H; subst; constructor; auto.
Qed.

Lemma lc_btyp_of_lc_bskl_erase : forall B,
  lc_bskl (btyp_to_bskl B) -> lc_btyp B.
Proof.
  intros B H. apply lc_btyp_of_degree.
  apply degree_btyp_of_degree_bskl_erase.
  apply degree_bskl_wrt_bskl_of_lc_bskl; exact H.
Qed.

Lemma is_ityp_of_erase_inh : forall B,
  lc_btyp B -> forall P, btyp_to_bskl B = pskl_to_bskl_inh P -> is_ityp B.
Proof.
  intros B H; induction H; intros P Heq;
    destruct P; simpl in Heq; try discriminate.
  -  apply is_ityp__unit.
  -  apply is_ityp__var.
  -
    inversion Heq. apply is_ityp__arrow;
      [ eapply IHlc_btyp1 | eapply IHlc_btyp2 ]; eassumption.
  -
    inversion Heq.
    apply is_ityp__all with (L := empty). intros α _.
    apply (H0 α (open_pskl_wrt_pskl P (pskl_var_f α))).
    rewrite btyp_to_bskl_open, pskl_to_bskl_inh_open. simpl.
    rewrite H2. reflexivity.
Qed.

Lemma ad_pat_sub_mod_comp_ty : forall M Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_ty | M ] R ⩽ Q }}ad ->
  uskl_no_ghost R ->
  forall Bt, Q = btyp_to_bskl Bt -> mod_comp_ty Bt M.
Proof.
  intros M Ψ Θ R Q H.
  remember a_sub_mode_ty as NM eqn:HNM.
  induction H; subst; try discriminate; destr_join; intros Hng Bt HeqB.
  -
    apply mod_comp_ty__ti. eapply is_styp_of_btyp_to_bskl; eassumption.
  -
    apply mod_comp_ty__tc.
    eapply is_ityp_of_erase_inh; [ | symmetry; exact HeqB ].
    apply lc_btyp_of_lc_bskl_erase. rewrite <- HeqB.
    eapply ad_pat_consis_target_lc; eassumption.
  -
    destruct Bt as [ | n | α | B1 B2 | B0 | B0 ]; simpl in HeqB;
      try discriminate.
    inversion HeqB; subst.
    apply mod_comp_ty__tc. apply is_ityp__all with (L := L). intros α Hα.
    apply mod_comp_ty_tc_inv.
    apply (H0 α Hα eq_refl Hng (open_btyp_wrt_btyp B0 (btyp_var_f α))).
    rewrite btyp_to_bskl_open. reflexivity.
  -
    destruct Bt as [ | n | α | B1 B2 | B0 | B0 ]; simpl in HeqB;
      try discriminate.
    inversion HeqB; subst.
    apply mod_comp_ty__fn. apply (IHad_pat_sub eq_refl (proj2 Hng) B2). reflexivity.
  -
    apply (IHad_pat_sub eq_refl); [ | exact HeqB ].
    apply uskl_no_ghost_open; [ exact Hng | ].
    apply uskl_no_ghost_of_ghost_free.
    match goal with Ht : a_tags_sort _ _ ψ |- _ => inversion Ht; assumption end.
  -
    apply (IHad_pat_sub eq_refl); [ | exact HeqB ].
    apply uskl_no_ghost_open; [ exact Hng | ].
    apply uskl_no_ghost_of_ghost_free.
    match goal with Ht : a_tags_sort _ _ ψ |- _ => inversion Ht; assumption end.
  -  apply (IHad_pat_sub eq_refl (uskl_no_ghost_ptyp τ) Bt); exact HeqB.
Qed.

Lemma a_tyequiv_lc : forall Θ A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a -> {{ ⊢ Θ }}a -> lc_ptyp A /\ lc_ptyp A'.
Proof.
  intros Θ A A' H; induction H; intros Hwf.
  -  split; assumption.
  -  destruct (IHa_tyequiv Hwf); split; assumption.
  -
    destruct (IHa_tyequiv1 Hwf); destruct (IHa_tyequiv2 Hwf);
      split; assumption.
  -
    split; [ apply lc_ptyp_var_f | ].
    apply mono_ptyp_lc. eapply a_wf_aenv_binds_def_mono; eassumption.
  -
    destruct (IHa_tyequiv1 Hwf); destruct (IHa_tyequiv2 Hwf).
    split; apply lc_ptyp_arrow; assumption.
  -
    destruct (atom_fresh L) as [α Hα].
    destruct (H0 α Hα Hwf) as [Hl Hr].
    split; eapply lc_ptyp_all_exists; eassumption.
Qed.

Corollary a_tyequiv_lc_r : forall Θ A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a -> {{ ⊢ Θ }}a -> lc_ptyp A'.
Proof. intros * H Hwf. apply (proj2 (a_tyequiv_lc H Hwf)). Qed.

Lemma ad_sd_typing_mod_comp_ty : forall M Θ e B,
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad -> {{ ⊢ Θ }}a -> mod_comp_ty B M.
Proof.
  intros M Θ e B H; induction H; intros Hwf.
  -  eapply ad_pat_sub_mod_comp_ty;
      [ eassumption | apply uskl_no_ghost_ptyp | reflexivity ].
  -  eapply ad_pat_sub_mod_comp_ty;
      [ eassumption | apply uskl_no_ghost_ptyp | reflexivity ].
  -  eapply ad_pat_sub_mod_comp_ty;
      [ eassumption | apply uskl_no_ghost_ptyp | reflexivity ].
  -
    apply mod_comp_ty__tc. apply is_ityp_ptyp_to_btyp_inh.
    eapply a_tyequiv_lc_r; eassumption.
  -
    apply mod_comp_ty__tc. apply is_ityp__all with (L := L `union` dom Θ).
    intros α Hα. apply mod_comp_ty_tc_inv. apply H0;
      [ clear - Hα; fsetdec | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ] ].
  -
    apply mod_comp_ty__tc. apply is_ityp__arrow;
      [ apply is_ityp_ptyp_to_btyp_inh; eapply a_wf_ptyp_lc; eassumption | assumption ].
  -
    apply mod_comp_ty__tc. apply is_ityp__all with (L := L `union` dom Θ).
    intros α Hα. apply mod_comp_ty_tc_inv. apply H0;
      [ clear - Hα; fsetdec | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ] ].
  -
    apply mod_comp_ty__tc. apply is_ityp__arrow;
      [ apply is_ityp_ptyp_to_btyp_inh; eapply a_tyequiv_lc_r; eassumption
      | assumption ].
  -  assumption.
  -  assumption.
  -
    eapply mod_comp_ty_fn_inv. apply IHad_sd_typing1; exact Hwf.
Qed.

Lemma a_guess_mono_refine_size : forall n Θ P Ξ A,
  size_pskl P <= n ->
  a_guess_mono Θ P Ξ A ->
  forall Θ1 Δ,
  (forall α, α `in` ftvar_in_pskl P -> α `in` Δ \/ a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono Ξ -> a_binds_tvar α1 Θ1) ->
  (forall α1, binds α1 abind_flex_mono Ξ -> α1 `notin` Δ) ->
  {{ Θ1 ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A)) }}ad.
Proof.
  induction n as [| n IHn]; intros Θ P Ξ A Hsz H;
    [ destruct H; cbn in Hsz; lia | ].
  destruct H as [ Θ α Hα | Θ P Ξ A Hg | Θ α | Θ
                | Θ P Q Ξ1 Ξ2 A B Hg1 Hg2
                | Θ P Ξ A β Hfr Hg ];
    cbn in Hsz; intros Θ1 Δ Hvars HΞ HΞΔ.
  -
    replace (pskl_to_bskl_inh (ptyp_to_pskl (ptyp_var_f α)))
      with (pskl_to_bskl_syn (pskl_var_f α)) by reflexivity.
    apply ad_refine_syn__ghost.
    assert (Hn : α `notin` Δ)
      by (apply HΞΔ; unfold binds; left; reflexivity).
    simpl. clear - Hn; fsetdec.
  -
    apply ad_refine_syn_univ_ghost_remove_intro.
    eapply IHn; [ lia | exact Hg | exact Hvars | exact HΞ | exact HΞΔ ].
  -
    apply ad_refine_syn__var.
  -  apply ad_refine_syn__unit.
  -
    apply ad_refine_syn_arrow_intro;
      [ eapply IHn with (P := P) | eapply IHn with (P := Q) ];
      solve [ lia | eassumption
            | intros α Hα; apply Hvars; simpl; clear - Hα; fsetdec
            | intros α1 Hb; first [ apply HΞ | apply HΞΔ ];
              unfold binds in *; apply in_or_app; auto ].
  -
    apply ad_refine_syn_all_intro
      with (L := dom Ξ `union` dom Θ1 `union` Δ `union` ftvar_in_aenv Θ
                   `union` ftvar_in_pskl P `union` ftvar_in_ptyp A
                   `union` singleton β).
    intros α Hα.
    repeat rewrite <- pskl_to_bskl_inh_open.
    rewrite <- ptyp_to_pskl_open.
    eapply IHn with (P := open_pskl_wrt_pskl P (pskl_var_f α))
                    (Θ := (α ~ abind_tvar) ++ Θ);
      [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia | | | | ].
    + apply a_guess_mono_open_at;
        [ apply a_guess_mono__forall with (β := β); [ exact Hfr | exact Hg ]
        | clear - Hα; fsetdec ].
    + intros β0 Hβ0.
      apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in Hβ0.
      simpl in Hβ0.
      destruct (union_1 Hβ0) as [HY' | HY'].
      * apply singleton_1 in HY'; subst. left. clear; fsetdec.
      * destruct (Hvars _ HY') as [HΔ | Htv];
          [ left; clear - HΔ; fsetdec
          | right; apply a_binds_tvar_cons_tvar; right; exact Htv ].
    + intros α1 Hb. apply a_binds_tvar_cons_tvar. right. apply HΞ, Hb.
    + intros α1 Hb.
      assert (Hne : α1 <> α)
        by (intros ->; apply binds_In in Hb; clear - Hα Hb; fsetdec).
      specialize (HΞΔ α1 Hb). clear - Hne HΞΔ; fsetdec.
Qed.

Corollary a_guess_mono_refine : forall Θ P Ξ A Θ1 Δ,
  a_guess_mono Θ P Ξ A ->
  (forall α, α `in` ftvar_in_pskl P -> α `in` Δ \/ a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono Ξ -> a_binds_tvar α1 Θ1) ->
  (forall α1, binds α1 abind_flex_mono Ξ -> α1 `notin` Δ) ->
  {{ Θ1 ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A)) }}ad.
Proof. intros. eapply a_guess_mono_refine_size; eauto. Qed.

Lemma ad_pat_consis_mono_to_refine : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θ }}a ->
  forall A Δ, R = ptyp_to_uskl_syn A -> mono_ptyp A ->
  {{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn A) ⊳ Qt }}ad.
Proof.
  intros Ψ Θ R Qt Hc Hwf; induction Hc; intros A0 Δ HeqS HmA0;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in *.
  -
    destruct HmA0; simpl in HeqS; try discriminate.
    simpl. apply ad_refine_syn__unit.
  -
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst. simpl. apply ad_refine_syn__var.
  -
    destruct HmA0 as [ | | A1 A2 Hm1 Hm2 ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl. apply ad_refine_syn_arrow_intro; [ eapply IHHc1 | eapply IHHc2 ];
      solve [ reflexivity | assumption ].
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
    simpl. eapply ad_refine_syn__flex_l; [ eassumption | ].
    eapply IHHc; solve [ reflexivity | assumption ].
  -
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_refine_syn__flex_r; [ eassumption | ].
    eapply IHHc; solve [ reflexivity | assumption ].
Qed.

Lemma a_split_refines_gen : forall Θ0 A0 P Q Θ1 Θ' Qb,
  {{ Θ0 ⊲ (ptyp_to_pskl A0) ▹ P ⇢ Q ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl A0) }}a ->
  Θ1 ⊴ Θ' ->
  {{ ⊢ Θ' }}a ->
  {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh Q) ⊳ Qb }}ad ->
  {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (ptyp_to_pskl A0))
    ⊳ (bskl_arrow (pskl_to_bskl_inh P) Qb) }}ad.
Proof.
  intros Θ0 A0 P Q Θ1 Θ' Qb Hs Hwf HwfP Hle Hwf' HQb.
  inversion Hs; subst.
  -
    match goal with
    | Heq : pskl_arrow ?PP ?QQ = ptyp_to_pskl ?X |- _ =>
        destruct X as [ | | | Ad Ac | ]; simpl in Heq; try discriminate;
        inversion Heq; subst
    end.
    simpl.
    apply ad_refine_syn_arrow_intro; [ | exact HQb ].
    apply ad_refine_syn_refl_inh.
    inversion HwfP; subst.
    eapply a_wf_pskl_isub; [ | exact Hle ]. assumption.
  -
    match goal with
    | Heq : pskl_ghost = ptyp_to_pskl ?X |- _ =>
        destruct X; simpl in Heq; discriminate
    end.
  -
    match goal with
    | Heq : pskl_var_f ?a = ptyp_to_pskl ?X |- _ =>
        destruct X; simpl in Heq; try discriminate;
        inversion Heq; subst
    end.
    match goal with
    | Hf1 : ?β0 `notin` ftvar_in_aenv Θ0,
      Hf2 : ?α10 `notin` add ?β0 (ftvar_in_aenv Θ0) |- _ =>
        rename Hf1 into Hfβ; rename Hf2 into Hfα1;
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds;
        assert (Hfrβ : β0 `notin` dom Θ0) by (clear - Hfβ Hds; fsetdec);
        assert (Hfrα1 : α10 `notin` add β0 (dom Θ0))
          by (clear - Hfα1 Hds; fsetdec)
    end.
    assert (HwfX : {{ ⊢ ((α1 ~ abind_flex_mono)
                               ++ (β ~ abind_flex_mono) ++ Θ0) }}a).
    { apply a_wf_aenv__flex;
        [ simpl_env; repeat rewrite dom_app; simpl;
          clear - Hfrα1; fsetdec | ].
      apply a_wf_aenv__flex; [ clear - Hfrβ; fsetdec | exact Hwf ]. }
    assert (HwfArr : {{ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θ0)
                       ⨟ empty ⊢ₚₛ (pskl_arrow (pskl_var_f β)
                                                (pskl_var_f α1)) }}a).
    { apply a_wf_pskl__arrow; apply a_wf_pskl__var; right; left;
        [ unfold binds; simpl; right; left; reflexivity
        | unfold binds; simpl; left; reflexivity ]. }
    match goal with
    | Hc : a_consis _ _ _ _ _ _ _ |- _ => inversion Hc; subst
    end.
    match goal with
    | Ha : {{ _ ⊲[ nil ] _ ≔ _ ⊣ _ }}a |- _ =>
        pose proof (a_assign_sound Ha a_decls__nil
                      ltac:(simpl_env; exact HwfX)
                      ltac:(simpl_env; exact HwfArr)) as [Hle1 Hcons];
        pose proof (a_assign_preserves_wf Ha a_decls__nil
                      ltac:(simpl_env; exact HwfX)
                      ltac:(simpl_env; exact HwfArr)) as Hwf1
    end.
    inversion Hcons; subst.
    match goal with
    | Hb : binds _ (abind_flex_mono_def ?τx) Θ1,
      Hc2 : {{ _ ⨟ Θ1 ⊢ˢ _ ∼ (ptyp_to_bskl_syn ?τx) }}ad |- _ =>
        rename Hb into Hbdef; rename Hc2 into Hcns
    end.
    match type of Hbdef with
    | binds _ (abind_flex_mono_def ?τx) _ => rename τx into τ0
    end.
    assert (Hmτ : mono_ptyp τ0)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    assert (Hmarr : mono_ptyp (ptyp_arrow (ptyp_var_f β) (ptyp_var_f α1)))
      by (repeat constructor).
    assert (Hsym : {{ empty ⨟ Θ1 ⊢ˢ (ptyp_to_uskl_syn τ0)
             ∼ (ptyp_to_bskl_syn (ptyp_arrow (ptyp_var_f β)
                                             (ptyp_var_f α1))) }}ad).
    { eapply consis_mono_sym with
        (A := ptyp_arrow (ptyp_var_f β) (ptyp_var_f α1)) (A' := τ0);
        [ exact Hcns | exact Hwf1 | reflexivity | reflexivity
        | exact Hmarr | exact Hmτ ]. }
    assert (Hmid : {{ Θ1 ⨟ empty ⊢ᵣ (ptyp_to_bskl_syn τ0)
             ⊳ (ptyp_to_bskl_syn (ptyp_arrow (ptyp_var_f β)
                                             (ptyp_var_f α1))) }}ad).
    { eapply ad_pat_consis_mono_to_refine with (A := τ0);
        [ exact Hsym | exact Hwf1 | reflexivity | exact Hmτ ]. }
    assert (Hmid' : {{ Θ1 ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh (ptyp_to_pskl τ0))
              ⊳ (btyp_to_bskl
                   (ptyp_to_btyp_inh
                      (ptyp_arrow (ptyp_var_f β) (ptyp_var_f α1)))) }}ad).
    { rewrite btyp_to_bskl_ptyp_to_btyp_inh.
      unfold ptyp_to_bskl_syn in Hmid.
      rewrite (mono_bskl_syn_inh (ptyp_to_pskl τ0)) in Hmid;
        [ | apply mono_ptyp_to_bskl_syn; exact Hmτ ].
      rewrite (mono_bskl_syn_inh
                 (ptyp_to_pskl (ptyp_arrow (ptyp_var_f β) (ptyp_var_f α1))))
        in Hmid;
        [ | apply mono_ptyp_to_bskl_syn; exact Hmarr ].
      exact Hmid. }
    assert (Heqv : {{ Θ1 ⊢ τ0 ≡ᵗ
              (btyp_to_ptyp (ptyp_to_btyp_inh
                 (ptyp_arrow (ptyp_var_f β) (ptyp_var_f α1)))) }}a).
    { eapply ad_refine_syn_inh_tyequiv with (A := τ0);
        [ exact Hmid' | exact Hwf1 | reflexivity | reflexivity ]. }
    rewrite btyp_to_ptyp_ptyp_to_btyp_inh in Heqv.
    pose proof (a_tyequiv_isub_le Hle Heqv) as Heqv'.
    pose proof (a_tyequiv_pskl Heqv') as Hskleq.
    assert (Harr : {{ Θ' ⨟ empty ⊢ᵣ
              (pskl_to_bskl_inh
                 (ptyp_to_pskl (ptyp_arrow (ptyp_var_f β) (ptyp_var_f α1))))
              ⊳ (bskl_arrow (pskl_to_bskl_inh (pskl_var_f β)) Qb) }}ad).
    { simpl.
      apply ad_refine_syn_arrow_intro; [ | exact HQb ].
      apply ad_refine_syn__var. }
    pose proof (proj2 (skl_tyequiv_refine_syn_transport Hskleq Hwf'
                         (fun x b h => h))
                  empty _ Harr) as Hτ0.
    simpl.
    eapply ad_refine_syn__flex_l;
      [ eapply a_isub_binds_flex_def; [ exact Hle | exact Hbdef ] | ].
    unfold ptyp_to_bskl_syn.
    rewrite (mono_bskl_syn_inh (ptyp_to_pskl τ0));
      [ | apply mono_ptyp_to_bskl_syn; exact Hmτ ].
    exact Hτ0.
Qed.

Lemma a_wf_exp_ftv_dom : forall Θ e,
  {{ Θ ⊢ᵉ e }}a -> ftvar_in_exp e [<=] dom Θ.
Proof.
  intros Θ e H; induction H; simpl;
    try solve [ clear; fsetdec | assumption ].
  -
    pose proof (a_wf_ptyp_ftv_dom H) as Hd. clear - Hd IHa_wf_exp. fsetdec.
  -
    destruct (atom_fresh L) as [x Hx].
    pose proof (H0 x Hx) as Hd.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_lower e (exp_var_f x)) as Hl.
    clear - Hd Hl; fsetdec.
  -
    destruct (atom_fresh L) as [x Hx].
    pose proof (a_wf_ptyp_ftv_dom H) as Hd0.
    pose proof (H1 x Hx) as Hd.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_lower e (exp_var_f x)) as Hl.
    clear - Hd0 Hd Hl; fsetdec.
  -  clear - IHa_wf_exp1 IHa_wf_exp2; fsetdec.
Qed.

Lemma btyp_of_erased_ptyp : forall Q A,
  bskl_to_pskl Q = ptyp_to_pskl A ->
  exists B, btyp_to_bskl B = Q /\ btyp_to_ptyp B = A.
Proof.
  induction Q as [ | k | α0 | Q1 IHQ1 Q2 IHQ2 | Q0 IHQ | Q0 IHQ | | Q0 IHQ ];
    intros A0 Heq; destruct A0; simpl in Heq; try discriminate.
  - exists btyp_unit; split; reflexivity.
  - inversion Heq. exists (btyp_var_b k); simpl; split; congruence.
  - inversion Heq. exists (btyp_var_f α0); simpl; split; congruence.
  - inversion Heq.
    destruct (IHQ1 _ H0) as [B1 [HeB1 HeA1]].
    destruct (IHQ2 _ H1) as [B2 [HeB2 HeA2]].
    exists (btyp_arrow B1 B2); simpl; split; congruence.
  - inversion Heq. destruct (IHQ _ H0) as [B0 [HeB HeA]].
    exists (btyp_all_syn B0); simpl; split; congruence.
  - inversion Heq. destruct (IHQ _ H0) as [B0 [HeB HeA]].
    exists (btyp_all_inh B0); simpl; split; congruence.
Qed.

Lemma btyp_to_ptyp_arrow_inv : forall B A1 A2,
  btyp_to_ptyp B = ptyp_arrow A1 A2 ->
  exists B1 B2, B = btyp_arrow B1 B2 /\
                btyp_to_ptyp B1 = A1 /\ btyp_to_ptyp B2 = A2.
Proof.
  intros B A1 A2 Heq; destruct B; simpl in Heq; try discriminate.
  inversion Heq; subst. exists B1, B2; repeat split.
Qed.

Lemma a_wf_ptyp_of_scope_pskl : forall Θ P,
  a_scope_pskl Θ P -> forall A, P = ptyp_to_pskl A -> a_wf_ptyp Θ A.
Proof.
  intros Θ P [Hlc Hb]; revert Θ Hb; induction Hlc; intros Θ Hb A0 Heq;
    destruct A0; simpl in Heq; try discriminate; inversion Heq; subst;
    simpl in Hb.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. apply Hb. clear; fsetdec.
  - apply a_wf_ptyp__arrow;
      [ eapply IHHlc1 | eapply IHHlc2 ]; try reflexivity;
      intros β Hβ; apply Hb; clear - Hβ; fsetdec.
  - apply a_wf_ptyp__all with (L := ftvar_in_pskl (ptyp_to_pskl A0)).
    intros α Hα. eapply (H0 α); [ | rewrite ptyp_to_pskl_open; reflexivity ].
    intros β Hβ. apply a_binds_tvar_cons_tvar.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                  (ptyp_to_pskl A0) (pskl_var_f α)) as Hup.
    simpl in Hup.
    destruct (β == α) as [-> | Hne]; [ left; reflexivity | right ].
    apply Hb. clear - Hup Hβ Hne. fsetdec.
Qed.

Lemma binds_strip_prefix_mid : forall (b : abind) x Θa Ξ Θ,
  binds x b (Θa ++ Ξ ++ Θ) -> x `notin` dom Ξ -> binds x b (Θa ++ Θ).
Proof.
  intros b x Θa Ξ Θ Hb Hx. unfold binds in *.
  apply in_app_or in Hb; destruct Hb as [Hb | Hb];
    [ apply in_or_app; left; exact Hb | ].
  apply in_app_or in Hb; destruct Hb as [Hb | Hb];
    [ exfalso; apply Hx; eapply binds_In; exact Hb
    | apply in_or_app; right; exact Hb ].
Qed.

Lemma a_binds_tvar_strip_prefix_mid : forall α Θa Ξ Θ,
  a_binds_tvar α (Θa ++ Ξ ++ Θ) -> α `notin` dom Ξ ->
  a_binds_tvar α (Θa ++ Θ).
Proof.
  intros α Θa Ξ Θ [Hb | [Hb | [τ Hb]]] Hα;
    [ left | right; left | right; right; exists τ ];
    eapply binds_strip_prefix_mid; eassumption.
Qed.

Lemma a_wf_ptyp_strip_mid : forall Θa Ξ Θ A,
  a_wf_ptyp (Θa ++ Ξ ++ Θ) A ->
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
  a_wf_ptyp (Θa ++ Θ) A.
Proof.
  intros Θa Ξ Θ A H.
  remember (Θa ++ Ξ ++ Θ) as Θfull eqn:HΘ.
  revert Θa HΘ. induction H; intros Θa HΘ Hfv; subst.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var.
    eapply a_binds_tvar_strip_prefix_mid;
      [ exact H | intros Hin; apply (Hfv _ Hin); simpl; clear; fsetdec ].
  - apply a_wf_ptyp__arrow;
      [ apply IHa_wf_ptyp1 | apply IHa_wf_ptyp2 ];
      solve [ reflexivity
            | intros γ Hγ; pose proof (Hfv γ Hγ) as Hn;
              simpl in Hn; clear - Hn; fsetdec ].
  - apply a_wf_ptyp__all with (L := L `union` dom Ξ). intros α Hα.
    rewrite_env (((α ~ abind_tvar) ++ Θa) ++ Θ).
    apply (H0 α ltac:(clear - Hα; solve_notin_auto));
      [ simpl_env; reflexivity | ].
    intros γ Hγ.
    pose proof (Hfv γ Hγ) as Hn.
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A (ptyp_var_f α)) as Hup.
    simpl in Hup.
    assert (Hne : γ <> α) by (intros ->; clear - Hα Hγ; fsetdec).
    clear - Hn Hup Hne; fsetdec.
Qed.

Corollary a_wf_ptyp_strip_prefix : forall Ξ Θ A,
  a_wf_ptyp (Ξ ++ Θ) A ->
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
  a_wf_ptyp Θ A.
Proof.
  intros Ξ Θ A H Hfv. rewrite_env (nil ++ Θ).
  eapply a_wf_ptyp_strip_mid; [ simpl_env; exact H | exact Hfv ].
Qed.

Lemma a_wf_exp_strip_prefix : forall Θall e,
  {{ Θall ⊢ᵉ e }}a ->
  forall Ξ Θ, Θall = Ξ ++ Θ ->
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_exp e) ->
  {{ Θ ⊢ᵉ e }}a.
Proof.
  intros Θall e H; induction H; intros Ξ Θ' Heq Hfv; subst; simpl in Hfv.
  - apply a_wf_exp__unit.
  - apply a_wf_exp__var.
  - apply a_wf_exp__anno.
    + eapply a_wf_ptyp_strip_prefix;
        [ exact H
        | intros γ Hγ; pose proof (Hfv γ Hγ) as Hn; clear - Hn; fsetdec ].
    + eapply IHa_wf_exp;
        [ reflexivity
        | intros γ Hγ; pose proof (Hfv γ Hγ) as Hn; clear - Hn; fsetdec ].
  - apply a_wf_exp__freeze.
    eapply IHa_wf_exp; [ reflexivity | exact Hfv ].
  - apply a_wf_exp__abs with (L := L). intros x Hx.
    eapply H0; [ exact Hx | reflexivity | ].
    intros γ Hγ. pose proof (Hfv γ Hγ) as Hn.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup. clear - Hn Hup; fsetdec.
  - apply a_wf_exp__abs_anno with (L := L).
    + eapply a_wf_ptyp_strip_prefix;
        [ exact H
        | intros γ Hγ; pose proof (Hfv γ Hγ) as Hn; clear - Hn; fsetdec ].
    + intros x Hx.
      eapply H1; [ exact Hx | reflexivity | ].
      intros γ Hγ. pose proof (Hfv γ Hγ) as Hn.
      pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
      simpl in Hup. clear - Hn Hup; fsetdec.
  - apply a_wf_exp__app;
      [ eapply IHa_wf_exp1 | eapply IHa_wf_exp2 ];
      solve [ reflexivity
            | intros γ Hγ; pose proof (Hfv γ Hγ) as Hn; clear - Hn; fsetdec ].
Qed.

Corollary a_wf_exp_strip_tm : forall x (b : abind) Θ e,
  {{ ((x ~ b) ++ Θ) ⊢ᵉ e }}a -> ~ abind_is_ty b -> {{ Θ ⊢ᵉ e }}a.
Proof.
  intros x b Θ e H Hb.
  eapply a_wf_exp_mono;
    [ exact H | apply (@aenv_tbinds_le_strip_tm nil x b Θ); exact Hb ].
Qed.

Lemma ad_sd_typing_wf_exp : forall M Θ e B,
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad -> {{ Θ ⊢ᵉ e }}a.
Proof.
  intros M Θ e B H; induction H.
  - apply a_wf_exp__unit.
  - apply a_wf_exp__var.
  - apply a_wf_exp__anno; assumption.
  - apply a_wf_exp__freeze; assumption.
  -
    destruct (atom_fresh (L `union` ftvar_in_exp (exp_abs e))) as [α Hα].
    eapply a_wf_exp_strip_prefix;
      [ apply (H0 α ltac:(clear - Hα; fsetdec)) | reflexivity | ].
    intros γ Hγ. simpl in Hγ.
    assert (γ = α) by (clear - Hγ; fsetdec). subst γ.
    clear - Hα; fsetdec.
  -
    apply a_wf_exp__abs with (L := L). intros x Hx.
    eapply a_wf_exp_strip_tm;
      [ apply (H2 x Hx) | intros []; discriminate ].
  -
    destruct (atom_fresh (L `union` ftvar_in_exp (exp_abs_anno A e)))
      as [α Hα].
    eapply a_wf_exp_strip_prefix;
      [ apply (H0 α ltac:(clear - Hα; fsetdec)) | reflexivity | ].
    intros γ Hγ. simpl in Hγ.
    assert (γ = α) by (clear - Hγ; fsetdec). subst γ.
    clear - Hα; fsetdec.
  -
    apply a_wf_exp__abs_anno with (L := L); [ assumption | ]. intros x Hx.
    eapply a_wf_exp_strip_tm;
      [ apply (H3 x Hx) | intros []; discriminate ].
  -
    apply a_wf_exp__abs with (L := L). intros x Hx.
    eapply a_wf_exp_strip_tm;
      [ apply (H3 x Hx) | intros []; discriminate ].
  -
    apply a_wf_exp__abs_anno with (L := L); [ assumption | ]. intros x Hx.
    eapply a_wf_exp_strip_tm;
      [ apply (H5 x Hx) | intros []; discriminate ].
  -  apply a_wf_exp__app; assumption.
Qed.

Lemma a_wf_exp_lc : forall Θ e, {{ Θ ⊢ᵉ e }}a -> lc_exp e.
Proof.
  intros Θ e H; induction H.
  - apply lc_exp_unit.
  - apply lc_exp_var_f.
  - apply lc_exp_anno; [ assumption | eapply a_wf_ptyp_lc; eassumption ].
  - apply lc_exp_freeze; assumption.
  - destruct (atom_fresh L) as [x Hx].
    apply (lc_exp_abs_exists x). apply H0. exact Hx.
  - destruct (atom_fresh L) as [x Hx].
    apply (lc_exp_abs_anno_exists x);
      [ eapply a_wf_ptyp_lc; eassumption | apply H1; exact Hx ].
  - apply lc_exp_app; assumption.
Qed.

Lemma a_decls_binds_flex : forall Ξ y (b : abind),
  a_decls Ξ -> binds y b Ξ -> b = abind_flex_mono.
Proof.
  intros Ξ y b Hd; induction Hd; intros Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
    [ exact Heq | apply IHHd; exact Hb' ].
Qed.

Lemma bskl_ghost_free_inh_ptyp : forall A,
  bskl_ghost_free (pskl_to_bskl_inh (ptyp_to_pskl A)).
Proof. induction A; simpl; intuition. Qed.

Lemma ftvar_in_bskl_inh_ptyp : forall A,
  ftvar_in_bskl (pskl_to_bskl_inh (ptyp_to_pskl A)) [=] ftvar_in_ptyp A.
Proof. induction A; simpl; fsetdec. Qed.

Lemma a_wf_ptyp_all_open_at : forall Θ A0 α,
  a_wf_ptyp Θ (ptyp_all A0) ->
  a_wf_ptyp ((α ~ abind_tvar) ++ Θ) (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)).
Proof.
  intros Θ A0 α Hwf.
  inversion Hwf as [ | | | L0 Θx A0x Hbody Heq1 Heq2 ]; subst.
  destruct (atom_fresh (L0 `union` ftvar_in_ptyp A0 `union` singleton α))
    as [β0 Hβ0].
  pose proof (@a_wf_ptyp_rename_tvar _ _
                (Hbody β0 ltac:(clear - Hβ0; solve_notin_auto)) nil β0 Θ α eq_refl)
    as Hr.
  simpl in Hr.
  rewrite <- (subst_ptyp_in_ptyp_intro β0 A0 (ptyp_var_f α)
                ltac:(clear - Hβ0; solve_notin_auto)) in Hr.
  exact Hr.
Qed.

Lemma a_typing_abs_body_input : forall {x Θ0 P Q αs A} {Ξ Θ2 : aenv} {e},
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Q }}a ->
  {{ Θ0 ⊢ᵉ (exp_abs e) }}a ->
  a_guess_mono Θ0 P αs A ->
  uniq (αs ++ Θ0) ->
  x `notin` dom (Ξ ++ αs ++ Θ0) `union` dom Θ2 `union` fvar_in_exp e ->
  a_decls αs /\ a_wf_ptyp (αs ++ Θ0) A /\
  ({{ ⊢ ((x ~ abind_var_typ A) ++ αs ++ Θ0) }}a) /\
  ({{ ((x ~ abind_var_typ A) ++ αs ++ Θ0) ⨟ empty ⊢ₚₛ Q }}a) /\
  ({{ ((x ~ abind_var_typ A) ++ αs ++ Θ0)
        ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a).
Proof.
  intros x Θ0 P Q αs A Ξ Θ2 e Hwf HwfPP HwfQ Hexp Hg Huq Hfr.
  assert (Hdecls : a_decls αs) by (eapply a_guess_mono_decls; eassumption).
  assert (HwfAg : a_wf_ptyp (αs ++ Θ0) A).
  { eapply a_guess_mono_wf; [ exact Hg | | ].
    - intros α1 Hα1. apply a_binds_tvar_weaken_cons.
      exact (a_wf_pskl_ftv_binds HwfPP Hα1).
    - intros α1 Hb. unfold a_binds_tvar. right; left.
      unfold binds; apply in_or_app; left; exact Hb. }
  split; [ exact Hdecls | ]. split; [ exact HwfAg | ].
  split.
  { apply a_wf_aenv__var_typ; [ | exact HwfAg | ].
    - rewrite !dom_app in *. clear - Hfr. fsetdec.
    - apply a_wf_aenv_decls_app; assumption. }
  split.
  - eapply a_wf_pskl_weaken; [ | exact HwfQ ].
    intros z c Hbz. apply binds_app_3. apply binds_app_3. exact Hbz.
  - eapply a_wf_exp_mono; [ exact (a_wf_exp_abs_pick x Hexp) | ].
    intros z c Hty Hbz. apply binds_app_3. apply binds_app_3. exact Hbz.
Qed.

Lemma a_typing_sound_check_step_of_rule : forall t α Θ0 Θ1 A0 A Ξ,
  (forall L Θ B,
     (forall β, β `notin` L ->
        {{ ((β ~ abind_tvar) ++ Θ) ⊢ˢᵈ[ mode_tc ] t
          ⦂ (open_btyp_wrt_btyp B (btyp_var_f β)) }}ad) ->
     {{ Θ ⊢ˢᵈ[ mode_tc ] t ⦂ (btyp_all_inh B) }}ad) ->
  a_suffix Ξ ->
  uniq (Ξ ++ Θ0) ->
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
  α `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union`
    ftvar_in_ptyp A0 `union` ftvar_in_ptyp A `union` ftvar_in_exp t ->
  {{ ((α ~ abind_tvar) ++ Θ0)
    ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
    t ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
    ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}a ->
  ({{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a ->
   {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
      (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) }}a ->
   a_ty_mode_compat mode_tc (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ->
   {{ ((α ~ abind_tvar) ++ Θ0) ⊢ᵉ t }}a ->
   ((α ~ abind_tvar) ++ Θ0) ⊴ (Ξ ++ (α ~ abind_tvar) ++ Θ1) /\
   {{ ⊢ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}a /\
   a_wf_ptyp (Ξ ++ (α ~ abind_tvar) ++ Θ1) (open_ptyp_wrt_ptyp A (ptyp_var_f α)) /\
   exists Bt, btyp_to_ptyp Bt = open_ptyp_wrt_ptyp A (ptyp_var_f α) /\
     ({{ (Ξ ++ (α ~ abind_tvar) ++ Θ1) ⊢ˢᵈ[ mode_tc ] t ⦂ Bt }}ad) /\
     ({{ (Ξ ++ (α ~ abind_tvar) ++ Θ1) ⨟ empty ⊢ᵣ
        (pskl_to_bskl_inh (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))))
        ⊳ (btyp_to_bskl Bt) }}ad)) ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl (ptyp_all A0)) }}a ->
  {{ Θ0 ⊢ᵉ t }}a ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> {{ Θ0 ⨟ empty ⊢ₚₛ Ps }}a) ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 (ptyp_all A) /\
  exists Bt, btyp_to_ptyp Bt = ptyp_all A /\
    ({{ Θ1 ⊢ˢᵈ[ mode_tc ] t ⦂ Bt }}ad) /\
    ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (ptyp_to_pskl (ptyp_all A0)))
       ⊳ (btyp_to_bskl Bt) }}ad).
Proof.
  intros t α Θ0 Θ1 A0 A Ξ Hrule H H0 H1 H2 H3 IHa_typing Hwf HwfP0 Hexp Hskl.
  assert (HwfA0 : a_wf_ptyp Θ0 (ptyp_all A0))
    by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfP0).
  assert (Hfve : ftvar_in_exp (t) [<=] dom Θ0)
    by (apply a_wf_exp_ftv_dom; exact Hexp).
  assert (HΞΘ0 : forall γ, γ `in` dom Ξ -> γ `notin` dom Θ0)
    by (intros γ Hγ; clear - H0 Hγ; destruct_uniq;
        unfold disjoint in *; fsetdec).
  assert (HftvA0 : ftvar_in_ptyp A0 [<=] dom Θ0)
    by (pose proof (a_wf_ptyp_ftv_dom HwfA0) as Hd; simpl in Hd; exact Hd).
  assert (Hα : α `notin` dom Ξ `union` dom Θ0 `union` dom Θ1
                 `union` ftvar_in_ptyp A0 `union` ftvar_in_ptyp A
                 `union` ftvar_in_exp (t))
    by (clear - H2; rewrite !dom_app in H2; fsetdec).
  assert (Hwfα : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
    by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]).
  assert (HwfA0α : a_wf_ptyp ((α ~ abind_tvar) ++ Θ0)
                     (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
    by (apply a_wf_ptyp_all_open_at; exact HwfA0).
  destruct (IHa_typing Hwfα
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA0α)
              (a_ty_mode_compat__tc _)
              (a_wf_exp_weaken_cons α abind_tvar Hexp))
    as [Hle [Hwfo [HwfAo [Bα [HeBα [Hdα Hrefα]]]]]].
  assert (HBα : Bα = ptyp_to_btyp_inh
                       (open_ptyp_wrt_ptyp A (ptyp_var_f α))).
  { apply btyp_check_colouring; [ | exact HeBα ].
    apply mod_comp_ty_tc_inv.
    eapply ad_sd_typing_mod_comp_ty; eassumption. }
  subst Bα. rewrite btyp_to_bskl_ptyp_to_btyp_inh in Hrefα.
  assert (Huniq0 : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ1))
    by (apply a_wf_aenv_uniq; exact Hwfo).
  assert (Hisub : Θ0 ⊴ Θ1)
    by (eapply a_isub_strip_tvar_mid;
        [ exact Huniq0 | exact H0 | clear - Hα; fsetdec | exact Hle ]).
  assert (Hwf1 : {{ ⊢ Θ1 }}a)
    by (eapply a_wf_aenv_strip_prefix_suffix_local; exact Hwfo).
  assert (HwfAα1 : a_wf_ptyp ((α ~ abind_tvar) ++ Θ1)
                     (open_ptyp_wrt_ptyp A (ptyp_var_f α))).
  { eapply a_wf_ptyp_strip_prefix; [ exact HwfAo | ].
    intros γ Hγ.
    pose proof (H1 γ Hγ) as Hn.
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A (ptyp_var_f α))
      as Hup.
    simpl in Hup.
    assert (Hne : γ <> α) by (intros ->; clear - Hα Hγ; fsetdec).
    clear - Hn Hup Hne; fsetdec. }
  assert (HwfAll : a_wf_ptyp Θ1 (ptyp_all A)).
  { apply a_wf_ptyp__all
      with (L := ftvar_in_ptyp A `union` singleton α).
    intros β Hβ.
    pose proof (@a_wf_ptyp_rename_tvar _ _ HwfAα1 nil α Θ1 β eq_refl)
      as Hr.
    simpl in Hr.
    rewrite <- (subst_ptyp_in_ptyp_intro α A (ptyp_var_f β)
                  ltac:(clear - Hα; solve_notin_auto)) in Hr.
    exact Hr. }

  assert (Hdefs1 : forall β0 τ,
            binds β0 (abind_flex_mono_def τ) Θ1 ->
            α `notin` ftvar_in_ptyp τ).
  { intros β0 τ Hb Hc.
    pose proof (@a_wf_aenv_binds_def_wf Θ1 β0 τ Hwf1 Hb) as Hwτ.
    pose proof (a_wf_ptyp_ftv_dom Hwτ) as Hd.
    clear - Hα Hc Hd; fsetdec. }
  assert (Hvt1 : forall y A', binds y (abind_var_typ A') Θ1 ->
            α `notin` ftvar_in_ptyp A').
  { intros y A' Hb Hc.
    assert (HwA' : a_wf_ptyp Θ1 A')
      by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
    pose proof (a_wf_ptyp_ftv_dom HwA') as Hd.
    clear - Hα Hc Hd; fsetdec. }
  assert (Hvs1 : forall y Ps, binds y (abind_var_skl Ps) Θ1 ->
            α `notin` ftvar_in_pskl Ps).
  { intros y Ps Hb Hc.
    assert (Hb0 : binds y (abind_var_skl Ps) Θ0).
    { assert (Hbin : binds y (abind_var_skl Ps) ((α ~ abind_tvar) ++ Θ0)).
      { apply (a_typing_tm_ge H3); [ exact I | ].
        apply binds_app_3. apply binds_app_3. exact Hb. }
      destruct (binds_cons_1 _ _ _ _ _ _ Hbin) as [[_ He] | Hb0'];
        [ discriminate | exact Hb0' ]. }
    pose proof (Hskl _ _ Hb0) as Hwps.
    pose proof (a_wf_pskl_ftv_binds Hwps Hc) as Ht;
      apply a_binds_tvar_in_dom in Ht; clear - Hα Ht; fsetdec. }

  assert (Hdα1 : {{ ((α ~ abind_tvar) ++ Θ1) ⊢ˢᵈ[ mode_tc ] (t)
                   ⦂ (ptyp_to_btyp_inh
                        (open_ptyp_wrt_ptyp A (ptyp_var_f α))) }}ad).
  { eapply ad_sd_typing_strip_suffix;
      [ exact H | exact Hwfo | | exact Hdα ].
    intros γ Hγ.
    rewrite ftvar_ptyp_to_btyp_inh.
    pose proof (H1 γ Hγ) as Hn.
    pose proof (HΞΘ0 γ Hγ) as Hdd.
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A (ptyp_var_f α))
      as Hup.
    simpl in Hup.
    assert (Hne : γ <> α) by (intros ->; clear - Hα Hγ; fsetdec).
    clear - Hn Hup Hne Hdd Hfve; fsetdec. }
  split; [ exact Hisub | ]. split; [ exact Hwf1 | ].
  split; [ exact HwfAll | ].
  exists (ptyp_to_btyp_inh (ptyp_all A)).
  split; [ apply btyp_to_ptyp_ptyp_to_btyp_inh | ].
  split.
  + simpl. apply Hrule
      with (L := dom Θ1 `union` ftvar_in_ptyp A
                   `union` ftvar_in_exp (t) `union` singleton α).
    * intros β Hβ.
      rewrite <- ptyp_to_btyp_inh_open_var.
      pose proof (@ad_sd_typing_rename_tvar _ _ _ _ Hdα1 nil α Θ1 β
                    eq_refl
                    ltac:(simpl; clear - Hα; solve_notin_auto)
                    ltac:(simpl; clear - Hβ; solve_notin_auto)
                    ltac:(simpl; exact Hdefs1)
                    ltac:(exact Hvt1)
                    ltac:(exact Hvs1)) as Hr.
      simpl in Hr.
      rewrite (subst_ptyp_in_exp_fresh_eq t)
        in Hr; [ | clear - Hα; fsetdec ].
      rewrite subst_var_ptyp_to_btyp_inh in Hr.
      rewrite <- (subst_ptyp_in_ptyp_intro α A (ptyp_var_f β)
                    ltac:(clear - Hα; solve_notin_auto)) in Hr.
      exact Hr.
  + rewrite btyp_to_bskl_ptyp_to_btyp_inh. simpl.
    apply ad_refine_syn_all_intro
      with (L := dom Θ0 `union` dom Ξ `union` dom Θ1
                   `union` ftvar_in_ptyp A `union` ftvar_in_ptyp A0
                   `union` singleton α).
    intros β Hβ.
    repeat rewrite <- pskl_to_bskl_inh_open.
    repeat rewrite <- ptyp_to_pskl_open.
    assert (Hsub : forall X, α `notin` ftvar_in_ptyp X ->
              subst_bskl_in_bskl (bskl_var_f β) α
                (pskl_to_bskl_inh (ptyp_to_pskl
                   (open_ptyp_wrt_ptyp X (ptyp_var_f α))))
              = pskl_to_bskl_inh (ptyp_to_pskl
                   (open_ptyp_wrt_ptyp X (ptyp_var_f β)))).
    { intros X HX.
      change (bskl_var_f β) with (pskl_to_bskl_inh (pskl_var_f β)).
      rewrite <- pskl_to_bskl_inh_subst.
      change (pskl_var_f β) with (ptyp_to_pskl (ptyp_var_f β)).
      rewrite <- ptyp_to_pskl_subst.
      rewrite <- (subst_ptyp_in_ptyp_intro α X (ptyp_var_f β) HX).
      reflexivity. }
    rewrite <- (Hsub A0 ltac:(clear - Hα; solve_notin_auto)).
    rewrite <- (Hsub A ltac:(clear - Hα; solve_notin_auto)).
    eapply ad_refine_syn_defs_mono with (Θ := Θ1);
      [ | intros ? ? Hb; apply binds_app_iff; right; exact Hb ].
    eapply ad_refine_syn_delta_mono;
      [ eapply ad_refine_syn_ghost_free_strip_rename;
          [ exact Hrefα
          | reflexivity
          | apply bskl_ghost_free_inh_ptyp
          | exact Hwfo
          | exact Huniq0
          | intros γ Hγ;
            rewrite !ftvar_in_bskl_inh_ptyp in Hγ;
            pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper
                          A0 (ptyp_var_f α)) as Hup0;
            pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper
                          A (ptyp_var_f α)) as HupA;
            simpl in Hup0, HupA;
            assert (HγA : γ `in` ftvar_in_ptyp A -> γ `notin` dom Ξ)
              by (intros HA Hin; exact (H1 γ Hin HA));
            assert (HγA0 : γ `in` ftvar_in_ptyp A0 -> γ `notin` dom Ξ)
              by (intros HA0 Hin;
                  exact (HΞΘ0 γ Hin ltac:(clear - HA0 HftvA0; solve_notin_auto)));
            assert (Hγα : γ = α -> γ `notin` dom Ξ)
              by (intros ->; clear - Hα; fsetdec);
            clear - Hγ Hup0 HupA HγA HγA0 Hγα; fsetdec ]
      | clear; fsetdec ].
Qed.

Lemma a_typing_sound_check_base_body :
  forall {x Θc A B B1 e} {Ξ Θo : aenv},
  {{ ⊢ Θc }}a -> a_wf_ptyp Θc A -> a_wf_ptyp Θc B ->
  {{ Θc ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a ->
  a_suffix Ξ -> uniq (Ξ ++ Θc) ->
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1) ->
  x `notin` dom (Ξ ++ Θc) `union` dom Θo `union` fvar_in_exp e ->
  ({{ ⊢ ((x ~ abind_var_typ A) ++ Θc) }}a ->
   {{ ((x ~ abind_var_typ A) ++ Θc) ⨟ empty ⊢ₚₛ (ptyp_to_pskl B) }}a ->
   a_ty_mode_compat mode_tc (ptyp_to_pskl B) ->
   {{ ((x ~ abind_var_typ A) ++ Θc) ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a ->
   ((x ~ abind_var_typ A) ++ Θc) ⊴ (Ξ ++ (x ~ abind_var_typ A) ++ Θo) /\
   {{ ⊢ (Ξ ++ (x ~ abind_var_typ A) ++ Θo) }}a /\
   a_wf_ptyp (Ξ ++ (x ~ abind_var_typ A) ++ Θo) B1 /\
   exists Bt, btyp_to_ptyp Bt = B1 /\
     ({{ (Ξ ++ (x ~ abind_var_typ A) ++ Θo) ⊢ˢᵈ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ Bt }}ad) /\
     ({{ (Ξ ++ (x ~ abind_var_typ A) ++ Θo) ⨟ empty
         ⊢ᵣ (pskl_to_bskl_inh (ptyp_to_pskl B)) ⊳ (btyp_to_bskl Bt) }}ad)) ->
  Θc ⊴ Θo /\ ({{ ⊢ Θo }}a) /\ a_wf_ptyp Θo B1 /\
  (forall y,
     {{ ((y ~ abind_var_typ A) ++ Θo) ⊢ˢᵈ[ mode_tc ]
       (open_exp_wrt_exp e (exp_var_f y)) ⦂ (ptyp_to_btyp_inh B1) }}ad) /\
  ({{ Θo ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (ptyp_to_pskl B))
       ⊳ (btyp_to_bskl (ptyp_to_btyp_inh B1)) }}ad).
Proof.
  intros x Θc A B B1 e Ξ Θo Hwfc HwfA HwfB Hexpx Hsuf Huq HΞ Hfr IH.
  assert (Hx : x `notin` dom Θc `union` dom Ξ `union` dom Θo
                 `union` fvar_in_exp e)
    by (clear - Hfr; rewrite !dom_app in Hfr; fsetdec).
  assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θc) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact Hwfc ]).
  destruct (IH Hwfx
              (a_wf_pskl_weaken_cons x (abind_var_typ A)
                 (a_wf_ptyp_to_wf_pskl empty HwfB))
              (a_ty_mode_compat__tc B)
              (a_wf_exp_weaken_cons x (abind_var_typ A) Hexpx))
    as [Hle [Hwfout [HwfBout [Bt [HeBt [Hdb Hrefb]]]]]].
  assert (HBt : Bt = ptyp_to_btyp_inh B1).
  { apply btyp_check_colouring; [ | exact HeBt ].
    apply mod_comp_ty_tc_inv. eapply ad_sd_typing_mod_comp_ty; eassumption. }
  subst Bt.
  assert (Huniq2 : uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θo))
    by (apply a_wf_aenv_uniq; exact Hwfout).
  assert (HΞΘc : forall γ, γ `in` dom Ξ -> γ `notin` dom Θc)
    by (intros γ Hγ; clear - Huq Hγ; destruct_uniq;
        unfold disjoint in *; fsetdec).
  split.
  { eapply a_isub_strip_var_typ_mid; [ exact Huniq2 | exact Huq | exact Hle ]. }
  split.
  { eapply a_wf_aenv_strip_prefix.
    eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []. }
  split.
  { eapply a_wf_ptyp_strip_prefix; [ | exact HΞ ].
    eapply a_wf_ptyp_mono;
      [ exact HwfBout | apply aenv_tbinds_le_strip_tm; intros [] ]. }
  split.
  { intros y. apply ad_sd_typing_rename_tm with (x := x);
      [ eapply ad_sd_typing_strip_suffix;
          [ exact Hsuf | simpl_env; exact Hwfout | | simpl_env; exact Hdb ]
      | exact I
      | clear - Hx; fsetdec ].
    intros γ Hγ.
    rewrite ftvar_ptyp_to_btyp_inh.
    pose proof (HΞ γ Hγ) as Hn. pose proof (HΞΘc γ Hγ) as Hd1.
    pose proof (a_wf_exp_ftv_dom Hexpx) as Hfv.
    clear - Hn Hd1 Hfv; fsetdec. }
  { pose proof (a_wf_ptyp_ftv_dom HwfB) as HftvB.
    eapply ad_refine_syn_strip_suffix with (Ξ := Ξ);
      [ exact Hsuf
      | eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []
      | intros γ Hγ;
        rewrite btyp_to_bskl_ptyp_to_btyp_inh;
        rewrite !ftvar_in_bskl_inh_ptyp;
        pose proof (HΞ γ Hγ) as Hn;
        pose proof (HΞΘc γ Hγ) as Hd1;
        clear - Hn Hd1 HftvB; fsetdec
      | eapply ad_refine_syn_strip_tm_typ; exact Hrefb ]. }
Qed.

Theorem a_typing_sound : forall m Θ0 P0 e A Θ1,
  {{ Θ0 ⊢[ m ; P0 ] e ⦂ A ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat m P0 ->
  {{ Θ0 ⊢ᵉ e }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  exists Bt, btyp_to_ptyp Bt = A /\
    ({{ Θ1 ⊢ˢᵈ[ m ] e ⦂ Bt }}ad) /\
    ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ (btyp_to_bskl Bt) }}ad).
Proof.
  intros m Θ0 P0 e A Θ1 H; induction H; intros Hwf HwfP0 Hmod Hexp;
    pose proof (fun y Ps Hb => @a_wf_aenv_binds_var_skl_wf _ y Ps Hwf Hb)
      as Hskl.
  -
    destruct (a_sub_sound H Hwf HwfP0
                ltac:(apply a_wf_pskl__unit)
                ltac:(intros Hd; discriminate)
                ltac:(intros _; exact Hmod))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    destruct (btyp_of_erased_ptyp _ _ HeQt) as [Bt [HeB HeA]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split.
    { apply a_wf_ptyp_of_wf_pskl_empty.
      eapply a_sub_output_wf;
        [ exact H | exact Hwf | exact HwfP0 | apply a_wf_pskl__unit ]. }
    exists Bt. split; [ exact HeA | ]. split; [ | rewrite HeB; exact Href ].
    apply ad_sd_typing__unit.
    rewrite HeB, ptyp_to_uskl_syn_via_pskl. exact Hjoin.
  -
    assert (HwfA : a_wf_ptyp Θ0 A)
      by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
    destruct (a_sub_sound H0 Hwf HwfP0
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA)
                ltac:(intros Hd; discriminate)
                ltac:(intros _; exact Hmod))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    destruct (btyp_of_erased_ptyp _ _ HeQt) as [Bt [HeB HeA]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split.
    { apply a_wf_ptyp_of_wf_pskl_empty.
      eapply a_sub_output_wf;
        [ exact H0 | exact Hwf | exact HwfP0
        | apply a_wf_ptyp_to_wf_pskl; exact HwfA ]. }
    exists Bt. split; [ exact HeA | ]. split; [ | rewrite HeB; exact Href ].
    eapply ad_sd_typing__var;
      [ apply (a_sub_tm_le H0); [ exact I | exact H ]
      | rewrite HeB, ptyp_to_uskl_syn_via_pskl; exact Hjoin ].
  -
    destruct (a_wf_exp_anno_inv Hexp) as [HwfA Hexp0].
    destruct (IHa_typing Hwf
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA)
                (a_ty_mode_compat__tc A) Hexp0)
      as [Hle1 [Hwf1 [_ [Bt [HeBt [Hd1 Href1]]]]]].
    assert (HeBt' : Bt = ptyp_to_btyp_inh A).
    { apply btyp_check_colouring; [ | exact HeBt ].
      apply mod_comp_ty_tc_inv.
      eapply ad_sd_typing_mod_comp_ty; eassumption. }
    subst Bt.
    assert (HwfA1 : a_wf_ptyp Θ1 A) by (eapply a_wf_ptyp_isub; eassumption).
    destruct (a_sub_sound H0 Hwf1
                ltac:(eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hle1 ])
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA1)
                ltac:(intros Hd; discriminate)
                ltac:(intros _; exact Hmod))
      as [Hle2 [Hwf2 [Qt [HeQt [Hjoin Href]]]]].
    destruct (btyp_of_erased_ptyp _ _ HeQt) as [Bo [HeB HeA]].
    split; [ eapply a_isub_trans; eassumption | ]. split; [ exact Hwf2 | ].
    split.
    { apply a_wf_ptyp_of_wf_pskl_empty.
      eapply a_sub_output_wf;
        [ exact H0 | exact Hwf1
        | eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hle1 ]
        | apply a_wf_ptyp_to_wf_pskl; exact HwfA1 ]. }
    exists Bo. split; [ exact HeA | ]. split; [ | rewrite HeB; exact Href ].
    eapply ad_sd_typing__anno;
      [ eapply a_wf_ptyp_isub; [ exact HwfA1 | exact Hle2 ]
      | eapply ad_sd_typing_isub_tm;
          [ exact Hd1 | exact Hle2 | eapply a_sub_tm_le; exact H0 ]
      | rewrite HeB, ptyp_to_uskl_syn_via_pskl; exact Hjoin ].
  -
    destruct (IHa_typing Hwf ltac:(apply a_wf_pskl__ghost)
                a_ty_mode_compat__ti (a_wf_exp_freeze_inv Hexp))
      as [Hle1 [Hwf1 [HwfB1 [Bt [HeBt [Hd1 Href1]]]]]].
    destruct (ad_refine_syn_syn_l Href1 pskl_ghost eq_refl) as [P' HQt].
    assert (HBt : Bt = ptyp_to_btyp_syn B)
      by (rewrite <- HeBt; eapply btyp_syn_painting_inv; exact HQt).
    assert (HwfA0 : a_wf_ptyp Θ0 A)
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfP0).
    assert (HwfA1 : a_wf_ptyp Θ1 A) by (eapply a_wf_ptyp_isub; eassumption).
    destruct (a_consis_chk_sound H0 Hwf1
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA1)
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfB1))
      as [Hle2 [Hwf2 _]].
    assert (Hle : Θ0 ⊴ Θ2) by (eapply a_isub_trans; eassumption).
    split; [ exact Hle | ]. split; [ exact Hwf2 | ].
    split; [ eapply a_wf_ptyp_isub; [ exact HwfA0 | exact Hle ] | ].
    exists (ptyp_to_btyp_inh A).
    split; [ apply btyp_to_ptyp_ptyp_to_btyp_inh | ].
    split.
    + eapply ad_sd_typing__freeze;
        [ rewrite <- HBt; eapply ad_sd_typing_isub_tm;
            [ exact Hd1 | exact Hle2 | eapply a_consis_chk_tm_le; exact H0 ]
        | eapply a_consis_chk_tyequiv; eassumption ].
    + rewrite btyp_to_bskl_ptyp_to_btyp_inh.
      apply ad_refine_syn_refl_inh.
      eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hle ].
  -
    destruct (a_split_ty_shape H0 Hmod H) as [HeqΘ Hshape]; subst Θ1.
    destruct (a_split_ty_pieces H0 Hmod H HwfP0) as [HwfPP [HwfQ Hmod']].
    destruct (a_typing_abs_body_input Hwf HwfPP HwfQ Hexp H1 H2 H4)
      as [Hdecls [HwfAg [Hwfx [HwfQx Hexpx]]]].
    assert (Hx : x `notin` dom Θ0 `union` dom αs `union` dom Ξ
                   `union` dom Θ2 `union` fvar_in_exp e)
      by (clear - H4; rewrite !dom_app in H4; fsetdec).
    destruct (IHa_typing Hwfx HwfQx Hmod' Hexpx)
      as [Hle [Hwfout [HwfBout [Bt [HeBt [Hdb Hrefb]]]]]].
    assert (Huniq2 : uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfout).
    assert (Hlc2 : lc_aenv Θ2).
    { apply a_wf_aenv_lc_aenv in Hwfout.
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout].
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout]. exact Hwfout. }
    assert (Hisubαs : (αs ++ Θ0) ⊴ (Ξ ++ Θ2))
      by (eapply a_isub_peel_tm_mid; [ | eassumption .. ]; exact I).
    assert (Hisub : Θ0 ⊴ (Ξ ++ Θ2))
      by (eapply a_isub_strengthen_decls_src; eassumption).
    assert (Hwf2 : {{ ⊢ (Ξ ++ Θ2) }}a)
      by (eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []).
    assert (HwfA2 : a_wf_ptyp (Ξ ++ Θ2) A)
      by (eapply a_wf_ptyp_isub; [ exact HwfAg | exact Hisubαs ]).
    assert (HwfB2 : a_wf_ptyp (Ξ ++ Θ2) B).
    { eapply a_wf_ptyp_mono;
        [ exact HwfBout | apply aenv_tbinds_le_strip_tm; intros [] ]. }
    assert (Hmc : mod_comp_ty (btyp_arrow (ptyp_to_btyp_inh A) Bt) m).
    { pose proof (ad_sd_typing_mod_comp_ty Hdb Hwfout) as Hmq.
      destruct Hshape as [[HP0 [HP HQ]] | HP0]; subst.
      - pose proof (a_ty_mode_compat_ghost_inv Hmod) as Hm; subst m.
        inversion H1; subst.
        apply mod_comp_ty__ti. apply is_styp__arrow;
          [ simpl; apply is_styp__var | ].
        apply mod_comp_ty_ti_inv; exact Hmq.
      - destruct (a_ty_mode_compat_arrow_inv Hmod H) as [m' [Hm Hm']];
          subst m. apply mod_comp_ty__fn. exact Hmq. }
    assert (Hbody : forall y,
              {{ ((y ~ abind_var_typ A) ++ (Ξ ++ Θ2)) ⊢ˢᵈ[ decr_mode m ]
                (open_exp_wrt_exp e (exp_var_f y)) ⦂ Bt }}ad).
    { intros y. apply ad_sd_typing_rename_tm with (x := x);
        [ apply ad_sd_typing_suffix_moving
            with (Ξ := Ξ) (Θ2 := (x ~ abind_var_typ A)); exact Hdb
        | exact I
        | clear - Hx; simpl_env; fsetdec ]. }
    assert (Href2 : {{ (Ξ ++ Θ2) ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0)
                      ⊳ (bskl_arrow (pskl_to_bskl_inh (ptyp_to_pskl A))
                                    (btyp_to_bskl Bt)) }}ad).
    { destruct Hshape as [[HP0 [HP HQ]] | HP0]; subst; simpl.
      -
        destruct (ad_refine_syn_syn_l Hrefb pskl_ghost eq_refl) as [P' HQt].
        inversion H1; subst.
        rewrite HQt.
        change (bskl_arrow (pskl_to_bskl_inh (ptyp_to_pskl (ptyp_var_f α)))
                           (pskl_to_bskl_syn P'))
          with (pskl_to_bskl_syn (pskl_arrow (pskl_var_f α) P')).
        apply ad_refine_syn_ghost_empty.
      - apply ad_refine_syn_arrow_intro;
          [ eapply a_guess_mono_refine;
              [ exact H1
              | intros α1 Hα1; right;
                pose proof (a_wf_pskl_ftv_binds
                            ltac:(eapply a_wf_pskl_isub;
                                  [ exact HwfPP | exact Hisub ]) Hα1) as Ht; exact Ht
              | intros α1 Hb; eapply a_isub_binds_flex;
                  [ exact Hisubαs
                  | unfold binds; apply in_or_app; left; exact Hb ]
              | intros α1 _; clear; fsetdec ]
          | eapply ad_refine_syn_strip_tm_typ; exact Hrefb ]. }
    split; [ exact Hisub | ]. split; [ exact Hwf2 | ].
    split; [ apply a_wf_ptyp__arrow; assumption | ].
    exists (btyp_arrow (ptyp_to_btyp_inh A) Bt).
    split.
    { simpl. rewrite btyp_to_ptyp_ptyp_to_btyp_inh, HeBt. reflexivity. }
    split.
    + apply ad_sd_typing__abs with (L := singleton x);
        [ exact H | exact HwfA2 | exact Hmc | intros y Hy; apply Hbody ].
    + simpl. rewrite btyp_to_bskl_ptyp_to_btyp_inh. exact Href2.
  -
    destruct (a_split_ty_shape H0 Hmod H) as [HeqΘ Hshape]; subst Θ1.
    pose proof (a_wf_exp_abs_anno_inv Hexp) as HwfA.
    destruct (a_split_ty_pieces H0 Hmod H HwfP0) as [HwfPP [HwfQ Hmod']].
    destruct (a_consis_chk_sound H1 Hwf HwfPP
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA))
      as [Hlec [Hwfc _]].
    assert (HwfAc : a_wf_ptyp Θ2 A) by (eapply a_wf_ptyp_isub; eassumption).
    assert (Hx : x `notin` dom Θ2 `union` dom Ξ `union` dom Θ3
                   `union` fvar_in_exp e)
      by (clear - H3; rewrite !dom_app in H3; fsetdec).
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ2) }}a)
      by (apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfAc | exact Hwfc ]).
    destruct (IHa_typing Hwfx
                (a_wf_pskl_weaken_cons x (abind_var_typ A)
                   ltac:(eapply a_wf_pskl_isub; [ exact HwfQ | exact Hlec ]))
                Hmod'
                (a_wf_exp_weaken_cons x (abind_var_typ A)
                   (a_wf_exp_isub (a_wf_exp_abs_anno_pick x Hexp) Hlec)))
      as [Hle [Hwfout [HwfBout [Bt [HeBt [Hdb Hrefb]]]]]].
    assert (Huniq3 : uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ3))
      by (apply a_wf_aenv_uniq; exact Hwfout).
    assert (Hlc3 : lc_aenv Θ3).
    { apply a_wf_aenv_lc_aenv in Hwfout.
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout].
      apply lc_aenv_app_inv in Hwfout as [_ Hwfout]. exact Hwfout. }
    assert (Hisub : Θ2 ⊴ (Ξ ++ Θ3))
      by (eapply a_isub_peel_tm_mid; [ | eassumption .. ]; exact I).
    assert (Hisub0 : Θ0 ⊴ (Ξ ++ Θ3)) by (eapply a_isub_trans; eassumption).
    assert (Hwf3 : {{ ⊢ (Ξ ++ Θ3) }}a)
      by (eapply a_wf_aenv_strip_tm_mid; [ | exact Hwfout ]; intros []).
    assert (HwfA3 : a_wf_ptyp (Ξ ++ Θ3) A)
      by (eapply a_wf_ptyp_isub; [ exact HwfA | exact Hisub0 ]).
    assert (HwfB3 : a_wf_ptyp (Ξ ++ Θ3) B).
    { eapply a_wf_ptyp_mono;
        [ exact HwfBout | apply aenv_tbinds_le_strip_tm; intros [] ]. }
    assert (Hbody : forall y,
              {{ ((y ~ abind_var_typ A) ++ (Ξ ++ Θ3)) ⊢ˢᵈ[ decr_mode m ]
                (open_exp_wrt_exp e (exp_var_f y)) ⦂ Bt }}ad).
    { intros y. apply ad_sd_typing_rename_tm with (x := x);
        [ apply ad_sd_typing_suffix_moving
            with (Ξ := Ξ) (Θ2 := (x ~ abind_var_typ A)); exact Hdb
        | exact I
        | clear - Hx; simpl_env; fsetdec ]. }
    pose proof (ad_sd_typing_mod_comp_ty Hdb Hwfout) as Hmq.
    split; [ exact Hisub0 | ]. split; [ exact Hwf3 | ].
    split; [ apply a_wf_ptyp__arrow; assumption | ].
    destruct Hshape as [[HP0 [HP HQ]] | HP0].
    +
      subst P0 P Q.
      pose proof (a_ty_mode_compat_ghost_inv Hmod) as Hm; subst m.
      destruct (ad_refine_syn_syn_l Hrefb pskl_ghost eq_refl) as [P' HQt].
      exists (btyp_arrow (ptyp_to_btyp_syn A) Bt).
      split.
      { simpl. rewrite btyp_to_ptyp_ptyp_to_btyp_syn, HeBt. reflexivity. }
      split.
      * eapply ad_sd_typing__abs_anno with (L := singleton x) (A' := A);
          [ exact H | exact HwfA3
          | apply a_tyequiv__refl; eapply a_wf_ptyp_lc; exact HwfA3
          | apply btyp_to_ptyp_ptyp_to_btyp_syn
          | | intros y Hy; apply Hbody ].
        apply mod_comp_ty__ti. apply is_styp__arrow;
          [ apply is_styp_ptyp_to_btyp_syn; eapply a_wf_ptyp_lc; exact HwfA3
          | apply mod_comp_ty_ti_inv; exact Hmq ].
      * simpl. rewrite btyp_to_bskl_ptyp_to_btyp_syn, HQt.
        change (bskl_arrow (pskl_to_bskl_syn (ptyp_to_pskl A))
                           (pskl_to_bskl_syn P'))
          with (pskl_to_bskl_syn (pskl_arrow (ptyp_to_pskl A) P')).
        apply ad_refine_syn_ghost_empty.
    +
      subst P0.
      destruct (a_consis_chk_annot_refine H1 Hwf HwfA HwfPP)
        as [B1 [HeB1 HrefA]].
      destruct (a_ty_mode_compat_arrow_inv Hmod H) as [m' [Hm Hm']]; subst m.
      exists (btyp_arrow B1 Bt).
      split.
      { simpl. rewrite HeB1, HeBt. reflexivity. }
      split.
      * eapply ad_sd_typing__abs_anno with (L := singleton x) (A' := A);
          [ exact H | exact HwfA3
          | apply a_tyequiv__refl; eapply a_wf_ptyp_lc; exact HwfA3
          | exact HeB1
          | apply mod_comp_ty__fn; exact Hmq
          | intros y Hy; apply Hbody ].
      * simpl. apply ad_refine_syn_arrow_intro;
          [ eapply ad_refine_syn_isub; [ exact HrefA | exact Hisub ]
          | eapply ad_refine_syn_strip_tm_typ; exact Hrefb ].
  -
    eapply a_typing_sound_check_step_of_rule; try eassumption.
    intros; eapply ad_sd_typing__abs_check_step; eassumption.
  -
    destruct (a_split_wf H Hwf HwfP0) as [Hles [Hwfs [HwfPA HwfPB]]].
    assert (HwfAs : a_wf_ptyp Θ1 A)
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfPA).
    assert (HwfBs : a_wf_ptyp Θ1 B)
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfPB).
    assert (Hexpx : {{ Θ1 ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a)
      by (apply (a_wf_exp_isub (a_wf_exp_abs_pick x Hexp) Hles)).
    destruct (a_typing_sound_check_base_body Hwfs HwfAs HwfBs Hexpx
                H0 H1 H2 H3 IHa_typing)
      as [Hisub1 [Hwf2 [HwfB2 [Hbody Hrefb2]]]].
    assert (Hisub : Θ0 ⊴ Θ2) by (eapply a_isub_trans; eassumption).
    split; [ exact Hisub | ]. split; [ exact Hwf2 | ].
    split;
      [ apply a_wf_ptyp__arrow;
          [ eapply a_wf_ptyp_isub; [ exact HwfAs | exact Hisub1 ]
          | exact HwfB2 ] | ].
    exists (btyp_arrow (ptyp_to_btyp_inh A) (ptyp_to_btyp_inh B1)).
    split.
    { simpl. rewrite !btyp_to_ptyp_ptyp_to_btyp_inh. reflexivity. }
    split.
    + apply ad_sd_typing__abs_check_base with (L := singleton x);
        [ eapply a_wf_ptyp_isub; [ exact HwfAs | exact Hisub1 ]
        | apply is_ityp_ptyp_to_btyp_inh; eapply a_wf_ptyp_lc; exact HwfB2
        | intros y Hy; apply Hbody ].
    + simpl. rewrite !btyp_to_bskl_ptyp_to_btyp_inh.
      eapply a_split_refines_gen with (Θ1 := Θ1);
        [ exact H | exact Hwf | exact HwfP0 | exact Hisub1 | exact Hwf2 | ].
      rewrite <- (btyp_to_bskl_ptyp_to_btyp_inh B1).
      exact Hrefb2.
  -
    eapply a_typing_sound_check_step_of_rule; try eassumption.
    intros; eapply ad_sd_typing__abs_anno_check_step; eassumption.
  -
    pose proof (a_wf_exp_abs_anno_inv Hexp) as HwfAan.
    destruct (a_split_wf H Hwf HwfP0) as [Hles [Hwfs [HwfPA HwfPB]]].
    assert (HwfAs : a_wf_ptyp Θ1 A')
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfPA).
    assert (HwfBs : a_wf_ptyp Θ1 B)
      by (apply a_wf_ptyp_of_wf_pskl_empty; exact HwfPB).
    assert (HwfAan1 : a_wf_ptyp Θ1 A)
      by (eapply a_wf_ptyp_isub; [ exact HwfAan | exact Hles ]).
    destruct (a_consis_chk_sound H0 Hwfs
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAan1)
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAs))
      as [Hlec [Hwfc _]].
    assert (Hequiv : {{ Θ2 ⊢ A' ≡ᵗ A }}a)
      by (eapply a_consis_chk_tyequiv;
          [ exact H0 | exact Hwfs | exact HwfAan1 | exact HwfAs ]).
    assert (Hle02 : Θ0 ⊴ Θ2)
      by (eapply a_isub_trans; [ exact Hles | exact Hlec ]).
    assert (HwfAan2 : a_wf_ptyp Θ2 A)
      by (eapply a_wf_ptyp_isub; [ exact HwfAan1 | exact Hlec ]).
    assert (Hexpx : {{ Θ2 ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a)
      by (apply (a_wf_exp_isub (a_wf_exp_abs_anno_pick x Hexp) Hle02)).
    destruct (a_typing_sound_check_base_body Hwfc HwfAan2
                (a_wf_ptyp_isub HwfBs Hlec) Hexpx H1 H2 H3 H4 IHa_typing)
      as [Hisub2 [Hwf3 [HwfB3 [Hbody Hrefb2]]]].
    assert (Hisub : Θ0 ⊴ Θ3)
      by (eapply a_isub_trans; [ exact Hle02 | exact Hisub2 ]).
    assert (Hle13 : Θ1 ⊴ Θ3)
      by (eapply a_isub_trans; [ exact Hlec | exact Hisub2 ]).
    assert (HwfA3 : a_wf_ptyp Θ3 A')
      by (eapply a_wf_ptyp_isub; [ exact HwfAs | exact Hle13 ]).
    split; [ exact Hisub | ]. split; [ exact Hwf3 | ].
    split; [ apply a_wf_ptyp__arrow; [ exact HwfA3 | exact HwfB3 ] | ].
    exists (btyp_arrow (ptyp_to_btyp_inh A') (ptyp_to_btyp_inh B1)).
    split.
    { simpl. rewrite !btyp_to_ptyp_ptyp_to_btyp_inh. reflexivity. }
    split.
    + apply ad_sd_typing__abs_anno_check_base with (L := singleton x);
        [ eapply a_wf_ptyp_isub; [ exact HwfAan2 | exact Hisub2 ]
        | apply a_tyequiv__sym;
          eapply a_tyequiv_isub_le; [ exact Hisub2 | exact Hequiv ]
        | apply is_ityp_ptyp_to_btyp_inh; eapply a_wf_ptyp_lc; exact HwfB3
        | intros y Hy; apply Hbody ].
    + simpl. rewrite !btyp_to_bskl_ptyp_to_btyp_inh.
      eapply a_split_refines_gen with (Θ1 := Θ1);
        [ exact H | exact Hwf | exact HwfP0 | exact Hle13 | exact Hwf3 | ].
      rewrite <- (btyp_to_bskl_ptyp_to_btyp_inh B1).
      exact Hrefb2.
  -
    destruct (a_wf_exp_app_inv Hexp) as [Hexp1 Hexp2].
    destruct (a_pat_sound H Hwf ltac:(apply a_wf_pskl__ghost)
                a_sk_mode_compat__tc Hexp2)
      as [Hle1 [Hwf1 [Qt1 [HeQt1 [Hpat1 Href1]]]]].
    destruct (ad_refine_syn_syn_l Href1 pskl_ghost eq_refl) as [P' HQt1].
    subst Qt1. rewrite bskl_to_pskl_pskl_to_bskl_syn in HeQt1. subst P.
    assert (HwfPin : {{ Θ1 ⨟ empty ⊢ₚₛ P' }}a)
      by (pose proof (ad_pat_target_wf Hpat1 Hwf1) as Hw;
          rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw; exact Hw).
    destruct (IHa_typing1 Hwf1
                ltac:(apply a_wf_pskl__arrow;
                      [ exact HwfPin
                      | eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hle1 ] ])
                ltac:(apply a_ty_mode_compat__fn; exact Hmod)
                (a_wf_exp_isub Hexp1 Hle1))
      as [Hle2 [Hwf2 [HwfAB [Bf [HeBf [Hdf Hreff]]]]]].
    destruct (btyp_to_ptyp_arrow_inv _ HeBf) as [B1 [B2 [HeqBf [HeB1 HeB2]]]].
    subst Bf. simpl in Hreff.
    destruct (ad_refine_syn_arrow_inv Hreff) as [HrefA HrefB].
    destruct (a_wf_ptyp_arrow_inv HwfAB) as [HwfAdom HwfBcod].
    destruct (IHa_typing2 Hwf2
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAdom)
                (a_ty_mode_compat__tc A)
                ltac:(eapply a_wf_exp_isub;
                      [ eapply a_wf_exp_isub; [ exact Hexp2 | exact Hle1 ]
                      | exact Hle2 ]))
      as [Hle3 [Hwf3 [HwfA' [Ba [HeBa [Hda Hrefa]]]]]].
    assert (HBa : Ba = ptyp_to_btyp_inh A').
    { apply btyp_check_colouring; [ | exact HeBa ].
      apply mod_comp_ty_tc_inv. eapply ad_sd_typing_mod_comp_ty; eassumption. }
    subst Ba.
    assert (Hequiv : {{ Θ3 ⊢ (btyp_to_ptyp B1) ≡ᵗ A' }}a).
    { rewrite HeB1.
      replace A' with (btyp_to_ptyp (ptyp_to_btyp_inh A'))
        by apply btyp_to_ptyp_ptyp_to_btyp_inh.
      eapply ad_refine_syn_inh_tyequiv;
        [ exact Hrefa | exact Hwf3 | reflexivity | reflexivity ]. }
    split; [ eapply a_isub_trans;
             [ exact Hle1 | eapply a_isub_trans; eassumption ] | ].
    split; [ exact Hwf3 | ].
    split; [ rewrite <- HeB2; eapply a_wf_ptyp_isub;
             [ rewrite HeB2; exact HwfBcod | exact Hle3 ] | ].
    exists B2. split; [ exact HeB2 | ]. split.
    + eapply ad_sd_typing__app with (P := P') (A2 := A') (B1 := B1);
        [ eapply ad_pat_isub_tm;
            [ exact Hpat1
            | eapply a_isub_trans; eassumption
            | eapply aenv_tm_le_trans;
                [ eapply a_typing_tm_le; exact H0
                | eapply a_typing_tm_le; exact H1 ] ]
        | eapply ad_refine_syn_isub; [ exact HrefA | exact Hle3 ]
        | eapply ad_sd_typing_isub_tm;
            [ exact Hdf | exact Hle3 | eapply a_typing_tm_le; exact H1 ]
        | exact Hequiv
        | exact Hda ].
    + eapply ad_refine_syn_isub; [ exact HrefB | exact Hle3 ].
Qed.

Lemma a_typing_dom_mono : forall m Θ0 P0 e B Θ1,
  {{ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}a -> dom Θ0 [<=] dom Θ1.
Proof.
  intros m Θ0 P0 e B Θ1 H; induction H as
    [ m0 Θa P0a A Θb Hsub
    | m0 Θa P0a x A B0 Θb Hb Hsub
    | m0 Θa P0a ea A B0 Θb Θc Ht IHt Hsub
    | Θa ea A B0 Θb Θc Ht IHt Hchk
    | x m0 Θa Θb Θc P0a Pa Q0 αs A ea B0 Ξ Hne Hsp Hgm Huq Hsuf Hxf Ht IHt
    | x m0 Θa Θb Θc Θd P0a Pa Q0 A ea B0 Ξ Hne Hsp Hchk Hsuf Hxf Ht IHt
    | α Θa Θb A0 ea A Ξ Hsuf Huq Hgam Hαf Ht IHt
    | x Θa Θb Θc A0 A B0 B1 ea Ξ Hsp Hsuf Huq Hgam Hxf Ht IHt
    | α Θa Θb A0 Aan ea A Ξ Hsuf Huq Hgam Hαf Ht IHt
    | x Θa Θb Θc Θd A0 A' A B0 B1 ea Ξ Hsp Hchk Hsuf Huq Hgam Hxf Ht IHt
    | m0 Θa Θb Θc Θd Pa Q0 A A' B0 e1 e2 Hp2 Ht1 IHt1 Ht2 IHt2 ];
    try (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Hsub)).
  -
    pose proof ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Hsub) as Hd.
    clear - IHt Hd. fsetdec.
  -
    pose proof (a_consis_chk_dom_mono Hchk) as Hd.
    clear - IHt Hd. fsetdec.
  -
    pose proof (a_split_dom_mono Hsp) as Hd1.
    simpl_env in Hxf. simpl_env in IHt. simpl_env.
    intros a Ha.
    assert (Ha1 : a `in` dom Θb) by (clear - Ha Hd1; fsetdec).
    assert (Hax : a <> x) by (intros ->; clear - Ha1 Hxf; fsetdec).
    assert (Ha2 : a `in` union (singleton x) (union (dom αs) (dom Θb)))
      by (clear - Ha1; fsetdec).
    apply IHt in Ha2. clear - Ha2 Hax. fsetdec.
  -
    pose proof (a_split_dom_mono Hsp) as Hd1.
    pose proof (a_consis_chk_dom_mono Hchk) as Hd2.
    simpl_env in Hxf. simpl_env in IHt. simpl_env.
    intros a Ha.
    assert (Ha1 : a `in` dom Θc) by (clear - Ha Hd1 Hd2; fsetdec).
    assert (Hax : a <> x) by (intros ->; clear - Ha1 Hxf; fsetdec).
    assert (Ha2 : a `in` union (singleton x) (dom Θc))
      by (clear - Ha1; fsetdec).
    apply IHt in Ha2. clear - Ha2 Hax. fsetdec.
  -
    simpl_env in Hαf. simpl_env in IHt. simpl_env.
    assert (Hdisj : disjoint Ξ Θa) by (clear - Huq; solve_uniq).
    unfold disjoint in Hdisj.
    intros a Ha.
    assert (Hax : a <> α) by (intros ->; clear - Ha Hαf; fsetdec).
    assert (Ha2 : a `in` union (singleton α) (dom Θa))
      by (clear - Ha; fsetdec).
    apply IHt in Ha2. clear - Ha2 Hax Ha Hdisj. fsetdec.
  -
    pose proof (a_split_dom_mono Hsp) as Hd1.
    simpl_env in Hxf. simpl_env in IHt. simpl_env.
    assert (Hdisj : disjoint Ξ Θb) by (clear - Huq; solve_uniq).
    unfold disjoint in Hdisj.
    intros a Ha.
    assert (Ha1 : a `in` dom Θb) by (clear - Ha Hd1; fsetdec).
    assert (Hax : a <> x) by (intros ->; clear - Ha1 Hxf; fsetdec).
    assert (Ha2 : a `in` union (singleton x) (dom Θb))
      by (clear - Ha1; fsetdec).
    apply IHt in Ha2. clear - Ha2 Hax Ha1 Hdisj. fsetdec.
  -
    simpl_env in Hαf. simpl_env in IHt. simpl_env.
    assert (Hdisj : disjoint Ξ Θa) by (clear - Huq; solve_uniq).
    unfold disjoint in Hdisj.
    intros a Ha.
    assert (Hax : a <> α) by (intros ->; clear - Ha Hαf; fsetdec).
    assert (Ha2 : a `in` union (singleton α) (dom Θa))
      by (clear - Ha; fsetdec).
    apply IHt in Ha2. clear - Ha2 Hax Ha Hdisj. fsetdec.
  -
    pose proof (a_split_dom_mono Hsp) as Hd1.
    pose proof (a_consis_chk_dom_mono Hchk) as Hd2.
    simpl_env in Hxf. simpl_env in IHt. simpl_env.
    assert (Hdisj : disjoint Ξ Θc) by (clear - Huq; solve_uniq).
    unfold disjoint in Hdisj.
    intros a Ha.
    assert (Ha1 : a `in` dom Θc) by (clear - Ha Hd1 Hd2; fsetdec).
    assert (Hax : a <> x) by (intros ->; clear - Ha1 Hxf; fsetdec).
    assert (Ha2 : a `in` union (singleton x) (dom Θc))
      by (clear - Ha1; fsetdec).
    apply IHt in Ha2. clear - Ha2 Hax Ha1 Hdisj. fsetdec.
  -
    pose proof (a_pat_dom_mono Hp2) as Hd1.
    clear - Hd1 IHt1 IHt2. fsetdec.
Qed.

Lemma a_typing_fvar_binds : forall m Θ0 P0 e B Θ1,
  {{ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}a ->
  forall x, x `in` fvar_in_exp e ->
  exists bd, binds x bd Θ0 /\ abind_is_tm bd.
Proof.
  intros m Θ0 P0 e B Θ1 H; induction H as
    [ m0 Θa P0a A Θb Hsub
    | m0 Θa P0a x0 A B0 Θb Hb Hsub
    | m0 Θa P0a ea A B0 Θb Θc Ht IHt Hsub
    | Θa ea A B0 Θb Θc Ht IHt Hchk
    | x0 m0 Θa Θb Θc P0a Pa Q0 αs A ea B0 Ξ Hne Hsp Hgm Huq Hsuf Hxf Ht IHt
    | x0 m0 Θa Θb Θc Θd P0a Pa Q0 A ea B0 Ξ Hne Hsp Hchk Hsuf Hxf Ht IHt
    | α Θa Θb A0 ea A Ξ Hsuf Huq Hgam Hαf Ht IHt
    | x0 Θa Θb Θc A0 A B0 B1 ea Ξ Hsp Hsuf Huq Hgam Hxf Ht IHt
    | α Θa Θb A0 Aan ea A Ξ Hsuf Huq Hgam Hαf Ht IHt
    | x0 Θa Θb Θc Θd A0 A' A B0 B1 ea Ξ Hsp Hchk Hsuf Huq Hgam Hxf Ht IHt
    | m0 Θa Θb Θc Θd Pa Q0 A A' B0 e1 e2 Hp2 Ht1 IHt1 Ht2 IHt2 ];
    intros x Hx; simpl in Hx;
    try (exfalso; clear - Hx; fsetdec).
  -
    assert (E : x = x0) by (clear - Hx; fsetdec). subst x0.
    exists (abind_var_typ A). split; [ exact Hb | exact I ].
  -  apply IHt. exact Hx.
  -  apply IHt. exact Hx.
  -
    simpl_env in Hxf.
    assert (Hne0 : x <> x0) by (intros ->; clear - Hx Hxf; fsetdec).
    assert (Hx' : x `in` fvar_in_exp (open_exp_wrt_exp ea (exp_var_f x0))).
    { pose proof (fvar_in_exp_open_exp_wrt_exp_lower ea (exp_var_f x0)) as Hl.
      clear - Hx Hl. fsetdec. }
    destruct (IHt x Hx') as (bd & Hb & Htm).
    apply binds_cons_1 in Hb. destruct Hb as [[E _] | Hb];
      [ exfalso; apply Hne0; exact E | ].
    apply binds_app_1 in Hb. destruct Hb as [Hb | Hb].
    { exfalso.
      assert (Hdecls : a_decls αs) by (eapply a_guess_mono_decls; exact Hgm).
      pose proof (@a_decls_binds_flex αs x bd Hdecls Hb) as E.
      subst bd. simpl in Htm. exact Htm. }
    exists bd. split; [ | exact Htm ].
    apply (a_split_tm_ge Hsp); [ exact Htm | exact Hb ].
  -
    simpl_env in Hxf.
    assert (Hne0 : x <> x0) by (intros ->; clear - Hx Hxf; fsetdec).
    assert (Hx' : x `in` fvar_in_exp (open_exp_wrt_exp ea (exp_var_f x0))).
    { pose proof (fvar_in_exp_open_exp_wrt_exp_lower ea (exp_var_f x0)) as Hl.
      clear - Hx Hl. fsetdec. }
    destruct (IHt x Hx') as (bd & Hb & Htm).
    apply binds_cons_1 in Hb. destruct Hb as [[E _] | Hb];
      [ exfalso; apply Hne0; exact E | ].
    exists bd. split; [ | exact Htm ].
    apply (a_split_tm_ge Hsp); [ exact Htm | ].
    apply (a_consis_chk_tm_ge Hchk); [ exact Htm | exact Hb ].
  -
    destruct (IHt x Hx) as (bd & Hb & Htm).
    apply binds_cons_1 in Hb. destruct Hb as [[E Ebd] | Hb];
      [ exfalso; subst bd; simpl in Htm; exact Htm | ].
    exists bd. split; [ exact Hb | exact Htm ].
  -
    simpl_env in Hxf.
    assert (Hne0 : x <> x0) by (intros ->; clear - Hx Hxf; fsetdec).
    assert (Hx' : x `in` fvar_in_exp (open_exp_wrt_exp ea (exp_var_f x0))).
    { pose proof (fvar_in_exp_open_exp_wrt_exp_lower ea (exp_var_f x0)) as Hl.
      clear - Hx Hl. fsetdec. }
    destruct (IHt x Hx') as (bd & Hb & Htm).
    apply binds_cons_1 in Hb. destruct Hb as [[E _] | Hb];
      [ exfalso; apply Hne0; exact E | ].
    exists bd. split; [ | exact Htm ].
    apply (a_split_tm_ge Hsp); [ exact Htm | exact Hb ].
  -
    destruct (IHt x Hx) as (bd & Hb & Htm).
    apply binds_cons_1 in Hb. destruct Hb as [[E Ebd] | Hb];
      [ exfalso; subst bd; simpl in Htm; exact Htm | ].
    exists bd. split; [ exact Hb | exact Htm ].
  -
    simpl_env in Hxf.
    assert (Hne0 : x <> x0) by (intros ->; clear - Hx Hxf; fsetdec).
    assert (Hx' : x `in` fvar_in_exp (open_exp_wrt_exp ea (exp_var_f x0))).
    { pose proof (fvar_in_exp_open_exp_wrt_exp_lower ea (exp_var_f x0)) as Hl.
      clear - Hx Hl. fsetdec. }
    destruct (IHt x Hx') as (bd & Hb & Htm).
    apply binds_cons_1 in Hb. destruct Hb as [[E _] | Hb];
      [ exfalso; apply Hne0; exact E | ].
    exists bd. split; [ | exact Htm ].
    apply (a_split_tm_ge Hsp); [ exact Htm | ].
    apply (a_consis_chk_tm_ge Hchk); [ exact Htm | exact Hb ].
  -
    destruct (AtomSetProperties.In_dec x (fvar_in_exp e2)) as [Hx2 | Hx2].
    + destruct (IHt2 x Hx2) as (bd & Hb & Htm).
      exists bd. split; [ | exact Htm ].
      apply (a_pat_tm_ge Hp2); [ exact Htm | ].
      apply (a_typing_tm_ge Ht1); [ exact Htm | exact Hb ].
    + assert (Hx1 : x `in` fvar_in_exp e1) by (clear - Hx Hx2; fsetdec).
      destruct (IHt1 x Hx1) as (bd & Hb & Htm).
      exists bd. split; [ | exact Htm ].
      apply (a_pat_tm_ge Hp2); [ exact Htm | exact Hb ].
Qed.
