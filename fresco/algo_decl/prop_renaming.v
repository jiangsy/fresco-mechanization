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
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.def_typing.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_precise.
Require Import src.fresco.algo.basic.prop_suffix_erase.

Set Implicit Arguments.

Lemma tbinds_le_subst_mid : forall β' α Θ1 Θ0,
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  aenv_tbinds_le (Θ1 ++ (β' ~ abind_tvar) ++ Θ0)
    ((subst_aenv (ptyp_var_f β') α Θ1) ++ (β' ~ abind_tvar) ++ Θ0).
Proof.
  intros β' α Θ1 Θ0 Hdefs x b Hty Hb.
  apply binds_app_1 in Hb as [Hb | Hb]; [ | apply binds_app_3; exact Hb ].
  apply binds_app_2.
  pose proof (@binds_subst_aenv (ptyp_var_f β') α x b Θ1 Hb) as Hb'.
  destruct b as [ | A | P | | τ ]; simpl in Hty; try contradiction;
    simpl in Hb'.
  - exact Hb'.
  - exact Hb'.
  - rewrite subst_ptyp_in_ptyp_fresh_eq in Hb';
      [ exact Hb' | eapply Hdefs; apply binds_app_2; exact Hb ].
Qed.

Lemma subst_var_ptyp_to_pskl : forall A α β',
  subst_pskl_in_pskl (pskl_var_f β') α (ptyp_to_pskl A)
  = ptyp_to_pskl (subst_ptyp_in_ptyp (ptyp_var_f β') α A).
Proof. intros. rewrite ptyp_to_pskl_subst. reflexivity. Qed.

Lemma subst_var_pskl_to_uskl_syn : forall P α β',
  subst_uskl_in_uskl (uskl_var_f β') α (bskl_to_uskl (pskl_to_bskl_syn P))
  = bskl_to_uskl (pskl_to_bskl_syn (subst_pskl_in_pskl (pskl_var_f β') α P)).
Proof.
  intros. rewrite <- subst_var_bskl_syn, bskl_to_uskl_subst. reflexivity.
Qed.

Lemma subst_var_btyp_to_bskl : forall B α β',
  subst_bskl_in_bskl (bskl_var_f β') α (btyp_to_bskl B)
  = btyp_to_bskl (subst_btyp_in_btyp (btyp_var_f β') α B).
Proof. intros. rewrite btyp_to_bskl_subst. reflexivity. Qed.

Lemma subst_var_btyp_to_ptyp : forall B α β',
  subst_ptyp_in_ptyp (ptyp_var_f β') α (btyp_to_ptyp B)
  = btyp_to_ptyp (subst_btyp_in_btyp (btyp_var_f β') α B).
Proof. intros. rewrite btyp_to_ptyp_subst. reflexivity. Qed.

Lemma subst_var_ptyp_to_btyp_syn : forall A α β',
  subst_btyp_in_btyp (btyp_var_f β') α (ptyp_to_btyp_syn A)
  = ptyp_to_btyp_syn (subst_ptyp_in_ptyp (ptyp_var_f β') α A).
Proof. intros. rewrite ptyp_to_btyp_syn_subst. reflexivity. Qed.

Lemma subst_var_ptyp_to_btyp_inh : forall A α β',
  subst_btyp_in_btyp (btyp_var_f β') α (ptyp_to_btyp_inh A)
  = ptyp_to_btyp_inh (subst_ptyp_in_ptyp (ptyp_var_f β') α A).
Proof. intros. rewrite ptyp_to_btyp_inh_subst. reflexivity. Qed.

Lemma subst_var_ptyp_to_uskl_syn : forall A α β',
  subst_uskl_in_uskl (uskl_var_f β') α (ptyp_to_uskl_syn A)
  = ptyp_to_uskl_syn (subst_ptyp_in_ptyp (ptyp_var_f β') α A).
Proof. intros. rewrite ptyp_to_uskl_syn_subst. reflexivity. Qed.

Lemma a_wf_ptyp_rename_tvar : forall Θfull A,
  a_wf_ptyp Θfull A ->
  forall Θ1 α Θ0 β',
  Θfull = Θ1 ++ (α ~ abind_tvar) ++ Θ0 ->
  a_wf_ptyp (Θ1 ++ (β' ~ abind_tvar) ++ Θ0)
    (subst_ptyp_in_ptyp (ptyp_var_f β') α A).
Proof.
  intros Θfull A H.
  induction H; intros Θ1 α0 Θ0 β' ->; simpl.
  - apply a_wf_ptyp__unit.
  - destruct_if as [-> | Hne].
    + apply a_wf_ptyp__var. unfold a_binds_tvar. left.
      apply binds_app_3. unfold binds; simpl; left; reflexivity.
    + apply a_wf_ptyp__var.
      apply (@a_binds_tvar_insert_mid α Θ1 (β' ~ abind_tvar) Θ0).
      eapply a_binds_tvar_strip_mid; eauto;
        try (intro Hc; inversion Hc; subst; congruence);
        try (intros τ0 Hc; inversion Hc).
  - apply a_wf_ptyp__arrow;
      [ apply IHa_wf_ptyp1 | apply IHa_wf_ptyp2 ]; reflexivity.
  - apply a_wf_ptyp__all with (L := L `union` singleton α0).
    intros α1 Hα1.
    assert (Hne : α0 <> α1) by (clear - Hα1; fsetdec).
    rewrite subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_var;
      auto using lc_ptyp_var_f.
    apply (H0 α1 ltac:(clear - Hα1; solve_notin_auto) ((α1 ~ abind_tvar) ++ Θ1));
      simpl_env; reflexivity.
Qed.

Lemma a_tyequiv_rename_tvar : forall Θfull A B,
  {{ Θfull ⊢ A ≡ᵗ B }}a ->
  forall Θ1 α Θ0 β',
  Θfull = Θ1 ++ (α ~ abind_tvar) ++ Θ0 ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  {{ (Θ1 ++ (β' ~ abind_tvar) ++ Θ0) ⊢
    (subst_ptyp_in_ptyp (ptyp_var_f β') α A) ≡ᵗ
    (subst_ptyp_in_ptyp (ptyp_var_f β') α B) }}a.
Proof.
  intros Θfull A B H.
  induction H; intros Θ1 α0 Θ0 β' ->; intros Hdom Hdefs; simpl.
  -
    apply a_tyequiv__refl.
    apply subst_ptyp_in_ptyp_lc_ptyp; auto using lc_ptyp_var_f.
  -
    apply a_tyequiv__sym. apply IHa_tyequiv; auto.
  -
    eapply a_tyequiv__trans;
      [ apply IHa_tyequiv1 | apply IHa_tyequiv2 ]; auto.
  -
    assert (Hb' : binds α (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α <> α0).
    { intro; subst. apply binds_In in Hb'. clear - Hdom Hb'. fsetdec. }
    assert (Hfr : α0 `notin` ftvar_in_ptyp τ) by eauto.
    destruct_var_eqs.
    rewrite subst_ptyp_in_ptyp_fresh_eq; [ | exact Hfr ].
    apply a_tyequiv__flex_def.
    apply (@binds_weaken abind α (abind_flex_mono_def τ)
             Θ1 (β' ~ abind_tvar) Θ0); auto.
  -
    apply a_tyequiv__arrow;
      [ apply IHa_tyequiv1 | apply IHa_tyequiv2 ]; auto.
  -
    apply a_tyequiv__all with (L := L `union` singleton α0).
    intros α1 Hα1.
    assert (Hne : α0 <> α1) by (clear - Hα1; fsetdec).
    rewrite !subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_var;
      auto using lc_ptyp_var_f.
    apply (H0 α1 ltac:(clear - Hα1; solve_notin_auto) Θ1); auto.
Qed.

Lemma a_wf_pskl_rename_paint : forall Θ1 α Θ0 P β',
  {{ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ P }}a ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  {{ ((subst_aenv (ptyp_var_f β') α Θ1) ++ (β' ~ abind_tvar) ++ Θ0) ⨟ empty
    ⊢ₚₛ (subst_pskl_in_pskl (pskl_var_f β') α P) }}a.
Proof.
  intros * H Hdefs.
  eapply a_wf_pskl_mono;
    [ apply a_wf_pskl_rename_tvar; [ exact H | clear; fsetdec | clear; fsetdec ]
    | apply tbinds_le_subst_mid; exact Hdefs ].
Qed.

Lemma a_wf_ptyp_rename_paint : forall Θ1 α Θ0 A β',
  a_wf_ptyp (Θ1 ++ (α ~ abind_tvar) ++ Θ0) A ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  a_wf_ptyp ((subst_aenv (ptyp_var_f β') α Θ1) ++ (β' ~ abind_tvar) ++ Θ0)
    (subst_ptyp_in_ptyp (ptyp_var_f β') α A).
Proof.
  intros * H Hdefs.
  eapply a_wf_ptyp_mono;
    [ exact (@a_wf_ptyp_rename_tvar _ _ H Θ1 α Θ0 β' eq_refl)
    | apply tbinds_le_subst_mid; exact Hdefs ].
Qed.

Lemma a_tyequiv_rename_paint : forall Θ1 α Θ0 A B β',
  {{ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) ⊢ A ≡ᵗ B }}a ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  {{ ((subst_aenv (ptyp_var_f β') α Θ1) ++ (β' ~ abind_tvar) ++ Θ0) ⊢
    (subst_ptyp_in_ptyp (ptyp_var_f β') α A) ≡ᵗ
    (subst_ptyp_in_ptyp (ptyp_var_f β') α B) }}a.
Proof.
  intros * H Hdom Hdefs.
  eapply a_tyequiv_ctx_mono;
    [ exact (@a_tyequiv_rename_tvar _ _ _ H Θ1 α Θ0 β' eq_refl Hdom Hdefs)
    | apply tbinds_le_subst_mid; exact Hdefs ].
Qed.

Lemma ad_refine_syn_rename_paint : forall Θ1 α Θ0 Q P β',
  {{ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ᵣ Q ⊳ P }}ad ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  {{ ((subst_aenv (ptyp_var_f β') α Θ1) ++ (β' ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ᵣ
    (subst_bskl_in_bskl (bskl_var_f β') α Q) ⊳
    (subst_bskl_in_bskl (bskl_var_f β') α P) }}ad.
Proof.
  intros * H Hdom Hdefs.
  eapply ad_refine_syn_mono;
    [ apply ad_refine_syn_rename_ctx_gen;
        [ exact H | exact Hdom | exact Hdefs | clear; fsetdec ]
    | apply tbinds_le_subst_mid; exact Hdefs ].
Qed.

Lemma ad_pat_sub_rename_paint : forall NM M Ψ Θ1 α Θ0 R Q β',
  {{ Ψ ⨟ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) ⊢ˢ[ NM | M ] R ⩽ Q }}ad ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  {{ Ψ ⨟ ((subst_aenv (ptyp_var_f β') α Θ1) ++ (β' ~ abind_tvar) ++ Θ0)
     ⊢ˢ[ NM | M ] (subst_uskl_in_uskl (uskl_var_f β') α R)
                ⩽ (subst_bskl_in_bskl (bskl_var_f β') α Q) }}ad.
Proof.
  intros * Hn Hdom Hdefs.
  eapply ad_pat_sub_mono;
    [ apply ad_pat_sub_rename_tvar; [ exact Hn | exact Hdom | exact Hdefs ]
    | apply tbinds_le_subst_mid; exact Hdefs ].
Qed.

Lemma ad_pat_rename_tvar : forall M Θfull e Q,
  {{ Θfull ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall Θ1 α Θ0 β',
  Θfull = Θ1 ++ (α ~ abind_tvar) ++ Θ0 ->
  α `notin` dom (Θ1 ++ Θ0) ->
  β' `notin` add α (dom (Θ1 ++ Θ0)) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  (forall y A', binds y (abind_var_typ A') Θ0 -> α `notin` ftvar_in_ptyp A') ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> α `notin` ftvar_in_pskl Ps) ->
  {{ ((subst_aenv (ptyp_var_f β') α Θ1) ++ (β' ~ abind_tvar) ++ Θ0) ⊢ˢ[ M ]
    (subst_ptyp_in_exp (ptyp_var_f β') α e) ⦂
    (subst_bskl_in_bskl (bskl_var_f β') α Q) }}ad.
Proof.
  intros M Θfull e Q H Θ1 α Θ0 β' HeqΘ Hdom Hβ' Hdefs Hvt Hvs.
  revert Θ1 HeqΘ Hdom Hβ' Hdefs.
  induction H; intros Θ1 ->; intros Hdom Hβ' Hdefs; simpl.
  -
    apply ad_pat__unit.
    + rewrite <- bskl_to_pskl_subst_var.
      apply a_wf_pskl_rename_paint; [ exact H | exact Hdefs ].
    + exact (@ad_pat_sub_rename_paint _ _ _ Θ1 α Θ0 _ _ β' H0 Hdom Hdefs).
  -
    apply binds_app_1 in H as [Hb1 | Hb2];
      [ | apply binds_app_1 in Hb2 as [Hbm | Hb0] ].
    +
      apply ad_pat__var with
        (b := subst_abind (ptyp_var_f β') α b)
        (P := subst_pskl_in_pskl (pskl_var_f β') α P).
      * apply binds_app_2.
        apply (@binds_subst_aenv (ptyp_var_f β') α x b Θ1 Hb1).
      * change (pskl_var_f β') with (ptyp_to_pskl (ptyp_var_f β')).
        apply abind_to_pskl_subst; exact H0.
      * rewrite <- bskl_to_pskl_subst_var.
        apply a_wf_pskl_rename_paint; [ exact H1 | exact Hdefs ].
      * pose proof (@ad_pat_sub_rename_paint _ _ _ Θ1 α Θ0 _ _ β'
                      H2 Hdom Hdefs) as Hs.
        rewrite subst_var_pskl_to_uskl_syn in Hs. exact Hs.
    +
      exfalso. destruct Hbm as [Heq | []].
      inversion Heq; subst. simpl in H0. discriminate.
    +
      assert (Hfr : α `notin` ftvar_in_pskl P).
      { destruct b; simpl in H0; try discriminate; inversion H0; subst.
        - rewrite ftvar_ptyp_to_pskl. eauto.
        - eauto. }
      apply ad_pat__var with (b := b) (P := P).
      * apply binds_app_3. simpl. right. exact Hb0.
      * exact H0.
      * rewrite <- bskl_to_pskl_subst_var.
        apply a_wf_pskl_rename_paint; [ exact H1 | exact Hdefs ].
      * pose proof (@ad_pat_sub_rename_paint _ _ _ Θ1 α Θ0 _ _ β'
                      H2 Hdom Hdefs) as Hs.
        rewrite subst_var_pskl_to_uskl_syn in Hs.
        rewrite subst_pskl_in_pskl_fresh_eq in Hs; [ exact Hs | exact Hfr ].
  -
    apply ad_pat__anno.
    + rewrite <- bskl_to_pskl_subst_var.
      apply a_wf_pskl_rename_paint; [ exact H | exact Hdefs ].
    + pose proof (@ad_pat_sub_rename_paint _ _ _ Θ1 α Θ0 _ _ β'
                    H0 Hdom Hdefs) as Hs.
      rewrite subst_var_pskl_to_uskl_syn, subst_var_ptyp_to_pskl in Hs.
      exact Hs.
  -
    rewrite subst_var_bskl_syn.
    apply ad_pat__freeze.
    pose proof (IHad_pat Θ1 eq_refl Hdom Hβ' Hdefs) as IHx.
    rewrite subst_var_bskl_syn in IHx. exact IHx.
  -
    rewrite subst_var_bskl_inh.
    apply ad_pat__abs
      with (L := L `union` singleton α `union` singleton β'
                   `union` dom (Θ1 ++ Θ0)).
    + exact H.
    + apply a_wf_pskl_rename_paint; [ exact H0 | exact Hdefs ].
    + rewrite <- subst_var_bskl_inh.
      change (bskl_var_f β') with (ptyp_to_bskl_syn (ptyp_var_f β')).
      change (bskl_arrow
                (subst_bskl_in_bskl (ptyp_to_bskl_syn (ptyp_var_f β')) α
                   (pskl_to_bskl_inh P))
                (subst_bskl_in_bskl (ptyp_to_bskl_syn (ptyp_var_f β')) α Q))
        with (subst_bskl_in_bskl (ptyp_to_bskl_syn (ptyp_var_f β')) α
                (bskl_arrow (pskl_to_bskl_inh P) Q)).
      apply mod_comp_sk_subst_mono; [ exact H1 | apply mono_ptyp__var ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
      apply (H3 x ltac:(clear - Hx; solve_notin_auto)
               ((x ~ abind_var_skl P) ++ Θ1));
        [ simpl_env; reflexivity
        | clear - Hdom Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | clear - Hβ' Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | intros β1 τ1 Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb1];
          [ discriminate | eauto ] ].
  -
    rewrite subst_var_btyp_to_bskl.
    apply ad_pat__abs_anno
      with (L := L `union` singleton α `union` singleton β'
                   `union` dom (Θ1 ++ Θ0))
           (B := subst_btyp_in_btyp (btyp_var_f β') α B).
    + exact H.
    + apply a_wf_ptyp_rename_paint; [ exact H0 | exact Hdefs ].
    + subst A. rewrite subst_var_btyp_to_ptyp. reflexivity.
    + rewrite <- subst_var_btyp_to_bskl.
      change (bskl_var_f β') with (ptyp_to_bskl_syn (ptyp_var_f β')).
      change (bskl_arrow
                (subst_bskl_in_bskl (ptyp_to_bskl_syn (ptyp_var_f β')) α
                   (btyp_to_bskl B))
                (subst_bskl_in_bskl (ptyp_to_bskl_syn (ptyp_var_f β')) α Q))
        with (subst_bskl_in_bskl (ptyp_to_bskl_syn (ptyp_var_f β')) α
                (bskl_arrow (btyp_to_bskl B) Q)).
      apply mod_comp_sk_subst_mono; [ exact H2 | apply mono_ptyp__var ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
      apply (H4 x ltac:(clear - Hx; solve_notin_auto)
               ((x ~ abind_var_typ A) ++ Θ1));
        [ simpl_env; reflexivity
        | clear - Hdom Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | clear - Hβ' Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | intros β1 τ1 Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb1];
          [ discriminate | eauto ] ].
  -
    apply ad_pat__app with
      (P := subst_pskl_in_pskl (pskl_var_f β') α P)
      (Q1 := subst_bskl_in_bskl (bskl_var_f β') α Q1).
    + pose proof (IHad_pat1 Θ1 eq_refl Hdom Hβ' Hdefs) as IHx.
      rewrite subst_var_bskl_syn in IHx. exact IHx.
    + rewrite <- subst_var_bskl_inh.
      apply ad_refine_syn_rename_paint;
        [ exact H0 | exact Hdom | exact Hdefs ].
    + exact (IHad_pat2 Θ1 eq_refl Hdom Hβ' Hdefs).
  -
    rewrite subst_var_bskl_syn.
    apply ad_pat__abs_check
      with (L := L `union` singleton α `union` singleton β'
                   `union` dom (Θ1 ++ Θ0))
           (P := subst_pskl_in_pskl (pskl_var_f β') α P).
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
    rewrite <- subst_var_bskl_syn.
    apply (H0 x ltac:(clear - Hx; solve_notin_auto)
             ((x ~ abind_var_skl pskl_ghost) ++ Θ1));
      [ simpl_env; reflexivity
      | clear - Hdom Hx; simpl; repeat rewrite dom_app in *; fsetdec
      | clear - Hβ' Hx; simpl; repeat rewrite dom_app in *; fsetdec
      | intros β1 τ1 Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb1];
        [ discriminate | eauto ] ].
  -
    rewrite subst_var_bskl_syn, subst_var_btyp_to_bskl,
      subst_var_ptyp_to_btyp_syn.
    apply ad_pat__abs_anno_check
      with (L := L `union` singleton α `union` singleton β'
                   `union` dom (Θ1 ++ Θ0))
           (P := subst_pskl_in_pskl (pskl_var_f β') α P);
      [ apply a_wf_ptyp_rename_paint; [ exact H | exact Hdefs ] | ].
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
    rewrite <- subst_var_bskl_syn.
    apply (H1 x ltac:(clear - Hx; solve_notin_auto)
             ((x ~ abind_var_typ A) ++ Θ1));
      [ simpl_env; reflexivity
      | clear - Hdom Hx; simpl; repeat rewrite dom_app in *; fsetdec
      | clear - Hβ' Hx; simpl; repeat rewrite dom_app in *; fsetdec
      | intros β1 τ1 Hb;
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb1];
        [ discriminate | eauto ] ].
Qed.

Lemma ad_sd_typing_rename_tvar : forall M Θfull e B,
  {{ Θfull ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  forall Θ1 α Θ0 β',
  Θfull = Θ1 ++ (α ~ abind_tvar) ++ Θ0 ->
  α `notin` dom (Θ1 ++ Θ0) ->
  β' `notin` add α (dom (Θ1 ++ Θ0)) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  (forall y A', binds y (abind_var_typ A') Θ0 -> α `notin` ftvar_in_ptyp A') ->
  (forall y Ps, binds y (abind_var_skl Ps) Θ0 -> α `notin` ftvar_in_pskl Ps) ->
  {{ ((subst_aenv (ptyp_var_f β') α Θ1) ++ (β' ~ abind_tvar) ++ Θ0) ⊢ˢᵈ[ M ]
    (subst_ptyp_in_exp (ptyp_var_f β') α e) ⦂
    (subst_btyp_in_btyp (btyp_var_f β') α B) }}ad.
Proof.
  intros M Θfull e B H Θ1 α Θ0 β' HeqΘ Hdom Hβ' Hdefs Hvt Hvs.
  revert Θ1 HeqΘ Hdom Hβ' Hdefs.
  induction H; intros Θ1 ->; intros Hdom Hβ' Hdefs; simpl.
  -
    apply ad_sd_typing__unit.
    pose proof (@ad_pat_sub_rename_paint _ _ _ Θ1 α Θ0 _ _ β'
                  H Hdom Hdefs) as Hs.
    rewrite subst_var_btyp_to_bskl in Hs. exact Hs.
  -
    apply binds_app_1 in H as [Hb1 | Hb2];
      [ | apply binds_app_1 in Hb2 as [Hbm | Hb0] ].
    +
      apply ad_sd_typing__var
        with (A := subst_ptyp_in_ptyp (ptyp_var_f β') α A).
      * apply binds_app_2.
        change (abind_var_typ (subst_ptyp_in_ptyp (ptyp_var_f β') α A))
          with (subst_abind (ptyp_var_f β') α (abind_var_typ A)).
        apply (@binds_subst_aenv (ptyp_var_f β') α x (abind_var_typ A) Θ1 Hb1).
      * pose proof (@ad_pat_sub_rename_paint _ _ _ Θ1 α Θ0 _ _ β'
                      H0 Hdom Hdefs) as Hs.
        rewrite subst_var_btyp_to_bskl, subst_var_ptyp_to_uskl_syn in Hs.
        exact Hs.
    +
      exfalso. destruct Hbm as [Heq | []]. inversion Heq.
    +
      assert (Hfr : α `notin` ftvar_in_ptyp A) by eauto.
      apply ad_sd_typing__var with (A := A).
      * apply binds_app_3. simpl. right. exact Hb0.
      * pose proof (@ad_pat_sub_rename_paint _ _ _ Θ1 α Θ0 _ _ β'
                      H0 Hdom Hdefs) as Hs.
        rewrite subst_var_btyp_to_bskl, subst_var_ptyp_to_uskl_syn in Hs.
        rewrite subst_ptyp_in_ptyp_fresh_eq in Hs; [ exact Hs | exact Hfr ].
  -
    apply ad_sd_typing__anno.
    + apply a_wf_ptyp_rename_paint; [ exact H | exact Hdefs ].
    + pose proof (IHad_sd_typing Θ1 eq_refl Hdom Hβ' Hdefs) as IHx.
      rewrite subst_var_ptyp_to_btyp_inh in IHx. exact IHx.
    + pose proof (@ad_pat_sub_rename_paint _ _ _ Θ1 α Θ0 _ _ β'
                    H1 Hdom Hdefs) as Hs.
      rewrite subst_var_btyp_to_bskl, subst_var_ptyp_to_uskl_syn in Hs.
      exact Hs.
  -
    rewrite subst_var_ptyp_to_btyp_inh.
    apply ad_sd_typing__freeze
      with (B := subst_ptyp_in_ptyp (ptyp_var_f β') α B).
    + pose proof (IHad_sd_typing Θ1 eq_refl Hdom Hβ' Hdefs) as IHx.
      rewrite subst_var_ptyp_to_btyp_syn in IHx. exact IHx.
    + apply a_tyequiv_rename_paint; [ exact H0 | exact Hdom | exact Hdefs ].
  -
    apply ad_sd_typing__abs_check_step
      with (L := L `union` singleton α `union` singleton β'
                   `union` dom (Θ1 ++ Θ0)).
    + intros α1 Hα1.
      rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var;
        [ | clear - Hα1; fsetdec | apply lc_btyp_var_f ].
      apply (H0 α1 ltac:(clear - Hα1; solve_notin_auto) ((α1 ~ abind_tvar) ++ Θ1));
        [ simpl_env; reflexivity
        | clear - Hdom Hα1; simpl; repeat rewrite dom_app in *; fsetdec
        | clear - Hβ' Hα1; simpl; repeat rewrite dom_app in *; fsetdec
        | intros β1 τ1 Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb1];
          [ discriminate | eauto ] ].
  -
    rewrite subst_var_ptyp_to_btyp_inh.
    apply ad_sd_typing__abs_check_base
      with (L := L `union` singleton α `union` singleton β'
                   `union` dom (Θ1 ++ Θ0)).
    + apply a_wf_ptyp_rename_paint; [ exact H | exact Hdefs ].
    + change (btyp_var_f β') with (ptyp_to_btyp_syn (ptyp_var_f β')).
      apply is_ityp_subst_mono; [ exact H0 | apply mono_ptyp__var ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
      apply (H2 x ltac:(clear - Hx; solve_notin_auto)
               ((x ~ abind_var_typ A) ++ Θ1));
        [ simpl_env; reflexivity
        | clear - Hdom Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | clear - Hβ' Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | intros β1 τ1 Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb1];
          [ discriminate | eauto ] ].
  -
    apply ad_sd_typing__abs_anno_check_step
      with (L := L `union` singleton α `union` singleton β'
                   `union` dom (Θ1 ++ Θ0)).
    + intros α1 Hα1.
      rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var;
        [ | clear - Hα1; fsetdec | apply lc_btyp_var_f ].
      apply (H0 α1 ltac:(clear - Hα1; solve_notin_auto) ((α1 ~ abind_tvar) ++ Θ1));
        [ simpl_env; reflexivity
        | clear - Hdom Hα1; simpl; repeat rewrite dom_app in *; fsetdec
        | clear - Hβ' Hα1; simpl; repeat rewrite dom_app in *; fsetdec
        | intros β1 τ1 Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb1];
          [ discriminate | eauto ] ].
  -
    rewrite subst_var_ptyp_to_btyp_inh.
    apply ad_sd_typing__abs_anno_check_base
      with (L := L `union` singleton α `union` singleton β'
                   `union` dom (Θ1 ++ Θ0))
           (A' := subst_ptyp_in_ptyp (ptyp_var_f β') α A').
    + apply a_wf_ptyp_rename_paint; [ exact H | exact Hdefs ].
    + apply a_tyequiv_rename_paint; [ exact H0 | exact Hdom | exact Hdefs ].
    + change (btyp_var_f β') with (ptyp_to_btyp_syn (ptyp_var_f β')).
      apply is_ityp_subst_mono; [ exact H1 | apply mono_ptyp__var ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
      apply (H3 x ltac:(clear - Hx; solve_notin_auto)
               ((x ~ abind_var_typ A) ++ Θ1));
        [ simpl_env; reflexivity
        | clear - Hdom Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | clear - Hβ' Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | intros β1 τ1 Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb1];
          [ discriminate | eauto ] ].
  -
    rewrite subst_var_ptyp_to_btyp_inh.
    apply ad_sd_typing__abs
      with (L := L `union` singleton α `union` singleton β'
                   `union` dom (Θ1 ++ Θ0)).
    + exact H.
    + apply a_wf_ptyp_rename_paint; [ exact H0 | exact Hdefs ].
    + rewrite <- subst_var_ptyp_to_btyp_inh.
      change (btyp_var_f β') with (ptyp_to_btyp_syn (ptyp_var_f β')).
      change (btyp_arrow
                (subst_btyp_in_btyp (ptyp_to_btyp_syn (ptyp_var_f β')) α
                   (ptyp_to_btyp_inh A))
                (subst_btyp_in_btyp (ptyp_to_btyp_syn (ptyp_var_f β')) α B))
        with (subst_btyp_in_btyp (ptyp_to_btyp_syn (ptyp_var_f β')) α
                (btyp_arrow (ptyp_to_btyp_inh A) B)).
      apply mod_comp_ty_subst_mono; [ exact H1 | apply mono_ptyp__var ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
      apply (H3 x ltac:(clear - Hx; solve_notin_auto)
               ((x ~ abind_var_typ A) ++ Θ1));
        [ simpl_env; reflexivity
        | clear - Hdom Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | clear - Hβ' Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | intros β1 τ1 Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb1];
          [ discriminate | eauto ] ].
  -
    apply ad_sd_typing__abs_anno
      with (L := L `union` singleton α `union` singleton β'
                   `union` dom (Θ1 ++ Θ0))
           (A' := subst_ptyp_in_ptyp (ptyp_var_f β') α A').
    + exact H.
    + apply a_wf_ptyp_rename_paint; [ exact H0 | exact Hdefs ].
    + apply a_tyequiv_rename_paint; [ exact H1 | exact Hdom | exact Hdefs ].
    + subst A'. rewrite subst_var_btyp_to_ptyp. reflexivity.
    + change (btyp_var_f β') with (ptyp_to_btyp_syn (ptyp_var_f β')).
      change (btyp_arrow
                (subst_btyp_in_btyp (ptyp_to_btyp_syn (ptyp_var_f β')) α B1)
                (subst_btyp_in_btyp (ptyp_to_btyp_syn (ptyp_var_f β')) α B2))
        with (subst_btyp_in_btyp (ptyp_to_btyp_syn (ptyp_var_f β')) α
                (btyp_arrow B1 B2)).
      apply mod_comp_ty_subst_mono; [ exact H3 | apply mono_ptyp__var ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var.
      apply (H5 x ltac:(clear - Hx; solve_notin_auto)
               ((x ~ abind_var_typ A) ++ Θ1));
        [ simpl_env; reflexivity
        | clear - Hdom Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | clear - Hβ' Hx; simpl; repeat rewrite dom_app in *; fsetdec
        | intros β1 τ1 Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb1];
          [ discriminate | eauto ] ].
  -
    apply ad_sd_typing__app with
      (P := subst_pskl_in_pskl (pskl_var_f β') α P)
      (A2 := subst_ptyp_in_ptyp (ptyp_var_f β') α A2)
      (B1 := subst_btyp_in_btyp (btyp_var_f β') α B1).
    + pose proof (@ad_pat_rename_tvar mode_tc _ _ _ H Θ1 α Θ0 β'
                    eq_refl Hdom Hβ' Hdefs Hvt Hvs) as Hp.
      rewrite subst_var_bskl_syn in Hp. exact Hp.
    + rewrite <- subst_var_bskl_inh, <- subst_var_btyp_to_bskl.
      apply ad_refine_syn_rename_paint;
        [ exact H0 | exact Hdom | exact Hdefs ].
    + exact (IHad_sd_typing1 Θ1 eq_refl Hdom Hβ' Hdefs).
    + rewrite <- subst_var_btyp_to_ptyp.
      apply a_tyequiv_rename_paint; [ exact H2 | exact Hdom | exact Hdefs ].
    + pose proof (IHad_sd_typing2 Θ1 eq_refl Hdom Hβ' Hdefs) as IHy.
      rewrite subst_var_ptyp_to_btyp_inh in IHy. exact IHy.
Qed.
