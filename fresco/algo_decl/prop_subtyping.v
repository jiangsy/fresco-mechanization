Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.prop_tag.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo_decl.prop_precision.

Set Implicit Arguments.

Lemma guarded_pskl_subst : forall P P' α,
  guarded_pskl P ->
  guarded_pskl P' ->
  lc_pskl P' ->
  guarded_pskl (subst_pskl_in_pskl P' α P).
Proof.
  intros P P' α H HgQ HlcQ. induction H; simpl.
  - auto with fresco.
  - destruct_if; auto with fresco.
  - apply guarded_pskl__arrow; apply subst_pskl_in_pskl_lc_pskl; auto.
Qed.

Lemma a_wf_pskl_subst_ctx : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ1 β b Θ2 P',
  Θ = Θ1 ++ (β ~ b) ++ Θ2 ->
  β `notin` dom (Θ1 ++ Θ2) ->
  β `notin` Δ ->
  guarded_pskl P' ->
  {{ (Θ1 ++ Θ2) ⨟ empty ⊢ₚₛ P' }}a ->
  Δ ∩ ftvar_in_pskl P' [=] empty ->
  {{ (Θ1 ++ Θ2) ⨟ Δ ⊢ₚₛ subst_pskl_in_pskl P' β P }}a.
Proof.
  intros Θ Δ P H; induction H;
    intros Θ1 β b0 Θ2 Q0 Heqc Hfr HfrΔ HgQ HwfQ HdisQ; subst; simpl.
  - apply a_wf_pskl__unit.
  - destruct_if as [-> | Hne].
    + eapply a_wf_pskl_delta_mono; [ exact HwfQ | ].
      intros α Hα HαΔ. exfalso. clear - Hα HαΔ HdisQ.
      assert (α `in` Δ ∩ ftvar_in_pskl Q0) by fsetdec. fsetdec.
    + apply a_wf_pskl__var.
      apply a_binds_tvar_strip_mid with (c := β) (b := b0);
        [ exact H
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intros τ0 He; inversion He; subst; exact (Hne eq_refl) ].
  - apply a_wf_pskl__arrow; eauto.
  - apply a_wf_pskl__all
      with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2) `union` Δ).
    intros β0 Hβ0.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | intro He; subst; clear - Hβ0; fsetdec
        | eapply a_wf_pskl_lc; eauto ].
    assert (Hβ0Q : β0 `notin` ftvar_in_pskl Q0).
    { intro Hin. pose proof (a_wf_pskl_ftv_dom HwfQ Hin) as Hd.
      clear - Hd Hβ0. fsetdec. }
    match goal with
    | IH : forall α, α `notin` L -> _ |- _ =>
        specialize (IH β0 ltac:(clear - Hβ0; fsetdec)
                      ((β0 ~ abind_tvar) ++ Θ1) β b0 Θ2 Q0);
        simpl_env in IH; apply IH
    end; auto.
    all: try (clear - Hfr Hβ0; simpl_env in *; fsetdec).
    all: try (clear - HfrΔ Hβ0; fsetdec).
    all: try (clear - HdisQ Hβ0Q; fsetdec).
    all: try (eapply a_wf_pskl_tvar_mono; [ exact HwfQ | ];
              intros α Hα; apply a_binds_tvar_cons_tvar; auto).
  - apply a_wf_pskl__ghost.
  - apply a_wf_pskl__univ_ghost.
    + apply guarded_pskl_subst; auto. eapply a_wf_pskl_lc; eauto.
    + rewrite aenv_minus_app.
      match goal with
      | IH : context [ {{ _ ⨟ _ ⊢ₚₛ subst_pskl_in_pskl _ _ _ }}a ] |- _ =>
          apply IH with (b := b0)
      end; auto; try (clear; fsetdec).
      * rewrite !aenv_minus_app.
        unfold aenv_minus at 2. simpl.
        replace (AtomSetImpl.mem β Δ) with false
          by (symmetry; apply not_mem_iff; assumption).
        reflexivity.
      * intro Hin. simpl_env in Hin. apply union_iff in Hin.
        destruct Hin as [Hin | Hin]; apply dom_aenv_minus in Hin;
          clear - Hin Hfr; simpl_env in Hfr; destruct Hin; fsetdec.
      * rewrite <- aenv_minus_app.
        apply (a_wf_pskl_tvar_mono_ftv HwfQ).
        intros α Hα Hb. apply a_binds_tvar_aenv_minus. split; [ exact Hb | ].
        intro HαΔ. clear - Hα HαΔ HdisQ.
        assert (α `in` Δ ∩ ftvar_in_pskl Q0) by fsetdec. fsetdec.
Qed.

Lemma a_wf_pskl_subst_mid_def : forall Ξ Θ β τ P,
  {{ ⊢ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ) }}a ->
  {{ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ) ⨟ empty ⊢ₚₛ P }}a ->
  {{ (Ξ ++ Θ) ⨟ empty ⊢ₚₛ subst_pskl_in_pskl (ptyp_to_pskl τ) β P }}a.
Proof.
  intros Ξ Θ β τ P Hwf HwfP.
  assert (Htail : {{ ⊢ ((β ~ abind_flex_mono_def τ) ++ Θ) }}a)
    by (eapply a_wf_aenv_strip_prefix; exact Hwf).
  inversion Htail as [ | | βz τz Θz Hβ Hwfτ Hm HwfΘ | | | ]; subst.
  assert (Hfresh : β `notin` dom (Ξ ++ Θ)).
  { pose proof (a_wf_aenv_uniq Hwf) as Huq.
    clear - Huq. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec. }
  assert (Hpaint : {{ (Ξ ++ Θ) ⨟ empty ⊢ₚₛ ptyp_to_pskl τ }}a).
  { apply a_wf_ptyp_to_wf_pskl. eapply a_wf_ptyp_weaken;
      [ intros x bd Hb; apply binds_app_3; exact Hb | exact Hwfτ ]. }
  eapply a_wf_pskl_subst_ctx;
    [ exact HwfP | reflexivity | exact Hfresh | clear; fsetdec
    | apply mono_ptyp_to_pskl_guarded; exact Hm | exact Hpaint
    | clear; fsetdec ].
Qed.

Lemma ftag_ptyp_to_uskl_syn : forall A,
  ftag_in_uskl (ptyp_to_uskl_syn A) [=] empty.
Proof.
  intro A. unfold ptyp_to_uskl_syn. apply ftag_bskl_to_uskl.
Qed.

Lemma binds_mid_flex_absurd : forall Θ1 β (τ : ptyp) Θ2,
  binds β (abind_flex_mono_def τ) (Θ1 ++ (β ~ abind_flex_mono) ++ Θ2) ->
  β `notin` dom (Θ1 ++ Θ2) ->
  False.
Proof.
  intros * Hb Hfr. unfold binds in Hb.
  apply in_app_or in Hb; destruct Hb as [Hb | Hb];
    [ apply binds_In in Hb; simpl_env in *; fsetdec | ].
  apply in_app_or in Hb; destruct Hb as [Hb | Hb];
    [ | apply binds_In in Hb; simpl_env in *; fsetdec ].
  destruct Hb as [Heq | Habs]; [ inversion Heq | inversion Habs ].
Qed.

Lemma pskl_to_bskl_inh_subst_mono : forall P τ α',
  mono_ptyp τ ->
  subst_bskl_in_bskl (ptyp_to_bskl_syn τ) α' (pskl_to_bskl_inh P)
  = pskl_to_bskl_inh (subst_pskl_in_pskl (ptyp_to_pskl τ) α' P).
Proof.
  induction P; intros τ α' Hm; simpl; try reflexivity;
    try (rewrite IHP1; auto; rewrite IHP2; auto; reflexivity);
    try (rewrite IHP; auto; reflexivity).
  repeat destruct_if;
    try contradiction; try reflexivity.
  symmetry. apply ptyp_to_bskl_inh_syn_eq; assumption.
Qed.

Lemma binds_mid_def_eq : forall Θ1 β (τ τ0 : ptyp) Θ2,
  binds β (abind_flex_mono_def τ)
    (Θ1 ++ (β ~ abind_flex_mono_def τ0) ++ Θ2) ->
  β `notin` dom (Θ1 ++ Θ2) ->
  τ = τ0.
Proof.
  intros * Hb Hfr. unfold binds in Hb.
  apply in_app_or in Hb; destruct Hb as [Hb | Hb];
    [ apply binds_In in Hb; simpl_env in *; exfalso; fsetdec | ].
  apply in_app_or in Hb; destruct Hb as [Hb | Hb];
    [ | apply binds_In in Hb; simpl_env in *; exfalso; fsetdec ].
  destruct Hb as [Heq | Habs]; [ inversion Heq; reflexivity | inversion Habs ].
Qed.

Lemma ad_pat_consis_subst_flex_def : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Θ1 β τ0 Θ2,
  Θ = Θ1 ++ (β ~ abind_flex_mono_def τ0) ++ Θ2 ->
  β `notin` dom (Θ1 ++ Θ2) ->
  mono_ptyp τ0 ->
  β `notin` ftvar_in_ptyp τ0 ->
  (forall α, α `in` ftvar_in_ptyp τ0 -> a_binds_tvar α (Θ1 ++ Θ2)) ->
  (forall α1 τ, binds α1 (abind_flex_mono_def τ) (Θ1 ++ Θ2) ->
     β `notin` ftvar_in_ptyp τ) ->
  {{ Ψ ⨟ (Θ1 ++ Θ2) ⊢ˢ (subst_uskl_in_uskl (ptyp_to_uskl_syn τ0) β R)
                    ∼ (subst_bskl_in_bskl (ptyp_to_bskl_syn τ0) β Q) }}ad.
Proof.
  intros Ψ Θ R Q H; induction H;
    intros Θ1 β τ0 Θ2 Heqc Hfr Hm Hfrτ Hvis Hdefs; subst; simpl.
  4: eapply ad_pat_consis__forall_inh_tagged
       with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)); [ | eassumption ].
  5: apply ad_pat_consis__forall_inh_untagged
       with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
  6: apply ad_pat_consis__forall_syn_tagged
       with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
  7: apply ad_pat_consis__forall_syn
       with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).
  12: apply ad_pat_consis__univ_ghost_inh
        with (L := L `union` {{β}} `union` dom (Θ1 ++ Θ2)).

  4, 5, 6, 7, 12:
    lazymatch goal with
    | IH : forall α, α `notin` ?L -> forall Θ1 : list _, _ |- _ =>
      intros α Hα;
      assert (Hβα : β <> α) by (clear - Hα; fsetdec);
      assert (HαL : α `notin` L) by (clear - Hα; solve_notin_auto);
      try rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var
        by (solve [exact Hβα | apply mono_ptyp_to_uskl_syn_lc; exact Hm]);
      rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var
        by (solve [exact Hβα | apply mono_ptyp_to_bskl_syn_lc; exact Hm]);
      specialize (IH α HαL ((α ~ abind_tvar) ++ Θ1) β τ0 Θ2);
      simpl_env in IH; simpl_env; apply IH; auto;
        [ intros β0 Hβ0; apply a_binds_tvar_weaken_cons; auto
        | intros α1 τ Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
          [ discriminate | eauto ] ]
    end.
  - apply ad_pat_consis__unit; assumption.
  - repeat destruct_if; try contradiction.
    + eapply ad_pat_consis_psi_cong;
        [ apply consis_mono_refl; assumption
        | fsetdec_empty ].
    + apply ad_pat_consis__var; [ assumption | ].
      match goal with Hne : α <> β |- _ =>
        eapply a_binds_tvar_strip_mid;
          [ eassumption
          | intro He; inversion He; subst; exact (Hne eq_refl)
          | intro He; inversion He; subst; exact (Hne eq_refl)
          | intros τ1 He; inversion He; subst; exact (Hne eq_refl) ]
      end.
  - eapply ad_pat_consis__arrow; eauto.
  - apply ad_pat_consis__ghostg; assumption.
  - apply ad_pat_consis__dot_univ_ghost; eauto.
  - rewrite pskl_to_bskl_inh_subst_mono; [ | assumption ].
    apply ad_pat_consis__ghost; assumption.
  - apply ad_pat_consis__univ_ghost; eauto.

  - apply ad_pat_consis__univ_ghost_drop; eauto.
  -
    destruct_if as [-> | Hne].
    +
      assert (Heqdef : τ = τ0) by (eapply binds_mid_def_eq; eauto).
      rewrite Heqdef in *; clear Heqdef.
      match goal with
      | IH : forall Θ1 : list _, _ |- _ =>
          specialize (IH Θ1 β τ0 Θ2 ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs)
      end.
      rewrite subst_uskl_in_uskl_fresh_eq in *; [ auto | ].
      rewrite ftvar_ptyp_to_uskl_syn. exact Hfrτ.
    + assert (Hb' : binds α (abind_flex_mono_def τ) (Θ1 ++ Θ2)).
      { eapply binds_strip_mid; eauto.
        intro He; inversion He; subst; exact (Hne eq_refl). }
      apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb' | ].
      match goal with
      | IH : forall Θ1 : list _, _ |- _ =>
          specialize (IH Θ1 β τ0 Θ2 ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs)
      end.
      rewrite subst_uskl_in_uskl_fresh_eq in *; [ auto | ].
      rewrite ftvar_ptyp_to_uskl_syn. eauto.
  -
    destruct_if as [-> | Hne].
    + assert (Heqdef : τ = τ0) by (eapply binds_mid_def_eq; eauto).
      rewrite Heqdef in *; clear Heqdef.
      match goal with
      | IH : forall Θ1 : list _, _ |- _ =>
          specialize (IH Θ1 β τ0 Θ2 ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs)
      end.
      rewrite subst_bskl_in_bskl_fresh_eq in *; [ auto | ].
      rewrite ftvar_ptyp_to_bskl_syn. exact Hfrτ.
    + assert (Hb' : binds α (abind_flex_mono_def τ) (Θ1 ++ Θ2)).
      { eapply binds_strip_mid; eauto.
        intro He; inversion He; subst; exact (Hne eq_refl). }
      apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb' | ].
      match goal with
      | IH : forall Θ1 : list _, _ |- _ =>
          specialize (IH Θ1 β τ0 Θ2 ltac:(reflexivity) Hfr Hm Hfrτ Hvis Hdefs)
      end.
      rewrite subst_bskl_in_bskl_fresh_eq in *; [ auto | ].
      rewrite ftvar_ptyp_to_bskl_syn. eauto.
Qed.

Lemma ad_pat_consis_subst_flex : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Θ1 β Θ2,
  Θ = Θ1 ++ (β ~ abind_flex_mono) ++ Θ2 ->
  β `notin` dom (Θ1 ++ Θ2) ->
  (forall α1 τ, binds α1 (abind_flex_mono_def τ) (Θ1 ++ Θ2) ->
     β `notin` ftvar_in_ptyp τ) ->
  {{ Ψ ⨟ (Θ1 ++ Θ2) ⊢ˢ (subst_uskl_in_uskl uskl_unit β R)
                    ∼ (subst_bskl_in_bskl bskl_unit β Q) }}ad.
Proof.
  intros Ψ Θ R Q H Θ1 β Θ2 -> Hfr Hdefs.
  assert (Htransport : {{ Ψ ⨟ (Θ1 ++ (β ~ abind_flex_mono_def ptyp_unit) ++ Θ2)
                           ⊢ˢ R ∼ Q }}ad).
  { eapply ad_pat_consis_transport; [exact H | | ].
    - intros α Hα. destruct (α == β) as [-> | Hne].
      + right; right. exists ptyp_unit.
        unfold binds. apply in_or_app. right. left. reflexivity.
      + destruct Hα as [Hb | [Hb | [τ Hb]]];
          [left | right; left | right; right; exists τ];
          unfold binds in *; apply in_app_or in Hb;
          destruct Hb as [Hb | [Heq | Hb]];
          solve [ apply in_or_app; left; exact Hb
                | inversion Heq; subst; contradiction
                | apply in_or_app; right; right; exact Hb ].
    - intros α τ Hb. unfold binds in *.
      apply in_app_or in Hb. destruct Hb as [Hb | [Heq | Hb]];
        [apply in_or_app; left; exact Hb | discriminate
        |apply in_or_app; right; right; exact Hb]. }
  eapply (ad_pat_consis_subst_flex_def Htransport) with (τ0 := ptyp_unit);
    auto using mono_ptyp.
  simpl; intros; fsetdec.
Qed.

Lemma uskl_ghost_free_subst : forall R ψ α,
  uskl_ghost_free R ->
  uskl_ghost_free ψ ->
  lc_uskl ψ ->
  uskl_ghost_free (subst_uskl_in_uskl ψ α R).
Proof.
  intros R ψ α HR; revert α; induction HR; intros α0 Hψ Hlc; simpl.
  - apply uskl_ghost_free__unit.
  - destruct_if as [-> | Hne]; [ exact Hψ | apply uskl_ghost_free__var ].
  - apply uskl_ghost_free__arrow; [ apply IHHR1 | apply IHHR2 ]; assumption.
  - apply uskl_ghost_free__all_tag with (L := L `union` singleton α0).
    intros β Hβ.
    assert (HYX : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ α0 β HYX Hlc).
    apply H0; [ clear - Hβ; fsetdec | assumption | assumption ].
  - apply uskl_ghost_free__all_syn with (L := L `union` singleton α0).
    intros β Hβ.
    assert (HYX : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ α0 β HYX Hlc).
    apply H0; [ clear - Hβ; fsetdec | assumption | assumption ].
Qed.

Lemma uskl_ghost_free_subst_unit : forall ψ β,
  uskl_ghost_free ψ ->
  uskl_ghost_free (subst_uskl_in_uskl uskl_unit β ψ).
Proof.
  intros. eapply uskl_ghost_free_subst;
    eauto using uskl_ghost_free__unit, lc_uskl_unit.
Qed.

Lemma a_tags_sort_subst_unit : forall NM Ψ' ψ β,
  a_tags_sort NM Ψ' ψ ->
  a_tags_sort NM Ψ' (subst_uskl_in_uskl uskl_unit β ψ).
Proof.
  intros NM Ψ' ψ β H; destruct H.
  - apply a_tags_sort__sk;
      [ apply is_dskl_subst_unit; assumption
      | apply d_tags_skl_subst_unit; assumption ].
  - apply a_tags_sort__ty;
      [ apply is_dskl_subst_unit; assumption
      | apply d_tags_skl_subst_unit; assumption
      | apply uskl_ghost_free_subst_unit; assumption ].
Qed.

Lemma mono_ptyp_to_uskl_syn_ghost_free : forall τ,
  mono_ptyp τ -> uskl_ghost_free (ptyp_to_uskl_syn τ).
Proof.
  induction 1; simpl;
    [ apply uskl_ghost_free__unit | apply uskl_ghost_free__var
    | apply uskl_ghost_free__arrow; auto ].
Qed.

Lemma mono_ptyp_to_uskl_syn_tags : forall τ Ψ,
  mono_ptyp τ -> Ψ [=] empty -> d_tags_skl Ψ (ptyp_to_uskl_syn τ).
Proof.
  intros τ Ψ Hm; revert Ψ; induction Hm; intros Ψ He; simpl.
  - apply d_tags_skl__unit; assumption.
  - apply d_tags_skl__var; assumption.
  - apply d_tags_skl__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHm1 | apply IHHm2 | | ]; clear - He; fsetdec.
Qed.

Lemma d_tags_skl_subst_mono : forall Δ ψ τ β,
  d_tags_skl Δ ψ -> mono_ptyp τ ->
  d_tags_skl Δ (subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β ψ).
Proof.
  intros Δ ψ τ β H Hm; induction H; simpl.
  - auto with fresco.
  - destruct_if; auto using mono_ptyp_to_uskl_syn_tags with fresco.
  - eauto with fresco.
  - apply d_tags_skl__all_tag with (L := L `union` {{β}}) (Ψ0 := Ψ0);
      [ | assumption | assumption ].
    intros β0 Hβ0.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ auto | intro He; subst; clear - Hβ0; fsetdec
      | apply mono_ptyp_to_uskl_syn_lc; assumption ].
  - auto with fresco.
  - auto with fresco.
Qed.

Lemma uskl_ghost_free_subst_mono : forall ψ τ β,
  uskl_ghost_free ψ -> mono_ptyp τ ->
  uskl_ghost_free (subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β ψ).
Proof.
  intros. eapply uskl_ghost_free_subst;
    eauto using mono_ptyp_to_uskl_syn_ghost_free, mono_ptyp_to_uskl_syn_lc.
Qed.

Lemma a_tags_sort_subst_mono : forall NM Ψ' ψ τ β,
  a_tags_sort NM Ψ' ψ -> mono_ptyp τ ->
  a_tags_sort NM Ψ' (subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β ψ).
Proof.
  intros NM Ψ' ψ τ β H Hm; destruct H.
  - apply a_tags_sort__sk;
      auto using is_dskl_subst_mono, d_tags_skl_subst_mono.
  - apply a_tags_sort__ty;
      auto using is_dskl_subst_mono, d_tags_skl_subst_mono,
                 uskl_ghost_free_subst_mono.
Qed.

Lemma a_isub_strip_tvar_mid : forall α Ξ Θ0 Θ1,
  uniq (Ξ ++ (α ~ abind_tvar) ++ Θ1) ->
  uniq (Ξ ++ Θ0) ->
  α `notin` dom Θ0 ->
  ((α ~ abind_tvar) ++ Θ0) ⊴ (Ξ ++ (α ~ abind_tvar) ++ Θ1) ->
  Θ0 ⊴ Θ1.
Proof.
  intros α Ξ Θ0 Θ1 Huq HuqΞ Hα [[κ [Hid Hinc]] Hdef].
  destruct (a_inc_tvar_inv Hinc) as [Ξ' [Θ2 [Heq [Hsuf Hinc']]]].
  destruct (uniq_mid _ _ _ _ _ _ _ _ Huq Heq) as [<- [_ <-]].
  split.
  - exists κ. split; [ exact Hid | exact Hinc' ].
  - intros β τ Hb.
    assert (HβΘ0 : β `in` dom Θ0) by (eapply binds_In; eauto).
    assert (Hbw : binds β (abind_flex_mono_def τ)
                    (Ξ ++ (α ~ abind_tvar) ++ Θ1))
      by (apply Hdef; unfold binds; right; exact Hb).
    unfold binds in Hbw. apply in_app_or in Hbw.
    destruct Hbw as [Hbw | Hbw].
    { exfalso.
      assert (HβΞ : β `in` dom Ξ) by (eapply binds_In; exact Hbw).
      clear - HuqΞ HβΘ0 HβΞ.
      destruct_uniq. unfold disjoint in *. fsetdec. }
    simpl in Hbw. destruct Hbw as [Heqp | Hbw].
    { exfalso. inversion Heqp. }
    exact Hbw.
Qed.

Lemma mono_ptyp_to_bskl_syn_ghost_free : forall τ,
  mono_ptyp τ -> bskl_ghost_free (ptyp_to_bskl_syn τ).
Proof. induction 1; simpl; intuition. Qed.

Lemma a_wf_aenv_strip_prefix_suffix_local : forall Ξ α Θ,
  {{ ⊢ (Ξ ++ (α ~ abind_tvar) ++ Θ) }}a ->
  {{ ⊢ Θ }}a.
Proof.
  induction Ξ as [ | [α1 b] Ξ' IH ]; intros α Θ Hwf; simpl_env in *.
  - inversion Hwf; subst; assumption.
  - inversion Hwf; subst; simpl_env in *; eapply IH; eassumption.
Qed.

Lemma ad_refine_syn_ghost_free_strip_rename_gen : forall Θfull Δ Q Q',
  {{ Θfull ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Ξ α Θ1 β,
  Θfull = Ξ ++ (α ~ abind_tvar) ++ Θ1 ->
  bskl_ghost_free Q ->
  {{ ⊢ Θfull }}a ->
  uniq Θfull ->
  (forall α τ, α `in` (ftvar_in_bskl Q `union` ftvar_in_bskl Q') ->
     ~ binds α (abind_flex_mono_def τ) Ξ) ->
  {{ Θ1 ⨟ (add β (remove α Δ)) ⊢ᵣ (subst_bskl_in_bskl (bskl_var_f β) α Q) ⊳ (subst_bskl_in_bskl (bskl_var_f β) α Q') }}ad.
Proof.
  intros Θfull Δ Q Q' H; induction H;
    intros Ξ0 α0 Θt β Heqc Hg Hwf Huq Hfv; subst; simpl in *.

  9, 10: lazymatch goal with
  | Hlookup : binds ?α (abind_flex_mono_def ?τ) _ |- _ =>
    assert (HaΞ : ~ binds α (abind_flex_mono_def τ) Ξ0)
      by (apply Hfv; clear; fsetdec);
    assert (Hbb : binds α (abind_flex_mono_def τ) Θt)
      by (match goal with
          | HbX : binds α (abind_flex_mono_def τ) _ |- _ =>
            unfold binds in HbX; apply in_app_or in HbX;
            destruct HbX as [HbX | [Heqp | HbX]];
              [ contradiction | discriminate | exact HbX ]
          end);
    assert (HwfΘt : {{ ⊢ Θt }}a)
      by (eapply a_wf_aenv_strip_prefix_suffix_local; simpl_env in *; eauto);
    assert (Hτsc : ftvar_in_ptyp τ [<=] dom Θt)
      by (eapply a_wf_aenv_def_ftv_dom; eauto);
    assert (Hα0Θt : α0 `notin` dom Θt)
      by (clear - Huq; simpl_env in Huq; destruct_uniq;
          unfold disjoint in *; simpl_env in *; fsetdec);
    destruct_if as [Heq | Hne];
      [ subst; apply binds_In in Hbb; contradiction | ]
  end.
  - apply ad_refine_syn__unit.
  - destruct_if; apply ad_refine_syn__var.
  - destruct Hg as [Hg1 Hg2].
    apply ad_refine_syn_arrow_intro;
      [ eapply IHad_refine_syn1 | eapply IHad_refine_syn2 ];
      eauto; intros α τ Hα; apply Hfv; clear - Hα; fsetdec.
  - apply ad_refine_syn_all_intro
      with (L := L `union` {{α0}} `union` {{β}} `union` dom (Ξ0 ++ Θt)
                   `union` ftvar_in_bskl Q `union` ftvar_in_bskl Q').
    intros α Hα.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - Hα; fsetdec | apply lc_bskl_var_f ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ | intro He; subst; clear - Hα; fsetdec | apply lc_bskl_var_f ].
    assert (HαΞ : α `notin` dom Ξ0) by (clear - Hα; simpl_env in *; fsetdec).
    eapply ad_refine_syn_defs_mono;
      [ | intros γ τ Hb; unfold binds; right; exact Hb ].
    eapply ad_refine_syn_delta_mono;
      [ eapply (H1 α ltac:(clear - Hα; solve_notin_auto)
                  ((α ~ abind_tvar) ++ Ξ0) α0 Θt β);
        [ reflexivity
        | apply bskl_ghost_free_open_rec; assumption
        | apply a_wf_aenv__tvar; [ clear - Hα; simpl_env in *; fsetdec
                                 | assumption ]
        | apply uniq_push; [ assumption | clear - Hα; simpl_env in *; fsetdec ]
        | intros α2 τ2 Hα2 Hb2;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb2) as [[_ Heqb] | Hb2'];
          [ discriminate | ];
          pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                        Q (bskl_var_f α)) as Hup1;
          pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                        Q' (bskl_var_f α)) as Hup2;
          simpl in Hup1, Hup2;
          assert (HZQP : α2 `in` (ftvar_in_bskl Q `union` ftvar_in_bskl Q')
                         \/ α2 `in` singleton α)
            by (clear - Hα2 Hup1 Hup2; fsetdec);
          destruct HZQP as [HZQP | HZX];
            [ exact (Hfv α2 τ2 ltac:(clear - HZQP; fsetdec) Hb2')
            | assert (HZeq : α2 = α) by (clear - HZX; fsetdec);
              subst α2; apply HαΞ; eapply binds_In; exact Hb2' ] ]
      | clear - Hα; fsetdec ].
  - destruct Hg.
  - destruct Hg.
  - destruct Hg.
  - destruct Hg.
  -
    eapply ad_refine_syn__flex_l; [ exact Hbb | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f β) α0).
    2:{ rewrite ftvar_ptyp_to_bskl_syn.
        clear - Hτsc Hα0Θt. fsetdec. }
    eapply IHad_refine_syn; eauto.
    * apply mono_ptyp_to_bskl_syn_ghost_free.
      eapply a_wf_aenv_binds_def_mono; [ exact HwfΘt | exact Hbb ].
    * intros α2 τ2 Hα2 Hb2.
      rewrite ftvar_ptyp_to_bskl_syn in Hα2.
      assert (HZfv : α2 `in` ftvar_in_ptyp τ \/ α2 `in` ftvar_in_bskl Q')
        by (clear - Hα2; fsetdec).
      destruct HZfv as [Hα2τ | HZQ];
        [ | exact (Hfv α2 τ2 ltac:(clear - HZQ; fsetdec) Hb2) ].
      assert (Hα2Θt : α2 `in` dom Θt) by (clear - Hτsc Hα2τ; fsetdec).
      apply binds_In in Hb2.
      clear - Huq Hα2Θt Hb2. simpl_env in Huq. destruct_uniq.
      unfold disjoint in *. simpl_env in *. fsetdec.
  -
    eapply ad_refine_syn__flex_r; [ exact Hbb | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f β) α0).
    2:{ rewrite ftvar_ptyp_to_bskl_syn.
        clear - Hτsc Hα0Θt. fsetdec. }
    eapply IHad_refine_syn; eauto.
    intros α2 τ2 Hα2 Hb2.
    rewrite ftvar_ptyp_to_bskl_syn in Hα2.
    assert (HZfv : α2 `in` ftvar_in_ptyp τ \/ α2 `in` ftvar_in_bskl Q)
      by (clear - Hα2; fsetdec).
    destruct HZfv as [Hα2τ | HZP];
      [ | exact (Hfv α2 τ2 ltac:(clear - HZP; fsetdec) Hb2) ].
    assert (Hα2Θt : α2 `in` dom Θt) by (clear - Hτsc Hα2τ; fsetdec).
    apply binds_In in Hb2.
      clear - Huq Hα2Θt Hb2. simpl_env in Huq. destruct_uniq.
    unfold disjoint in *. simpl_env in *. fsetdec.
Qed.

Lemma ad_refine_syn_ghost_free_strip_rename : forall Θfull Δ Q Q',
  {{ Θfull ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Ξ α Θ1 β,
  Θfull = Ξ ++ (α ~ abind_tvar) ++ Θ1 ->
  bskl_ghost_free Q ->
  {{ ⊢ Θfull }}a ->
  uniq Θfull ->
  (forall α, α `in` (ftvar_in_bskl Q `union` ftvar_in_bskl Q') ->
     α `notin` dom Ξ) ->
  {{ Θ1 ⨟ (add β (remove α Δ)) ⊢ᵣ (subst_bskl_in_bskl (bskl_var_f β) α Q) ⊳ (subst_bskl_in_bskl (bskl_var_f β) α Q') }}ad.
Proof.
  intros * H Ξ α Θ1 β Heq Hg Hwf Huq Hfv.
  eapply ad_refine_syn_ghost_free_strip_rename_gen; eauto.
  intros γ τ Hγ Hb. apply binds_In in Hb. exact (Hfv γ Hγ Hb).
Qed.

Lemma ad_refine_syn_fold_def_source : forall Θ Δ Qs Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  forall β τ Q0,
  binds β (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ ->
  Qs = subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q0 ->
  {{ Θ ⨟ Δ ⊢ᵣ Q0 ⊳ Qt }}ad.
Proof.
  intros Θ Δ Qs Qt H; induction H; intros β τ0 Q0 Hb Hm HeqQs.

  10: { eapply ad_refine_syn__flex_r; eauto. }
  all: destruct Q0; simpl in HeqQs;
    try match goal with
        | Hif : context [ if ?e then _ else _ ] |- _ =>
            let He := fresh "Hne" in destruct e as [-> | He]
        end;
    try discriminate HeqQs.
  -  apply ad_refine_syn__unit.
  -
    eapply ad_refine_syn__flex_l; [ exact Hb | ].
    rewrite <- HeqQs. apply ad_refine_syn__unit.
  -
    eapply ad_refine_syn__flex_l; [ exact Hb | ].
    rewrite <- HeqQs. apply ad_refine_syn__var; assumption.
  -
    inversion HeqQs; subst. apply ad_refine_syn__var; assumption.
  -
    eapply ad_refine_syn__flex_l; [ exact Hb | ].
    rewrite <- HeqQs. apply ad_refine_syn_arrow_intro; assumption.
  -
    inversion HeqQs; subst.
    apply ad_refine_syn_arrow_intro;
      [ eapply IHad_refine_syn1; eauto
      | eapply IHad_refine_syn2; eauto ].
  -
    destruct τ0; simpl in HeqQs; discriminate.
  -
    inversion HeqQs; subst.
    apply ad_refine_syn_all_intro with (L := L `union` {{β}}).
    intros α Hα.
    match goal with
    | IH : forall α, α `notin` L -> _ |- _ =>
        eapply (IH α ltac:(clear - Hα; solve_notin_auto))
    end; [ unfold binds; right; exact Hb | exact Hm | ].
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ reflexivity
      | intro He; subst; clear - Hα; fsetdec
      | apply mono_ptyp_to_bskl_syn_lc; exact Hm ].
  -
    destruct τ0; simpl in HeqQs; discriminate.
  -
    apply ad_refine_syn__ghost; assumption.
  -
    destruct τ0; simpl in HeqQs; discriminate.
  -
    inversion HeqQs; subst.
    apply ad_refine_syn_univ_ghost_remove_intro.
    eapply IHad_refine_syn; eauto.
  -
    destruct τ0; simpl in HeqQs; discriminate.
  -
    inversion HeqQs; subst.
    apply ad_refine_syn_univ_ghost_fill_intro with (L := L `union` {{β}}).
    intros α Hα.
    match goal with
    | IH : forall α, α `notin` L -> _ |- _ =>
        eapply (IH α ltac:(clear - Hα; solve_notin_auto))
    end; [ | exact Hm | simpl; reflexivity ].
    unfold binds. simpl. right. exact Hb.
  -
    destruct τ0; simpl in HeqQs; discriminate.
  -
    inversion HeqQs; subst.
    apply ad_refine_syn_univ_ghost_keep_intro.
    eapply IHad_refine_syn; eauto.
  -
    eapply ad_refine_syn__flex_l; [ exact Hb | ].
    rewrite <- HeqQs.
    eapply ad_refine_syn__flex_l; eassumption.
  -
    inversion HeqQs; subst.
    eapply ad_refine_syn__flex_l; eassumption.
Qed.

Lemma uskl_to_pskl_close_rec : forall ψ α k,
  uskl_to_pskl (close_uskl_wrt_uskl_rec k α ψ)
  = close_pskl_wrt_pskl_rec k α (uskl_to_pskl ψ).
Proof.
  induction ψ; intros α0 k; simpl; try (f_equal; auto; fail).
  - destruct (lt_ge_dec n k); reflexivity.
  - destruct_if;
      reflexivity.
Qed.

Lemma uskl_to_pskl_close : forall ψ α,
  ⌊ close_uskl_wrt_uskl α ψ ⌋ˢ = close_pskl_wrt_pskl α ⌊ ψ ⌋ˢ.
Proof.
  intros. unfold close_uskl_wrt_uskl, close_pskl_wrt_pskl.
  apply uskl_to_pskl_close_rec.
Qed.

Lemma pskl_decorate_exists : forall P,
  lc_pskl P ->
  forall L, exists Ψ ψ,
    Ψ ∩ L [=] empty /\
    is_dskl ψ /\
    d_tags_skl Ψ ψ /\
    ⌊ ψ ⌋ˢ = P /\
    (pskl_ghost_free P -> uskl_ghost_free ψ).
Proof.
  intros P Hlc; induction Hlc; intros L.
  -
    exists empty, uskl_unit. repeat apply conj;
      [ fsetdec | apply is_dskl__unit | apply d_tags_skl__unit; fsetdec
      | reflexivity | intros _; apply uskl_ghost_free__unit ].
  -
    exists empty, (uskl_var_f α). repeat apply conj;
      [ fsetdec | apply is_dskl__var | apply d_tags_skl__var; fsetdec
      | reflexivity | intros _; apply uskl_ghost_free__var ].
  -
    destruct (IHHlc1 L) as [Ψ1 [ψ1 [Hd1 [Ht1 [Hg1 [He1 Hgf1]]]]]].
    destruct (IHHlc2 (L `union` Ψ1))
      as [Ψ2 [ψ2 [Hd2 [Ht2 [Hg2 [He2 Hgf2]]]]]].
    exists (Ψ1 `union` Ψ2), (uskl_arrow ψ1 ψ2). repeat apply conj.
    + clear - Hd1 Hd2. fsetdec.
    + apply is_dskl__arrow; assumption.
    + apply d_tags_skl__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
        [ assumption | assumption | clear - Hd2; fsetdec | fsetdec ].
    + simpl. rewrite He1, He2. reflexivity.
    + intros Hg. simpl in Hg. destruct Hg as [Hga Hgb].
      apply uskl_ghost_free__arrow; [ apply Hgf1; auto | apply Hgf2; auto ].
  -
    destruct (atom_fresh (L `union` ftvar_in_pskl P1)) as [α0 FrX].
    destruct (H0 α0 (L `union` singleton α0))
      as [Ψ0 [ψ0 [Hd0 [Ht0 [Hg0 [He0 Hgf0]]]]]].
    destruct (atom_fresh (L `union` Ψ0)) as [ε Frε].
    exists (add ε Ψ0), (uskl_all_tag ε (close_uskl_wrt_uskl α0 ψ0)).
    repeat apply conj.
    + clear - Hd0 Frε. fsetdec.
    + apply is_dskl__all_tag with (L := singleton α0).
      intros β Hβ.
      rewrite <- subst_uskl_in_uskl_spec.
      change (uskl_var_f β) with (ptyp_to_uskl_syn (ptyp_var_f β)).
      apply is_dskl_subst_mono; [ exact Ht0 | apply mono_ptyp__var ].
    + apply d_tags_skl__all_tag with (L := singleton α0) (Ψ0 := Ψ0);
        [ | clear - Frε; fsetdec | fsetdec ].
      intros β Hβ.
      rewrite <- subst_uskl_in_uskl_spec.
      change (uskl_var_f β) with (ptyp_to_uskl_syn (ptyp_var_f β)).
      apply d_tags_skl_subst_mono; [ exact Hg0 | apply mono_ptyp__var ].
    + simpl. rewrite uskl_to_pskl_close. rewrite He0.
      rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        [ reflexivity | clear - FrX; fsetdec ].
    + intros Hg. simpl in Hg.
      apply uskl_ghost_free__all_tag with (L := singleton α0).
      intros β Hβ.
      rewrite <- subst_uskl_in_uskl_spec.
      change (uskl_var_f β) with (ptyp_to_uskl_syn (ptyp_var_f β)).
      apply uskl_ghost_free_subst_mono; [ | apply mono_ptyp__var ].
      apply Hgf0. unfold open_pskl_wrt_pskl. apply pskl_ghost_free_open_rec.
      exact Hg.
  -
    exists empty, uskl_dot_ghost. repeat apply conj;
      [ fsetdec | apply is_dskl__dot_ghost | apply d_tags_skl__dot_ghost; fsetdec
      | reflexivity | intros Hg; simpl in Hg; contradiction ].
  -
    destruct (IHHlc L) as [Ψ0 [ψ0 [Hd0 [Ht0 [Hg0 [He0 Hgf0]]]]]].
    exists Ψ0, (uskl_dot_univ_ghost ψ0). repeat apply conj.
    + exact Hd0.
    + auto with fresco.
    + auto with fresco.
    + simpl. rewrite He0. reflexivity.
    + intros Hg. simpl in Hg. contradiction.
Qed.

Lemma uskl_ghost_free_to_pskl : forall R,
  uskl_ghost_free R -> pskl_ghost_free ⌊ R ⌋ˢ.
Proof.
  intros R H; induction H; cbn.
  - exact I.
  - exact I.
  - split; assumption.
  - destruct (atom_fresh L) as [α Hα]; specialize (H0 α Hα).
    rewrite uskl_to_pskl_open in H0; unfold open_pskl_wrt_pskl in H0.
    eapply pskl_ghost_free_open_rec_inv; exact H0.
  - destruct (atom_fresh L) as [α Hα]; specialize (H0 α Hα).
    rewrite uskl_to_pskl_open in H0; unfold open_pskl_wrt_pskl in H0.
    eapply pskl_ghost_free_open_rec_inv; exact H0.
Qed.

Lemma a_extract_ty_ghost_free : forall Θ0 α M P P0 Ξ P1,
  a_extract Θ0 a_sub_mode_ty α M P P0 Ξ P1 ->
  pskl_ghost_free P1.
Proof.
  intros * Hex; inversion Hex; subst.
  match goal with
  | Hg : a_guess _ a_sub_mode_ty _ _ _ |- _ => inversion Hg; subst
  end.
  apply ptyp_to_pskl_ghost_free.
Qed.

Lemma a_tags_sort_decorate_exists : forall Θ0 NM α M P P0 Ξ P1,
  a_extract Θ0 NM α M P P0 Ξ P1 ->
  lc_pskl P1 ->
  forall L, exists Ψg ψg,
    Ψg ∩ L [=] empty /\
    a_tags_sort NM Ψg ψg /\
    ⌊ ψg ⌋ˢ = P1.
Proof.
  intros Θ0 NM α M P P0 Ξ P1 Hex Hlc L.
  destruct (pskl_decorate_exists Hlc L)
    as [Ψg [ψg [Hint [Htskl [Hdtags [Herase Hgf]]]]]].
  exists Ψg, ψg. repeat apply conj; [ exact Hint | | exact Herase ].
  destruct NM.
  - apply a_tags_sort__ty; [ exact Htskl | exact Hdtags | ].
    apply Hgf. eapply a_extract_ty_ghost_free; eauto.
  - apply a_tags_sort__sk; [ exact Htskl | exact Hdtags ].
Qed.

Lemma ad_partial_precise_arrow_arrow_inv : forall Θ Δ Ψ P1 P2 ψ1 ψ2,
  {{ Θ ⨟ Δ ⊢ˢ (pskl_arrow P1 P2) ⊑ᵖ[ Ψ ] (uskl_arrow ψ1 ψ2) }}ad ->
  exists Ψ1 Ψ2, ({{ Θ ⨟ Δ ⊢ˢ P1 ⊑ᵖ[ Ψ1 ] ψ1 }}ad) /\ ({{ Θ ⨟ Δ ⊢ˢ P2 ⊑ᵖ[ Ψ2 ] ψ2 }}ad)
    /\ Ψ [=] Ψ1 `union` Ψ2.
Proof.
  intros Θ Δ Ψ P1 P2 ψ1 ψ2 H; inversion H; subst.
  match goal with
  | Hp1 : {{ Θ ⨟ Δ ⊢ˢ P1 ⊑ᵖ[ ?A ] ψ1 }}ad, Hp2 : {{ Θ ⨟ Δ ⊢ˢ P2 ⊑ᵖ[ ?B ] ψ2 }}ad |- _ =>
    exists A, B; split; [ exact Hp1 | split; [ exact Hp2 | assumption ] ]
  end.
Qed.

Lemma ad_partial_precise_delta_shrink : forall Θ Δf Ψ P ψ,
  {{ Θ ⨟ Δf ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall Δ, Δ [<=] Δf ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θ Δf Ψ P ψ H; induction H; intros Δ0 Hsub.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; assumption.
  - eapply ad_ppre__arrow;
      [ exact (IHad_partial_precise1 Δ0 Hsub)
      | exact (IHad_partial_precise2 Δ0 Hsub)
      | assumption ].
  - eapply ad_ppre__forall with (L := L); [ | eassumption ].
    intros α0 Hα0.
    apply (H0 α0 Hα0 (add α0 Δ0)). clear - Hsub; fsetdec.
  -
    apply ad_ppre__ghost; [ assumption | ].
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      clear - Hint Hsub; fsetdec end.
  - apply ad_ppre__univ_ghost_remove. exact (IHad_partial_precise Δ0 Hsub).
  - eapply ad_ppre__univ_ghost_fill with (L := L).
    intros α0 Hα0. exact (H0 α0 Hα0 Δ0 Hsub).
  - apply ad_ppre__univ_ghost_keep. exact (IHad_partial_precise Δ0 Hsub).
  - eapply ad_ppre__flex_l; [ eassumption | ].
    exact (IHad_partial_precise Δ0 Hsub).
  - eapply ad_ppre__flex_r; [ eassumption | ].
    exact (IHad_partial_precise Δ0 Hsub).
Qed.

Lemma ad_partial_precise_delta_cong : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall Δ', Δ [=] Δ' ->
  {{ Θ ⨟ Δ' ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θ Δ Ψ P ψ H Δ' Heq.
  apply (ad_partial_precise_delta_shrink H). clear - Heq; fsetdec.
Qed.

Lemma ad_partial_precise_delta_weaken_fresh : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall Δ',
  Δ' ∩ ftvar_in_uskl ψ [=] empty ->
  delta_def_fresh Δ' Θ ->
  {{ Θ ⨟ (Δ `union` Δ') ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Δ' HΔ' Hdf.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; assumption.
  - simpl in HΔ'.
    eapply ad_ppre__arrow;
      [ apply IHad_partial_precise1; [ clear - HΔ'; fsetdec | exact Hdf ]
      | apply IHad_partial_precise2; [ clear - HΔ'; fsetdec | exact Hdf ]
      | assumption ].
  -
    simpl in HΔ'.
    eapply ad_ppre__forall with (L := L `union` Δ'); [ | eassumption ].
    intros α0 Hα0.
    assert (HSX : Δ' ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f α0)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0))
        as Hup.
      simpl in Hup. clear - HΔ' Hα0 Hup. fsetdec. }
    assert (Hdf' : delta_def_fresh Δ' ((α0 ~ abind_tvar) ++ Θ))
      by (apply delta_def_fresh_weaken_tvar; exact Hdf).
    eapply ad_partial_precise_delta_cong;
      [ apply (H0 α0 ltac:(clear - Hα0; solve_notin_auto) Δ' HSX Hdf')
      | clear; fsetdec ].
  -
    apply ad_ppre__ghost; [ assumption | ].
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      clear - Hint HΔ'; fsetdec end.
  - apply ad_ppre__univ_ghost_remove; auto.
  -
    eapply ad_ppre__univ_ghost_fill with (L := L `union` Δ').
    intros α0 Hα0.
    assert (HSX : Δ' ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f α0)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0))
        as Hup.
      simpl in Hup. clear - HΔ' Hα0 Hup. fsetdec. }
    assert (Hdf' : delta_def_fresh Δ' ((α0 ~ abind_tvar) ++ Θ))
      by (apply delta_def_fresh_weaken_tvar; exact Hdf).
    apply (H0 α0 ltac:(clear - Hα0; solve_notin_auto) Δ' HSX Hdf').
  -
    simpl in HΔ'.
    apply ad_ppre__univ_ghost_keep; apply IHad_partial_precise; auto.
  - eapply ad_ppre__flex_l; [ eassumption | ].
    apply IHad_partial_precise; auto.
  -
    eapply ad_ppre__flex_r; [ eassumption | ].
    apply IHad_partial_precise; [ | exact Hdf ].
    rewrite ftvar_ptyp_to_uskl_syn.
    apply inter_empty_pointwise.
    intros y Hy. eapply Hdf; [ exact Hy | eassumption ].
Qed.

Lemma ad_partial_precise_open_tvar_fresh : forall Θ Δ Ψ P ψ β,
  {{ ⊢ Θ }}a -> β `notin` dom Θ -> β `notin` ftvar_in_uskl ψ ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ) ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros * Hwf Hβ Hψ Hp.
  eapply ad_partial_precise_delta_cong with (Δ := Δ `union` singleton β).
  - eapply ad_partial_precise_delta_weaken_fresh with (Δ' := singleton β).
    + apply ad_partial_precise_weaken_tvar; exact Hp.
    + clear - Hψ; fsetdec.
    + intros γ α τ Hγ Hb.
      eapply (delta_def_fresh_open_tvar Hwf Hβ (delta_def_fresh_empty Θ));
        [ clear - Hγ; fsetdec | exact Hb ].
  - clear; fsetdec.
Qed.

Lemma ad_partial_precise_no_ghost_subject_delta_mono : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  pskl_no_ghost P ->
  forall Δ', Δ [<=] Δ' ->
  {{ Θ ⨟ Δ' ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Hnh Δ' Hsub.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; assumption.
  - simpl in Hnh; destruct Hnh.
    eapply ad_ppre__arrow; eauto.
  - simpl in Hnh.
    eapply ad_ppre__forall with (L := L); [ | eassumption ].
    intros α Hα.
    apply (H0 α Hα); [ apply pskl_no_ghost_open; exact Hnh | ].
    clear - Hsub; fsetdec.
  - simpl in Hnh; contradiction.
  - simpl in Hnh.
    apply ad_ppre__univ_ghost_remove; auto.
  - simpl in Hnh.
    eapply ad_ppre__univ_ghost_fill with (L := L); eauto.
  - simpl in Hnh.
    apply ad_ppre__univ_ghost_keep; auto.
  - eapply ad_ppre__flex_l; [ eassumption | ].
    apply IHad_partial_precise;
      [ apply ptyp_to_pskl_no_ghost | exact Hsub ].
  - eapply ad_ppre__flex_r; [ eassumption | ]. auto.
Qed.

Lemma ad_partial_precise_rename : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall αr βr,
  αr `in` Δ ->
  αr `notin` dom Θ ->
  βr `notin` dom Θ -> βr `notin` Δ ->
  βr `notin` ftvar_in_pskl P -> βr `notin` ftvar_in_uskl ψ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     αr `notin` ftvar_in_ptyp τ /\ βr `notin` ftvar_in_ptyp τ) ->
  {{ Θ ⨟ (add βr (remove αr Δ)) ⊢ˢ
    (subst_pskl_in_pskl (pskl_var_f βr) αr P)
    ⊑ᵖ[ Ψ ] (subst_uskl_in_uskl (uskl_var_f βr) αr ψ) }}ad.
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros αr βr HαΔ HαΘ HβΘ HβΔ HYP Hβψ Hdefs; simpl in *.
  -  apply ad_ppre__unit; assumption.
  -
    destruct (eq_var α αr); apply ad_ppre__var; assumption.
  -
    eapply ad_ppre__arrow;
      [ apply IHad_partial_precise1; auto
      | apply IHad_partial_precise2; auto
      | assumption ].
  -
    eapply ad_ppre__forall
      with (L := L `union` singleton αr `union` singleton βr
                   `union` Δ `union` dom Θ); [ | eassumption ].
    intros α2 Hα2.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα2; fsetdec | apply lc_pskl_var_f ].
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    eapply ad_partial_precise_delta_cong;
      [ apply (H0 α2 ltac:(clear - Hα2; solve_notin_auto) αr βr);
        [ clear - HαΔ; fsetdec
        | simpl; clear - HαΘ Hα2; fsetdec
        | simpl; clear - HβΘ Hα2; fsetdec
        | clear - HβΔ Hα2; fsetdec
        | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P
                        (pskl_var_f α2)) as Hup;
          simpl in Hup; clear - HYP Hα2 Hup; fsetdec
        | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                        (uskl_var_f α2)) as Hup;
          simpl in Hup; clear - Hβψ Hα2 Hup; fsetdec
        | intros α τ Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
          [ discriminate Hc | exact (Hdefs _ _ Hb') ] ]
      | clear - Hα2; fsetdec ].
  -
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      assert (Hαψ : αr `notin` ftvar_in_uskl ψ)
        by (clear - Hint HαΔ; fsetdec);
      rewrite (subst_uskl_in_uskl_fresh_eq _ _ _ Hαψ);
      apply ad_ppre__ghost; [ assumption | clear - Hint Hβψ; fsetdec ]
    end.
  -
    apply ad_ppre__univ_ghost_remove.
    apply IHad_partial_precise; auto.
  -
    eapply ad_ppre__univ_ghost_fill
      with (L := L `union` singleton αr `union` singleton βr
                   `union` Δ `union` dom Θ).
    intros α2 Hα2.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    replace (pskl_univ_ghost (subst_pskl_in_pskl (pskl_var_f βr) αr P))
      with (subst_pskl_in_pskl (pskl_var_f βr) αr (pskl_univ_ghost P))
      by reflexivity.
    apply (H0 α2 ltac:(clear - Hα2; solve_notin_auto) αr βr).
    + exact HαΔ.
    + simpl. clear - HαΘ Hα2; fsetdec.
    + simpl. clear - HβΘ Hα2; fsetdec.
    + exact HβΔ.
    + simpl. simpl in HYP. exact HYP.
    + pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                    (uskl_var_f α2)) as Hup;
      simpl in Hup; clear - Hβψ Hα2 Hup; fsetdec.
    + intros α τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | exact (Hdefs _ _ Hb') ].
  -
    apply ad_ppre__univ_ghost_keep.
    apply IHad_partial_precise; auto.
  -
    assert (Hne : α <> αr).
    { intros ->. apply HαΘ. eapply binds_In; eassumption. }
    destruct_if as [Hc | _]; [ exfalso; auto | ].
    destruct (Hdefs _ _ H) as [Hατ Hβτ].
    eapply ad_ppre__flex_l; [ eassumption | ].
    assert (Hfr : αr `notin` ftvar_in_pskl (ptyp_to_pskl τ))
      by (rewrite ftvar_ptyp_to_pskl; exact Hατ).
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f βr) αr Hfr).
    apply IHad_partial_precise; auto.
    rewrite ftvar_ptyp_to_pskl. exact Hβτ.
  -
    assert (Hne : α <> αr).
    { intros ->. apply HαΘ. eapply binds_In; eassumption. }
    destruct_if as [Hc | _]; [ exfalso; auto | ].
    destruct (Hdefs _ _ H) as [Hατ Hβτ].
    eapply ad_ppre__flex_r; [ eassumption | ].
    assert (Hfr : αr `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ))
      by (rewrite ftvar_ptyp_to_uskl_syn; exact Hατ).
    rewrite <- (subst_uskl_in_uskl_fresh_eq
                  (ptyp_to_uskl_syn τ) (uskl_var_f βr) αr Hfr).
    apply IHad_partial_precise; auto.
    rewrite ftvar_ptyp_to_uskl_syn. exact Hβτ.
Qed.
