Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.prop_tag.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_mod_compat.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.consistency.prop_consis_precise.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_precise.
Require Import src.fresco.algo.subtyping.prop_rigid_substitution.
Require Import src.fresco.algo.subtyping.prop_solve_extension.
Require Import src.fresco.algo.subtyping.prop_completeness_solve_eq_var.
Require Import src.fresco.algo.subtyping.prop_completeness_lookeq_solve.

Set Implicit Arguments.

Lemma ad_ppre_guarded_dot_univ_ghost_absurd : forall Θ0 Θ κ Δ Ψ P ψ0,
  {{ ⊢ Θ }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  guarded_pskl P ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ P) ⊑ᵖ[ Ψ ] (uskl_dot_univ_ghost ψ0) }}ad ->
  False.
Proof.
  intros Θ0 Θ κ Δ Ψ P ψ0 HwfΘ Hκ Hg Hpre.
  destruct Hg as [ | α | P1 P2 Hlc1 Hlc2 ]; cbn [msubst_pskl] in Hpre.
  - inversion Hpre.
  - eapply ad_ppre_mono_paint_dot_univ_ghost_absurd;
      [ exact HwfΘ | exact Hpre | reflexivity | reflexivity
      | eapply a_inc_lookup_mono; exact Hκ ].
  - inversion Hpre.
Qed.

Lemma uskl_rsubst_guarded_erase : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  lc_uskl R ->
  guarded_pskl ⌊ R' ⌋ˢ ->
  guarded_pskl ⌊ R ⌋ˢ.
Proof.
  intros NM Θ Δρ Ψρ R' R H Hlc Hg; destruct H; cbn [uskl_to_pskl] in Hg |- *;
    try assumption; try solve [ inversion Hg ].
  -  apply guarded_pskl__var.
  -
    inversion Hlc; subst.
    apply guarded_pskl__arrow; apply lc_uskl_to_pskl; assumption.
Qed.

Lemma a_solve_sub_ghost_output : forall Θ0 m P0 Ξ Pa,
  {{ Θ0 ⊢ₛ pskl_ghost ≼[ m ] P0 ⤳ Ξ ⨾ Pa }}a ->
  Pa = pskl_ghost \/ exists B, Pa = pskl_univ_ghost B.
Proof.
  intros Θ0 m P0 Ξ Pa H.
  remember pskl_ghost as Ph eqn:HeqP.
  induction H; try discriminate HeqP; subst;
    solve [ left; reflexivity
          | right; eexists; reflexivity
          | match goal with Hg : guarded_pskl pskl_ghost |- _ => inversion Hg end
          |
            apply IHa_solve_sub; reflexivity ].
Qed.

Lemma ad_ppre_ghost_subject_tags : forall Θ Δ Ψ ψ,
  {{ Θ ⨟ Δ ⊢ˢ pskl_ghost ⊑ᵖ[ Ψ ] ψ }}ad ->
  Ψ [=] empty.
Proof.
  intros Θ Δ Ψ ψ H.
  remember pskl_ghost as P eqn:HeqP.
  induction H; try discriminate HeqP; subst;
    solve [ assumption | apply IHad_partial_precise; reflexivity ].
Qed.

Lemma ad_ppre_univ_ghost_strip : forall Θ Δ Ψ B ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ (pskl_univ_ghost B) ⊑ᵖ[ Ψ ] ψ }}ad ->
  guarded_pskl ⌊ ψ ⌋ˢ ->
  {{ Θ ⨟ Δ ⊢ˢ B ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θ Δ Ψ B ψ HwfΘ H.
  remember (pskl_univ_ghost B) as P eqn:HeqP.
  revert B HeqP; induction H; intros B' HeqP Hg;
    try discriminate HeqP; inversion HeqP; subst.
  -  assumption.
  -
    cbn [uskl_to_pskl] in Hg; inversion Hg.
  -
    cbn [uskl_to_pskl] in Hg; inversion Hg.
  -
    eapply ad_ppre__flex_r; [ eassumption | ].
    apply (IHad_partial_precise HwfΘ B' eq_refl).
    match goal with |- guarded_pskl ⌊ ptyp_to_uskl_syn ?τ ⌋ˢ =>
      replace (uskl_to_pskl (ptyp_to_uskl_syn τ)) with (ptyp_to_pskl τ)
        by (symmetry; apply uskl_to_pskl_ptyp)
    end.
    apply mono_ptyp_to_pskl_guarded.
    eapply a_wf_aenv_binds_def_mono; eassumption.
Qed.

Lemma ad_ppre_lift_dot_univ_ghost : forall Θ Δ Ψ P ψ0,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ0 }}ad ->
  Δ ∩ ftvar_in_uskl ψ0 [=] empty ->
  guarded_pskl ⌊ ψ0 ⌋ˢ ->
  (P = pskl_ghost \/ exists B, P = pskl_univ_ghost B) ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (uskl_dot_univ_ghost ψ0) }}ad.
Proof.
  intros Θ Δ Ψ P ψ0 HwfΘ Hpre HΔ Hg Hshape.
  destruct Hshape as [-> | (B & ->)].
  -
    apply ad_ppre__ghost;
      [ eapply ad_ppre_ghost_subject_tags; exact Hpre
      | cbn [ftvar_in_uskl]; exact HΔ ].
  -
    apply ad_ppre__univ_ghost_keep.
    eapply ad_ppre_univ_ghost_strip; eassumption.
Qed.

Lemma ad_partial_precise_src_ftv_avoid : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall α, α `notin` ftvar_in_uskl ψ ->
  α `notin` Δ ->
  (forall τ, ~ binds α (abind_flex_mono_def τ) Θ) ->
  α `notin` def_ftv Θ ->
  α `notin` ftvar_in_pskl P.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros α0 Hψ HΔ Hnf Hdf;
    cbn [ftvar_in_pskl ftvar_in_uskl] in *.
  - clear; fsetdec.
  -  clear - Hψ; fsetdec.
  -
    pose proof (IHad_partial_precise1 α0 ltac:(clear - Hψ; solve_notin_auto) HΔ Hnf Hdf).
    pose proof (IHad_partial_precise2 α0 ltac:(clear - Hψ; solve_notin_auto) HΔ Hnf Hdf).
    clear - H2 H3; fsetdec.
  -
    pick fresh α for (L `union` ftvar_in_pskl P `union` ftvar_in_uskl ψ
                        `union` singleton α0).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α)) as Hup.
    cbn in Hup.
    assert (Hαα0 : α <> α0)
      by (apply not_eq_sym; apply notin_singleton_1; clear - Fr; solve_notin).
    pose proof (H0 α ltac:(clear - Fr; solve_notin) α0
                  ltac:(clear - Hup Hψ Hαα0; solve_notin_auto)
                  ltac:(clear - HΔ Hαα0; solve_notin_auto)
                  ltac:(intros τ0 Hb;
                        destruct (binds_cons_1 _ _ _ _ _ _ Hb)
                          as [[_ Habs] | Hb']; [ discriminate Habs | ];
                        exact (Hnf τ0 Hb'))
                  ltac:(cbn [def_ftv]; exact Hdf)) as Hα.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f α)) as Hlo.
    clear - Hα Hlo; fsetdec.
  -  clear; fsetdec.
  - apply IHad_partial_precise; assumption.
  -
    pick fresh α for (L `union` ftvar_in_pskl P `union` ftvar_in_uskl ψ
                        `union` singleton α0 `union` dom Θ).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α)) as Hup.
    cbn in Hup.
    assert (Hαα0 : α <> α0)
      by (apply not_eq_sym; apply notin_singleton_1; clear - Fr; solve_notin).
    pose proof (H0 α ltac:(clear - Fr; solve_notin) α0
                  ltac:(clear - Hup Hψ Hαα0; solve_notin_auto)
                  HΔ
                  ltac:(intros τ0 Hb;
                        destruct (binds_cons_1 _ _ _ _ _ _ Hb)
                          as [[_ Habs] | Hb']; [ discriminate Habs | ];
                        exact (Hnf τ0 Hb'))
                  ltac:(cbn [def_ftv]; exact Hdf)) as Hα.
    cbn [ftvar_in_pskl] in Hα. clear - Hα; fsetdec.
  - apply IHad_partial_precise; assumption.
  -
    intros Hin.
    assert (Heq : α0 = α) by (clear - Hin; fsetdec); subst.
    exact (Hnf τ H).
  -
    apply IHad_partial_precise; try assumption.
    rewrite ftvar_ptyp_to_uskl_syn.
    intros Hin. apply Hdf.
    pose proof (@def_ftv_binds Θ α τ H) as Hsub. clear - Hsub Hin; fsetdec.
Qed.

Lemma uskl_to_pskl_ftv : forall R,
  ftvar_in_pskl ⌊ R ⌋ˢ [=] ftvar_in_uskl R.
Proof.
  induction R; cbn [uskl_to_pskl ftvar_in_pskl ftvar_in_uskl];
    solve [ clear; fsetdec | fsetdec ].
Qed.

Lemma uskl_rsubst_rename : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  forall α1 α2,
  α1 `notin` dom Θ -> α1 `notin` Δρ ->
  uskl_rsubst NM Θ Δρ Ψρ (subst_uskl_in_uskl (uskl_var_f α2) α1 R')
                      (subst_uskl_in_uskl (uskl_var_f α2) α1 R).
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros α1 α2 HαΘ HαΔ.
  -
    apply ursubst__refl;
      [ apply subst_uskl_in_uskl_lc_uskl; [ exact H | apply lc_uskl_var_f ]
      | exact H0 ].
  -
    assert (Hne : α <> α1) by (intros ->; contradiction).
    assert (Hfr : α1 `notin` ftvar_in_uskl ψ'').
    { pose proof (a_wf_pskl_ftv_dom H1) as Hd.
      rewrite uskl_to_pskl_ftv in Hd. clear - Hd HαΘ; fsetdec. }
    rewrite (@subst_uskl_in_uskl_fresh_eq ψ'' (uskl_var_f α2) α1 Hfr).
    cbn [subst_uskl_in_uskl].
    match goal with |- context [if ?c then _ else _] =>
      destruct c as [Heq | _]; [ subst; contradiction | ] end.
    eapply ursubst__leaf; eassumption.
  -
    cbn [subst_uskl_in_uskl].
    eapply ursubst__arrow; [ apply IHuskl_rsubst1 | apply IHuskl_rsubst2 | exact H1 ];
      assumption.
  -
    cbn [subst_uskl_in_uskl].
    apply ursubst__all_syn with (L := L `union` singleton α1); intros α Hα.
    assert (Hne : α1 <> α) by (apply notin_singleton_1; clear - Hα; solve_notin).
    repeat rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      solve [ apply H0; solve [ clear - Hα; solve_notin | assumption ]
            | exact Hne | apply lc_uskl_var_f ].
  -
    cbn [subst_uskl_in_uskl].
    apply ursubst__all_tag with (L := L `union` singleton α1) (ε := ε);
      intros α Hα.
    assert (Hne : α1 <> α) by (apply notin_singleton_1; clear - Hα; solve_notin).
    repeat rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      solve [ apply H0; solve [ clear - Hα; solve_notin | assumption ]
            | exact Hne | apply lc_uskl_var_f ].
  -  cbn [subst_uskl_in_uskl]; apply ursubst__univ_ghost; auto.
  -  cbn [subst_uskl_in_uskl]; apply ursubst__dot_univ_ghost; auto.
Qed.

Lemma uskl_rsubst_subst_open_rename : forall NM Θ Δρ Ψ R' R ψb β α0 α,
  uskl_rsubst NM Θ (add β Δρ) Ψ
    (subst_uskl_in_uskl ψb β (open_uskl_wrt_uskl R' (uskl_var_f α0)))
    (open_uskl_wrt_uskl R (uskl_var_f α0)) ->
  lc_uskl ψb ->
  α0 `notin` dom Θ `union` Δρ `union` singleton β `union` ftvar_in_uskl R
    `union` ftvar_in_uskl R' `union` ftvar_in_uskl ψb ->
  α `notin` singleton β ->
  uskl_rsubst NM Θ (add β Δρ) Ψ
    (open_uskl_wrt_uskl (subst_uskl_in_uskl ψb β R') (uskl_var_f α))
    (open_uskl_wrt_uskl R (uskl_var_f α)).
Proof.
  intros NM Θ Δρ Ψ R' R ψb β α0 α Hr Hlcb Hα0 Hα.
  assert (Hβα : β <> α) by (intros ->; solve_notin_auto).
  pose proof (uskl_rsubst_rename Hr (α1 := α0) α) as Hren.
  rewrite (@subst_uskl_in_uskl_subst_uskl_in_uskl
             (open_uskl_wrt_uskl R' (uskl_var_f α0)) (uskl_var_f α) ψb β α0)
    in Hren by (cbn [ftvar_in_uskl]; solve_notin_auto).
  rewrite (@subst_uskl_in_uskl_fresh_eq ψb (uskl_var_f α) α0) in Hren
    by solve_notin_auto.
  rewrite <- (@subst_uskl_in_uskl_intro α0 R' (uskl_var_f α)) in Hren
    by solve_notin_auto.
  rewrite <- (@subst_uskl_in_uskl_intro α0 R (uskl_var_f α)) in Hren
    by solve_notin_auto.
  rewrite (@subst_uskl_in_uskl_open_uskl_wrt_uskl_var R' ψb β α Hβα Hlcb).
  apply Hren; solve_notin_auto.
Qed.

Lemma uskl_rsubst_subst_refl : forall NM Θ Δρ R β ψb Ψb,
  lc_uskl R ->
  a_tags_sort NM Ψb ψb ->
  {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψb ⌋ˢ }}a ->
  lc_uskl ψb ->
  exists Ψρ',
    Ψρ' [<=] Ψb /\
    (β `in` ftvar_in_uskl R -> Ψb [<=] Ψρ') /\
    uskl_rsubst NM Θ (add β Δρ) Ψρ' (subst_uskl_in_uskl ψb β R) R.
Proof.
  intros NM Θ Δρ R β ψb Ψb Hlc Htags Hwf Hlcb.
  induction Hlc; cbn [subst_uskl_in_uskl ftvar_in_uskl].
  -
    exists empty; repeat split;
      [ clear; fsetdec | intros Hin; clear - Hin; fsetdec
      | apply ursubst__refl; [ apply lc_uskl_unit | clear; fsetdec ] ].
  -
    match goal with |- context [if ?c then _ else _] =>
      destruct c as [-> | Hne] end.
    + exists Ψb; repeat split;
        [ clear; fsetdec | intros _; clear; fsetdec
        | eapply ursubst__leaf;
            [ clear; fsetdec | exact Htags | exact Hwf | clear; fsetdec ] ].
    + exists empty; repeat split;
        [ clear; fsetdec
        | intros Hin; exfalso; clear - Hin Hne; fsetdec
        | apply ursubst__refl; [ apply lc_uskl_var_f | clear; fsetdec ] ].
  -
    destruct IHHlc1 as (Ψ1 & Hs1 & Hocc1 & Hr1).
    destruct IHHlc2 as (Ψ2 & Hs2 & Hocc2 & Hr2).
    exists (Ψ1 `union` Ψ2); repeat split;
      [ clear - Hs1 Hs2; fsetdec
      | intros Hin;
        destruct (AtomSetProperties.In_dec β (ftvar_in_uskl R1)) as [Hi | Hi];
          [ pose proof (Hocc1 Hi); clear - H; fsetdec
          | assert (Hi2 : β `in` ftvar_in_uskl R2) by (clear - Hin Hi; fsetdec);
            pose proof (Hocc2 Hi2); clear - H; fsetdec ]
      | eapply ursubst__arrow; [ exact Hr1 | exact Hr2 | clear; fsetdec ] ].
  -
    match goal with IH : forall α, _ |- _ =>
      pick fresh α0 for (dom Θ `union` ftvar_in_uskl R `union` singleton β
                           `union` ftvar_in_uskl ψb `union` Δρ);
      destruct (IH α0) as (Ψ1 & Hs1 & Hocc1 & Hr1)
    end.
    exists Ψ1; repeat split.
    + exact Hs1.
    +
      intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      clear - Hin Hlo; fsetdec.
    + apply ursubst__all_syn with (L := dom Θ `union` singleton α0
                                      `union` ftvar_in_uskl R
                                      `union` ftvar_in_uskl ψb
                                      `union` singleton β);
        intros α Hα.
      eapply uskl_rsubst_subst_open_rename with (1 := Hr1).
      * exact Hlcb.
      * clear - Fr. solve_notin_auto.
      * clear - Hα. solve_notin_auto.
  -
    match goal with IH : forall α, _ |- _ =>
      pick fresh α0 for (dom Θ `union` ftvar_in_uskl R `union` singleton β
                           `union` ftvar_in_uskl ψb `union` Δρ);
      destruct (IH α0) as (Ψ1 & Hs1 & Hocc1 & Hr1)
    end.
    exists Ψ1; repeat split.
    + exact Hs1.
    +
      intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      clear - Hin Hlo; fsetdec.
    + apply ursubst__all_tag with (ε := ε) (L := dom Θ `union` singleton α0
                                      `union` ftvar_in_uskl R
                                      `union` ftvar_in_uskl ψb
                                      `union` singleton β);
        intros α Hα.
      eapply uskl_rsubst_subst_open_rename with (1 := Hr1).
      * exact Hlcb.
      * clear - Fr. solve_notin_auto.
      * clear - Hα. solve_notin_auto.
  -
    exists empty; repeat split;
      [ clear; fsetdec | intros Hin; clear - Hin; fsetdec
      | apply ursubst__refl; [ apply lc_uskl_ghost | clear; fsetdec ] ].
  -
    destruct IHHlc as (Ψ1 & Hs1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hocc1 | apply ursubst__univ_ghost; exact Hr1 ].
  -
    exists empty; repeat split;
      [ clear; fsetdec | intros Hin; clear - Hin; fsetdec
      | apply ursubst__refl; [ apply lc_uskl_dot_ghost | clear; fsetdec ] ].
  -
    destruct IHHlc as (Ψ1 & Hs1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hocc1 | apply ursubst__dot_univ_ghost; exact Hr1 ].
Qed.

Lemma arrow_tag_split : forall Ψt Ψt1 Ψt2 Ψi Ψi1 Ψi2 Ψa,
  Ψt [=] Ψt1 `union` Ψt2 ->
  Ψt1 ∩ Ψt2 [=] empty ->
  Ψi [=] Ψi1 `union` Ψi2 ->
  Ψi1 [<=] Ψt1 -> Ψi2 [<=] Ψt2 ->
  Ψi `union` Ψa [=] Ψt ->
  Ψi1 `union` (Ψa ∩ Ψt1) [=] Ψt1 /\
  Ψi2 `union` (Ψa ∩ Ψt2) [=] Ψt2.
Proof.
  intros Ψt Ψt1 Ψt2 Ψi Ψi1 Ψi2 Ψa Ht Hd Hi Hs1 Hs2 Heq.
  split; clear - Ht Hd Hi Hs1 Hs2 Heq; fsetdec.
Qed.

Lemma uskl_rsubst_subst : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  forall β ψb Ψb,
  a_tags_sort NM Ψb ψb ->
  {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψb ⌋ˢ }}a ->
  lc_uskl ψb ->
  β `notin` dom Θ ->
  β `notin` Δρ ->
  exists Ψρ',
    Ψρ' [<=] Ψρ `union` Ψb /\
    Ψρ [<=] Ψρ' /\
    (β `in` ftvar_in_uskl R -> Ψb [<=] Ψρ') /\
    uskl_rsubst NM Θ (add β Δρ) Ψρ' (subst_uskl_in_uskl ψb β R') R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H;
    intros β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ.
  -
    destruct (@uskl_rsubst_subst_refl NM Θ Δρ R β ψb Ψb H Htags Hwfb Hlcb)
      as (Ψ1 & Hs1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ clear - Hs1; fsetdec | clear - H0; fsetdec | exact Hocc1 | exact Hr1 ].
  -
    assert (Hfr : β `notin` ftvar_in_uskl ψ'').
    { pose proof (a_wf_pskl_ftv_dom H1) as Hd.
      rewrite uskl_to_pskl_ftv in Hd. clear - Hd HβΘ; fsetdec. }
    rewrite (@subst_uskl_in_uskl_fresh_eq ψ'' ψb β Hfr).
    exists Ψρ; repeat split;
      [ clear; fsetdec | clear; fsetdec
      |
        intros Hin; exfalso; cbn [ftvar_in_uskl] in Hin;
        assert (Heq : β = α) by (clear - Hin; fsetdec); subst;
        contradiction
      | eapply ursubst__leaf;
          [ clear - H; fsetdec | exact H0 | exact H1 | exact H2 ] ].
  -
    destruct (IHuskl_rsubst1 β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψa1 & Hs1 & Hm1 & Hocc1 & Hr1).
    destruct (IHuskl_rsubst2 β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψa2 & Hs2 & Hm2 & Hocc2 & Hr2).
    exists (Ψa1 `union` Ψa2); repeat split.
    + clear - Hs1 Hs2 H1; fsetdec.
    + clear - Hm1 Hm2 H1; fsetdec.
    + intros Hin; cbn [ftvar_in_uskl] in Hin.
      destruct (AtomSetProperties.In_dec β (ftvar_in_uskl R1)) as [Hi | Hi];
        [ pose proof (Hocc1 Hi); clear - H2; fsetdec
        | assert (Hi2 : β `in` ftvar_in_uskl R2) by (clear - Hin Hi; fsetdec);
          pose proof (Hocc2 Hi2); clear - H2; fsetdec ].
    + cbn [subst_uskl_in_uskl].
      eapply ursubst__arrow; [ exact Hr1 | exact Hr2 | clear; fsetdec ].
  -
    pick fresh α0 for (L `union` dom Θ `union` Δρ `union` singleton β
                         `union` ftvar_in_uskl R `union` ftvar_in_uskl R'
                         `union` ftvar_in_uskl ψb).
    destruct (H0 α0 ltac:(clear - Fr; solve_notin) β ψb Ψb
                Htags Hwfb Hlcb HβΘ HβΔ) as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split.
    + exact Hs1.
    + exact Hm1.
    + intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      cbn [ftvar_in_uskl] in Hin. clear - Hin Hlo; fsetdec.
    + cbn [subst_uskl_in_uskl].
      apply ursubst__all_syn with (L := L `union` dom Θ `union` Δρ
                                       `union` singleton α0
                                       `union` singleton β
                                       `union` ftvar_in_uskl R
                                       `union` ftvar_in_uskl R'
                                       `union` ftvar_in_uskl ψb);
        intros α Hα.
      eapply uskl_rsubst_subst_open_rename with (1 := Hr1).
      * exact Hlcb.
      * clear - Fr. solve_notin_auto.
      * clear - Hα. solve_notin_auto.
  -
    pick fresh α0 for (L `union` dom Θ `union` Δρ `union` singleton β
                         `union` ftvar_in_uskl R `union` ftvar_in_uskl R'
                         `union` ftvar_in_uskl ψb).
    destruct (H0 α0 ltac:(clear - Fr; solve_notin) β ψb Ψb
                Htags Hwfb Hlcb HβΘ HβΔ) as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split.
    + exact Hs1.
    + exact Hm1.
    + intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      cbn [ftvar_in_uskl] in Hin. clear - Hin Hlo; fsetdec.
    + cbn [subst_uskl_in_uskl].
      apply ursubst__all_tag with (ε := ε)
        (L := L `union` dom Θ `union` Δρ `union` singleton α0
                `union` singleton β `union` ftvar_in_uskl R
                `union` ftvar_in_uskl R' `union` ftvar_in_uskl ψb);
        intros α Hα.
      eapply uskl_rsubst_subst_open_rename with (1 := Hr1).
      * exact Hlcb.
      * clear - Fr. solve_notin_auto.
      * clear - Hα. solve_notin_auto.
  -
    destruct (IHuskl_rsubst β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hm1 | exact Hocc1
      | cbn [subst_uskl_in_uskl]; apply ursubst__univ_ghost; exact Hr1 ].
  -
    destruct (IHuskl_rsubst β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hm1 | exact Hocc1
      | cbn [subst_uskl_in_uskl]; apply ursubst__dot_univ_ghost; exact Hr1 ].
Qed.

Lemma a_solve_sub_complete_rsubst_var :
  forall NM m Θ0 Θ Θw κ Δ Δρ Ψ' Ψi Ψa α Pi P0,
  {{ ⊢ Θ }}a ->
  a_tags_sort NM Ψ' (uskl_var_f α) ->
  Ψi `union` Ψa [<=] Ψ' ->
  rsubst_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  α `in` Δρ ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_var_f α) }}ad ->
  forall L,
  solve_sub_ext Θ0 Θw m Pi P0 L
    (fun κ' Pa =>
       {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] (uskl_var_f α) }}ad).
Proof.
  intros NM m Θ0 Θ Θw κ Δ Δρ Ψ' Ψi Ψa α Pi P0
    HwfΘ Htags Hsub Hfresh Hdelta HαΔρ Hapart HwfPi Hpre L.
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
  eapply solve_sub_ext_nil with (Pa := Pi);
    [ rewrite HeqPi; apply a_solve_sub__var
    | exact HwfPi
    | cbn [app]; rewrite Heqm;
      apply ad_ppre__var; clear - HΨie HΨae; fsetdec ].
Qed.

Lemma uskl_rsubst_ftag_target_sub : forall NM Θ Δρ Ψρ R' R,
  uskl_rsubst NM Θ Δρ Ψρ R' R ->
  ftag_in_uskl R [<=] ftag_in_uskl R'.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; cbn [ftag_in_uskl];
    try solve [ clear; fsetdec | clear - IHuskl_rsubst; fsetdec
              | clear - IHuskl_rsubst1 IHuskl_rsubst2; fsetdec ].
  -
    pick fresh α for L.
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    rewrite (ftag_in_uskl_open_var R α) in Hα.
    rewrite (ftag_in_uskl_open_var R' α) in Hα.
    exact Hα.
  -
    pick fresh α for L.
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    rewrite (ftag_in_uskl_open_var R α) in Hα.
    rewrite (ftag_in_uskl_open_var R' α) in Hα.
    clear - Hα; fsetdec.
Qed.

Lemma ad_ppre_guarded_all_tag_absurd : forall Θ0 Θ κ Δ Ψ Ψd P ε ψ,
  {{ ⊢ Θ }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  guarded_pskl P ->
  d_tags_skl Ψd (uskl_all_tag ε ψ) ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ P) ⊑ᵖ[ Ψ ] (uskl_all_tag ε ψ) }}ad ->
  False.
Proof.
  intros Θ0 Θ κ Δ Ψ Ψd P ε ψ HwfΘ Hκ Hg Hd Hpre.
  destruct Hg as [ | α | P1 P2 Hlc1 Hlc2 ]; cbn [msubst_pskl] in Hpre.
  - inversion Hpre.
  - assert (HΨde : Ψd [=] empty)
      by (eapply ad_partial_precise_mono_subject_target_tags_empty;
            [ exact HwfΘ | exact Hpre | reflexivity
            | eapply a_inc_lookup_mono; exact Hκ | exact Hd ]).
    destruct (d_tags_skl_all_tag_inv Hd) as (Ld & Ψ0 & _ & _ & Heq).
    assert (Hin : ε `in` empty) by (clear - HΨde Heq; fsetdec).
    clear - Hin; fsetdec.
  - inversion Hpre.
Qed.

Lemma arrow_grid : forall NM M Θ0 Θ Θw κ Δ Δρ Ψt Ψi Ψa ψ1 ψ2 Pi P01 P02,
  {{ ⊢ Θ }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  a_tags_sort NM Ψt (uskl_arrow ψ1 ψ2) ->
  Ψi `union` Ψa [=] Ψt ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P01 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P02 }}a ->
  (forall Pi1 Pi2 Ψi1 Ψi2 L,
     {{ Θ0 ⨟ empty ⊢ₚₛ Pi1 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi2 }}a ->
     (forall α, α `in` Δρ ->
        α `notin` pskl_shielded_ftv (msubst_pskl κ Pi1)) ->
     (forall α, α `in` Δρ ->
        α `notin` pskl_shielded_ftv (msubst_pskl κ Pi2)) ->
     Ψi [=] Ψi1 `union` Ψi2 ->
     {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi1) ⊑ᵖ[ Ψi1 ] ψ1 }}ad ->
     {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi2) ⊑ᵖ[ Ψi2 ] ψ2 }}ad ->
     exists Ξ1 Ξ2 Pa1 Pa2 κ1 κ2,
       {{ Θ0 ⊢ₑ Pi1 ∼ P01 ⤳ Ξ1 ⨾ Pa1 }}a /\
       {{ (Ξ1 ++ Θ0) ⊢ₛ Pi2 ≼[ M ] P02 ⤳ Ξ2 ⨾ Pa2 }}a /\
       all_flex_mono (Ξ2 ++ Ξ1) /\
       uniq (Ξ2 ++ Ξ1) /\
       keys (κ2 ++ κ1) = keys (Ξ2 ++ Ξ1) /\
       (forall α, α `in` dom (Ξ2 ++ Ξ1) -> α `notin` L) /\
       Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) (κ2 ++ κ1) /\
       {{ ((Ξ2 ++ Ξ1) ++ Θ0) ⨟ empty ⊢ₚₛ Pa1 }}a /\
       {{ ((Ξ2 ++ Ξ1) ++ Θ0) ⨟ empty ⊢ₚₛ Pa2 }}a /\
       {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl ((κ2 ++ κ1) ++ κ) (pskl_arrow Pa1 Pa2))
         ⊑ᵖ[ Ψi `union` Ψa ] (uskl_arrow ψ1 ψ2) }}ad) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_arrow ψ1 ψ2) }}ad ->
  forall L,
  solve_sub_ext Θ0 Θw (mode_fn M) Pi (pskl_arrow P01 P02) L
    (fun κ' Pa =>
       {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa)
         ⊑ᵖ[ Ψi `union` Ψa ] (uskl_arrow ψ1 ψ2) }}ad).
Proof.
  intros NM M Θ0 Θ Θw κ Δ Δρ Ψt Ψi Ψa ψ1 ψ2 Pi P01 P02
         HwfΘ Hκ Htags Htageq HwfP01 HwfP02 KEY.
  revert Ψi Ψa Htageq KEY.
  induction Pi as [ | nPi | β | Pi1 IH1 Pi2 IH2 | Pi0 IH0 | | Pi0 IH0 ];
    intros Ψi Ψa Htageq KEY HwfPi Hapart Hpre L;
    cbn [msubst_pskl] in Hpre.
  -  inversion Hpre.
  -  inversion HwfPi.
  -
    assert (Hml : mono_ptyp (msubst_lookup κ β))
      by (eapply a_inc_lookup_mono; exact Hκ).
    assert (HΨte : Ψt [=] empty)
      by (eapply ad_partial_precise_mono_subject_target_tags_empty;
            [ exact HwfΘ | exact Hpre | reflexivity | exact Hml
            | exact (a_tags_sort_d_tags Htags) ]).
    eapply solve_sub_ext_nil with (Pa := pskl_var_f β);
      [ apply a_solve_sub__var
      | exact HwfPi
      | cbn [app msubst_pskl];
        eapply ad_partial_precise_psi_cong;
          [ exact Hpre | clear - Htageq HΨte; fsetdec ] ].
  -
    inversion Hpre; subst.
    match goal with
      Hp1 : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ Pi1 ⊑ᵖ[ ?Ψa1 ] ψ1 }}ad,
      Hp2 : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ Pi2 ⊑ᵖ[ ?Ψa2 ] ψ2 }}ad,
      Hun : Ψi [=] _ |- _ =>
      destruct (KEY Pi1 Pi2 Ψa1 Ψa2 L
                  ltac:(inversion HwfPi; assumption)
                  ltac:(inversion HwfPi; assumption)
                  ltac:(intros α0 Hα0; pose proof (Hapart α0 Hα0) as Hs;
                        cbn [msubst_pskl pskl_shielded_ftv] in Hs;
                        clear - Hs; solve_notin_auto)
                  ltac:(intros α0 Hα0; pose proof (Hapart α0 Hα0) as Hs;
                        cbn [msubst_pskl pskl_shielded_ftv] in Hs;
                        clear - Hs; solve_notin_auto)
                  Hun Hp1 Hp2)
        as (Ξ1 & Ξ2 & Pa1 & Pa2 & κ1 & κ2
            & Hs1 & Hs2 & Hfm & Hu & Hk & Hfr & HF & Hw1 & Hw2 & Hp)
    end.
    exists (Ξ2 ++ Ξ1), (pskl_arrow Pa1 Pa2), (κ2 ++ κ1).
    repeat split; try assumption.
    + apply a_solve_sub__arrow; assumption.
    + apply a_wf_pskl__arrow; assumption.
  -  inversion Hpre.
  -
    inversion Hpre; subst.
    match goal with Hd : Δ ∩ ftvar_in_uskl (uskl_arrow ψ1 ψ2) [=] empty,
                    He : Ψi [=] empty |- _ =>
      destruct (KEY pskl_ghost pskl_ghost empty empty L
                  (a_wf_pskl__ghost Θ0 empty) (a_wf_pskl__ghost Θ0 empty)
                  ltac:(intros α0 Hα0; cbn; clear; solve_notin_auto)
                  ltac:(intros α0 Hα0; cbn; clear; solve_notin_auto)
                  ltac:(clear - He; solve_notin_auto)
                  ltac:(cbn [msubst_pskl]; apply ad_ppre__ghost;
                        [ clear; solve_notin_auto
                        | cbn [ftvar_in_uskl] in Hd; clear - Hd; solve_notin_auto ])
                  ltac:(cbn [msubst_pskl]; apply ad_ppre__ghost;
                        [ clear; solve_notin_auto
                        | cbn [ftvar_in_uskl] in Hd; clear - Hd; solve_notin_auto ]))
        as (Ξ1 & Ξ2 & Pa1 & Pa2 & κ1 & κ2
            & Hs1 & Hs2 & Hfm & Hu & Hk & Hfr & HF & Hw1 & Hw2 & Hp)
    end.
    exists (Ξ2 ++ Ξ1), (pskl_univ_ghost (pskl_arrow Pa1 Pa2)), (κ2 ++ κ1).
    repeat split; try assumption.
    + apply a_solve_sub__ghost_l_fn; assumption.
    + apply a_wf_pskl__univ_ghost.
      * apply guarded_pskl__arrow; eapply a_wf_pskl_lc; eassumption.
      * rewrite aenv_minus_empty. apply a_wf_pskl__arrow; assumption.
    + cbn [msubst_pskl] in Hp |- *.
      apply ad_ppre__univ_ghost_remove; exact Hp.
  -
    inversion Hpre; subst.
    match goal with Hbody : {{ _ ⨟ _ ⊢ˢ msubst_pskl κ Pi0 ⊑ᵖ[ Ψi ] _ }}ad |- _ =>
      destruct (IH0 Ψi Ψa Htageq KEY
                  ltac:(eapply a_wf_pskl_univ_ghost_inv; exact HwfPi)
                  ltac:(intros α0 Hα0; pose proof (Hapart α0 Hα0) as Hs;
                        cbn [msubst_pskl pskl_shielded_ftv] in Hs;
                        pose proof (pskl_shielded_ftv_sub_ftv
                                      (msubst_pskl κ Pi0)) as Hle;
                        clear - Hs Hle; fsetdec)
                  Hbody L)
        as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hw & Hp)
    end.
    exists Ξ, (pskl_univ_ghost Pa), κ'.
    repeat split; try assumption.
    + apply a_solve_sub__univ_ghost_l; exact Hs.
    + apply a_wf_pskl__univ_ghost.
      * eapply (proj1 a_solve_sub_eq_guarded).
        -- exact Hs.
        -- eapply a_wf_pskl_lc. eapply a_wf_pskl_univ_ghost_inv; exact HwfPi.
        -- apply lc_pskl_arrow; eapply a_wf_pskl_lc; eassumption.
        -- inversion HwfPi; assumption.
      * rewrite aenv_minus_empty; exact Hw.
    + cbn [msubst_pskl]. apply ad_ppre__univ_ghost_remove; exact Hp.
Qed.

Lemma pskl_shielded_ftv_close_rec_upper : forall P β k,
  pskl_shielded_ftv (close_pskl_wrt_pskl_rec k β P) [<=] pskl_shielded_ftv P.
Proof.
  induction P; intros β k; cbn [close_pskl_wrt_pskl_rec pskl_shielded_ftv];
    try solve [ clear; fsetdec ].
  - destruct (lt_ge_dec n k); cbn [pskl_shielded_ftv]; clear; fsetdec.
  - destruct (β == α); cbn [pskl_shielded_ftv]; clear; fsetdec.
  - specialize (IHP1 β k); specialize (IHP2 β k); fsetdec.
  - apply IHP.
  - pose proof (ftvar_in_pskl_close_pskl_wrt_pskl_rec P β k) as Hcl.
    clear - Hcl; fsetdec.
Qed.

Lemma pskl_shielded_ftv_close_upper : forall P β,
  pskl_shielded_ftv (close_pskl_wrt_pskl β P) [<=] pskl_shielded_ftv P.
Proof.
  intros P β; unfold close_pskl_wrt_pskl;
    apply pskl_shielded_ftv_close_rec_upper.
Qed.

Lemma solve_eq_generated_not_dom : forall Θ P Q Ξ P' (β0 : atom),
  {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a -> β0 `in` dom Θ -> β0 `notin` dom Ξ.
Proof.
  intros Θ P Q Ξ P' β0 H Hdom Hc.
  assert (Hgf : β0 `notin` ftvar_in_aenv Θ)
    by (eapply a_solve_eq_generated_fresh; eassumption).
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hds.
  clear - Hgf Hds Hdom; fsetdec.
Qed.

Lemma in_dom_app_r : forall (x : atom) (E F : aenv),
  x `in` dom F -> x `in` dom (E ++ F).
Proof. intros x E F H; rewrite dom_app; clear - H; fsetdec. Qed.

Lemma solve_binder_apart_dom : forall (b β0 : atom) (Θ : aenv) S,
  b `notin` S ->
  ftvar_in_aenv Θ [<=] S ->
  β0 `in` dom Θ ->
  β0 `notin` singleton b.
Proof.
  intros b β0 Θ S Hfr Hsub Hdom.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hds.
  clear - Hfr Hsub Hdom Hds; fsetdec.
Qed.

Lemma a_solve_sub_eq_unshielded :
  (forall Θ m P Q Ξ P', {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
     forall β0, β0 `in` dom Θ ->
     β0 `notin` pskl_shielded_ftv P -> β0 `notin` ftvar_in_pskl Q ->
     β0 `notin` pskl_shielded_ftv P') /\
  (forall Θ P Q Ξ P', {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
     forall β0, β0 `in` dom Θ ->
     β0 `notin` pskl_shielded_ftv P -> β0 `notin` ftvar_in_pskl Q ->
     β0 `notin` pskl_shielded_ftv P').
Proof.
  apply a_solve_sub_eq_mutind; intros;
    match goal with Hd : _ `in` dom _ |- _ => rename Hd into Hdom end;
    match goal with Hs : _ `notin` pskl_shielded_ftv _ |- _ =>
      rename Hs into Hsh end;
    match goal with Hf : _ `notin` ftvar_in_pskl _ |- _ =>
      rename Hf into Hft end;
    cbn [pskl_shielded_ftv ftvar_in_pskl] in Hsh, Hft |- *;
    try solve [ clear; fsetdec ];
    try solve [ assumption ].
  -
    match goal with
    | Hfr : ?b `notin` ?S,
      IH : forall b0, b0 `in` dom _ -> _ |- _ =>

      match S with context [ftvar_in_aenv _] => idtac end;
      pose proof (pskl_shielded_ftv_close_upper P' b) as Hcl;
      pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f b)) as Hop;
      cbn [ftvar_in_pskl] in Hop;
      assert (Hne : β0 `notin` singleton b)
        by (match goal with Hd : _ `in` dom ?T |- _ =>
              eapply (@solve_binder_apart_dom b β0 T S);
                [ exact Hfr | clear; fsetdec | exact Hd ] end);
      enough (Hbody : β0 `notin` pskl_shielded_ftv P')
        by (clear - Hbody Hcl; fsetdec);
      apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh Hop Hne; fsetdec | exact Hft ]
    end.
  -
    match goal with Hp : {{ _ ⊢ₛ _ ≼[ _ ] _ ⤳ _ ⨾ _ }}a |- _ =>
      intro Hin; destruct (a_solve_sub_ftv Hp Hin) as [Hl | Hr];
        [ clear - Hl Hsh Hft; fsetdec | clear - Hr Hdom; fsetdec ]
    end.
  -
    match goal with IH : forall b0, b0 `in` dom _ -> _ |- _ =>
      apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | exact Hsh | exact Hft ] end.
  -
    match goal with
    | Hfr : ?b `notin` ?S,
      IH : forall b0, b0 `in` dom _ -> _ |- _ =>

      match S with context [ftvar_in_aenv _] => idtac end;
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
        as Hop;
      cbn [ftvar_in_pskl] in Hop;
      assert (Hne : β0 `notin` singleton b)
        by (match goal with Hd : _ `in` dom ?T |- _ =>
              eapply (@solve_binder_apart_dom b β0 T S);
                [ exact Hfr | clear; fsetdec | exact Hd ] end);
      apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | exact Hsh | clear - Hft Hop Hne; fsetdec ]
    end.
  -
    apply notin_union_3;
      [ match goal with
        | IH : forall b0, _ -> _ -> _ -> _ `notin` pskl_shielded_ftv ?X
          |- _ `notin` pskl_shielded_ftv ?X =>
          apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh; fsetdec | clear - Hft; fsetdec ]
        end
      | match goal with
        | IH : forall b0, _ -> _ -> _ -> _ `notin` pskl_shielded_ftv ?X
          |- _ `notin` pskl_shielded_ftv ?X =>
          apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh; fsetdec | clear - Hft; fsetdec ]
        end ].
  -
    match goal with
    | He : {{ _ ⊢ₑ _ ∼ _ ⤳ ?X1 ⨾ _ }}a, Hs : {{ _ ⊢ₛ _ ≼[ _ ] _ ⤳ _ ⨾ _ }}a |- _ =>
      pose proof (a_solve_eq_ftv He) as Hfe;
      cbn [ftvar_in_pskl] in Hfe;
      assert (HβΞ1 : β0 `notin` dom X1)
        by (eapply solve_eq_generated_not_dom; eassumption);
      apply notin_union_3;
        [ clear - Hfe Hft HβΞ1; fsetdec
        | intro Hin; destruct (a_solve_sub_ftv Hs Hin) as [Hl | Hr];
            [ cbn [ftvar_in_pskl] in Hl; clear - Hl Hft; fsetdec
            | rewrite dom_app in Hr; clear - Hr Hdom; fsetdec ] ]
    end.
  -
    pose proof (pskl_shielded_ftv_ptyp_to_pskl A) as He.
    clear - He; fsetdec.
  -
    pose proof (pskl_shielded_ftv_sub_ftv Q) as Hle.
    clear - Hle Hft; fsetdec.
  -
    apply notin_union_3;
      [ match goal with
        | IH : forall b0, _ -> _ -> _ -> _ `notin` pskl_shielded_ftv ?X
          |- _ `notin` pskl_shielded_ftv ?X =>
          apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh; fsetdec | clear - Hft; fsetdec ]
        end
      | match goal with
        | IH : forall b0, _ -> _ -> _ -> _ `notin` pskl_shielded_ftv ?X
          |- _ `notin` pskl_shielded_ftv ?X =>
          apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh; fsetdec | clear - Hft; fsetdec ]
        end ].
  -
    match goal with
    | Hfr : ?b `notin` ?S,
      IH : forall b0, b0 `in` dom _ -> _ |- _ =>

      match S with context [ftvar_in_aenv _] => idtac end;
      pose proof (pskl_shielded_ftv_close_upper P' b) as Hcl;
      pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f b)) as HopP;
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f b))
        as HopQ;
      cbn [ftvar_in_pskl] in HopP, HopQ;
      assert (Hne : β0 `notin` singleton b)
        by (match goal with Hd : _ `in` dom ?T |- _ =>
              eapply (@solve_binder_apart_dom b β0 T S);
                [ exact Hfr | clear; fsetdec | exact Hd ] end);
      enough (Hbody : β0 `notin` pskl_shielded_ftv P')
        by (clear - Hbody Hcl; fsetdec);
      apply IH;
        [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh HopP Hne; fsetdec
        | clear - Hft HopQ Hne; fsetdec ]
    end.
  -
    match goal with Hp : {{ _ ⊢ₑ _ ∼ _ ⤳ ?X ⨾ _ }}a |- _ =>
      pose proof (a_solve_eq_ftv Hp) as Hfe;
      assert (HβΞ : β0 `notin` dom X)
        by (eapply solve_eq_generated_not_dom; eassumption);
      clear - Hfe Hsh Hft HβΞ; fsetdec
    end.
  -
    match goal with
    | Hfr : ?b `notin` ?S,
      IH : forall b0, b0 `in` dom _ -> _ |- _ =>

      match S with context [ftvar_in_aenv _] => idtac end;
      pose proof (pskl_shielded_ftv_close_upper P' b) as Hcl;
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f b))
        as HopQ;
      cbn [ftvar_in_pskl] in HopQ;
      assert (Hne : β0 `notin` singleton b)
        by (match goal with Hd : _ `in` dom ?T |- _ =>
              eapply (@solve_binder_apart_dom b β0 T S);
                [ exact Hfr | clear; fsetdec | exact Hd ] end);
      enough (Hbody : β0 `notin` pskl_shielded_ftv P')
        by (clear - Hbody Hcl; fsetdec);
      apply IH;
        [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | cbn [pskl_shielded_ftv]; exact Hsh
        | clear - Hft HopQ Hne; fsetdec ]
    end.
  -
    match goal with IH : forall b0, b0 `in` dom _ -> _ |- _ =>
      apply IH;
        [ exact Hdom
        | match goal with |- _ `notin` pskl_shielded_ftv ?X =>
            pose proof (pskl_shielded_ftv_sub_ftv X) as Hle;
            clear - Hsh Hle; fsetdec end
        | exact Hft ]
    end.
  -
    match goal with
    | Hfr : ?b `notin` ?S,
      IH : forall b0, b0 `in` dom _ -> _ |- _ =>

      match S with context [ftvar_in_aenv _] => idtac end;
      pose proof (pskl_shielded_ftv_close_upper P' b) as Hcl;
      pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f b)) as HopP;
      cbn [ftvar_in_pskl] in HopP;
      assert (Hne : β0 `notin` singleton b)
        by (match goal with Hd : _ `in` dom ?T |- _ =>
              eapply (@solve_binder_apart_dom b β0 T S);
                [ exact Hfr | clear; fsetdec | exact Hd ] end);
      enough (Hbody : β0 `notin` pskl_shielded_ftv P')
        by (clear - Hbody Hcl; fsetdec);
      apply IH;
        [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh HopP Hne; fsetdec
        | cbn [ftvar_in_pskl]; exact Hft ]
    end.
  -
    match goal with IH : forall b0, b0 `in` dom _ -> _ |- _ =>
      apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | exact Hsh | cbn [ftvar_in_pskl]; exact Hft ]
    end.
Qed.

Lemma a_wf_pskl_shielded_delta : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall α, α `in` Δ -> α `notin` pskl_shielded_ftv P.
Proof.
  intros Θ Δ P H; induction H; intros α0 Hα0; cbn [pskl_shielded_ftv];
    try solve [ clear; fsetdec ].
  - pose proof (IHa_wf_pskl1 α0 Hα0); pose proof (IHa_wf_pskl2 α0 Hα0).
    clear - H1 H2; fsetdec.
  - pick fresh β for (L `union` singleton α0).
    pose proof (H0 β ltac:(clear - Fr; solve_notin_auto) α0
                  ltac:(clear - Hα0; fsetdec)) as Hb.
    pose proof (pskl_shielded_ftv_open_lower P (pskl_var_f β)) as Hlo.
    clear - Hb Hlo; fsetdec.
  - intro Hin.
    pose proof (a_wf_pskl_ftv_dom H0) as Hd.
    assert (Hγd : α0 `in` dom (aenv_minus Θ Δ)) by (clear - Hd Hin; fsetdec).
    destruct (@dom_aenv_minus α0 Θ Δ Hγd) as [_ Hn]. contradiction.
Qed.

Lemma a_wf_pskl_tvar_to_delta_gen : forall Θ Δ P β,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  β `notin` pskl_shielded_ftv P ->
  {{ Θ ⨟ (add β Δ) ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P β H; induction H; intros Hsh; cbn [pskl_shielded_ftv] in Hsh.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var; exact H.
  - apply a_wf_pskl__arrow;
      [ apply IHa_wf_pskl1; clear - Hsh; fsetdec
      | apply IHa_wf_pskl2; clear - Hsh; fsetdec ].
  - apply a_wf_pskl__all with (L := L `union` singleton β).
    intros α Hα.
    eapply a_wf_pskl_delta_mono;
      [ apply H0; [ clear - Hα; fsetdec
                  | pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f α))
                      as Hop; cbn [ftvar_in_pskl] in Hop;
                    clear - Hsh Hop Hα; fsetdec ]
      | intros; clear - H2; fsetdec ].
  - apply a_wf_pskl__ghost.
  -
    apply a_wf_pskl__univ_ghost; [ exact H | ].
    eapply a_wf_pskl_tvar_mono_ftv; [ exact H0 | ].
    intros α Hα Hb.
    apply a_binds_tvar_aenv_minus in Hb; destruct Hb as [Hb Hn].
    apply a_binds_tvar_aenv_minus; split; [ exact Hb | ].
    clear - Hα Hn Hsh; fsetdec.
Qed.

Lemma a_wf_pskl_tvar_to_delta : forall Θ1 β Θ2 Δ P,
  {{ (Θ1 ++ (β ~ abind_tvar) ++ Θ2) ⨟ Δ ⊢ₚₛ P }}a ->
  β `notin` pskl_shielded_ftv P ->
  {{ ((β ~ abind_tvar) ++ Θ1 ++ Θ2) ⨟ (add β Δ) ⊢ₚₛ P }}a.
Proof.
  intros Θ1 β Θ2 Δ P H Hsh.
  apply a_wf_pskl_tvar_to_delta_gen; [ | exact Hsh ].
  eapply a_wf_pskl_tvar_mono; [ exact H | ].
  intros α [Hb | [Hb | [τ Hb]]]; unfold a_binds_tvar;
    [ left | right; left | right; right; exists τ ];
    apply binds_mid_to_front; exact Hb.
Qed.

Theorem a_solve_sub_complete_var :
  forall n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  (forall α, a_flex_tvar Θ0 α ->
     ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θw) ->
  Δρ ∩ dom Θw [=] empty ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  κ ∷ Θ0 ⊑ Θ ->
  uskl_rsubst NM Θ Δρ Ψρ ψsub ψa ->
  a_tags_sort NM Ψ' ψa ->
  {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψsub ⌋ˢ }}a ->
  Ψi `union` Ψa [=] Ψ' ->
  Ψρ ∩ Ψ' [=] empty ->
  rsubst_fresh Δρ Θ κ -> Δρ [<=] Δ ->
  (forall α, α `in` Δρ ->
     α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  (forall x b, binds x b Θs -> binds x b Θ) ->
  ad_pat_sub_fuel n NM M Ψsub Θs ψsub Q ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  solve_sub_ext Θ0 Θw M Pi P0 L
    (fun κ' Pa =>
       {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad).
Proof.
  intros n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HwfΘ HwfΘ0 HwfΘw Hmon Hnr Hκw HΔρw
         HwfPi HwfP0 HmodSK HmodTY Hκ Hrho Htags HwfSub
         Htageq Hinter Hrhof Hdelta Hapart Hdfresh Hpre
         HΨs1 HΨs2 Hext Hsub Hrefine.
  revert Θ Θ0 κ Δ Δρ Ψρ Ψ' Ψi Ψa ψa Pi P0
         HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
         HwfPi HwfP0 HmodSK HmodTY Hκ Hrho Htags HwfSub
         Htageq Hinter Hrhof Hdelta Hapart Hdfresh Hpre
         HΨs1 HΨs2 Hext Hrefine.
  induction Hsub; intros
    Θe Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa ψa Pi P0
    HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
    HwfPi HwfP0 HmodSK HmodTY Hκ Hrho Htags HwfSub
    Htageq Hinter Hrhof Hdelta Hapart Hdfresh Hpre
    HΨs1 HΨs2 Hext Hrefine Lav HLav;
    rename Θ into Θsm; rename Θe into Θ.
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
  -
    assert (HP0 : P0 = pskl_ghost).
    { destruct NM;
        [ pose proof (HmodTY eq_refl) as Hm | pose proof (HmodSK eq_refl) as Hm ];
        inversion Hm; reflexivity. }
    subst P0.

    eapply solve_sub_ext_nil with (Pa := Pi);
      [ apply a_solve_sub_vacuous_gen | exact HwfPi | cbn [app] ].
    eapply ad_partial_precise_psi_cong; [ exact Hpre | ].
    assert (HPsiae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
    clear - HPsiae; fsetdec.
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
      - pose proof (a_wf_pskl_lc HwfP0) as Hlc; inversion Hlc; subst.
        apply guarded_pskl__arrow; assumption.
      -
        exfalso.
        assert (HgQ : guarded_bskl (pskl_to_bskl_inh B))
          by (apply guarded_pskl_to_bskl_inh; exact H0).
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        destruct B; cbn [pskl_to_bskl_inh] in Hrefine, HgQ;
          try solve [ inversion HgQ ];
          inversion Hrefine; subst;
          solve [
                  eapply ad_refine_allinh_lhs_mono_absurd;
                    [ exact HwfΘ | eassumption | reflexivity | reflexivity
                    | eapply a_wf_aenv_binds_def_mono;
                        [ exact HwfΘ | eassumption ] ] ]. }

    destruct (@a_solve_eq_complete_var_at a_sub_mode_ty Θ0 Θ Θw κ Δ Δρ Ψρ Ψt
                Ψi Ψa Ψ T ψa (pskl_to_bskl_inh B) Pi P0
                HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfPi HwfP0 Hκ Hκw Hrho Htags
                ltac:(clear - Htageq; solve_notin_auto) Hinter Hrhof Hdelta Hapart
                Hdfresh Hpre HΨs1 HΨs2 (ad_consis_join_consis H1)
                Hrefine Lav HLav)
      as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hp).
    assert (HwfPa : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a)
      by (eapply a_solve_eq_wf; eassumption).

    destruct Pi as [ | nPi | β | Pi1 Pi2 | Pi' | | Pi' ].
    +
      exists Ξ, Pa, κ'. repeat split; try assumption.
      apply a_solve_sub__check; auto using guarded_pskl__unit.
    + inversion HwfPi.
    +
      exists Ξ, Pa, κ'. repeat split; try assumption.
      apply a_solve_sub__check; auto using guarded_pskl__var.
    +
      pose proof (a_wf_pskl_lc HwfPi) as Hlc; inversion Hlc; subst.
      exists Ξ, Pa, κ'. repeat split; try assumption.
      apply a_solve_sub__check; auto using guarded_pskl__arrow.
    +
      exfalso.
      cbn [msubst_pskl] in Hpre.
      inversion Hpre; subst.
      *
        inversion Hrho; subst;
          match goal with Hg : guarded_uskl _ |- _ => inversion Hg end.
      *
        eapply ad_ppre_allsyn_subject_mono_absurd;
          [ exact HwfΘ | eassumption | reflexivity | reflexivity
          | eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ] ].
    +
      destruct (a_solve_eq_ghost_subject_inv Hs) as [-> ->].
      assert (Hκnil : κ' = nil)
        by (destruct κ' as [ | p κ0 ]; [ reflexivity | discriminate Hk ]).
      subst κ'. cbn [app] in Hp.
      eapply solve_sub_ext_nil with (Pa := pskl_univ_ghost P0);
        [ apply a_solve_sub__ghost_l; eassumption
        | apply a_wf_pskl__univ_ghost;
            [ exact HgP0 | rewrite aenv_minus_empty; exact HwfP0 ]
        | cbn [app msubst_pskl]; apply ad_ppre__univ_ghost_remove; exact Hp ].
    +
      assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
      assert (HwfPi' : {{ Θ0 ⨟ empty ⊢ₚₛ Pi' }}a)
        by (eapply a_wf_pskl_univ_ghost_inv; exact HwfPi).
      inversion Hs; subst;
        try solve [ inversion HgP0
                  | match goal with Hng : nonghost_pskl _ |- _ =>
                      inversion Hng end ].
      match goal with Hbody : {{ Θ0 ⊢ₑ Pi' ∼ _ ⤳ _ ⨾ _ }}a |- _ =>
        exists Ξ, (pskl_univ_ghost Pa), κ';
        repeat split; try assumption
      end.
      * apply a_solve_sub__univ_ghost_l. apply a_solve_sub__check; assumption.
      * apply a_wf_pskl__univ_ghost.
        -- eapply (proj2 a_solve_sub_eq_guarded); eauto using a_wf_pskl_lc.
        -- rewrite aenv_minus_empty; exact HwfPa.
      * cbn [msubst_pskl]. apply ad_ppre__univ_ghost_remove. exact Hp.
  -
    pose proof (HmodTY eq_refl) as Hmod.
    inversion Hmod as [ | A HeqA | ]; subst.

    assert (Hng : guarded_pskl (ptyp_to_pskl A) -> False).
    { intros Hg.
      assert (Hbad : guarded_bskl (bskl_all_inh B)).
      { eapply ad_refine_syn_guarded_r_all.
        - exact HwfΘ.
        - exact Hrefine.
        - apply guarded_pskl_to_bskl_inh.
          eapply guarded_pskl_msubst_inc; eassumption.
        - eexists; left; reflexivity. }
      inversion Hbad. }
    destruct A as [ | nA | αA | A1 A2 | A0 ];
      cbn [ptyp_to_pskl] in HwfP0, Hrefine, Hapart, Hpre, Hng |- *.
    +  exfalso. apply Hng. apply guarded_pskl__unit.
    +  inversion HwfP0.
    +  exfalso. apply Hng. apply guarded_pskl__var.
    +
      exfalso. apply Hng.
      pose proof (a_wf_pskl_lc HwfP0) as Hlc; inversion Hlc; subst.
      apply guarded_pskl__arrow; assumption.
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
           `union` ftvar_in_aenv Θ0
           `union` dom κ `union` ftvar_in_uskl ψa `union` ftvar_in_pskl Pi
           `union` ftvar_in_pskl (ptyp_to_pskl A0) `union` def_ftv Θ
           `union` Δ).
      assert (HβΘ : β `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (HβΘ0 : β `notin` dom Θ0) by (clear - Fr; solve_notin).
      assert (Hβκ : β `notin` dom κ) by (clear - Fr; solve_notin).
      assert (Hβψa : β `notin` ftvar_in_uskl ψa) by (clear - Fr; solve_notin).
      assert (Hwfβ : {{ ⊢ ((β ~ abind_tvar) ++ Θ) }}a)
        by (apply a_wf_aenv__tvar; assumption).
      assert (Hwfβ0 : {{ ⊢ ((β ~ abind_tvar) ++ Θ0) }}a)
        by (apply a_wf_aenv__tvar; assumption).
      assert (Hweak : forall (x : atom) (b : abind),
                binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
        by (intros x b Hb; apply binds_app_3; exact Hb).
      destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HβΘ)
        as (HβΘw & Hmonβ & Hnrβ & Hκwβ).

      assert (HLavβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β Lav)
        by (rewrite ftvar_in_aenv_cons_tvar; clear - HLav; fsetdec).
      assert (HwfP0β : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                ⊢ₚₛ (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f β)) }}a).
      { eapply a_wf_pskl_delta_mono;
          [ apply (Hw0body β ltac:(clear - Fr; solve_notin))
          | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
      assert (HwfPiβ : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ Pi }}a)
        by (eapply a_wf_pskl_weaken; eassumption).
      assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
        by (apply a_inc_cons_tvar; exact Hκ).
      assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ))
        by (eapply delta_def_fresh_weaken_tvar; eassumption).
      assert (Hrhofβ : rsubst_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ)
        by (eapply rsubst_fresh_weaken_tvar; eassumption).
      assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad)
        by (eapply ad_partial_precise_weaken;
              [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
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
      edestruct (H0 β ltac:(clear - Fr; solve_notin)
                   ((β ~ abind_tvar) ++ Θ)
                   ((β ~ abind_tvar) ++ Θ0) κ Δ Δρ Ψρ Ψt Ψi Ψa ψa Pi
                   (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f β))
                   Hwfβ Hwfβ0 Hmonβ Hnrβ Hκwβ HΔρw HwfPiβ HwfP0β
                   ltac:(intro Hc; discriminate Hc)
                   ltac:(intros _;
                         rewrite <- ptyp_to_pskl_open;
                         apply a_ty_mode_compat__tc)
                   Hκβ
                   ltac:(eapply uskl_rsubst_weaken;
                         [ exact Hrho
                         | intros x b Hb; apply binds_app_3; exact Hb ])
                   Htags
                   ltac:(eapply a_wf_pskl_weaken;
                         [ intros x b Hb; apply binds_app_3; exact Hb
                         | exact HwfSub ])
                   Htageq Hinter Hrhofβ Hdelta Hapart Hdfreshβ
                   Hpreβ HΨs1 HΨs2
                   ltac:(intros x b Hb;
                         unfold binds in Hb |- *; simpl in Hb |- *;
                         destruct Hb as [Heqb | Hb'];
                           [ left; exact Heqb | right; apply Hext; exact Hb' ])
                   Hrefβ (add β Lav) HLavβ)
        as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & HwfPaβ & Hp).

      assert (HβΞ : β `notin` dom Ξ)
        by (intro Hc; pose proof (Hfr β Hc) as Hf; clear - Hf; fsetdec).
      assert (Hdκ : dom κ' [=] dom Ξ) by (apply keys_eq_dom; exact Hk).
      assert (HβPa : β `notin` ftvar_in_pskl Pa).
      { assert (HβΔ : β `notin` Δ) by (clear - Fr; solve_notin).
        assert (Hβdef : β `notin` def_ftv Θ) by (clear - Fr; solve_notin).
        assert (Hsrc : β `notin` ftvar_in_pskl (msubst_pskl (κ' ++ κ) Pa)).
        { eapply ad_partial_precise_src_ftv_avoid;
            [ exact Hp | exact Hβψa | exact HβΔ
            |
              intros τ0 Hb;
              destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                [ discriminate Habs
                | apply HβΘ; eapply binds_In; exact Hb' ]
            | cbn [def_ftv]; exact Hβdef ]. }
        pose proof (msubst_pskl_ftv_dom_lower (κ' ++ κ) Pa) as Hlo.
        rewrite dom_app in Hlo.
        clear - Hsrc Hlo Hβκ HβΞ Hdκ; fsetdec. }
      assert (HwfPa0 : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a)
        by (eapply (@a_wf_pskl_strip_tvar Ξ β Θ0); eassumption).
      assert (Hβκ' : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κ').
      { rewrite Forall_forall. intros p Hp0.
        pose proof (forall_wf_mono_images_dom HF p Hp0) as Hb.
        clear - Hb HβΘw; fsetdec. }
      exists Ξ, Pa, κ'.
      repeat split; try assumption.
      *
        apply a_solve_sub_forall_r_gen with (β := β).
        -- exact (ptyp_to_pskl_ghost_free (ptyp_all A0)).
        -- clear - Fr; solve_notin.
        -- exact Hs.
      * intros α0 Hα0; pose proof (Hfr α0 Hα0) as Hf; clear - Hf; fsetdec.
      * eapply ad_partial_precise_strengthen_tvar; exact Hp.
  -
    assert (HP0 : P0 = pskl_ghost)
      by (pose proof (HmodSK eq_refl) as Hm; inversion Hm; reflexivity).
    subst P0.

    eapply solve_sub_ext_nil with (Pa := Pi);
      [ apply a_solve_sub_vacuous_gen | exact HwfPi | cbn [app] ].
    eapply ad_partial_precise_psi_cong; [ exact Hpre | ].
    assert (HPsiae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
    clear - HPsiae; fsetdec.
  -
    match goal with Hj : {{ _ ⨟ Θ ⊢ˢ R1 ∼ᵣ Q1 }}ad |- _ =>
      pose proof (ad_consis_join_consis Hj) as Hcons end.
    match goal with Hu : Ψ [=] _ `union` _ |- _ => rename Hu into Hun end.
    assert (HP0 : exists P01 P02, P0 = pskl_arrow P01 P02 /\
                    (NM = a_sub_mode_sk -> a_sk_mode_compat M P02) /\
                    (NM = a_sub_mode_ty -> a_ty_mode_compat M P02)).
    { destruct NM.
      - pose proof (HmodTY eq_refl) as Hm; inversion Hm; subst.
        match goal with Hc : a_ty_mode_compat M ?Q0 |- _ =>
          exists P, Q0; repeat split;
            [ intro Hd; discriminate Hd | intros _; exact Hc ] end.
      - pose proof (HmodSK eq_refl) as Hm; inversion Hm; subst.
        match goal with Hc : a_sk_mode_compat M ?Q0 |- _ =>
          exists P, Q0; repeat split;
            [ intros _; exact Hc | intro Hd; discriminate Hd ] end. }
    destruct HP0 as (P01 & P02 & -> & HmodSK2 & HmodTY2).
    assert (HwfP01 : {{ Θ0 ⨟ empty ⊢ₚₛ P01 }}a) by (inversion HwfP0; assumption).
    assert (HwfP02 : {{ Θ0 ⨟ empty ⊢ₚₛ P02 }}a) by (inversion HwfP0; assumption).
    cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
    inversion Hrefine; subst.
    match goal with
      Hr1 : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P01) ⊳ _ }}ad,
      Hr2 : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P02) ⊳ _ }}ad |- _ =>
      rename Hr1 into Href1; rename Hr2 into Href2
    end.
    assert (KEY : forall ψ1 ψ2 Ψρ1 Ψρ2,
      uskl_rsubst NM Θ Δρ Ψρ1 R1 ψ1 ->
      uskl_rsubst NM Θ Δρ Ψρ2 R2 ψ2 ->
      Ψρ [=] Ψρ1 `union` Ψρ2 ->
      a_tags_sort NM Ψt (uskl_arrow ψ1 ψ2) ->
      forall Pi1 Pi2 Ψi1 Ψi2 L0,
      {{ Θ0 ⨟ empty ⊢ₚₛ Pi1 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi2 }}a ->
      (forall α, α `in` Δρ ->
         α `notin` pskl_shielded_ftv (msubst_pskl κ Pi1)) ->
      (forall α, α `in` Δρ ->
         α `notin` pskl_shielded_ftv (msubst_pskl κ Pi2)) ->
      Ψi [=] Ψi1 `union` Ψi2 ->
      {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi1) ⊑ᵖ[ Ψi1 ] ψ1 }}ad ->
      {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi2) ⊑ᵖ[ Ψi2 ] ψ2 }}ad ->
      exists Ξ1 Ξ2 Pa1 Pa2 κ1 κ2,
        {{ Θ0 ⊢ₑ Pi1 ∼ P01 ⤳ Ξ1 ⨾ Pa1 }}a /\
        {{ (Ξ1 ++ Θ0) ⊢ₛ Pi2 ≼[ M ] P02 ⤳ Ξ2 ⨾ Pa2 }}a /\
        all_flex_mono (Ξ2 ++ Ξ1) /\
        uniq (Ξ2 ++ Ξ1) /\
        keys (κ2 ++ κ1) = keys (Ξ2 ++ Ξ1) /\
        (forall α, α `in` dom (Ξ2 ++ Ξ1) -> α `notin` L0) /\
        Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) (κ2 ++ κ1) /\
        {{ ((Ξ2 ++ Ξ1) ++ Θ0) ⨟ empty ⊢ₚₛ Pa1 }}a /\
        {{ ((Ξ2 ++ Ξ1) ++ Θ0) ⨟ empty ⊢ₚₛ Pa2 }}a /\
        {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl ((κ2 ++ κ1) ++ κ) (pskl_arrow Pa1 Pa2))
          ⊑ᵖ[ Ψi `union` Ψa ] (uskl_arrow ψ1 ψ2) }}ad).
    { intros ψ1 ψ2 Ψρ1 Ψρ2 Hrho1 Hrho2 HΨρs Htags0 Pi1 Pi2 Ψi1 Ψi2 L0 HwfPi1 HwfPi2 Hsh1 Hsh2 HΨis Hpre1 Hpre2.
      destruct (a_tags_sort_arrow_inv Htags0)
        as (Ψt1 & Ψt2 & Htags1 & Htags2 & Htdisj & Htun).

      assert (Hft1 : Ψ1 [<=] Ψρ1 `union` Ψt1).
      { pose proof (ad_pat_consis_ftag_sub Hcons) as Ha.
        pose proof (uskl_rsubst_ftag_sub Hrho1) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags1)) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hft2 : Ψ2 [<=] Ψρ2 `union` Ψt2).
      { pose proof (ad_pat_sub_fuel_ftag_sub Hsub) as Ha.
        pose proof (uskl_rsubst_ftag_sub Hrho2) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags2)) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hi1 : Ψi1 [<=] Ψt1)
        by (eapply ad_partial_precise_tags_sub;
              [ exact HwfΘ | exact Hpre1
              | exact (a_tags_sort_d_tags Htags1) ]).
      assert (Hi2 : Ψi2 [<=] Ψt2)
        by (eapply ad_partial_precise_tags_sub;
              [ exact HwfΘ | exact Hpre2
              | exact (a_tags_sort_d_tags Htags2) ]).
      destruct (arrow_tag_split Htun Htdisj HΨis Hi1 Hi2 Htageq)
        as (Hsp1 & Hsp2).

      destruct (@a_solve_eq_complete_var_at NM Θ0 Θ Θw κ Δ Δρ Ψρ1 Ψt1 Ψi1
                  (Ψa ∩ Ψt1) Ψ1 R1 ψ1 Q1 Pi1 P01
                  HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfPi1 HwfP01 Hκ Hκw Hrho1 Htags1
                  ltac:(clear - Hsp1; solve_notin_auto)
                  ltac:(clear - Hinter HΨρs Htun; solve_notin_auto)
                  Hrhof Hdelta Hsh1 Hdfresh
                  Hpre1
                  ltac:(clear - Hft1 HΨs1 Hinter Htun Htdisj Hun HΨρs; solve_notin_auto)
                  ltac:(clear - HΨs2 Hun Htun Hft2 Hinter HΨρs Htdisj; solve_notin_auto)
                  Hcons Href1 (union L0 (ftvar_in_aenv Θ0))
                  ltac:(clear; solve_notin_auto))
        as (Ξ1 & Pa1 & κ1 & Hs1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hp1).
      assert (Hw1 : {{ (Ξ1 ++ Θ0) ⨟ empty ⊢ₚₛ Pa1 }}a)
        by (eapply a_solve_eq_wf; eassumption).
      assert (Hfr1c : forall x, x `in` dom Ξ1 -> x `notin` ftvar_in_aenv Θ0)
        by (intros x Hx; eapply a_solve_eq_generated_fresh; eassumption).
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdf0.
      assert (Hd1 : dom κ1 [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).
      assert (HwfΞ1 : {{ ⊢ (Ξ1 ++ Θ0) }}a).
      { apply a_wf_aenv_flex_prefix; [ exact Hfm1 | | exact HwfΘ0 ].
        assert (Hdd : dom Ξ1 ∩ dom Θ0 [<=] empty).
        { intros x Hx.
          assert (Hx1 : x `in` dom Ξ1) by (clear - Hx; fsetdec).
          assert (Hx2 : x `in` dom Θ0) by (clear - Hx; fsetdec).
          pose proof (Hfr1c x Hx1) as Hf. exfalso; clear - Hf Hdf0 Hx2; fsetdec. }
        apply uniq_app_4;
          [ exact Hu1 | eapply a_wf_aenv_uniq; exact HwfΘ0 | exact Hdd ]. }
      assert (HF1Θ : Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ1)
        by (eapply forall_wf_mono_weaken; [ exact Hmon | exact HF1 ]).
      assert (Hκ1 : (κ1 ++ κ) ∷ (Ξ1 ++ Θ0) ⊑ Θ)
        by (apply a_inc_flex_prefix_build; eassumption).
      pose proof (forall_wf_mono_images_dom HF1) as HF1d.
      destruct (solve_scope_flex_prefix (conj Hmon (conj Hnr Hκw)) Hk1 HF1d)
        as (_ & _ & Hκw1).
      assert (Htr2 : msubst_pskl (κ1 ++ κ) Pi2 = msubst_pskl κ Pi2).
      { apply msubst_pskl_prepend_fresh. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ1) by (clear - Hα0 Hd1; fsetdec).
        pose proof (Hfr1c α0 Hin) as Hf.
        pose proof (a_wf_pskl_ftv_dom HwfPi2) as Hfd.
        clear - Hf Hfd Hdf0; fsetdec. }
      assert (Htr0 : msubst_pskl (κ1 ++ κ) P02 = msubst_pskl κ P02).
      { apply msubst_pskl_prepend_fresh. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ1) by (clear - Hα0 Hd1; fsetdec).
        pose proof (Hfr1c α0 Hin) as Hf.
        pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
        clear - Hf Hfd Hdf0; fsetdec. }
      assert (HΔρΘ0 : Δρ [<=] dom Θ0).
      { intros α0 Hα0. destruct (Hrhof α0 Hα0) as (Hb & _ & _).
        apply binds_In with (a := abind_tvar).
        eapply a_inc_binds_tvar_rev; eassumption. }
      assert (Hrhof1 : rsubst_fresh Δρ Θ (κ1 ++ κ)).
      { intros α0 Hα0. destruct (Hrhof α0 Hα0) as (Hb & Him & Hdf).
        repeat split; [ exact Hb | | exact Hdf ].
        intros p Hp0. apply in_app_or in Hp0; destruct Hp0 as [Hp0 | Hp0];
          [ pose proof (HF1d p Hp0) as Hbd; clear - Hbd HΔρw Hα0; fsetdec
          | apply Him; exact Hp0 ]. }
      destruct (IHHsub Θ (Ξ1 ++ Θ0) (κ1 ++ κ) Δ Δρ Ψρ2 Ψt2 Ψi2 (Ψa ∩ Ψt2)
                  ψ2 Pi2 P02
                  HwfΘ HwfΞ1 Hmon Hnr Hκw1 HΔρw
                  ltac:(eapply a_wf_pskl_weaken;
                        [ intros x b Hb; apply binds_app_3; exact Hb
                        | exact HwfPi2 ])
                  ltac:(eapply a_wf_pskl_weaken;
                        [ intros x b Hb; apply binds_app_3; exact Hb
                        | exact HwfP02 ])
                  HmodSK2 HmodTY2 Hκ1 Hrho2 Htags2
                  ltac:(inversion HwfSub; assumption)
                  ltac:(clear - Hsp2; solve_notin_auto)
                  ltac:(clear - Hinter HΨρs Htun; solve_notin_auto)
                  Hrhof1 Hdelta
                  ltac:(rewrite Htr2; exact Hsh2)
                  Hdfresh
                  ltac:(rewrite Htr2; exact Hpre2)
                  ltac:(clear - Hft2 HΨs1 Hinter Htun Htdisj Hun HΨρs; solve_notin_auto)
                  ltac:(clear - HΨs2 Hun Htun Hft1 Hinter HΨρs Htdisj; solve_notin_auto)
                  Hext
                  ltac:(rewrite Htr0; exact Href2)
                  (union L0 (union (dom Ξ1) (ftvar_in_aenv Θ0)))
                  ltac:(repeat rewrite ftvar_in_aenv_app;
                        pose proof (all_flex_mono_ftvar_in_aenv Hfm1) as Hs1f;
                        clear - Hs1f; solve_notin_auto))
        as (Ξ2 & Pa2 & κ2 & Hs2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hw2 & Hp2).

      assert (Hd2 : dom κ2 [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
      assert (H21 : forall x, x `in` dom Ξ2 -> x `notin` dom Ξ1)
        by (intros x Hx; pose proof (Hfr2 x Hx) as Hf; clear - Hf; fsetdec).
      exists Ξ1, Ξ2, Pa1, Pa2, κ1, κ2.
      split; [ exact Hs1 | ]. split; [ exact Hs2 | ].
      split; [ apply all_flex_mono_app; assumption | ].
      split; [ apply uniq_app_4;
                 [ exact Hu2 | exact Hu1
                 | intros x Hx;
                   assert (Hx2 : x `in` dom Ξ2) by (clear - Hx; fsetdec);
                   assert (Hx1 : x `in` dom Ξ1) by (clear - Hx; fsetdec);
                   pose proof (H21 x Hx2) as Hf; exfalso; clear - Hf Hx1; fsetdec ]
             | ].
      split; [ rewrite !keys_app; rewrite Hk1, Hk2; reflexivity | ].
      split; [ intros α0 Hα0; rewrite dom_app in Hα0;
               apply union_1 in Hα0; destruct Hα0 as [Hα0 | Hα0];
                 [ pose proof (Hfr2 α0 Hα0) as Hf; clear - Hf; fsetdec
                 | pose proof (Hfr1 α0 Hα0) as Hf; clear - Hf; fsetdec ] | ].
      split; [ apply Forall_app; split; assumption | ].
      split; [
               eapply a_wf_pskl_weaken; [ | exact Hw1 ];
               intros x b Hb; rewrite (aenv_app_assoc Ξ2 Ξ1 Θ0);
               apply binds_app_3; exact Hb | ].
      split; [ rewrite (aenv_app_assoc Ξ2 Ξ1 Θ0); exact Hw2 | ].
      assert (Htr1 : msubst_pskl ((κ2 ++ κ1) ++ κ) Pa1
                     = msubst_pskl (κ1 ++ κ) Pa1).
      { rewrite (list_app_assoc κ2 κ1 κ).
        apply msubst_pskl_prepend_fresh. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ2) by (clear - Hα0 Hd2; fsetdec).
        assert (Hf : α0 `notin` ftvar_in_aenv (Ξ1 ++ Θ0))
          by (eapply a_solve_sub_generated_fresh; eassumption).
        pose proof (a_wf_pskl_ftv_dom Hw1) as Hfd.
        pose proof (dom_subset_ftvar_in_aenv (Ξ1 ++ Θ0)) as Hds.
        clear - Hf Hfd Hds; fsetdec. }
      cbn [msubst_pskl].
      eapply ad_ppre__arrow;
        [ rewrite Htr1; exact Hp1
        | rewrite (list_app_assoc κ2 κ1 κ); exact Hp2
        | clear - HΨis Htun Htdisj Htageq; fsetdec ]. }

    assert (Htsk : is_dskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rsubst_arrow_l_inv Hrho) as [[Heq HΨρe] | [Hleaf | Hcong]];
      [ |
        destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa;
        eapply a_solve_sub_complete_rsubst_var;
          solve [ eauto | clear - Htageq; fsetdec ]
      | ].

    { subst ψa.
      assert (Hlc1 : lc_uskl R1) by (inversion Htsk; apply is_dskl_lc; assumption).
      assert (Hlc2 : lc_uskl R2) by (inversion Htsk; apply is_dskl_lc; assumption).
      assert (Hrho1 : uskl_rsubst NM Θ Δρ empty R1 R1)
        by (apply ursubst__refl; [ exact Hlc1 | clear; fsetdec ]).
      assert (Hrho2 : uskl_rsubst NM Θ Δρ empty R2 R2)
        by (apply ursubst__refl; [ exact Hlc2 | clear; fsetdec ]).
      pose proof (KEY R1 R2 empty empty Hrho1 Hrho2
                    ltac:(clear - HΨρe; solve_notin_auto) Htags ) as KEY'.
      eapply arrow_grid; eassumption. }

    { destruct Hcong as (ψ1 & ψ2 & Ψρ1 & Ψρ2 & Heq & Hrho1 & Hrho2 & HΨρs);
        subst ψa.
      pose proof (KEY ψ1 ψ2 Ψρ1 Ψρ2 Hrho1 Hrho2 HΨρs Htags ) as KEY'.
      eapply arrow_grid; eassumption. }
  -
    match goal with
      Hd : ad_pat_sub_fuel _ _ _ _ _ (open_uskl_wrt_uskl R ψ) _ |- _ =>
      rename Hd into Hprem end.
    match goal with Ht : a_tags_sort _ _ ψ |- _ => rename Ht into Htagsg end.
    match goal with Hw : {{ _ ⨟ _ ⊢ₚₛ ⌊ ψ ⌋ˢ }}a |- _ => rename Hw into Hwfg0 end.
    assert (Hwfg : {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a)
      by (eapply a_wf_pskl_weaken; eassumption).
    match goal with
      Hf : _ ∩ (ftag_in_uskl (uskl_all_tag _ R)) [=] empty |- _ =>
      rename Hf into Hgfresh end.
    assert (Hlcg : lc_uskl ψ)
      by (apply is_dskl_lc; inversion Htagsg; assumption).

    assert (MAIN : forall L0 ψsrc,
      (forall α, α `notin` L0 ->
         uskl_rsubst NM Θ Δρ Ψρ (open_uskl_wrt_uskl R (uskl_var_f α))
                             (open_uskl_wrt_uskl ψsrc (uskl_var_f α))) ->
      a_tags_sort NM Ψt (uskl_all_tag ε ψsrc) ->
      {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_all_tag ε ψsrc) }}ad ->
      solve_sub_ext Θ0 Θw M Pi P0 Lav
        (fun κ' Pa =>
           {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa)
             ⊑ᵖ[ Ψi `union` Ψa ] (uskl_all_tag ε ψsrc) }}ad)).
    { intros L0 ψsrc Hfam Htags0 Hpre0.
      destruct (a_tags_sort_all_tag_inv Htags0)
        as (Lt & Ψt0 & Htbody & Hεt0 & HΨteq).

      assert (HftagR : ftag_in_uskl ψsrc [<=] ftag_in_uskl R).
      { pick fresh α1 for L0.
        pose proof (uskl_rsubst_ftag_target_sub
                      (Hfam α1 ltac:(clear - Fr; solve_notin))) as Hb.
        rewrite (ftag_in_uskl_open_var R α1) in Hb.
        rewrite (ftag_in_uskl_open_var ψsrc α1) in Hb. exact Hb. }
      assert (HRtag : ftag_in_uskl R [<=] Ψρ `union` ftag_in_uskl ψsrc).
      { pick fresh α1 for L0.
        pose proof (uskl_rsubst_ftag_sub
                      (Hfam α1 ltac:(clear - Fr; solve_notin))) as Hb.
        rewrite (ftag_in_uskl_open_var R α1) in Hb.
        rewrite (ftag_in_uskl_open_var ψsrc α1) in Hb. exact Hb. }
      assert (HΨt0eq : Ψt0 [=] ftag_in_uskl ψsrc).
      { pick fresh α1 for Lt.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags
                      (Htbody α1 ltac:(clear - Fr; solve_notin)))) as Hb.
        rewrite (ftag_in_uskl_open_var ψsrc α1) in Hb. exact Hb. }
      assert (HεΨt : ε `in` Ψt) by (clear - HΨteq; fsetdec).
      assert (HεR : ε `notin` ftag_in_uskl R)
        by (clear - HRtag Hinter HεΨt HΨt0eq Hεt0; fsetdec).
      assert (HεΨsub : ε `notin` Ψ).
      { pose proof (ad_pat_sub_fuel_ftag_sub Hprem) as Hb.
        pose proof (ftag_in_uskl_open_upper R ψ) as Hup.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htagsg)) as Hg.
        cbn [ftag_in_uskl] in Hgfresh.
        clear - Hb Hup Hg Hgfresh HεR; fsetdec. }
      assert (HεΨi : ε `in` Ψi)
        by (clear - Htageq HΨteq HεΨsub HΨs2; fsetdec).
      destruct Pi as [ | nPi | β0 | Pi1 Pi2 | Pi0 | | Pi0 ];
        cbn [msubst_pskl] in Hpre0.
      -  inversion Hpre0.
      -  inversion HwfPi.
      -
        exfalso.
        assert (HΨte : Ψt [=] empty)
          by (eapply ad_partial_precise_mono_subject_target_tags_empty;
                [ exact HwfΘ | exact Hpre0 | reflexivity
                | eapply a_inc_lookup_mono; exact Hκ
                | exact (a_tags_sort_d_tags Htags0) ]).
        clear - HΨte HεΨt; fsetdec.
      -  inversion Hpre0.
      -
        assert (Hex : exists Lp Ψi0,
                  (forall α, α `notin` Lp ->
                     {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ)
                       ⊢ˢ (open_pskl_wrt_pskl (msubst_pskl κ Pi0)
                            (pskl_var_f α))
                       ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψsrc (uskl_var_f α)) }}ad)
                  /\ Ψi [=] add ε Ψi0).
        { inversion Hpre0; subst; eexists; eexists; split; eassumption. }
        destruct Hex as (Lp & Ψi0 & Hpbody & HΨieq).
        assert (Hexw : exists Lw,
                  forall α, α `notin` Lw ->
                    {{ ((α ~ abind_tvar) ++ Θ0) ⨟ (add α empty)
                      ⊢ₚₛ (open_pskl_wrt_pskl Pi0 (pskl_var_f α)) }}a).
        { inversion HwfPi; subst; eexists; eassumption. }
        destruct Hexw as (Lw & Hwbody).
        pick fresh β for
          (L0 `union` Lt `union` Lp `union` Lw `union` dom Θ `union` dom Θ0
             `union` ftvar_in_aenv Θ0
             `union` dom κ `union` Δ `union` Δρ `union` def_ftv Θ
             `union` ftvar_in_uskl ψsrc `union` ftvar_in_uskl R
             `union` ftvar_in_uskl ψ `union` ftvar_in_pskl Pi0
             `union` ftvar_in_pskl P0).
        assert (HβΘ : β `notin` dom Θ) by (clear - Fr; solve_notin).
        assert (HβΘ0 : β `notin` dom Θ0) by (clear - Fr; solve_notin).
        assert (Hβκ : β `notin` dom κ) by (clear - Fr; solve_notin).
        assert (HβΔ : β `notin` Δ) by (clear - Fr; solve_notin).
        assert (HβΔρ : β `notin` Δρ) by (clear - Fr; solve_notin).
        assert (HβR : β `notin` ftvar_in_uskl R) by (clear - Fr; solve_notin).

        destruct (@uskl_rsubst_subst NM Θ Δρ Ψρ
                    (open_uskl_wrt_uskl R (uskl_var_f β))
                    (open_uskl_wrt_uskl ψsrc (uskl_var_f β))
                    (Hfam β ltac:(clear - Fr; solve_notin))
                    β ψ Ψ' Htagsg Hwfg Hlcg HβΘ HβΔρ)
          as (Ψρ' & HΨρ'sub & HΨρ'mono & HΨρ'occ & Hrho').
        rewrite <- (@subst_uskl_in_uskl_intro β R ψ) in Hrho';
          [ | exact HβR ].
        assert (HΨ'sub : Ψ' [<=] Ψρ').
        { destruct (AtomSetProperties.In_dec β
                      (ftvar_in_uskl (open_uskl_wrt_uskl ψsrc (uskl_var_f β))))
            as [Hin | Hni]; [ exact (HΨρ'occ Hin) | ].
          assert (HβRo : β `notin` ftvar_in_uskl
                           (open_uskl_wrt_uskl R (uskl_var_f β))).
          { pose proof (uskl_rsubst_ftv_subject_bound
                          (Hfam β ltac:(clear - Fr; solve_notin))) as Hb.
            clear - Hb Hni HβΘ; fsetdec. }
          assert (Heqo : open_uskl_wrt_uskl R ψ
                         = open_uskl_wrt_uskl R (uskl_var_f β)).
          { rewrite (@subst_uskl_in_uskl_intro β R ψ); [ | exact HβR ].
            apply subst_uskl_in_uskl_fresh_eq; exact HβRo. }
          pose proof (ad_pat_sub_fuel_ftag_sub Hprem) as Hb.
          rewrite Heqo in Hb. rewrite (ftag_in_uskl_open_var R β) in Hb.
          cbn [ftag_in_uskl] in Hgfresh.
          clear - Hb Hgfresh; fsetdec. }

        assert (Hwfβ : {{ ⊢ ((β ~ abind_tvar) ++ Θ) }}a)
          by (apply a_wf_aenv__tvar; assumption).
        assert (Hwfβ0 : {{ ⊢ ((β ~ abind_tvar) ++ Θ0) }}a)
          by (apply a_wf_aenv__tvar; assumption).
        assert (Hweak0 : forall (x : atom) (b : abind),
                  binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
          by (intros x b Hb; apply binds_app_3; exact Hb).
        assert (Hweak : forall (x : atom) (b : abind),
                  binds x b Θ -> binds x b ((β ~ abind_tvar) ++ Θ))
          by (intros x b Hb; apply binds_app_3; exact Hb).
        assert (HwfPiβ : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                  ⊢ₚₛ (open_pskl_wrt_pskl Pi0 (pskl_var_f β)) }}a).
        { eapply a_wf_pskl_delta_mono;
            [ apply (Hwbody β ltac:(clear - Fr; solve_notin))
            | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
        assert (HwfP0β : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
          by (eapply a_wf_pskl_weaken; eassumption).
        assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
          by (apply a_inc_cons_tvar; exact Hκ).
        assert (Hrhoβ : uskl_rsubst NM ((β ~ abind_tvar) ++ Θ) (add β Δρ) Ψρ'
                  (open_uskl_wrt_uskl R ψ)
                  (open_uskl_wrt_uskl ψsrc (uskl_var_f β)))
          by (eapply uskl_rsubst_weaken; eassumption).
        assert (Htagsβ : a_tags_sort NM Ψt0
                  (open_uskl_wrt_uskl ψsrc (uskl_var_f β)))
          by (apply Htbody; clear - Fr; solve_notin).
        assert (HwfSubβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty
                  ⊢ₚₛ ⌊ open_uskl_wrt_uskl R ψ ⌋ˢ }}a).
        { assert (Hexs : exists Lb, forall α, α `notin` Lb ->
                    {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α empty) ⊢ₚₛ
                      (open_pskl_wrt_pskl ⌊ R ⌋ˢ (pskl_var_f α)) }}a).
          { cbn [uskl_to_pskl] in HwfSub;
            inversion HwfSub; subst; eexists; eassumption. }
          destruct Hexs as (Lb & Hbody).
          rewrite uskl_to_pskl_open_gen.
          eapply a_wf_pskl_weaken; [ exact Hweak | ].
          eapply a_wf_pskl_open; eassumption. }
        assert (HΨi0sub : Ψi0 [<=] Ψt0)
          by (eapply ad_partial_precise_tags_sub;
                [ exact Hwfβ | apply (Hpbody β ltac:(clear - Fr; solve_notin))
                | exact (a_tags_sort_d_tags Htagsβ) ]).
        assert (Htageqβ : Ψi0 `union` Ψa [=] Ψt0)
          by (clear - Htageq HΨteq HΨieq HΨi0sub Hεt0 HεΨsub HΨs2; fsetdec).
        assert (Hinterβ : Ψρ' ∩ Ψt0 [=] empty).
        { cbn [ftag_in_uskl] in Hgfresh.
          clear - HΨρ'sub Hinter HΨteq HΨt0eq HftagR Hgfresh; fsetdec. }
        assert (Hrhofβ : rsubst_fresh (add β Δρ) ((β ~ abind_tvar) ++ Θ) κ)
          by (eapply rsubst_fresh_open_tvar; eassumption).
        assert (Hdeltaβ : add β Δρ [<=] add β Δ)
          by (clear - Hdelta; fsetdec).
        assert (Hapartβ : forall α0, α0 `in` (add β Δρ) ->
                  α0 `notin` pskl_shielded_ftv
                    (msubst_pskl κ (open_pskl_wrt_pskl Pi0 (pskl_var_f β)))).
        { intros α0 Hα0.
          destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin | Hni].
          - rewrite (@msubst_pskl_open Θ0 κ Θ Pi0 β Hκ Hβκ).
            pose proof (Hapart α0 Hin) as Hs.
            cbn [msubst_pskl pskl_shielded_ftv] in Hs.
            pose proof (pskl_shielded_ftv_open_upper (msubst_pskl κ Pi0)
                          (pskl_var_f β)) as Hup.
            cbn [ftvar_in_pskl] in Hup.
            assert (Hne : α0 <> β) by (clear - Hin HβΔρ; fsetdec).
            clear - Hs Hup Hne; fsetdec.
          -
            assert (Heqβ : α0 = β) by (clear - Hα0 Hni; fsetdec); subst α0.
            apply msubst_pskl_shielded_avoid.
            + intros pp Hpp.
              pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb.
              clear - Hb HβΘ; fsetdec.
            + apply (a_wf_pskl_shielded_delta
                       (Hwbody β ltac:(clear - Fr; solve_notin)));
              clear; fsetdec. }
        assert (Hdfreshβ : delta_def_fresh (add β Δ) ((β ~ abind_tvar) ++ Θ))
          by (eapply delta_def_fresh_open_tvar; eassumption).
        assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ)
                  ⊢ˢ (msubst_pskl κ (open_pskl_wrt_pskl Pi0 (pskl_var_f β)))
                  ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψsrc (uskl_var_f β)) }}ad).
        { rewrite (@msubst_pskl_open Θ0 κ Θ Pi0 β Hκ Hβκ).
          apply (Hpbody β ltac:(clear - Fr; solve_notin)). }
        assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                  (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad)
          by (eapply ad_refine_syn_weaken; eassumption).

        destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HβΘ)
          as (HβΘw & Hmonβ & Hnrβ & Hκwβ).
        assert (HΔρwβ : (add β Δρ) ∩ dom Θw [=] empty)
          by (clear - HΔρw HβΘw; fsetdec).
        assert (HLavβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β Lav)
          by (rewrite ftvar_in_aenv_cons_tvar; clear - HLav; fsetdec).
        edestruct (IHHsub ((β ~ abind_tvar) ++ Θ) ((β ~ abind_tvar) ++ Θ0) κ
                     (add β Δ) (add β Δρ) Ψρ' Ψt0 Ψi0 Ψa
                     (open_uskl_wrt_uskl ψsrc (uskl_var_f β))
                     (open_pskl_wrt_pskl Pi0 (pskl_var_f β)) P0
                     Hwfβ Hwfβ0 Hmonβ Hnrβ Hκwβ HΔρwβ
                     HwfPiβ HwfP0β HmodSK HmodTY Hκβ Hrhoβ
                     Htagsβ HwfSubβ Htageqβ Hinterβ Hrhofβ Hdeltaβ Hapartβ
                     Hdfreshβ Hpreβ
                     ltac:(clear - HΨs1 HΨρ'mono HΨ'sub; solve_notin_auto)
                     ltac:(clear - HΨs2; solve_notin_auto)
                     ltac:(intros x b Hb; apply binds_app_3; apply Hext;
                           exact Hb)
                     Hrefβ (add β Lav) HLavβ)
          as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & HwfPaβ & Hp).
        assert (HβΞ : β `notin` dom Ξ)
          by (intro Hc; pose proof (Hfr β Hc) as Hf; clear - Hf; fsetdec).
        assert (Hdκ : dom κ' [=] dom Ξ) by (apply keys_eq_dom; exact Hk).
        assert (Hβκ' : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κ').
        { rewrite Forall_forall. intros p Hp0.
          pose proof (forall_wf_mono_images_dom HF p Hp0) as Hb.
          clear - Hb HβΘw; fsetdec. }

        remember (close_pskl_wrt_pskl β Pa) as Pb eqn:HeqPb.
        assert (HopenPb : open_pskl_wrt_pskl Pb (pskl_var_f β) = Pa)
          by (subst Pb; apply open_pskl_wrt_pskl_close_pskl_wrt_pskl).
        assert (HβPb : β `notin` ftvar_in_pskl Pb)
          by (subst Pb; rewrite ftvar_in_pskl_close_pskl_wrt_pskl;
              clear; fsetdec).
        assert (HβPbκ : β `notin` ftvar_in_pskl (msubst_pskl (κ' ++ κ) Pb)).
        { apply msubst_pskl_ftv_avoid;
            [ intros pp Hpp; apply in_app_or in Hpp;
              destruct Hpp as [Hpp | Hpp];
                [ rewrite Forall_forall in Hβκ'; apply Hβκ'; exact Hpp
                | pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb;
                  clear - Hb HβΘ; fsetdec ]
            | exact HβPb ]. }
        assert (HshPiβ : β `notin` pskl_shielded_ftv
                           (open_pskl_wrt_pskl Pi0 (pskl_var_f β))).
        { apply (a_wf_pskl_shielded_delta
                   (Hwbody β ltac:(clear - Fr; solve_notin)));
          clear; fsetdec. }
        assert (HshPa : β `notin` pskl_shielded_ftv Pa).
        { eapply (proj1 a_solve_sub_eq_unshielded);
            [ exact Hs
            | simpl; clear; fsetdec
            | exact HshPiβ
            | pose proof (a_wf_pskl_ftv_dom HwfP0) as Hfd;
              clear - Hfd HβΘ0; fsetdec ]. }
        assert (HwfPaΔ : {{ ((β ~ abind_tvar) ++ Ξ ++ Θ0) ⨟ (add β empty) ⊢ₚₛ Pa }}a)
          by (eapply (@a_wf_pskl_tvar_to_delta Ξ β Θ0); eassumption).
        exists Ξ, (pskl_all_syn Pb), κ'.
        split; [ | split; [ exact Hfm | split; [ exact Hu
                 | split; [ exact Hk | split; [ | split; [ exact HF
                 | split ] ] ] ] ] ].
        +
          rewrite HeqPb.
          apply a_solve_sub__forall_l with (β := β);
            [ clear - Fr; solve_notin | exact Hs ].
        +
          intros α0 Hα0; pose proof (Hfr α0 Hα0) as Hf; clear - Hf; fsetdec.
        +
          apply (@a_wf_pskl_all_of_one_at (Ξ ++ Θ0) empty Pb β);
            [ rewrite HopenPb; exact HwfPaΔ | exact HβPb ].
        +
          assert (Hp' : {{ Θ ⨟ (add β Δ) ⊢ˢ (msubst_pskl (κ' ++ κ) Pa)
                    ⊑ᵖ[ Ψi0 `union` Ψa ]
                    (open_uskl_wrt_uskl ψsrc (uskl_var_f β)) }}ad)
            by (eapply ad_partial_precise_strengthen_tvar; exact Hp).
          assert (Hκa : (κ' ++ κ) ∷ (Ξ ++ (β ~ abind_tvar) ++ Θ0)
                          ⊑ ((β ~ abind_tvar) ++ Θ))
            by (apply a_inc_flex_prefix_build;
                  [ exact Hfm | exact Hk
                  | eapply forall_wf_mono_weaken; eassumption
                  | exact Hκβ ]).
          assert (Hβκa : β `notin` dom (κ' ++ κ))
            by (rewrite dom_app; clear - HβΞ Hβκ Hdκ; fsetdec).
          assert (Heqsub : msubst_pskl (κ' ++ κ) Pa
                    = open_pskl_wrt_pskl (msubst_pskl (κ' ++ κ) Pb)
                        (pskl_var_f β)).
          { rewrite <- HopenPb at 1.
            apply (@msubst_pskl_open (Ξ ++ (β ~ abind_tvar) ++ Θ0) (κ' ++ κ)
                     ((β ~ abind_tvar) ++ Θ) Pb β Hκa Hβκa). }
          rewrite Heqsub in Hp'.
          cbn [msubst_pskl].
          eapply ad_ppre__forall
            with (L := dom Θ `union` Δ `union` singleton β
                        `union` ftvar_in_uskl ψsrc
                        `union` ftvar_in_pskl (msubst_pskl (κ' ++ κ) Pb))
                 (Ψ0 := Ψi0 `union` Ψa);
            [ | clear - HΨieq; fsetdec ].
          intros α Hα.
          apply ad_partial_precise_weaken_tvar.
          assert (HαΘ : α `notin` dom Θ) by (clear - Hα; solve_notin).
          assert (HαΔ : α `notin` Δ) by (clear - Hα; solve_notin).
          assert (Hαβ : α `notin` singleton β) by (clear - Hα; solve_notin).
          assert (Hαψ : α `notin` ftvar_in_uskl ψsrc)
            by (clear - Hα; solve_notin).
          assert (HαPb : α `notin` ftvar_in_pskl (msubst_pskl (κ' ++ κ) Pb))
            by (clear - Hα; solve_notin).
          assert (Hdefs : forall α3 τ3, binds α3 (abind_flex_mono_def τ3) Θ ->
                    β `notin` ftvar_in_ptyp τ3 /\ α `notin` ftvar_in_ptyp τ3).
          { intros α3 τ3 Hb.
            pose proof (a_wf_ptyp_ftv_dom
                          (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb)) as Hd.
            split; [ clear - Hd HβΘ; fsetdec | clear - Hd HαΘ; fsetdec ]. }
          pose proof (@ad_partial_precise_rename Θ (add β Δ)
                        (Ψi0 `union` Ψa)
                        (open_pskl_wrt_pskl (msubst_pskl (κ' ++ κ) Pb)
                           (pskl_var_f β))
                        (open_uskl_wrt_uskl ψsrc (uskl_var_f β)) Hp' β α
                        ltac:(clear; solve_notin_auto) HβΘ HαΘ
                        ltac:(clear - HαΔ Hαβ; solve_notin_auto)
                        ltac:(pose proof
                                (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                   (msubst_pskl (κ' ++ κ) Pb)
                                   (pskl_var_f β)) as Hup;
                              cbn [ftvar_in_pskl] in Hup;
                              clear - HαPb Hαβ Hup; fsetdec)
                        ltac:(pose proof
                                (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                                   ψsrc (uskl_var_f β)) as Hup;
                              cbn [ftvar_in_uskl] in Hup;
                              clear - Hαψ Hαβ Hup; fsetdec)
                        Hdefs) as Hrn.
          rewrite <- (@subst_pskl_in_pskl_intro β (msubst_pskl (κ' ++ κ) Pb)
                        (pskl_var_f α)) in Hrn; [ | exact HβPbκ ].
          rewrite <- (@subst_uskl_in_uskl_intro β ψsrc (uskl_var_f α))
            in Hrn; [ | clear - Fr; solve_notin ].
          eapply ad_partial_precise_delta_cong;
            [ exact Hrn | clear - HβΔ; fsetdec ].
      -
        exfalso.
        pose proof (ad_ppre_ghost_subject_tags Hpre0) as HΨie.
        clear - HΨie HεΨi; fsetdec.
      -
        exfalso.
        assert (HgPi0 : guarded_pskl Pi0) by (inversion HwfPi; assumption).
        inversion Hpre0; subst.
        +
          eapply ad_ppre_guarded_all_tag_absurd;
            [ exact HwfΘ | exact Hκ | exact HgPi0
            | exact (a_tags_sort_d_tags Htags0) | eassumption ].
        +
          assert (Hexf : exists Lf Pf, forall α, α `notin` Lf ->
                    {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ˢ Pf ⊑ᵖ[ Ψi ]
                      (open_uskl_wrt_uskl ψsrc (uskl_var_f α)) }}ad)
            by (eexists; eexists; eassumption).
          destruct Hexf as (Lf & Pf & Hfill).
          pick fresh α2 for (Lf `union` Lt `union` dom Θ).
          assert (Hwf2 : {{ ⊢ ((α2 ~ abind_tvar) ++ Θ) }}a)
            by (apply a_wf_aenv__tvar; [ clear - Fr; solve_notin | exact HwfΘ ]).
          assert (HΨisub : Ψi [<=] Ψt0)
            by (eapply ad_partial_precise_tags_sub;
                  [ exact Hwf2
                  | apply (Hfill α2 ltac:(clear - Fr; solve_notin))
                  | exact (a_tags_sort_d_tags
                             (Htbody α2 ltac:(clear - Fr; solve_notin))) ]).
          clear - HΨisub HεΨi Hεt0; fsetdec. }

    destruct (uskl_rsubst_all_tag_l_inv Hrho) as [[Heq HΨρe] | [Hleaf | Hcong]].
    +
      subst ψa.
      assert (Htsk : is_dskl (uskl_all_tag ε R))
        by (inversion Htags; assumption).
      destruct (is_dskl_all_tag_inv Htsk) as (Li & Hti).
      eapply MAIN;
        solve [ intros α Hα; apply ursubst__refl;
                  [ apply is_dskl_lc; apply Hti; exact Hα
                  | clear - HΨρe; fsetdec ]
              | exact Htags | exact Hpre ].
    +
      destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa.
      eapply a_solve_sub_complete_rsubst_var;
        solve [ eauto | clear - Htageq; fsetdec ].
    +
      destruct Hcong as (L0 & ψsrc & Heq & Hfam); subst ψa.
      eapply MAIN;
        solve [ exact Hfam | exact Htags | exact Hpre ].
  -
    exfalso.
    assert (Htsk : is_dskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rsubst_all_syn_l_inv Hrho) as [[Heq _] | [Hleaf | Hcong]].
    + subst ψa; inversion Htsk.
    + destruct Hleaf as (α0 & Ψ'' & _ & _ & Htagsub & _ & _).
      assert (Htsk' : is_dskl (uskl_all_syn R)) by (inversion Htagsub; assumption).
      inversion Htsk'.
    + destruct Hcong as (L0 & R0 & Heq & _); subst ψa; inversion Htsk.
  -
    exfalso.
    assert (Htsk : is_dskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rsubst_ghost_l_inv Hrho) as [[Heq _] | Hleaf].
    + subst ψa; inversion Htsk.
    + destruct Hleaf as (α0 & Ψ'' & _ & _ & Htagsub & _ & _).
      assert (Htsk' : is_dskl uskl_ghost) by (inversion Htagsub; assumption).
      inversion Htsk'.
  -
    assert (HP0 : P0 = pskl_ghost).
    { pose proof (HmodSK eq_refl) as Hm; inversion Hm; subst;
        solve [ reflexivity | inversion H0 ]. }
    subst P0.

    eapply solve_sub_ext_nil with (Pa := Pi);
      [ apply a_solve_sub_vacuous_gen | exact HwfPi | cbn [app] ].
    eapply ad_partial_precise_psi_cong; [ exact Hpre | ].
    assert (HPsiae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
    clear - HPsiae; fsetdec.
  -
    exfalso.
    assert (Htsk : is_dskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rsubst_univ_ghost_l_inv Hrho) as [[Heq _] | [Hleaf | Hcong]].
    + subst ψa; inversion Htsk.
    + destruct Hleaf as (α0 & Ψ'' & _ & _ & Htagsub & _ & _).
      assert (Htsk' : is_dskl (uskl_univ_ghost R)) by (inversion Htagsub; assumption).
      inversion Htsk'.
    + destruct Hcong as (R0 & Heq & _); subst ψa; inversion Htsk.
  -
    assert (Htsk : is_dskl ψa) by (inversion Htags; assumption).

    assert (KEY : forall ψ0,
      uskl_rsubst a_sub_mode_sk Θ Δρ Ψρ R ψ0 ->
      a_tags_sort a_sub_mode_sk Ψt (uskl_dot_univ_ghost ψ0) ->
      {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_dot_univ_ghost ψ0) }}ad ->
      solve_sub_ext Θ0 Θw M Pi P0 Lav
        (fun κ' Pa =>
           {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa)
             ⊑ᵖ[ Ψi `union` Ψa ] (uskl_dot_univ_ghost ψ0) }}ad)).
    { intros ψ0 Hrho0 Htags0 Hpre0.
      assert (Htags0' : a_tags_sort a_sub_mode_sk Ψt ψ0)
        by (eapply a_tags_sort_dot_univ_ghost_inv; exact Htags0).
      assert (HwfSub' : {{ Θ ⨟ empty ⊢ₚₛ ⌊ R ⌋ˢ }}a)
        by (cbn [uskl_to_pskl] in HwfSub;
            eapply a_wf_pskl_univ_ghost_inv; exact HwfSub).
      destruct Pi as [ | nPi | β | Pi1 Pi2 | Pi' | | Pi' ].
      - exfalso; eapply ad_ppre_guarded_dot_univ_ghost_absurd;
          [ exact HwfΘ | exact Hκ | apply guarded_pskl__unit | exact Hpre0 ].
      - inversion HwfPi.
      - exfalso; eapply ad_ppre_guarded_dot_univ_ghost_absurd;
          [ exact HwfΘ | exact Hκ | apply guarded_pskl__var | exact Hpre0 ].
      - exfalso.
        assert (Hg : guarded_pskl (pskl_arrow Pi1 Pi2)).
        { pose proof (a_wf_pskl_lc HwfPi) as Hlcarr.
          inversion Hlcarr; subst; apply guarded_pskl__arrow; assumption. }
        eapply ad_ppre_guarded_dot_univ_ghost_absurd;
          [ exact HwfΘ | exact Hκ | exact Hg | exact Hpre0 ].
      -
        cbn [msubst_pskl] in Hpre0; inversion Hpre0.
      -
        cbn [msubst_pskl] in Hpre0.
        pose proof (ad_ppre_ghost_subject_tags Hpre0) as HΨie.
        assert (HΔψ0 : Δ ∩ ftvar_in_uskl ψ0 [=] empty).
        {
          inversion Hpre0; subst; cbn [ftvar_in_uskl] in *; assumption. }
        assert (Hpre0' : {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ pskl_ghost) ⊑ᵖ[ Ψi ] ψ0 }}ad)
          by (cbn [msubst_pskl]; apply ad_ppre__ghost; assumption).
        edestruct (IHHsub Θ Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa ψ0 pskl_ghost P0
                     HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
                     HwfPi HwfP0 HmodSK HmodTY Hκ Hrho0
                     Htags0' HwfSub' Htageq Hinter Hrhof Hdelta Hapart
                     Hdfresh Hpre0' HΨs1 HΨs2 Hext Hrefine Lav HLav)
          as (Ξ & Pa' & κ' & Hs' & Hfm & Hu & Hk & Hfr & HF & Hw' & Hp').
        exists Ξ, Pa', κ'.
        repeat split; try assumption.
        eapply ad_ppre_lift_dot_univ_ghost;
          [ exact HwfΘ | exact Hp' | exact HΔψ0
          |
            eapply uskl_rsubst_guarded_erase;
              [ exact Hrho0
              | apply is_dskl_lc; inversion Htags0'; assumption
              | cbn [uskl_to_pskl] in HwfSub;
                inversion HwfSub; assumption ]
          |
            destruct (a_solve_sub_ghost_output Hs') as [-> | (B & ->)];
              [ left; reflexivity
              | right; eexists; cbn [msubst_pskl]; reflexivity ] ].
      -
        assert (HwfPi' : {{ Θ0 ⨟ empty ⊢ₚₛ Pi' }}a)
          by (eapply a_wf_pskl_univ_ghost_inv; exact HwfPi).
        assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
        cbn [msubst_pskl] in Hpre0.
        inversion Hpre0; subst.
        +
          exfalso; eapply ad_ppre_guarded_dot_univ_ghost_absurd;
            [ exact HwfΘ | exact Hκ | exact HgPi' | eassumption ].
        +
          match goal with Hbody : {{ _ ⨟ _ ⊢ˢ _ ⊑ᵖ[ _ ] ψ0 }}ad |- _ =>
            rename Hbody into Hpre' end.
          assert (Hapart' : forall α0, α0 `in` Δρ ->
                    α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi')).
          { intros α0 Hα0. pose proof (Hapart α0 Hα0) as Hsh.
            cbn [msubst_pskl pskl_shielded_ftv] in Hsh.
            pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi')) as Hle.
            clear - Hsh Hle; fsetdec. }
          edestruct (IHHsub Θ Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa ψ0 Pi' P0
                       HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
                       HwfPi' HwfP0 HmodSK HmodTY Hκ Hrho0
                       Htags0' HwfSub' Htageq Hinter Hrhof Hdelta Hapart'
                       Hdfresh Hpre' HΨs1 HΨs2 Hext Hrefine Lav HLav)
            as (Ξ & Pa' & κ' & Hs' & Hfm & Hu & Hk & Hfr & HF & Hw' & Hp').
          exists Ξ, (pskl_univ_ghost Pa'), κ'.
          repeat split; try assumption.
          * apply a_solve_sub__univ_ghost_l; exact Hs'.
          * apply a_wf_pskl__univ_ghost.
            -- eapply (proj1 a_solve_sub_eq_guarded); eauto using a_wf_pskl_lc.
            -- rewrite aenv_minus_empty; exact Hw'.
          * cbn [msubst_pskl]; apply ad_ppre__univ_ghost_keep; exact Hp'. }
    destruct (uskl_rsubst_dot_univ_ghost_l_inv Hrho) as [[Heq HΨρe] | [Hleaf | Hcong]].
    +
      subst ψa.
      assert (Hlc : lc_uskl R) by (inversion Htsk; apply is_dskl_lc; assumption).
      apply KEY; solve [ apply ursubst__refl; assumption | assumption ].
    +
      destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa.
      eapply a_solve_sub_complete_rsubst_var;
        solve [ eauto | clear - Htageq; fsetdec ].
    +
      destruct Hcong as (ψ0 & Heq & Hrho0); subst ψa.
      apply KEY; assumption.
  -
    destruct (uskl_rsubst_var_l_inv Hrho) as [[Heq HΨρe] | Hleaf].
    +
      subst ψa.
      assert (HΨte : Ψt [=] empty)
        by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
      assert (Hmono : mono_ptyp τ)
        by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | exact H ]).
      assert (Hwfτ : a_wf_ptyp Θ τ)
        by (eapply a_wf_aenv_binds_def_wf; eassumption).
      assert (Hclean : (ftvar_in_uskl (ptyp_to_uskl_syn τ)) ∩ Δρ [=] empty).
      { rewrite ftvar_ptyp_to_uskl_syn.
        intros α0; split; intros Hin; [ | clear - Hin; fsetdec ].
        exfalso.
        assert (Hα0Δ : α0 `in` Δ) by (clear - Hin Hdelta; fsetdec).
        pose proof (Hdfresh α0 α τ Hα0Δ H) as Hbad.
        clear - Hin Hbad; fsetdec. }
      assert (Hrho' : uskl_rsubst NM Θ Δρ Ψρ
                        (ptyp_to_uskl_syn τ) (ptyp_to_uskl_syn τ))
        by (apply ursubst__refl;
            [ apply is_dskl_lc; apply mono_ptyp_to_uskl_syn_is_dskl; exact Hmono
            | exact HΨρe ]).
      edestruct (IHHsub Θ Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa (ptyp_to_uskl_syn τ) Pi P0
                   HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
                   HwfPi HwfP0 HmodSK HmodTY Hκ Hrho')
        as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hw & Hp).
      *
        eapply a_tags_sort_psi_cong;
          [ apply a_tags_sort_mono_paint; exact Hmono | clear - HΨte; fsetdec ].
      *
        match goal with |- {{ _ ⨟ _ ⊢ₚₛ ⌊ ptyp_to_uskl_syn ?τ0 ⌋ˢ }}a =>
          replace (uskl_to_pskl (ptyp_to_uskl_syn τ0)) with (ptyp_to_pskl τ0)
            by (symmetry; apply uskl_to_pskl_ptyp)
        end.
        apply mono_ptyp_wf_to_pskl_wf; assumption.
      * exact Htageq.
      * exact Hinter.
      * exact Hrhof.
      * exact Hdelta.
      * exact Hapart.
      * exact Hdfresh.
      *
        eapply ad_ppre_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdfresh | exact Hpre | reflexivity | exact H ].
      * exact HΨs1.
      * exact HΨs2.
      * exact Hext.
      * exact Hrefine.
      * exact HLav.
      *
        exists Ξ, Pa, κ'.
        repeat split; try assumption.
        eapply ad_ppre__flex_r; eassumption.
    +
      destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa.
      eapply a_solve_sub_complete_rsubst_var;
        solve [ eauto | clear - Htageq; fsetdec ].
Qed.
