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
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.consistency.prop_consis_precise.
Require Import src.fresco.algo.subtyping.prop_looksub.
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

Lemma uskl_to_pskl_msubst_uskl_syn : forall κ R',
  ⌊ msubst_uskl_syn κ R' ⌋ˢ = msubst_pskl κ (⌊ R' ⌋ˢ).
Proof.
  intros κ R'; induction R'; simpl;
    try reflexivity;
    try (rewrite IHR'; reflexivity);
    try (rewrite IHR'1, IHR'2; reflexivity).
  apply uskl_to_pskl_ptyp.
Qed.

Lemma ptyp_to_uskl_syn_var : forall α, ptyp_to_uskl_syn (ptyp_var_f α) = uskl_var_f α.
Proof. reflexivity. Qed.

Lemma msubst_uskl_syn_prepend_fresh : forall κ' κ R',
  (forall α, α `in` dom κ' -> α `notin` ftvar_in_uskl R') ->
  msubst_uskl_syn (κ' ++ κ) R' = msubst_uskl_syn κ R'.
Proof.
  intros κ' κ R'; induction R' as [ | n | α | R1 IHR'1 R2 IHR'2 | R0 IHR'0
                               | ε R0 IHR'0 | | R0 IHR'0 | | R0 IHR'0 ];
    intros Hfr; simpl in *; try reflexivity.
  -
    f_equal. apply msubst_lookup_app_notin.
    intro Hc. apply (Hfr α Hc). fsetdec.
  - rewrite IHR'1, IHR'2; [ reflexivity | | ];
      intros α Hα; specialize (Hfr α Hα); fsetdec.
  - rewrite IHR'0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
  - rewrite IHR'0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
  - rewrite IHR'0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
  - rewrite IHR'0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
Qed.

Lemma msubst_pskl_prepend_fresh : forall κ' κ P,
  (forall α, α `in` dom κ' -> α `notin` ftvar_in_pskl P) ->
  msubst_pskl (κ' ++ κ) P = msubst_pskl κ P.
Proof.
  intros κ' κ P; induction P as [ | n | α | P1 IHP1 P2 IHP2 | P0 IHP0 | | P0 IHP0 ];
    intros Hfr; simpl in *; try reflexivity.
  -
    f_equal. apply msubst_lookup_app_notin.
    intro Hc. apply (Hfr α Hc). fsetdec.
  - rewrite IHP1, IHP2; [ reflexivity | | ];
      intros α Hα; specialize (Hfr α Hα); fsetdec.
  - rewrite IHP0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
  - rewrite IHP0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
Qed.

Lemma ftag_in_uskl_subst_uskl_in_uskl : forall R0 α R',
  ftag_in_uskl (subst_uskl_in_uskl R0 α R')
    [<=] ftag_in_uskl R' `union` ftag_in_uskl R0.
Proof.
  intros R0 α R'; induction R' as [ | n | α0 | β1 IHR'1 β2 IHR'2 | β0 IHR'0
                               | ε β0 IHR'0 | | β0 IHR'0 | | β0 IHR'0 ];
    simpl; try fsetdec.

  match goal with |- context [if ?c then _ else _] => destruct c end;
    simpl; fsetdec.
Qed.

Lemma ftag_in_uskl_msubst_uskl_syn : forall κ R',
  ftag_in_uskl (msubst_uskl_syn κ R') [=] ftag_in_uskl R'.
Proof.
  intros κ R'; induction R' as [ | n | α | R1 IHR'1 R2 IHR'2 | R0 IHR'0
                             | ε R0 IHR'0 | | R0 IHR'0 | | R0 IHR'0 ];
    simpl; try fsetdec.
  pose proof (ftag_ptyp_to_uskl_syn (msubst_lookup κ α)) as Hgf.
  fsetdec.
Qed.

Lemma a_solve_cstr_app : forall Θ C1 𝒞2 Pi Pmid Pa Ξ1 Ξ2,
  Forall (fun c => exists Q, c = a_cstr_eq Q) C1 ->
  {{ Θ ⊩ C1 ⨾ Pi ⤳ Ξ1 ⨾ Pmid }}a ->
  {{ (Ξ1 ++ Θ) ⊩ 𝒞2 ⨾ Pmid ⤳ Ξ2 ⨾ Pa }}a ->
  {{ Θ ⊩ (C1 ++ 𝒞2) ⨾ Pi ⤳ (Ξ2 ++ Ξ1) ⨾ Pa }}a.
Proof.
  intros Θ C1; revert Θ; induction C1 as [ | c C1' IH ];
    intros Θ 𝒞2 Pi Pmid Pa Ξ1 Ξ2 Hall H1 H2.
  - inversion H1; subst. cbn [app] in *. rewrite app_nil_r. exact H2.
  - inversion Hall as [ | ? ? [Q ->] Hall' ]; subst.
    inversion H1 as [ | | ? ? ? ? Ξ1a Ξ1b ? P'' Heq Htail ]; subst.
    cbn [app]. rewrite <- (aenv_app_assoc Ξ2 Ξ1b Ξ1a).
    eapply a_solve_cstr__eq;
      [ exact Heq
      | eapply IH;
          [ exact Hall' | exact Htail
          | rewrite (aenv_app_assoc Ξ1b Ξ1a Θ) in H2; exact H2 ] ].
Qed.

Lemma pskl_ghost_dec : forall (P : pskl), P = pskl_ghost \/ P <> pskl_ghost.
Proof. destruct P; solve [ left; reflexivity | right; discriminate ]. Qed.

Lemma pskl_eq_var_dec : forall (P : pskl) (a : atom),
  P = pskl_var_f a \/ P <> pskl_var_f a.
Proof.
  intros P a.
  destruct P as [ | n | b | P1 P2 | P1 | | P1 ]; try (right; discriminate).
  destruct (b == a) as [-> | Hne]; [ left; reflexivity | right; congruence ].
Qed.

Lemma inter_dom_empty_of_forall : forall (S : atoms) (Ξ : aenv),
  (forall α0, α0 `in` dom Ξ -> α0 `notin` S) ->
  S ∩ dom Ξ [=] empty.
Proof.
  intros S Ξ Hfr.
  apply AtomSetProperties.empty_is_empty_1.
  intros x Hx. apply AtomSetFacts.inter_iff in Hx. destruct Hx as [H1 H2].
  exact (Hfr x H2 H1).
Qed.

Lemma a_lookeq_all_flex_mono : forall Θ α P P0 Ξ 𝒞,
  {{ Θ ⊢ P ∼[ α ] P0 ⤳ Ξ ⨾ 𝒞 }}a -> all_flex_mono Ξ.
Proof.
  intros Θ α P P0 Ξ 𝒞 H; unfold all_flex_mono; induction H.
  - constructor.
  - constructor.
  - constructor.
  - constructor; [ reflexivity | constructor ].
  - apply Forall_app; split; assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma msubst_pskl_lookup_congr : forall κ σ P,
  (forall α, msubst_lookup κ α = msubst_lookup σ α) ->
  msubst_pskl κ P = msubst_pskl σ P.
Proof.
  intros κ σ P Heq;
    induction P as [ | n | α | P1 IHP1 P2 IHP2 | P0 IHP0 | | P0 IHP0 ];
    simpl; try reflexivity.
  - rewrite Heq; reflexivity.
  - rewrite IHP1, IHP2; reflexivity.
  - rewrite IHP0; reflexivity.
  - rewrite IHP0; reflexivity.
Qed.

Lemma msubst_lookup_app_swap : forall κa κb κ α,
  (forall β, β `in` dom κa -> β `notin` dom κb) ->
  msubst_lookup (κa ++ κb ++ κ) α = msubst_lookup (κb ++ κa ++ κ) α.
Proof.
  intros κa κb κ α Hdisj.
  destruct (AtomSetProperties.In_dec α (dom κa)) as [Hina | Hnina].
  - rewrite (@msubst_lookup_app_in κa (κb ++ κ) α Hina).
    rewrite (@msubst_lookup_app_notin κb (κa ++ κ) α (Hdisj α Hina)).
    rewrite (@msubst_lookup_app_in κa κ α Hina). reflexivity.
  - rewrite (@msubst_lookup_app_notin κa (κb ++ κ) α Hnina).
    destruct (AtomSetProperties.In_dec α (dom κb)) as [Hinb | Hninb].
    + rewrite (@msubst_lookup_app_in κb (κa ++ κ) α Hinb).
      rewrite (@msubst_lookup_app_in κb κ α Hinb). reflexivity.
    + rewrite (@msubst_lookup_app_notin κb (κa ++ κ) α Hninb).
      rewrite (@msubst_lookup_app_notin κb κ α Hninb).
      rewrite (@msubst_lookup_app_notin κa κ α Hnina). reflexivity.
Qed.

Lemma msubst_pskl_app_swap : forall κa κb κ P,
  (forall β, β `in` dom κa -> β `notin` dom κb) ->
  msubst_pskl (κa ++ κb ++ κ) P = msubst_pskl (κb ++ κa ++ κ) P.
Proof.
  intros κa κb κ P Hdisj. apply msubst_pskl_lookup_congr.
  intro α. apply msubst_lookup_app_swap; exact Hdisj.
Qed.

Lemma binds_rot_app : forall (x : atom) (b : abind) A B C D,
  binds x b (A ++ B ++ C ++ D) -> binds x b (B ++ C ++ A ++ D).
Proof. intros x b A B C D H. analyze_binds H. Qed.

Lemma binds_rot_app_rev : forall (x : atom) (b : abind) A B C D,
  binds x b (B ++ C ++ A ++ D) -> binds x b (A ++ B ++ C ++ D).
Proof. intros x b A B C D H. analyze_binds H. Qed.

Lemma binds_app_perm5 : forall (x : atom) (b : abind) A B C D E,
  binds x b (A ++ B ++ C ++ D ++ E) -> binds x b (A ++ C ++ D ++ B ++ E).
Proof. intros x b A B C D E H. analyze_binds H. Qed.

Lemma a_wf_aenv_flex_prefix : forall Ξ Θ0,
  all_flex_mono Ξ -> uniq (Ξ ++ Θ0) -> {{ ⊢ Θ0 }}a -> {{ ⊢ (Ξ ++ Θ0) }}a.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros Θ0 Hfm Huq Hwf0.
  - simpl. exact Hwf0.
  - inversion Hfm as [ | ph pt Hb Hfm' ]; subst; simpl in Hb; subst b.
    simpl. apply a_wf_aenv__flex.
    + simpl_env in Huq; solve_uniq.
    + apply IH; [ exact Hfm' | simpl_env in Huq; solve_uniq | exact Hwf0 ].
Qed.

Lemma a_solve_cstr_ctx_change : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  forall Θ',
  ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
  (forall α, a_flex_tvar Θ α -> a_flex_tvar Θ' α) ->
  (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
  {{ Θ' ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a.
Proof.
  intros Θ 𝒞 P Ξ P' H; induction H; intros Θ' Hdom Hft Hfl.
  - apply a_solve_cstr__empty.
  - apply a_solve_cstr__sub. eapply (proj1 a_solve_sub_eq_ctx_change); eauto.
  - eapply a_solve_cstr__eq;
      [ eapply (proj2 a_solve_sub_eq_ctx_change);
          [ eassumption | eauto | eauto | eauto ]
      | apply IHa_solve_cstr;
          [ repeat rewrite ftvar_in_aenv_app; clear - Hdom; fsetdec
          | intros α0 Hf0; eapply a_flex_tvar_app_mono; [ exact Hft | exact Hf0 ]
          | intros P1 Hf1; eapply a_flex_app_anti; [ exact Hfl | exact Hf1 ] ] ].
Qed.

Lemma a_solve_cstr_weaken_mid_flex : forall Ξl Ξm Θ0 𝒞 P Ξ P',
  all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_a_cstrs 𝒞) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
  (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
  {{ (Ξl ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  {{ (Ξl ++ Ξm ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a.
Proof.
  intros Ξl Ξm Θ0 𝒞 P Ξ P' Hfm Hdisj HP HC Hfin Hblk Hsolve.
  remember (Ξl ++ Θ0) as Θ eqn:HeqΘ.
  revert Ξl Θ0 HeqΘ Hdisj HP HC Hfin Hblk.
  induction Hsolve; intros Ξl Θ0 HeqΘ Hdisj HP HC Hfin Hblk; subst.
  - apply a_solve_cstr__empty.
  -
    apply a_solve_cstr__sub.
    eapply a_solve_sub_weaken_mid_flex;
      [ eassumption | reflexivity | exact Hfm | exact Hdisj | exact HP
      | exact Hfin | exact Hblk ].
  -
    assert (Hb1 : forall x, x `in` dom Ξm -> x `notin` dom Ξ1)
      by (intros x Hx; specialize (Hblk x Hx);
          rewrite dom_app in Hblk; clear - Hblk; fsetdec).
    assert (Hb2 : forall x, x `in` dom Ξm -> x `notin` dom Ξ2)
      by (intros x Hx; specialize (Hblk x Hx);
          rewrite dom_app in Hblk; clear - Hblk; fsetdec).
    assert (Hmid : forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P'').
    { intros x Hx.
      pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ _ H) as Hf.
      specialize (HP x Hx). specialize (HC x Hx). specialize (Hb1 x Hx).
      simpl in HC. clear - Hf HP HC Hb1; fsetdec. }
    eapply a_solve_cstr__eq.
    + eapply a_solve_eq_weaken_mid_flex;
        [ eassumption | reflexivity | exact Hfm | exact Hdisj | exact HP
        | exact Hmid | exact Hb1 ].
    + rewrite <- (aenv_app_assoc Ξ1 Ξl (Ξm ++ Θ0)).
      apply IHHsolve;
        [ rewrite (aenv_app_assoc Ξ1 Ξl Θ0); reflexivity
        | intros x Hx; rewrite dom_app; rewrite dom_app;
          specialize (Hdisj x Hx); specialize (Hb1 x Hx);
          rewrite dom_app in Hdisj; clear - Hdisj Hb1; fsetdec
        | exact Hmid
        |
          intros x Hx; specialize (HC x Hx); simpl in HC;
          clear - HC; fsetdec
        | exact Hfin
        | exact Hb2 ].
Qed.

Lemma ftvar_in_uskl_msubst_uskl_syn_notin_dom : forall κ R α,
  α `notin` dom κ ->
  α `in` ftvar_in_uskl R ->
  α `in` ftvar_in_uskl (msubst_uskl_syn κ R).
Proof.
  intros κ R α Hdom Hin.
  rewrite <- (ftvar_in_pskl_uskl_to_pskl (msubst_uskl_syn κ R)).
  rewrite uskl_to_pskl_msubst_uskl_syn.
  apply msubst_pskl_ftv_keep; [ exact Hdom | ].
  rewrite ftvar_in_pskl_uskl_to_pskl; exact Hin.
Qed.

Ltac psia_leaf Hrec :=
  match goal with
  | HwfΘ : {{ ⊢ ?Θ }}a, Htsk : is_dskl ?ψa, Hmi : bskl_monoish ?Q |- _ =>
      let τψ := fresh "τψ" in let Hmn := fresh "Hmn" in let Heqψ := fresh "Heqψ" in
      destruct (ad_pat_consis_monoish_counterpart Hrec HwfΘ Htsk Hmi)
        as (_ & τψ & Hmn & Heqψ);
      exists τψ; repeat split;
        [ exact Hmn | exact Heqψ
        | eapply ad_pat_consis_mono_subject_wf;
            [ exact Hrec | exact Heqψ | exact Hmn ] ]
  end.

Lemma ad_pat_consis_subst_psia_mono : forall Ψs Θ Rsubj Q,
  {{ Ψs ⨟ Θ ⊢ˢ Rsubj ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  bskl_monoish Q ->
  forall R' ψa αs,
    Rsubj = subst_uskl_in_uskl ψa αs R' ->
    is_dskl ψa ->
    αs `in` ftvar_in_uskl R' ->
    exists τψ, mono_ptyp τψ /\ ψa = ptyp_to_uskl_syn τψ /\ a_wf_ptyp Θ τψ.
Proof.
  intros Ψs Θ Rsubj Q H. induction H;
    intros HwfΘ Hmi R' ψa αs HeqSubj Htsk Hα.
  -
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    + simpl in Hα; clear - Hα; exfalso; fsetdec.
    + destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj;
        [ subst ψa | discriminate HeqSubj ].
      assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ uskl_unit ∼ bskl_unit }}ad)
        by (apply ad_pat_consis__unit; assumption).
      psia_leaf Hrec.
  -
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj.
    + subst ψa.
      assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_var_f α) ∼ (bskl_var_f α) }}ad)
        by (apply ad_pat_consis__var; assumption).
      psia_leaf Hrec.
    + injection HeqSubj as ->. simpl in Hα.
      exfalso; apply Hβ; clear - Hα; fsetdec.
  -
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    +
      destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj;
        [ subst ψa | discriminate HeqSubj ].
      assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_arrow R1 R2) ∼ (bskl_arrow Q1 Q2) }}ad)
        by (eapply ad_pat_consis__arrow; [ exact H | exact H0 | exact H1 ]).
      psia_leaf Hrec.
    +
      injection HeqSubj as HeqR1 HeqR2.
      assert (HmiQ1 : bskl_monoish Q1) by (inversion Hmi; assumption).
      assert (HmiQ2 : bskl_monoish Q2) by (inversion Hmi; assumption).
      simpl in Hα; apply union_1 in Hα; destruct Hα as [Hα | Hα].
      * eapply IHad_pat_consis1;
          [ exact HwfΘ | exact HmiQ1 | exact HeqR1 | exact Htsk | exact Hα ].
      * eapply IHad_pat_consis2;
          [ exact HwfΘ | exact HmiQ2 | exact HeqR2 | exact Htsk | exact Hα ].
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    + destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj;
        [ subst ψa; inversion Htsk | discriminate HeqSubj ].
    + simpl in Hα; clear - Hα; exfalso; fsetdec.
  -  inversion Hmi.
  -  inversion Hmi.
  -
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    +
      destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj;
        [ subst ψa; inversion Htsk | discriminate HeqSubj ].
    +
      injection HeqSubj as HeqR.
      simpl in Hα.
      eapply IHad_pat_consis;
        [ exact HwfΘ | exact Hmi | exact HeqR | exact Htsk | exact Hα ].
  -
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj.
    2:{ simpl in Hα; exfalso; clear - Hα Hβ; fsetdec. }
    subst ψa.
    match goal with |- exists _, _ /\ uskl_var_f ?a = _ /\ _ =>
      exists (ptyp_var_f a) end.
    split; [ apply mono_ptyp__var | ].
    split; [ reflexivity | ].
    constructor; right; right; eexists; eassumption.
  -
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    eapply IHad_pat_consis;
      [ exact HwfΘ | apply bskl_monoish_paint; exact Hmd
      | exact HeqSubj | exact Htsk | exact Hα ].
Qed.

Lemma psia_rsubst_leaf_step : forall Ψs Θ Rsubj Q NM Δρ Ψρ ψa αs R',
  {{ Ψs ⨟ Θ ⊢ˢ Rsubj ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  bskl_monoish Q ->
  uskl_rsubst NM Θ Δρ Ψρ Rsubj (subst_uskl_in_uskl ψa αs R') ->
  R' = uskl_var_f αs ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  is_dskl ψa ->
  exists τψ, mono_ptyp τψ /\ ψa = ptyp_to_uskl_syn τψ /\ a_wf_ptyp Θ τψ.
Proof.
  intros Ψs Θ Rsubj Q NM Δρ Ψρ ψa αs R' Hcons HwfΘ Hmi Hrho HeqR Hclean Htsk.
  subst R'.
  assert (Hid : subst_uskl_in_uskl ψa αs (uskl_var_f αs) = ψa)
    by (simpl; match goal with |- context [if ?c then _ else _] => destruct c end;
        [ reflexivity | congruence ]).
  rewrite Hid in Hrho.
  destruct (uskl_rsubst_clean_eq Hrho Hclean) as [-> _].
  destruct (ad_pat_consis_monoish_counterpart Hcons HwfΘ Htsk Hmi)
    as (_ & τψ & Hmn & Heqψ).
  exists τψ; repeat split;
    [ exact Hmn | exact Heqψ
    | eapply ad_pat_consis_mono_subject_wf;
        [ exact Hcons | exact Heqψ | exact Hmn ] ].
Qed.

Lemma psia_rsubst_leaf_impossible : forall ψa αs R' βρ Δρ,
  subst_uskl_in_uskl ψa αs R' = uskl_var_f βρ ->
  βρ `in` Δρ ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  αs `notin` Δρ ->
  αs `in` ftvar_in_uskl R' ->
  False.
Proof.
  intros ψa αs R' βρ Δρ Heq Hβ Hclean Hαρ Hα.
  destruct R' as [ | nb | γ | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
    simpl in Heq; try discriminate Heq.
  destruct (eq_var γ αs) as [ -> | Hγ ]; simpl in Heq.
  -
    subst ψa. simpl in Hclean. clear - Hclean Hβ; fsetdec.
  -
    injection Heq as Heq; subst γ.
    simpl in Hα. clear - Hα Hαρ Hβ; fsetdec.
Qed.

Lemma ad_pat_consis_rsubst_psia_mono : forall Ψs Θ Rsubj Q,
  {{ Ψs ⨟ Θ ⊢ˢ Rsubj ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  bskl_monoish Q ->
  forall NM Δρ Ψρ R' ψa αs,
    uskl_rsubst NM Θ Δρ Ψρ Rsubj (subst_uskl_in_uskl ψa αs R') ->
    (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
    αs `notin` Δρ ->
    is_dskl ψa ->
    αs `in` ftvar_in_uskl R' ->
    exists τψ, mono_ptyp τψ /\ ψa = ptyp_to_uskl_syn τψ /\ a_wf_ptyp Θ τψ.
Proof.
  intros Ψs Θ Rsubj Q H. induction H;
    intros HwfΘ Hmi NM Δρ Ψρ R' ψa αs Hrho Hclean Hαρ Htsk Hα.
  -
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ uskl_unit ∼ bskl_unit }}ad)
      by (apply ad_pat_consis__unit; assumption).
    destruct (uskl_rsubst_unit_l_inv Hrho) as [ [Heq _] | Hleaf ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
  -
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_var_f α) ∼ (bskl_var_f α) }}ad)
      by (apply ad_pat_consis__var; assumption).
    destruct (uskl_rsubst_var_l_inv Hrho) as [ [Heq _] | Hleaf ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
  -
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_arrow R1 R2) ∼ (bskl_arrow Q1 Q2) }}ad)
      by (eapply ad_pat_consis__arrow; [ exact H | exact H0 | exact H1 ]).
    destruct (uskl_rsubst_arrow_l_inv Hrho) as [ [Heq _] | [ Hleaf | Hcong ] ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
    + destruct Hcong as (Ia & Ib & Ψr1 & Ψr2 & Heq & Hra & Hrb & _).
      destruct R' as [ | nb | γ | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
        simpl in Heq; try discriminate Heq.
      *
        destruct (eq_var γ αs) as [ -> | Hγ ]; simpl in Heq;
          [ | discriminate Heq ].
        eapply psia_rsubst_leaf_step;
          [ exact Hrec | exact HwfΘ | exact Hmi | exact Hrho | reflexivity
          | exact Hclean | exact Htsk ].
      *
        injection Heq as HeqA HeqB; subst Ia Ib.
        assert (HmiQ1 : bskl_monoish Q1) by (inversion Hmi; assumption).
        assert (HmiQ2 : bskl_monoish Q2) by (inversion Hmi; assumption).
        simpl in Hα; apply union_1 in Hα; destruct Hα as [Hα | Hα].
        -- eapply IHad_pat_consis1;
             [ exact HwfΘ | exact HmiQ1 | exact Hra | exact Hclean
             | exact Hαρ | exact Htsk | exact Hα ].
        -- eapply IHad_pat_consis2;
             [ exact HwfΘ | exact HmiQ2 | exact Hrb | exact Hclean
             | exact Hαρ | exact Htsk | exact Hα ].
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ uskl_ghost ∼ (pskl_to_bskl_inh P) }}ad)
      by (apply ad_pat_consis__ghost; assumption).
    destruct (uskl_rsubst_ghost_l_inv Hrho) as [ [Heq _] | Hleaf ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
  -  inversion Hmi.
  -  inversion Hmi.
  -
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_univ_ghost R) ∼ Q }}ad)
      by (apply ad_pat_consis__univ_ghost_drop; exact H).
    destruct (uskl_rsubst_univ_ghost_l_inv Hrho) as [ [Heq _] | [ Hleaf | Hcong ] ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
    + destruct Hcong as (I0 & Heq & Hr0).
      destruct R' as [ | nb | γ | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
        simpl in Heq; try discriminate Heq.
      * destruct (eq_var γ αs) as [ -> | Hγ ]; simpl in Heq;
          [ | discriminate Heq ].
        eapply psia_rsubst_leaf_step;
          [ exact Hrec | exact HwfΘ | exact Hmi | exact Hrho | reflexivity
          | exact Hclean | exact Htsk ].
      * injection Heq as Heq; subst I0.
        simpl in Hα.
        eapply IHad_pat_consis;
          [ exact HwfΘ | exact Hmi | exact Hr0 | exact Hclean
          | exact Hαρ | exact Htsk | exact Hα ].
  -
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_var_f α) ∼ Q }}ad)
      by (eapply ad_pat_consis__flex_l; [ exact H | exact H0 ]).
    destruct (uskl_rsubst_var_l_inv Hrho) as [ [Heq _] | Hleaf ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
  -
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    eapply IHad_pat_consis;
      [ exact HwfΘ | apply bskl_monoish_paint; exact Hmd
      | exact Hrho | exact Hclean | exact Hαρ | exact Htsk | exact Hα ].
Qed.

Lemma ad_pat_consis_arrow_refine_unify : forall Ψs Θ R Q,
  {{ ⊢ Θ }}a ->
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Ra Rb, R = uskl_arrow Ra Rb ->
  forall Δr Ql, delta_def_fresh Δr Θ -> {{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q }}ad ->
  lc_bskl Q ->
  exists Ψ1 Ψ2 Q1 Q2,
    Ψs [=] Ψ1 `union` Ψ2 /\
    ({{ Ψ1 ⨟ Θ ⊢ˢ Ra ∼ Q1 }}ad) /\
    ({{ Ψ2 ⨟ Θ ⊢ˢ Rb ∼ Q2 }}ad) /\
    ({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_arrow Q1 Q2) }}ad) /\
    ({{ Ψs ⨟ Θ ⊢ˢ (uskl_arrow Ra Rb) ∼ (bskl_arrow Q1 Q2) }}ad) /\
    lc_bskl (bskl_arrow Q1 Q2).
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros Ra Rb Heq Δr Ql Hdf Href Hlc;
    try discriminate Heq.
  -
    injection Heq as Hea Heb; subst.
    do 4 eexists.
    split; [ eassumption | ].
    split; [ eassumption | ].
    split; [ eassumption | ].
    split; [ exact Href | ].
    split; [ eapply ad_pat_consis__arrow; eassumption | exact Hlc ].
  -
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hdf
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdf | exact Href | reflexivity | eassumption ]
      | apply mono_bskl_lc, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_syn_guarded_r_not_all : forall Θ Δr Q Q',
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q ⊳ Q' }}ad ->
  guarded_bskl Q ->
  forall Q0, Q' <> bskl_all_inh Q0 /\ Q' <> bskl_all_syn Q0.
Proof.
  intros Θ Δr Q Q' HwfΘ Href; induction Href; intros Hg Q0;
    try solve [ inversion Hg | split; discriminate ].
  assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
  apply IHHref; [ exact HwfΘ | ].
  apply mono_bskl_guarded, mono_ptyp_to_bskl_syn; exact Hmτ.
Qed.

Lemma ad_refine_syn_msubst_guarded_not_all : forall Θ0 Θ κ P0 Q,
  {{ ⊢ Θ }}a -> κ ∷ Θ0 ⊑ Θ -> guarded_pskl P0 ->
  {{ Θ ⨟ empty ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0) ⊳ Q }}ad ->
  forall Q0, Q <> bskl_all_inh Q0 /\ Q <> bskl_all_syn Q0.
Proof.
  intros Θ0 Θ κ P0 Q HwfΘ Hκ Hg Href.
  apply (ad_refine_syn_guarded_r_not_all HwfΘ Href).
  apply guarded_pskl_to_bskl_inh; eapply guarded_pskl_msubst_inc; eassumption.
Qed.

Lemma a_wf_pskl_arrow_guarded : forall Θ Δ P1 P2,
  {{ Θ ⨟ Δ ⊢ₚₛ pskl_arrow P1 P2 }}a -> guarded_pskl (pskl_arrow P1 P2).
Proof.
  intros Θ Δ P1 P2 Hwf.
  pose proof (a_wf_pskl_lc Hwf) as Hlc; inversion Hlc; subst.
  apply guarded_pskl__arrow; assumption.
Qed.

Lemma ad_refine_syn_guarded_r_all : forall Θ Δr Q Q',
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q ⊳ Q' }}ad ->
  guarded_bskl Q ->
  (exists Q0, Q' = bskl_all_inh Q0 \/ Q' = bskl_all_syn Q0) ->
  guarded_bskl Q'.
Proof.
  intros Θ Δr Q Q' HwfΘ Href Hg (Q0 & HQ0).
  exfalso. destruct (ad_refine_syn_guarded_r_not_all HwfΘ Href Hg Q0).
  destruct HQ0; contradiction.
Qed.

Lemma ad_refine_syn_univ_ghost_rhs_src : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Q0, Q = bskl_univ_ghost Q0 ->
  (exists L0, Q' = bskl_univ_ghost L0) \/ Q' = bskl_ghost.
Proof.
  intros Θ Δr Q' Q HwfΘ Href; induction Href; intros Q0 Heq;
    try discriminate Heq.
  -
    right; reflexivity.
  -  left; eexists; reflexivity.
  -  left; eexists; reflexivity.
  -
    exfalso.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHref HwfΘ Q0 Heq) as [[L0 HL0] | HL0];
      destruct τ; simpl in HL0; try discriminate HL0; inversion Hmτ.
Qed.

Lemma ad_pat_consis_univ_ghost_guarded_unify : forall Ψs Θ R Q,
  {{ ⊢ Θ }}a ->
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall R0, R = uskl_univ_ghost R0 ->
  forall Δr Ql, delta_def_fresh Δr Θ -> {{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q }}ad ->
  guarded_bskl Q ->
  lc_bskl Q ->
  exists Q0,
    ({{ Ψs ⨟ Θ ⊢ˢ R0 ∼ Q0 }}ad) /\
    ({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q0 }}ad) /\
    guarded_bskl Q0 /\ lc_bskl Q0.
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros R0 Heq Δr Ql Hdf Href Hg Hlc;
    try discriminate Heq.
  -  inversion Hg.
  -  inversion Hg.
  -
    injection Heq as He; subst.
    eexists; split; [ eassumption | split; [ exact Href | split; [ exact Hg | exact Hlc ] ] ].
  -
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hdf
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdf | exact Href | reflexivity | eassumption ]
      | apply mono_bskl_guarded, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto
      | apply mono_bskl_lc, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_pat_consis_dot_univ_ghost_refine_unify : forall Ψs Θ R Q,
  {{ ⊢ Θ }}a ->
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall R0, R = uskl_dot_univ_ghost R0 ->
  forall Δr Ql, delta_def_fresh Δr Θ -> {{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q }}ad ->
  lc_bskl Q ->
  exists Q0,
    ({{ Ψs ⨟ Θ ⊢ˢ R0 ∼ Q0 }}ad) /\
    ({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_univ_ghost Q0) }}ad) /\
    lc_bskl Q0.
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros R0 Heq Δr Ql Hdf Href Hlc;
    try discriminate Heq.
  -
    injection Heq as He; subst.
    eexists; split; [ eassumption | split; [ exact Href | inversion Hlc; assumption ] ].
  -
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hdf
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdf | exact Href | reflexivity | eassumption ]
      | apply mono_bskl_lc, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma a_wf_ptyp_mono_strip_tvar : forall β Θ τ,
  mono_ptyp τ ->
  a_wf_ptyp ((β ~ abind_tvar) ++ Θ) τ ->
  β `notin` ftvar_in_ptyp τ ->
  a_wf_ptyp Θ τ.
Proof.
  intros β Θ τ Hm; induction Hm; intros Hwf Hfr; simpl in Hfr.
  - apply a_wf_ptyp__unit.
  - inversion Hwf; subst.
    apply a_wf_ptyp__var.
    apply (@a_binds_tvar_strip_mid α β abind_tvar nil Θ);
      [ assumption | intro Hc; inversion Hc; subst; clear - Hfr; fsetdec
      | intro Hc; inversion Hc | intros τ0 Hc; inversion Hc ].
  - inversion Hwf; subst.
    apply a_wf_ptyp__arrow;
      [ apply IHHm1; [ assumption | clear - Hfr; fsetdec ]
      | apply IHHm2; [ assumption | clear - Hfr; fsetdec ] ].
Qed.

Lemma a_inc_strip_tvar_mid : forall Ξ κa κb Θ0 β Θ,
  all_flex_mono Ξ ->
  keys κa = keys Ξ ->
  Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κa ->
  β `notin` dom Θ ->
  (κa ++ κb) ∷ (Ξ ++ (β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ) ->
  (κa ++ κb) ∷ (Ξ ++ Θ0) ⊑ Θ.
Proof.
  intros Ξ κa κb Θ0 β Θ Hfm Hmap Hfr Hβ Hinc.
  destruct (@a_inc_flex_prefix_split Ξ κa ((β ~ abind_tvar) ++ Θ0) κb
              ((β ~ abind_tvar) ++ Θ) Hfm Hmap Hinc) as [Hwm Hrest].
  destruct (a_inc_tvar_inv Hrest) as (Ξs & Θ2 & Heq & Hsuf & Hinc').
  assert (HΘ2 : Θ2 = Θ).
  { destruct Ξs as [ | [x b] Ξs' ]; simpl in Heq.
    - inversion Heq; subst; reflexivity.
    - inversion Heq; subst.
      exfalso. apply Hβ.
      repeat rewrite dom_app; simpl; clear; fsetdec. }
  subst Θ2.
  apply a_inc_flex_prefix_build; [ exact Hfm | exact Hmap | | exact Hinc' ].
  rewrite Forall_forall in Hwm, Hfr |- *.
  intros p Hp. destruct (Hwm p Hp) as [Hwfp Hmp].
  split; [ | exact Hmp ].
  eapply a_wf_ptyp_mono_strip_tvar;
    [ exact Hmp | exact Hwfp | apply Hfr; exact Hp ].
Qed.

Lemma a_solve_cstr_strip_tvar_mid : forall Ξ β Θ0 𝒞 P Ξo P',
  {{ (Ξ ++ (β ~ abind_tvar) ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ Ξo ⨾ P' }}a ->
  {{ (Ξ ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ Ξo ⨾ P' }}a.
Proof.
  intros Ξ β Θ0 𝒞 P Ξo P' H.
  eapply a_solve_cstr_ctx_change; [ exact H | | | ].
  -
    repeat rewrite ftvar_in_aenv_app; simpl; clear; fsetdec.
  - intros α Hft; destruct Hft as [Hb | [τ Hb]];
      [ left | right; exists τ ]; analyze_binds Hb.
  - intros P0 Hf; inversion Hf; subst;
      [ eapply a_flex__var | eapply a_flex__var_def ];
      apply binds_weaken; eassumption.
Qed.

Lemma solve_outputs_strip_tvar : forall {Ξs Ξc Θ0 Θ Θw κs κc κ Pa ψa β},
  all_flex_mono Ξs -> all_flex_mono Ξc ->
  keys κs = keys Ξs -> keys κc = keys Ξc ->
  Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs ->
  Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc ->
  β `notin` dom Θw -> β `notin` ftvar_in_uskl ψa -> β `notin` dom Θ ->
  β `notin` ftvar_in_pskl Pa ->
  {{ (Ξs ++ Ξc ++ (β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a ->
  {{ ⊢ (Ξc ++ (β ~ abind_tvar) ++ Θ0) }}a ->
  (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ (β ~ abind_tvar) ++ Θ0)
    ⊑ ((β ~ abind_tvar) ++ Θ) ->
  {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
  {{ ⊢ (Ξc ++ Θ0) }}a /\
  (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ.
Proof.
  intros Ξs Ξc Θ0 Θ Θw κs κc κ Pa ψa β Hfms Hfmc Hks Hkc HFs Himg
    HβΘw Hβψa HβΘ HβPa HwfPa HwfΞ Hinc.
  assert (Hβκs : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κs).
  { rewrite Forall_forall. intros p Hp.
    pose proof (forall_wf_mono_images_dom HFs p Hp) as Hb.
    clear - Hb HβΘw; fsetdec. }
  assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
  { rewrite Forall_forall in Himg |- *. intros p Hp.
    specialize (Himg p Hp). clear - Himg Hβψa; fsetdec. }
  refine (conj _ (conj _ _)).
  - rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
    apply (@a_wf_pskl_strip_tvar (Ξs ++ Ξc) β Θ0 empty Pa); [ | exact HβPa ].
    rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0)); exact HwfPa.
  - eapply a_wf_aenv_strip_mid; [ apply all_flex_mono_decls; exact Hfmc | exact HwfΞ ].
  -
    rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
    rewrite <- (list_app_assoc κs κc κ).
    apply a_inc_strip_tvar_mid with (β := β).
    + apply all_flex_mono_app; [ exact Hfms | exact Hfmc ].
    + rewrite !keys_app; rewrite Hks, Hkc; reflexivity.
    + apply Forall_app; split; [ exact Hβκs | exact Hβκc ].
    + exact HβΘ.
    + rewrite (list_app_assoc κs κc κ).
      rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0)).
      exact Hinc.
Qed.

Lemma a_solve_sub_forall_r_gen_n : forall n Θ P B Ξ P' β,
  size_pskl P <= n ->
  pskl_ghost_free (pskl_all_syn B) ->
  β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl B ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
     (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
  {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a.
Proof.
  induction n as [ | n IH ]; intros Θ P B Ξ P' β Hsz Hgf Hβ HD;
    [ exfalso; destruct P; simpl in Hsz; lia | ].
  destruct P as [ | k | α | P1 P2 | P0 | | P0 ].
  - apply a_solve_sub__forall_r with (β := β);
      [ exact Hgf | apply solve_l_off_unit | exact Hβ | exact HD ].
  - apply a_solve_sub__forall_r with (β := β);
      [ exact Hgf | apply solve_l_off_var_b | exact Hβ | exact HD ].
  -
    destruct (a_solve_sub_var_subject HD) as [-> ->].
    apply a_solve_sub__var.
  - apply a_solve_sub__forall_r with (β := β);
      [ exact Hgf | apply solve_l_off_arrow | exact Hβ | exact HD ].
  -
    destruct (a_solve_sub_inv_forall_l HD) as (β' & P'' & Hβ' & -> & Hp).
    apply a_solve_sub_ctx_exchange in Hp.
    simpl in Hsz, Hβ.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f β'))
      as Hup.
    rewrite ftvar_in_aenv_cons_tvar in Hβ'.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower B (pskl_var_f β))
      as Hlow.
    apply a_solve_sub__forall_l with (β := β').
    + clear - Hβ' Hlow. simpl in *. fsetdec.
    + apply (IH _ _ _ _ _ β).
      * rewrite size_pskl_open_pskl_wrt_pskl_var. lia.
      * exact Hgf.
      * rewrite ftvar_in_aenv_cons_tvar.
        assert (Hne : β <> β') by (clear - Hβ'; fsetdec).
        clear - Hβ Hup Hne. simpl in *. fsetdec.
      * exact Hp.
  - apply a_solve_sub__forall_r with (β := β);
      [ exact Hgf | apply solve_l_off_ghost | exact Hβ | exact HD ].
  -
    destruct (a_solve_sub_inv_univ_ghost_l HD) as (P'' & -> & Hp).
    simpl in Hsz, Hβ.
    apply a_solve_sub__univ_ghost_l.
    apply (IH _ _ _ _ _ β); [ lia | exact Hgf | exact Hβ | exact Hp ].
Qed.

Lemma a_solve_sub_forall_r_gen : forall Θ P B Ξ P' β,
  pskl_ghost_free (pskl_all_syn B) ->
  β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl B ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
     (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
  {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a.
Proof.
  intros. eapply a_solve_sub_forall_r_gen_n;
    [ apply le_n | eassumption | eassumption | eassumption ].
Qed.

Lemma a_solve_sub_open_target : forall Θ m0 Pi T Ξ Pa,
  {{ Θ ⊢ₛ Pi ≼[ m0 ] T ⤳ Ξ ⨾ Pa }}a ->
  forall B, T = pskl_all_syn B -> m0 = mode_tc ->
  exists γ,
    γ `notin` (ftvar_in_aenv Θ `union` ftvar_in_pskl Pi `union` ftvar_in_pskl B
                 `union` dom Ξ)
    /\ {{ ((γ ~ abind_tvar) ++ Θ) ⊢ₛ Pi ≼[ mode_tc ]
          (open_pskl_wrt_pskl B (pskl_var_f γ)) ⤳ Ξ ⨾ Pa }}a.
Proof.
  intros Θ m0 Pi T Ξ Pa H.
  induction H; intros B0 HT Hm0;
    try discriminate HT; try discriminate Hm0; subst.
  -
    pick fresh γ for
      (ftvar_in_aenv Θ `union` ftvar_in_pskl (pskl_var_f α)
         `union` ftvar_in_pskl B0).
    exists γ. split; [ simpl in Fr |- *; clear - Fr; fsetdec
                     | apply a_solve_sub__var ].
  -
    destruct (IHa_solve_sub B0 eq_refl eq_refl) as [γ [Hγ Hp]].
    rewrite ftvar_in_aenv_cons_tvar in Hγ.
    exists γ. split.
    + pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f β))
        as Hlo.
      simpl. clear - Hγ Hlo. fsetdec.
    + apply a_solve_sub_ctx_exchange in Hp.
      apply a_solve_sub__forall_l with (β := β); [ | exact Hp ].
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B0 (pskl_var_f γ))
        as Hup.
      rewrite ftvar_in_aenv_cons_tvar.
      simpl in H, Hup |- *. clear - H Hγ Hup. fsetdec.
  -
    destruct (IHa_solve_sub B0 eq_refl eq_refl) as [γ [Hγ Hp]].
    exists γ. split; [ simpl in Hγ |- *; clear - Hγ; fsetdec | ].
    apply a_solve_sub__univ_ghost_l; exact Hp.
  -
    exfalso. match goal with Hg : guarded_pskl _ |- _ => inversion Hg end.
  -
    injection HT as HTB; subst B0.
    match goal with
    | Hfr : ?b `notin` _ ,
      Hp : {{ ((?b ~ abind_tvar) ++ _) ⊢ₛ _ ≼[ _ ] _ ⤳ _ ⨾ _ }}a |- _ =>
        exists b;
        pose proof ((proj1 a_solve_sub_eq_generated_fresh_set)
                      _ _ _ _ _ _ Hp) as Hjf;
        rewrite ftvar_in_aenv_cons_tvar in Hjf;
        split; [ simpl in Hfr; clear - Hfr Hjf; fsetdec | exact Hp ]
    end.
  -
    exfalso. match goal with Hg : guarded_pskl _ |- _ => inversion Hg end.
Qed.

Lemma a_solve_sub_open_target_avoid : forall (L : atoms) Θ Pi B Ξ Pa,
  {{ Θ ⊢ₛ Pi ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ Pa }}a ->
  all_flex_mono Ξ ->
  ftvar_in_pskl Pa [<=] dom Ξ `union` ftvar_in_aenv Θ ->
  exists γ,
    γ `notin` (L `union` ftvar_in_aenv Θ `union` ftvar_in_pskl Pi
                 `union` ftvar_in_pskl B `union` dom Ξ
                 `union` ftvar_in_pskl Pa)
    /\ {{ ((γ ~ abind_tvar) ++ Θ) ⊢ₛ Pi ≼[ mode_tc ]
          (open_pskl_wrt_pskl B (pskl_var_f γ)) ⤳ Ξ ⨾ Pa }}a.
Proof.
  intros L Θ Pi B Ξ Pa H Hfm Hbound.
  destruct (a_solve_sub_open_target H eq_refl eq_refl) as [γ0 [Hγ0 Hd]].
  pose proof (all_flex_mono_ftvar_in_aenv Hfm) as HΞftv.
  assert (Hγ0Pa : γ0 `notin` ftvar_in_pskl Pa)
    by (clear - Hγ0 Hbound; fsetdec).
  pick fresh γ for
    (L `union` ftvar_in_aenv Θ `union` ftvar_in_pskl Pi `union` ftvar_in_pskl B
       `union` dom Ξ `union` ftvar_in_pskl Pa `union` singleton γ0).
  exists γ. split; [ clear - Fr; fsetdec | ].
  destruct (γ == γ0) as [-> | Hne]; [ exact Hd | ].
  pose proof ((proj1 (a_solve_sub_eq_swap γ0 γ)) _ _ _ _ _ _ Hd) as Hs.
  assert (Hctx : swap_aenv γ0 γ ((γ0 ~ abind_tvar) ++ Θ)
                 = (γ ~ abind_tvar) ++ Θ).
  { simpl. rewrite swap_atom_l.
    rewrite (swap_aenv_fresh_id γ0 γ Θ) by (clear - Hγ0 Fr; fsetdec).
    reflexivity. }
  rewrite Hctx in Hs.
  rewrite swap_pskl_open_var in Hs. rewrite swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id γ0 γ Pi) in Hs
    by (clear - Hγ0 Fr; fsetdec).
  rewrite (swap_pskl_fresh_id γ0 γ B) in Hs
    by (clear - Hγ0 Fr; fsetdec).
  rewrite (swap_pskl_fresh_id γ0 γ Pa) in Hs
    by (clear - Hγ0Pa Fr; fsetdec).
  rewrite (swap_aenv_fresh_id γ0 γ Ξ) in Hs
    by (clear - Hγ0 Fr HΞftv; fsetdec).
  exact Hs.
Qed.

Lemma a_solve_cstr_sub_single_inv : forall Θ m T Pi Ξ Pa,
  {{ Θ ⊩ (a_cstr_sub m T :: nil) ⨾ Pi ⤳ Ξ ⨾ Pa }}a ->
  {{ Θ ⊢ₛ Pi ≼[ m ] T ⤳ Ξ ⨾ Pa }}a.
Proof.
  intros Θ m T Pi Ξ Pa H. inversion H; subst. assumption.
Qed.

Lemma a_solve_cstr_sub_reopen : forall (L : atoms) Θ2 Pi B Ξs Pa,
  {{ Θ2 ⊩ (a_cstr_sub mode_tc (pskl_all_syn B) :: nil) ⨾ Pi ⤳ Ξs ⨾ Pa }}a ->
  all_flex_mono Ξs ->
  ftvar_in_pskl Pa [<=] dom Ξs `union` ftvar_in_aenv Θ2 ->
  (forall α0, α0 `in` dom Ξs ->
     α0 `notin` ftvar_in_a_cstrs (a_cstr_sub mode_tc (pskl_all_syn B) :: nil)) ->
  exists γ,
    γ `notin` (L `union` ftvar_in_aenv Θ2 `union` ftvar_in_pskl Pi
                 `union` ftvar_in_pskl B `union` dom Ξs `union` ftvar_in_pskl Pa)
    /\ {{ Θ2 ⊩ (a_cstr_sub mode_tc (open_pskl_wrt_pskl B (pskl_var_f γ)) :: nil)
          ⨾ Pi ⤳ Ξs ⨾ Pa }}a
    /\ (forall α0, α0 `in` dom Ξs ->
          α0 `notin` ftvar_in_a_cstrs
                       (a_cstr_sub mode_tc (open_pskl_wrt_pskl B (pskl_var_f γ))
                          :: nil)).
Proof.
  intros L Θ2 Pi B Ξs Pa Hsol Hfm Hbound Hap.
  pose proof (a_solve_cstr_sub_single_inv Hsol) as Hsolsub.
  destruct (a_solve_sub_open_target_avoid L Hsolsub Hfm Hbound)
    as [γ [Hγ Hsol']].
  exists γ. refine (conj Hγ (conj _ _)).
  - apply (@a_solve_cstr_strip_tvar_mid nil γ Θ2).
    apply a_solve_cstr__sub; exact Hsol'.
  - intros α0 Hα0.
    pose proof (Hap α0 Hα0) as Hf.
    pose proof (a_solve_sub_generated_fresh Hsol' Hα0) as Hg.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f γ)) as Hup.
    cbn [ftvar_in_a_cstrs ftvar_in_a_cstr] in Hf |- *.
    simpl in Hf, Hg, Hup.
    clear - Hf Hg Hup. fsetdec.
Qed.

Lemma a_looksub_solve_forall_l : forall n Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa β,
  size_pskl P' <= n ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl Q (pskl_var_f β))
     ≼[ α , mode_tc ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ Θ2 ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a ->
  P' <> pskl_ghost ->
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
                     `union` ftvar_in_pskl P') ->
  all_flex_mono Ξs ->
  ftvar_in_pskl Pa [<=] dom Ξs `union` ftvar_in_aenv Θ2 ->
  (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞) ->
  exists 𝒞',
    {{ Θ ⊢ (pskl_all_syn Q) ≼[ α , mode_tc ] P' ⤳ Ξ ⨾ 𝒞' }}a
    /\ {{ Θ2 ⊩ 𝒞' ⨾ Pi ⤳ Ξs ⨾ Pa }}a
    /\ (𝒞' = 𝒞
        \/ (Q = pskl_var_f α /\ Ξ = nil
            /\ exists T T', 𝒞 = a_cstr_sub mode_tc T :: nil
                          /\ 𝒞' = a_cstr_sub mode_tc T' :: nil))
    /\ (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞').
Proof.
  induction n as [ | n IHn ].
  { intros Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa β Hsz.
    exfalso. pose proof (size_pskl_min P'). lia. }
  intros Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa β Hsz Hlk Hsol Hnh Hβ Hfm Hbound Hap.

  destruct P' as [ | nq | γq | Pd1 Pd2 | B | | Pt ];
    try solve
      [ exists 𝒞;
        split; [ apply a_looksub_forall_l_adm with (β := β);
                   [ exact Hnh
                   | apply forall_r_off_nonall; intros ?; discriminate
                   | exact Hβ | exact Hlk ]
               | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ] ].

  destruct (pskl_ghost_free_dec (pskl_all_syn B)) as [Hgf | Hngf].
  2: { exists 𝒞.
       split; [ apply a_looksub_forall_l_adm with (β := β);
                  [ exact Hnh | apply forall_r_off_ghosty; exact Hngf
                  | exact Hβ | exact Hlk ]
              | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ]. }

  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_all_syn Q)))
    as [Hin | Hni].
  2: {
       assert (Hno : α `notin` ftvar_in_pskl
                       (open_pskl_wrt_pskl Q (pskl_var_f β)))
         by (apply ftv_open_absent; [ clear - Hβ; fsetdec | exact Hni ]).
       destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ Hlk Hno)
         as [-> ->].
       exists nil.
       split; [ apply a_looksub__absent; exact Hni | ].
       split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ]. }
  assert (Hβα : β <> α) by (clear - Hβ; fsetdec).
  destruct (a_looksub_open_target Hlk Hgf)
    as [ (Hvar & HΞ & H𝒞) | [b [Hb Hpeel]] ].
  -
    assert (HQ : Q = pskl_var_f α)
      by (eapply open_var_eq_var_inv; [ exact Hvar | exact Hβα ]). subst Q. subst Ξ. subst 𝒞.
    destruct (a_solve_cstr_sub_reopen (add α (ftvar_in_aenv Θ)) Hsol Hfm
                Hbound Hap) as (γ & Hγ & Hsol2 & HapG).
    pick fresh β1 for
      (add α (ftvar_in_aenv ((γ ~ abind_tvar) ++ Θ)
                `union` ftvar_in_pskl (pskl_var_f α)
                `union` ftvar_in_pskl
                          (open_pskl_wrt_pskl B (pskl_var_f γ)))).
    assert (Hleaf : {{ ((β1 ~ abind_tvar) ++ (γ ~ abind_tvar) ++ Θ)
                       ⊢ (open_pskl_wrt_pskl (pskl_var_f α) (pskl_var_f β1))
                       ≼[ α , mode_tc ]
                       (open_pskl_wrt_pskl B (pskl_var_f γ))
                       ⤳ nil ⨾ (a_cstr_sub mode_tc
                                  (open_pskl_wrt_pskl B (pskl_var_f γ))
                                :: nil) }}a).
    { unfold open_pskl_wrt_pskl; simpl. apply a_looksub__var. }
    destruct (IHn ((γ ~ abind_tvar) ++ Θ) α (pskl_var_f α)
                (open_pskl_wrt_pskl B (pskl_var_f γ)) nil
                (a_cstr_sub mode_tc (open_pskl_wrt_pskl B (pskl_var_f γ))
                 :: nil)
                Θ2 Pi Ξs Pa β1
                ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var;
                      cbn [size_pskl] in Hsz; lia)
                Hleaf Hsol2
                ltac:(apply ghost_free_open_var_neq_ghost; exact Hgf)
                ltac:(clear - Fr; fsetdec) Hfm Hbound HapG)
      as [𝒞'' [Hlk'' [Hsol'' [Hdisj Hap'']]]].
    exists 𝒞''. split.
    + apply a_looksub__forall_r with (β := γ);
        [ exact Hgf
        | simpl; clear - Hγ; fsetdec
        | simpl; clear; fsetdec
        | discriminate
        | exact Hlk'' ].
    + split; [ exact Hsol'' | ].
      split; [ | exact Hap'' ].
      right. split; [ reflexivity | ]. split; [ reflexivity | ].
      exists (pskl_all_syn B).
      destruct Hdisj as [ -> | (_ & _ & T & T' & HT & HT') ];
        [ exists (open_pskl_wrt_pskl B (pskl_var_f γ))
        | exists T' ]; split; solve [ reflexivity | exact HT' ].
  -
    assert (Hbβ : b <> β)
      by (rewrite ftvar_in_aenv_cons_tvar in Hb; clear - Hb; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
      as HupB.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower Q (pskl_var_f β))
      as HloQ.
    rewrite ftvar_in_aenv_cons_tvar in Hb.
    destruct (IHn ((b ~ abind_tvar) ++ Θ) α Q
                (open_pskl_wrt_pskl B (pskl_var_f b)) Ξ 𝒞 Θ2 Pi Ξs Pa β
                ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var;
                      cbn [size_pskl] in Hsz; lia)
                ltac:(apply a_looksub_ctx_exchange; exact Hpeel)
                Hsol
                ltac:(apply ghost_free_open_var_neq_ghost; exact Hgf)
                ltac:(rewrite ftvar_in_aenv_cons_tvar;
                      simpl in Hβ, HupB |- *;
                      clear - Hβ Hbβ HupB; fsetdec)
                Hfm Hbound Hap)
      as [𝒞'' [Hlk'' [Hsol'' [Hdisj Hap'']]]].
    exists 𝒞''. split.
    + apply a_looksub__forall_r with (β := b);
        [ exact Hgf
        | simpl; simpl in Hb; clear - Hb HloQ; fsetdec
        | exact Hin
        | discriminate
        | exact Hlk'' ].
    + split; [ exact Hsol'' | split; [ exact Hdisj | exact Hap'' ] ].
Qed.

Lemma a_looksub_solve_univ_ghost_l : forall n Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa,
  size_pskl P' <= n ->
  {{ Θ ⊢ Q ≼[ α , mode_tc ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ Θ2 ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a ->
  P' <> pskl_ghost ->
  all_flex_mono Ξs ->
  ftvar_in_pskl Pa [<=] dom Ξs `union` ftvar_in_aenv Θ2 ->
  (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞) ->
  exists 𝒞',
    {{ Θ ⊢ (pskl_univ_ghost Q) ≼[ α , mode_tc ] P' ⤳ Ξ ⨾ 𝒞' }}a
    /\ {{ Θ2 ⊩ 𝒞' ⨾ Pi ⤳ Ξs ⨾ Pa }}a
    /\ (𝒞' = 𝒞
        \/ (Q = pskl_var_f α /\ Ξ = nil
            /\ exists T T', 𝒞 = a_cstr_sub mode_tc T :: nil
                          /\ 𝒞' = a_cstr_sub mode_tc T' :: nil))
    /\ (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞').
Proof.
  induction n as [ | n IHn ].
  { intros Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa Hsz.
    exfalso. pose proof (size_pskl_min P'). lia. }
  intros Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa Hsz Hlk Hsol Hnh Hfm Hbound Hap.
  destruct P' as [ | nq | γq | Pd1 Pd2 | B | | Pt ];
    try solve
      [ exists 𝒞;
        split; [ apply a_looksub__univ_ghost_l;
                   [ exact Hnh
                   | apply forall_r_off_nonall; intros ?; discriminate
                   | exact Hlk ]
               | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ] ].
  destruct (pskl_ghost_free_dec (pskl_all_syn B)) as [Hgf | Hngf].
  2: { exists 𝒞.
       split; [ apply a_looksub__univ_ghost_l;
                  [ exact Hnh | apply forall_r_off_ghosty; exact Hngf
                  | exact Hlk ]
              | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ]. }
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_univ_ghost Q)))
    as [Hin | Hni].
  2: { simpl in Hni.
       destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ Hlk Hni)
         as [-> ->].
       exists nil.
       split; [ apply a_looksub__absent; simpl; exact Hni | ].
       split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ]. }
  destruct (a_looksub_open_target Hlk Hgf)
    as [ (Hvar & HΞ & H𝒞) | [b [Hb Hpeel]] ].
  -
    subst Q. subst Ξ. subst 𝒞.
    destruct (a_solve_cstr_sub_reopen (add α (ftvar_in_aenv Θ)) Hsol Hfm
                Hbound Hap) as (γ & Hγ & Hsol2 & HapG).
    destruct (IHn ((γ ~ abind_tvar) ++ Θ) α (pskl_var_f α)
                (open_pskl_wrt_pskl B (pskl_var_f γ)) nil
                (a_cstr_sub mode_tc (open_pskl_wrt_pskl B (pskl_var_f γ))
                 :: nil)
                Θ2 Pi Ξs Pa
                ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var;
                      cbn [size_pskl] in Hsz; lia)
                (a_looksub__var ((γ ~ abind_tvar) ++ Θ) α mode_tc
                   (open_pskl_wrt_pskl B (pskl_var_f γ)))
                Hsol2
                ltac:(apply ghost_free_open_var_neq_ghost; exact Hgf)
                Hfm Hbound HapG)
      as [𝒞'' [Hlk'' [Hsol'' [Hdisj Hap'']]]].
    exists 𝒞''. split.
    + apply a_looksub__forall_r with (β := γ);
        [ exact Hgf
        | simpl; clear - Hγ; fsetdec
        | simpl; clear; fsetdec
        | discriminate
        | exact Hlk'' ].
    + split; [ exact Hsol'' | ].
      split; [ | exact Hap'' ].
      right. split; [ reflexivity | ]. split; [ reflexivity | ].
      exists (pskl_all_syn B).
      destruct Hdisj as [ -> | (_ & _ & T & T' & HT & HT') ];
        [ exists (open_pskl_wrt_pskl B (pskl_var_f γ))
        | exists T' ]; split; solve [ reflexivity | exact HT' ].
  -
    destruct (IHn ((b ~ abind_tvar) ++ Θ) α Q
                (open_pskl_wrt_pskl B (pskl_var_f b)) Ξ 𝒞 Θ2 Pi Ξs Pa
                ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var;
                      cbn [size_pskl] in Hsz; lia)
                Hpeel Hsol
                ltac:(apply ghost_free_open_var_neq_ghost; exact Hgf)
                Hfm Hbound Hap)
      as [𝒞'' [Hlk'' [Hsol'' [Hdisj Hap'']]]].
    exists 𝒞''. split.
    + apply a_looksub__forall_r with (β := b);
        [ exact Hgf
        | simpl; simpl in Hb; clear - Hb; fsetdec
        | exact Hin
        | discriminate
        | exact Hlk'' ].
    + split; [ exact Hsol'' | split; [ exact Hdisj | exact Hap'' ] ].
Qed.

Lemma a_looksub_solve_forall_l_mode : forall Θ α m Q P' Ξ 𝒞 Θ2 Pi Ξs Pa β,
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl Q (pskl_var_f β))
     ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ Θ2 ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a ->
  P' <> pskl_ghost ->
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
                     `union` ftvar_in_pskl P') ->
  all_flex_mono Ξs ->
  ftvar_in_pskl Pa [<=] dom Ξs `union` ftvar_in_aenv Θ2 ->
  (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞) ->
  exists 𝒞',
    {{ Θ ⊢ (pskl_all_syn Q) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞' }}a
    /\ {{ Θ2 ⊩ 𝒞' ⨾ Pi ⤳ Ξs ⨾ Pa }}a
    /\ (𝒞' = 𝒞
        \/ (Q = pskl_var_f α /\ Ξ = nil
            /\ exists T T', 𝒞 = a_cstr_sub m T :: nil
                          /\ 𝒞' = a_cstr_sub m T' :: nil))
    /\ (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞').
Proof.
  intros Θ α m Q P' Ξ 𝒞 Θ2 Pi Ξs Pa β Hlk Hsol Hnh Hβ Hfm Hbound Hap.
  destruct m as [ | | m' ];
    try solve
      [ exists 𝒞;
        split; [ apply a_looksub_forall_l_adm with (β := β);
                   [ exact Hnh | apply forall_r_off_nontc; discriminate
                   | exact Hβ | exact Hlk ]
               | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ] ].
  eapply a_looksub_solve_forall_l;
    [ apply le_n | exact Hlk | exact Hsol | exact Hnh | exact Hβ
    | exact Hfm | exact Hbound | exact Hap ].
Qed.

Lemma a_looksub_solve_univ_ghost_l_mode : forall Θ α m Q P' Ξ 𝒞 Θ2 Pi Ξs Pa,
  {{ Θ ⊢ Q ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ Θ2 ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a ->
  P' <> pskl_ghost ->
  all_flex_mono Ξs ->
  ftvar_in_pskl Pa [<=] dom Ξs `union` ftvar_in_aenv Θ2 ->
  (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞) ->
  exists 𝒞',
    {{ Θ ⊢ (pskl_univ_ghost Q) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞' }}a
    /\ {{ Θ2 ⊩ 𝒞' ⨾ Pi ⤳ Ξs ⨾ Pa }}a
    /\ (𝒞' = 𝒞
        \/ (Q = pskl_var_f α /\ Ξ = nil
            /\ exists T T', 𝒞 = a_cstr_sub m T :: nil
                          /\ 𝒞' = a_cstr_sub m T' :: nil))
    /\ (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞').
Proof.
  intros Θ α m Q P' Ξ 𝒞 Θ2 Pi Ξs Pa Hlk Hsol Hnh Hfm Hbound Hap.
  destruct m as [ | | m' ];
    try solve
      [ exists 𝒞;
        split; [ apply a_looksub__univ_ghost_l;
                   [ exact Hnh | apply forall_r_off_nontc; discriminate
                   | exact Hlk ]
               | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ] ].
  eapply a_looksub_solve_univ_ghost_l;
    [ apply le_n | exact Hlk | exact Hsol | exact Hnh
    | exact Hfm | exact Hbound | exact Hap ].
Qed.

Lemma msubst_uskl_syn_open_rec : forall Θ1 ζ Θ R' R0 k,
  ζ ∷ Θ1 ⊑ Θ ->
  msubst_uskl_syn ζ (open_uskl_wrt_uskl_rec k R0 R')
  = open_uskl_wrt_uskl_rec k (msubst_uskl_syn ζ R0) (msubst_uskl_syn ζ R').
Proof.
  intros Θ1 ζ Θ R'; induction R'; intros R0 k Hinc; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - symmetry.
    apply open_uskl_wrt_uskl_rec_degree_uskl_wrt_uskl.
    apply degree_uskl_wrt_uskl_O.
    apply degree_uskl_wrt_uskl_of_lc_uskl.
    apply mono_ptyp_to_uskl_syn_lc.
    eapply a_inc_lookup_mono; exact Hinc.
Qed.

Lemma msubst_uskl_syn_open : forall Θ1 ζ Θ R α,
  ζ ∷ Θ1 ⊑ Θ ->
  α `notin` dom ζ ->
  msubst_uskl_syn ζ (open_uskl_wrt_uskl R (uskl_var_f α))
  = open_uskl_wrt_uskl (msubst_uskl_syn ζ R) (uskl_var_f α).
Proof.
  intros Θ1 ζ Θ R α Hinc Hα.
  unfold open_uskl_wrt_uskl.
  rewrite (msubst_uskl_syn_open_rec R (uskl_var_f α) 0 Hinc).
  simpl. rewrite msubst_lookup_notin by exact Hα.
  reflexivity.
Qed.

Lemma subst_msubst_uskl_syn_open : forall Θ1 κ Θ ψa α R0 β,
  κ ∷ Θ1 ⊑ Θ ->
  α `notin` dom κ ->
  β `notin` dom κ ->
  β <> α ->
  lc_uskl ψa ->
  subst_uskl_in_uskl ψa α (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β)))
  = open_uskl_wrt_uskl
      (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R0)) (uskl_var_f β).
Proof.
  intros Θ1 κ Θ ψa α R0 β Hinc Hα Hβ Hne Hlc.
  rewrite (@msubst_uskl_syn_open Θ1 κ Θ R0 β Hinc Hβ).
  rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
    [ reflexivity | auto | exact Hlc ].
Qed.

Lemma ad_pat_consis_all_syn_refine_unify : forall Ψs Θ R Q,
  {{ ⊢ Θ }}a ->
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall R0, R = uskl_all_syn R0 ->
  forall Δr Ql, delta_def_fresh Δr Θ -> {{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q }}ad ->
  lc_bskl Q ->
  exists L Q0,
    (forall α, α `notin` L ->
       {{ Ψs ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ (open_uskl_wrt_uskl R0 (uskl_var_f α))
            ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f α)) }}ad) /\
    (forall α, lc_bskl (open_bskl_wrt_bskl Q0 (bskl_var_f α))) /\
    (({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_all_inh Q0) }}ad) \/
     ({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_all_syn Q0) }}ad)).
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros R0 Heq Δr Ql Hdf Href Hlc;
    try discriminate Heq.
  -
    injection Heq as He; subst.
    exists L, Q; split; [ assumption | split; [ inversion Hlc; auto | left; exact Href ] ].
  -
    injection Heq as He; subst.
    exists L, Q; split; [ assumption | split; [ inversion Hlc; auto | right; exact Href ] ].
  -
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hdf
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdf | exact Href | reflexivity | eassumption ]
      | apply mono_bskl_lc, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_pat_consis_all_tag_refine_unify : forall Ψs Θ R Q,
  {{ ⊢ Θ }}a ->
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall εr R0, R = uskl_all_tag εr R0 ->
  forall Δr Ql, delta_def_fresh Δr Θ -> {{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q }}ad ->
  lc_bskl Q ->
  exists L Q0 Ψ0,
    (forall α, α `notin` L ->
       {{ Ψ0 ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ (open_uskl_wrt_uskl R0 (uskl_var_f α))
            ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f α)) }}ad) /\
    (forall α, lc_bskl (open_bskl_wrt_bskl Q0 (bskl_var_f α))) /\
    ((({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_all_inh Q0) }}ad) /\ Ψs [=] add εr Ψ0) \/
     (({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_all_syn Q0) }}ad) /\ Ψs [=] Ψ0)).
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros εr R0 Heq Δr Ql Hdf Href Hlc;
    try discriminate Heq.
  -
    injection Heq as He1 He2; subst.
    exists L, Q, Ψ0; split;
      [ assumption | split; [ inversion Hlc; auto | left; split; assumption ] ].
  -
    injection Heq as He1 He2; subst.
    exists L, Q, Ψ; split;
      [ assumption
      | split; [ inversion Hlc; auto | right; split; [ exact Href | clear; fsetdec ] ] ].
  -
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hdf
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdf | exact Href | reflexivity | eassumption ]
      | apply mono_bskl_lc, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Fixpoint def_ftv (Θ : aenv) : atoms :=
  match Θ with
  | nil => empty
  | (α, abind_flex_mono_def τ) :: Θ' => add α (ftvar_in_ptyp τ `union` def_ftv Θ')
  | _ :: Θ' => def_ftv Θ'
  end.

Lemma def_ftv_binds : forall Θ α τ,
  binds α (abind_flex_mono_def τ) Θ ->
  add α (ftvar_in_ptyp τ) [<=] def_ftv Θ.
Proof.
  induction Θ as [ | [x b] Θ' IH ]; intros α τ Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Heqb] | Hb'].
  - subst. simpl. clear; fsetdec.
  - specialize (IH _ _ Hb'). destruct b; simpl; clear - IH; fsetdec.
Qed.

Lemma def_ftv_dom : forall Θ, {{ ⊢ Θ }}a -> def_ftv Θ [<=] dom Θ.
Proof.
  intros Θ H; induction H; simpl; try (clear - IHa_wf_aenv; fsetdec).
  - clear; fsetdec.
  - pose proof (a_wf_ptyp_ftv_dom H0) as Hf.
    clear - Hf IHa_wf_aenv; fsetdec.
Qed.

Lemma ad_pat_consis_target_ftv : forall Ψ Θ ψ Q,
  {{ Ψ ⨟ Θ ⊢ˢ ψ ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  is_dskl ψ ->
  ftvar_in_bskl Q [<=] ftvar_in_uskl ψ `union` def_ftv Θ.
Proof.
  intros Ψ Θ ψ Q H; induction H; intros HwfΘ Htsk; simpl in *;
    try solve [ inversion Htsk | clear; fsetdec ].
  -
    inversion Htsk; subst.
    specialize (IHad_pat_consis1 HwfΘ ltac:(assumption)).
    specialize (IHad_pat_consis2 HwfΘ ltac:(assumption)).
    clear - IHad_pat_consis1 IHad_pat_consis2; fsetdec.
  -
    inversion Htsk; subst.
    match goal with Ht : forall α, α `notin` ?Lt -> is_dskl _ |- _ =>
      rename Ht into Htb; remember Lt as Lt0 eqn:HeqLt; clear HeqLt end.
    pick fresh α for (L `union` Lt0 `union` dom Θ `union` ftvar_in_bskl Q
                        `union` ftvar_in_uskl R `union` def_ftv Θ).
    specialize (H0 α ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)
                  (Htb α ltac:(auto))).
    simpl in H0.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f α)) as Hlo.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)) as Hup.
    simpl in Hup. clear - H0 Hlo Hup Fr; fsetdec.
  -
    inversion Htsk; subst.
    match goal with Ht : forall α, α `notin` ?Lt -> is_dskl _ |- _ =>
      rename Ht into Htb; remember Lt as Lt0 eqn:HeqLt; clear HeqLt end.
    pick fresh α for (L `union` Lt0 `union` dom Θ `union` ftvar_in_bskl Q
                        `union` ftvar_in_uskl R `union` def_ftv Θ).
    specialize (H0 α ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)
                  (Htb α ltac:(auto))).
    simpl in H0.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f α)) as Hlo.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)) as Hup.
    simpl in Hup. clear - H0 Hlo Hup Fr; fsetdec.
  -
    inversion Htsk; subst.
    specialize (IHad_pat_consis HwfΘ ltac:(assumption)).
    clear - IHad_pat_consis; fsetdec.
  -
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    specialize (IHad_pat_consis HwfΘ (mono_ptyp_to_uskl_syn_is_dskl Hmτ)).
    rewrite ftvar_ptyp_to_uskl_syn in IHad_pat_consis.
    pose proof (@def_ftv_binds _ _ _ H) as Hdb.
    clear - IHad_pat_consis Hdb; fsetdec.
  -
    pose proof (@def_ftv_binds _ _ _ H) as Hdb.
    clear - Hdb; fsetdec.
Qed.

Lemma ad_refine_syn_src_ftv : forall Θ Δ Q' Q0,
  {{ Θ ⨟ Δ ⊢ᵣ Q' ⊳ Q0 }}ad ->
  {{ ⊢ Θ }}a ->
  ftvar_in_bskl Q' [<=] ftvar_in_bskl Q0 `union` def_ftv Θ.
Proof.
  intros Θ Δ Q' Q0 H; induction H; intros HwfΘ; simpl in *;
    try solve [ clear; fsetdec ].
  -
    specialize (IHad_refine_syn1 HwfΘ); specialize (IHad_refine_syn2 HwfΘ).
    clear - IHad_refine_syn1 IHad_refine_syn2; fsetdec.
  -
    pick fresh α for (L `union` ftvar_in_bskl Q `union` ftvar_in_bskl Q'
                        `union` dom Θ `union` def_ftv Θ).
    specialize (H1 α ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)).
    simpl in H1.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f α)) as Hlo.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f α)) as Hup.
    simpl in Hup. clear - H1 Hlo Hup Fr; fsetdec.
  -
    specialize (IHad_refine_syn HwfΘ). clear - IHad_refine_syn; fsetdec.
  -
    pick fresh α for (L `union` ftvar_in_bskl Q `union` ftvar_in_bskl Q'
                        `union` dom Θ `union` def_ftv Θ).
    specialize (H1 α ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)).
    simpl in H1.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f α)) as Hup.
    simpl in Hup. clear - H1 Hup Fr; fsetdec.
  -
    specialize (IHad_refine_syn HwfΘ). clear - IHad_refine_syn; fsetdec.
  -
    pose proof (@def_ftv_binds _ _ _ H) as Hdb. clear - Hdb; fsetdec.
  -
    specialize (IHad_refine_syn HwfΘ).
    rewrite ftvar_ptyp_to_bskl_syn in IHad_refine_syn.
    pose proof (@def_ftv_binds _ _ _ H) as Hdb.
    clear - IHad_refine_syn Hdb; fsetdec.
Qed.

Lemma msubst_pskl_ftv_dom_lower : forall κ P,
  ftvar_in_pskl P [<=] ftvar_in_pskl (msubst_pskl κ P) `union` dom κ.
Proof.
  intros κ P α Hα.
  destruct (AtomSetProperties.In_dec α (dom κ)) as [Hd | Hd];
    [ clear - Hd; fsetdec | ].
  pose proof (@msubst_pskl_ftv_lower κ P α Hα) as Hlow.
  rewrite msubst_lookup_notin in Hlow by exact Hd.
  simpl in Hlow. clear - Hlow; fsetdec.
Qed.

Definition uskl_guarded_head (R : uskl) : Prop :=
  R = uskl_unit \/ (exists α, R = uskl_var_f α) \/
  (exists R1 R2, R = uskl_arrow R1 R2).

Definition bskl_guarded_head (Q : bskl) : Prop :=
  Q = bskl_unit \/ (exists α, Q = bskl_var_f α) \/
  (exists Q1 Q2, Q = bskl_arrow Q1 Q2).

Lemma ad_pat_consis_guarded_head_target : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  uskl_guarded_head R ->
  bskl_guarded_head Q.
Proof.
  intros Ψ Θ R Q H; induction H; intros HwfΘ Hgh;
    try solve [ destruct Hgh as [Habs | [[α Habs] | [R1 [R2 Habs]]]];
                discriminate Habs ].
  - left; reflexivity.
  - right; left; eexists; reflexivity.
  - right; right; do 2 eexists; reflexivity.
  -
    apply IHad_pat_consis; [ exact HwfΘ | ].
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct Hmτ; simpl;
      [ left; reflexivity
      | right; left; eexists; reflexivity
      | right; right; do 2 eexists; reflexivity ].
  -
    right; left; eexists; reflexivity.
Qed.

Lemma guarded_uskl_head : forall R, guarded_uskl R -> uskl_guarded_head R.
Proof.
  intros R H; inversion H;
    [ left | right; left; eexists | right; right; do 2 eexists ]; reflexivity.
Qed.

Lemma rsubst_ftv_apart_mono : forall Δρ P0 Pi P0' Pi',
  (forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi) ->
  ftvar_in_pskl P0' [<=] ftvar_in_pskl P0 ->
  ftvar_in_pskl Pi' [<=] ftvar_in_pskl Pi ->
  forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl P0' `union` ftvar_in_pskl Pi'.
Proof.
  intros Δρ P0 Pi P0' Pi' H HP HPi α0 Hα0.
  specialize (H α0 Hα0). clear - H HP HPi; fsetdec.
Qed.

Lemma a_wf_aenv_solve_block : forall Θ 𝒞 P Ξ P',
  {{ ⊢ Θ }}a -> {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  all_flex_mono Ξ -> uniq Ξ ->
  {{ ⊢ (Ξ ++ Θ) }}a.
Proof.
  intros Θ 𝒞 P Ξ P' HwfΘ HSolve Hfms Hus.
  apply a_wf_aenv_flex_prefix; [ exact Hfms | | exact HwfΘ ].
  assert (Hdd : dom Ξ ∩ dom Θ [<=] empty).
  { intros x Hx.
    assert (Hx1 : x `in` dom Ξ) by (clear - Hx; fsetdec).
    assert (Hx2 : x `in` dom Θ) by (clear - Hx; fsetdec).
    pose proof (a_solve_cstr_generated_fresh HSolve Hx1) as Hf.
    pose proof (dom_subset_ftvar_in_aenv Θ) as Hds.
    exfalso; clear - Hf Hds Hx2; fsetdec. }
  apply uniq_app_4; [ exact Hus | eapply a_wf_aenv_uniq; exact HwfΘ | exact Hdd ].
Qed.

Lemma msubst_pskl_prepend_fresh2 : forall κs κc κ P,
  (forall α0, α0 `in` dom κs -> α0 `notin` ftvar_in_pskl P) ->
  (forall α0, α0 `in` dom κc -> α0 `notin` ftvar_in_pskl P) ->
  msubst_pskl (κs ++ κc ++ κ) P = msubst_pskl κ P.
Proof.
  intros κs κc κ P Hs Hc.
  rewrite msubst_pskl_prepend_fresh by exact Hs.
  apply msubst_pskl_prepend_fresh; exact Hc.
Qed.

Lemma msubst_uskl_syn_prepend_fresh2 : forall κs κc κ R,
  (forall α0, α0 `in` dom κs -> α0 `notin` ftvar_in_uskl R) ->
  (forall α0, α0 `in` dom κc -> α0 `notin` ftvar_in_uskl R) ->
  msubst_uskl_syn (κs ++ κc ++ κ) R = msubst_uskl_syn κ R.
Proof.
  intros κs κc κ R Hs Hc.
  rewrite msubst_uskl_syn_prepend_fresh by exact Hs.
  apply msubst_uskl_syn_prepend_fresh; exact Hc.
Qed.

Lemma a_cstrs_bound_fresh : forall {Θ0 Θ κ ψa} {Ξc : aenv} {C x},
  {{ ⊢ Θ }}a -> κ ∷ Θ0 ⊑ Θ ->
  ftvar_in_a_cstrs C [<=] ftvar_in_uskl ψa `union` dom Ξc `union` dom κ
                          `union` def_ftv Θ ->
  x `notin` ftvar_in_uskl ψa `union` dom Ξc `union` dom Θ0 `union` dom Θ ->
  x `notin` ftvar_in_a_cstrs C.
Proof.
  intros Θ0 Θ κ ψa Ξc C x HwfΘ Hκ HftvC Hx.
  assert (Hxκ : x `notin` dom κ).
  { intro Hc. destruct (a_inc_dom_flex Hκ Hc) as [Hb | [τ0 Hb]];
      apply binds_In in Hb; clear - Hx Hb; fsetdec. }
  pose proof (def_ftv_dom HwfΘ) as Hdf.
  clear - HftvC Hx Hxκ Hdf; fsetdec.
Qed.

Lemma a_solve_cstr_arrow_merge :
  forall {Θ0 C1 C2 Pi Pa1 Pa2 Ξc1 Ξc2 Ξs1 Ξs2},
  Forall (fun c => exists Q, c = a_cstr_eq Q) C1 ->
  {{ (Ξc1 ++ Θ0) ⊩ C1 ⨾ Pi ⤳ Ξs1 ⨾ Pa1 }}a ->
  {{ (Ξc2 ++ Ξs1 ++ Ξc1 ++ Θ0) ⊩ C2 ⨾ Pa1 ⤳ Ξs2 ⨾ Pa2 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  all_flex_mono Ξc2 ->
  (forall x, x `in` dom Ξc2 -> x `notin` dom (Ξs1 ++ Ξc1 ++ Θ0)) ->
  (forall x, x `in` dom Ξc2 -> x `notin` ftvar_in_a_cstrs C1) ->
  {{ ((Ξc1 ++ Ξc2) ++ Θ0) ⊩ (C1 ++ C2) ⨾ Pi ⤳ (Ξs2 ++ Ξs1) ⨾ Pa2 }}a.
Proof.
  intros Θ0 C1 C2 Pi Pa1 Pa2 Ξc1 Ξc2 Ξs1 Ξs2
    Heq1 HSolve1 HSolve2 HwfPi HfmΞ2 HΞ2disj HΞ2C1.
  assert (HΞ2Ξs1 : forall x, x `in` dom Ξc2 -> x `notin` dom Ξs1)
    by (intros x Hx; pose proof (HΞ2disj x Hx) as Hf;
        repeat rewrite dom_app in Hf; clear - Hf; fsetdec).
  assert (HΞ2Ξc1Θ0 : forall x, x `in` dom Ξc2 -> x `notin` dom (Ξc1 ++ Θ0))
    by (intros x Hx; pose proof (HΞ2disj x Hx) as Hf;
        repeat rewrite dom_app in Hf; rewrite dom_app; clear - Hf; fsetdec).
  assert (HΞ2Pi : forall x, x `in` dom Ξc2 -> x `notin` ftvar_in_pskl Pi).
  { intros x Hx; pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfd;
    pose proof (HΞ2Ξc1Θ0 x Hx) as Hf; rewrite dom_app in Hf;
    simpl in Hfd; clear - Hfd Hf; fsetdec. }
  assert (HΞ2Pa1 : forall x, x `in` dom Ξc2 -> x `notin` ftvar_in_pskl Pa1).
  { intros x Hx;
    pose proof (a_solve_cstr_ftv_eq HSolve1 Heq1) as Hfe;
    pose proof (HΞ2Pi x Hx) as HxPi;
    pose proof (HΞ2C1 x Hx) as HxC1;
    pose proof (HΞ2Ξs1 x Hx) as HxS1;
    clear - Hfe HxPi HxC1 HxS1; fsetdec. }
  rewrite (aenv_app_assoc Ξc1 Ξc2 Θ0).
  eapply a_solve_cstr_app; [ exact Heq1 | | ].
  - apply a_solve_cstr_weaken_mid_flex;
      [ exact HfmΞ2 | exact HΞ2Ξc1Θ0 | exact HΞ2Pi | exact HΞ2C1
      | exact HΞ2Pa1 | exact HΞ2Ξs1 | exact HSolve1 ].
  -
    eapply a_solve_cstr_ctx_change;
      [ exact HSolve2
      | repeat rewrite ftvar_in_aenv_app; clear; fsetdec
      | intros α1 Hg; destruct Hg as [Hb | [τ Hb]];
          [ left | right; exists τ ]; apply binds_rot_app; exact Hb
      | intros P0 Hf; inversion Hf; subst;
          [ eapply a_flex__var | eapply a_flex__var_def ];
          apply binds_rot_app_rev; eassumption ].
Qed.

Lemma a_inc_arrow_merge :
  forall {Θ0 Θ κ Ξs1 Ξc1 Ξs2 Ξc2 κs1 κc1 κs2 κc2},
  all_flex_mono Ξs1 -> all_flex_mono Ξc1 ->
  all_flex_mono Ξs2 -> all_flex_mono Ξc2 ->
  keys κs1 = keys Ξs1 -> keys κc1 = keys Ξc1 ->
  keys κs2 = keys Ξs2 -> keys κc2 = keys Ξc2 ->
  κ ∷ Θ0 ⊑ Θ ->
  (κs1 ++ κc1 ++ κ) ∷ (Ξs1 ++ Ξc1 ++ Θ0) ⊑ Θ ->
  (κs2 ++ κc2 ++ κs1 ++ κc1 ++ κ) ∷ (Ξs2 ++ Ξc2 ++ Ξs1 ++ Ξc1 ++ Θ0) ⊑ Θ ->
  ((κs2 ++ κs1) ++ (κc1 ++ κc2) ++ κ)
    ∷ ((Ξs2 ++ Ξs1) ++ (Ξc1 ++ Ξc2) ++ Θ0) ⊑ Θ.
Proof.
  intros Θ0 Θ κ Ξs1 Ξc1 Ξs2 Ξc2 κs1 κc1 κs2 κc2
    Hfms1 HfmΞ1 Hfms2 HfmΞ2 Hks1 Hmap1 Hks2 Hmap2 Hκ Hinc1 Hinc2.
  destruct (@a_inc_flex_prefix_split Ξs1 κs1 (Ξc1 ++ Θ0) (κc1 ++ κ) Θ
              Hfms1 Hks1 Hinc1) as [Hws1 HincC1].
  destruct (@a_inc_flex_prefix_split Ξc1 κc1 Θ0 κ Θ HfmΞ1 Hmap1 HincC1)
    as [Hwm1 _].
  destruct (@a_inc_flex_prefix_split Ξs2 κs2 (Ξc2 ++ Ξs1 ++ Ξc1 ++ Θ0)
              (κc2 ++ κs1 ++ κc1 ++ κ) Θ Hfms2 Hks2 Hinc2) as [Hws2 HincC2].
  destruct (@a_inc_flex_prefix_split Ξc2 κc2 (Ξs1 ++ Ξc1 ++ Θ0)
              (κs1 ++ κc1 ++ κ) Θ HfmΞ2 Hmap2 HincC2) as [Hwm2 _].
  rewrite (list_app_assoc κs2 κs1 ((κc1 ++ κc2) ++ κ)).
  rewrite (list_app_assoc κc1 κc2 κ).
  rewrite (aenv_app_assoc Ξs2 Ξs1 ((Ξc1 ++ Ξc2) ++ Θ0)).
  rewrite (aenv_app_assoc Ξc1 Ξc2 Θ0).
  apply a_inc_flex_prefix_build; [ exact Hfms2 | exact Hks2 | exact Hws2 | ].
  apply a_inc_flex_prefix_build; [ exact Hfms1 | exact Hks1 | exact Hws1 | ].
  apply a_inc_flex_prefix_build; [ exact HfmΞ1 | exact Hmap1 | exact Hwm1 | ].
  apply a_inc_flex_prefix_build; [ exact HfmΞ2 | exact Hmap2 | exact Hwm2 | exact Hκ ].
Qed.

Lemma rsubst_fresh_arrow_prefix : forall {Δρ Θ κ Θw ψa κs1 κc1},
  rsubst_fresh Δρ Θ κ -> Δρ ∩ dom Θw [=] empty ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs1 ->
  Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc1 ->
  rsubst_fresh Δρ Θ (κs1 ++ κc1 ++ κ).
Proof.
  intros Δρ Θ κ Θw ψa κs1 κc1 Hrfr HΔρw Hψaap HFs1 Himg1 α0 Hα0.
  destruct (Hrfr α0 Hα0) as (Hb & Hκim & Hdef).
  refine (conj Hb (conj _ Hdef)).
  intros p Hp. apply in_app_or in Hp; destruct Hp as [Hp | Hp].
  - pose proof (forall_wf_mono_images_dom HFs1 p Hp) as Hw.
    clear - Hw HΔρw Hα0; fsetdec.
  - apply in_app_or in Hp; destruct Hp as [Hp | Hp].
    + rewrite Forall_forall in Himg1. pose proof (Himg1 p Hp) as Hi.
      clear - Hi Hψaap Hα0; fsetdec.
    + exact (Hκim p Hp).
Qed.

Lemma rsubst_fresh_shielded : forall {Δρ Θ κ P},
  rsubst_fresh Δρ Θ κ ->
  (forall α0, α0 `in` Δρ -> α0 `notin` ftvar_in_pskl P) ->
  forall α0, α0 `in` Δρ -> α0 `notin` pskl_shielded_ftv (msubst_pskl κ P).
Proof.
  intros Δρ Θ κ P Hrfr HP α0 Hα0.
  pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ P)) as Hsh.
  enough (Hne : α0 `notin` ftvar_in_pskl (msubst_pskl κ P))
    by (clear - Hsh Hne; fsetdec).
  destruct (Hrfr α0 Hα0) as (_ & Hκim & _).
  apply msubst_pskl_ftv_avoid; [ exact Hκim | exact (HP α0 Hα0) ].
Qed.

Lemma arrow_merge_scopes : forall {Θ0 Ξs1 Ξc1 Ξs2 Ξc2 Pa2 C1 C2},
  uniq Ξs1 -> uniq Ξs2 -> all_flex_mono Ξc1 -> all_flex_mono Ξc2 ->
  {{ ⊢ Θ0 }}a ->
  (forall x, x `in` dom Ξs2 -> x `notin` dom Ξs1 `union` ftvar_in_a_cstrs C1) ->
  (forall x, x `in` dom Ξs2 -> x `notin` ftvar_in_a_cstrs C2) ->
  (forall x, x `in` dom Ξs1 -> x `notin` ftvar_in_a_cstrs C1) ->
  (forall x, x `in` dom Ξs1 -> x `notin` ftvar_in_a_cstrs C2) ->
  {{ ⊢ (Ξc2 ++ Ξs1 ++ Ξc1 ++ Θ0) }}a ->
  {{ (Ξs2 ++ Ξc2 ++ Ξs1 ++ Ξc1 ++ Θ0) ⨟ empty ⊢ₚₛ Pa2 }}a ->
  uniq (Ξs2 ++ Ξs1) /\
  {{ ((Ξs2 ++ Ξs1) ++ (Ξc1 ++ Ξc2) ++ Θ0) ⨟ empty ⊢ₚₛ Pa2 }}a /\
  {{ ⊢ ((Ξc1 ++ Ξc2) ++ Θ0) }}a /\
  (forall x, x `in` dom (Ξs2 ++ Ξs1) -> x `notin` ftvar_in_a_cstrs (C1 ++ C2)).
Proof.
  intros Θ0 Ξs1 Ξc1 Ξs2 Ξc2 Pa2 C1 C2 Hus1 Hus2 HfmΞ1 HfmΞ2 HwfΘ0
    HΞs2 Hapart2 Hapart1 HC2s1 HwfΞ2 HwfPa2.
  refine (conj _ (conj _ (conj _ _))).
  - assert (Hdd : dom Ξs2 ∩ dom Ξs1 [<=] empty).
    { intros x Hx.
      assert (Hx2 : x `in` dom Ξs2) by (clear - Hx; fsetdec).
      assert (Hx1 : x `in` dom Ξs1) by (clear - Hx; fsetdec).
      pose proof (HΞs2 x Hx2) as Hf. exfalso; clear - Hf Hx1; fsetdec. }
    apply uniq_app_4; [ exact Hus2 | exact Hus1 | exact Hdd ].
  - eapply a_wf_pskl_weaken; [ | exact HwfPa2 ].
    intros x b Hb.
    rewrite (aenv_app_assoc Ξs2 Ξs1 ((Ξc1 ++ Ξc2) ++ Θ0)).
    rewrite (aenv_app_assoc Ξc1 Ξc2 Θ0).
    apply binds_app_perm5; exact Hb.
  - apply a_wf_aenv_flex_prefix; [ apply all_flex_mono_app; assumption | | exact HwfΘ0 ].
    pose proof (a_wf_aenv_uniq HwfΞ2) as Huq. clear - Huq; solve_uniq.
  - intros x Hx. rewrite dom_app in Hx. rewrite ftvar_in_a_cstrs_app.
    destruct (AtomSetProperties.In_dec x (dom Ξs2)) as [Hin2 | Hnin2].
    + pose proof (Hapart2 x Hin2) as Ha2. pose proof (HΞs2 x Hin2) as Hf2.
      clear - Ha2 Hf2. fsetdec.
    + assert (Hin1 : x `in` dom Ξs1) by (clear - Hx Hnin2; fsetdec).
      pose proof (Hapart1 x Hin1) as Ha1. pose proof (HC2s1 x Hin1) as Hc2.
      clear - Ha1 Hc2. fsetdec.
Qed.

Lemma solve_scope_arrow_prefix : forall {Θ0 Θ Θw κ ψa Ξs1 Ξc1 κs1 κc1},
  solve_scope Θ0 Θ Θw κ -> ftvar_in_uskl ψa [<=] dom Θw ->
  keys κc1 = keys Ξc1 ->
  Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc1 ->
  keys κs1 = keys Ξs1 ->
  Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs1 ->
  solve_scope (Ξs1 ++ Ξc1 ++ Θ0) Θ Θw (κs1 ++ κc1 ++ κ).
Proof.
  intros Θ0 Θ Θw κ ψa Ξs1 Ξc1 κs1 κc1 Hsc Hψaw Hmap1 Himg1 Hks1 HFs1.
  apply solve_scope_flex_prefix;
    [ | exact Hks1 | exact (forall_wf_mono_images_dom HFs1) ].
  apply solve_scope_flex_prefix; [ exact Hsc | exact Hmap1 | ].
  intros p Hp. rewrite Forall_forall in Himg1.
  pose proof (Himg1 p Hp) as Hb. clear - Hb Hψaw; fsetdec.
Qed.

Lemma rsubst_component_tags : forall {NM Θ Δρ Ψρc Ψc Rsub Rc ψa α κ Ψ'},
  Ψc [<=] ftag_in_uskl Rsub ->
  uskl_rsubst NM Θ Δρ Ψρc Rsub (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ Rc)) ->
  Ψ' [=] ftag_in_uskl ψa ->
  Ψc [<=] union (ftag_in_uskl Rc) (union Ψρc (Ψc ∩ Ψ')).
Proof.
  intros NM Θ Δρ Ψρc Ψc Rsub Rc ψa α κ Ψ' Hf Hrho Hψatag.
  pose proof (uskl_rsubst_ftag_sub Hrho) as Hr.
  pose proof (ftag_in_uskl_subst_uskl_in_uskl ψa α (msubst_uskl_syn κ Rc)) as Hb.
  pose proof (ftag_in_uskl_msubst_uskl_syn κ Rc) as Hm.
  clear - Hf Hr Hb Hm Hψatag; fsetdec.
Qed.

Lemma msubst_pskl_arrow_merge : forall κs1 κc1 κs2 κc2 κ P,
  (forall β0, β0 `in` dom κc1 -> β0 `notin` dom κc2) ->
  (forall β0, β0 `in` dom κc2 -> β0 `notin` dom κs1) ->
  msubst_pskl ((κs2 ++ κs1) ++ (κc1 ++ κc2) ++ κ) P
  = msubst_pskl (κs2 ++ κc2 ++ κs1 ++ κc1 ++ κ) P.
Proof.
  intros κs1 κc1 κs2 κc2 κ P Hdisj12 Hdisj2s1.
  rewrite (list_app_assoc κs2 κs1 ((κc1 ++ κc2) ++ κ)).
  rewrite (list_app_assoc κc1 κc2 κ).
  apply msubst_pskl_lookup_congr. intro β.
  apply msubst_lookup_app_agree.
  rewrite (@msubst_lookup_app_swap κc2 κs1 (κc1 ++ κ) β Hdisj2s1).
  apply msubst_lookup_app_agree.
  apply (@msubst_lookup_app_swap κc1 κc2 κ β Hdisj12).
Qed.

Lemma a_lookeq_flex_p0_complete :
  forall NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q Pi R' α Θs Δρ Ψρ Rsub β0 L,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a -> {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (pskl_var_f β0) }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α0, a_flex_tvar Θ0 α0 ->
     ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw) ->
  ftvar_in_uskl ψa [<=] dom Θw ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  {{ Ψsub ⨟ Θ ⊢ˢ Rsub ∼ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β0))) ⊳ Q }}ad ->
  uskl_rsubst NM Θs Δρ Ψρ Rsub
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ->
  (forall x b, binds x b Θs -> binds x b Θ) ->
  rsubst_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  Δρ ∩ dom Θw [=] empty ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl (pskl_var_f β0) `union` ftvar_in_pskl Pi) ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  ftvar_in_uskl ψa ∩ Δρ [=] empty ->
  ftvar_in_aenv Θ0 [<=] L ->
  Δρ [<=] dom Θ -> Δρ [<=] dom Θ0 ->
  (forall κ0 : list (atom * ptyp),
     Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ0 ->
     Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ0) ->
  (forall α0 τ0, binds α0 (abind_flex_mono_def τ0) Θ ->
     binds α0 (abind_flex_mono_def τ0) Θw) ->
  ⌊ R' ⌋ˢ <> pskl_var_f α ->
  α `in` ftvar_in_pskl ⌊ R' ⌋ˢ ->
  α `notin` dom κ ->
  (forall p : atom * ptyp, In p κ -> α `notin` ftvar_in_ptyp (snd p)) ->
  α `in` ftvar_in_uskl R' ->
  a_binds_tvar β0 Θ0 ->
  a_flex_tvar Θ0 β0 ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    {{ Θ0 ⊢ ⌊ R' ⌋ˢ ∼[ α ] (pskl_var_f β0) ⤳ Ξc ⨾ 𝒞 }}a /\
    {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
    all_flex_mono Ξs /\ uniq Ξs /\ keys κs = keys Ξs /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` L) /\
    Forall (fun p : atom * ptyp =>
              a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
    {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξc ++ Θ0) }}a /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p : atom * ptyp =>
              ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    ftvar_in_a_cstrs 𝒞
      [<=] ftvar_in_uskl ψa `union` dom Ξc `union` dom κ `union` def_ftv Θ /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa)
        ⊑ᵖ[ (Ψi `union` Ψa) ] ψa }}ad /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞).
Proof.
  intros NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q Pi R' α Θs Δρ Ψρ Rsub β0 L
    HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0 HwfPi Hκ Hκw Hψaw HαΘ HαΘ0
    Htags Hsub Hdfresh Hpre Hcons0 Hrefine Hrho0 HΘs Hrfr HΔρΔ HΔρw
    HΔρftv HΔρPi Hψaap HL HΔρΘ HΔρΘ0 HFw Hdefs HPnα Hin Hακdom Hκav
    HαR Hbt0 Hflx.

set (τ0 := msubst_lookup κ β0) in *.
assert (Hτ0mono : mono_ptyp τ0) by (eapply a_inc_lookup_mono; eauto).
assert (Hmsβ : msubst_pskl κ (pskl_var_f β0) = ptyp_to_pskl τ0)
  by reflexivity.
rewrite Hmsβ in Hrefine.
rewrite (ptyp_to_bskl_inh_syn_eq Hτ0mono) in Hrefine.

assert (Hmi : bskl_monoish (Q))
  by (eapply ad_refine_mono_paint_rhs_monoish;
        [ exact HwfΘ | exact Hrefine | reflexivity | exact Hτ0mono ]).

assert (Htskψa : is_dskl ψa) by (inversion Htags; subst; assumption).
assert (HαT : α `in` ftvar_in_uskl (msubst_uskl_syn κ (R')))
  by (apply ftvar_in_uskl_msubst_uskl_syn_notin_dom;
        [ exact Hακdom | simpl; exact HαR ]).
assert (Hαρ : α `notin` Δρ).
{ intro Hc. destruct (Hrfr α Hc) as (Hb & _ & _).
  apply binds_In in Hb. contradiction. }
destruct (@ad_pat_consis_rsubst_psia_mono Ψsub Θ
            (Rsub) (Q) Hcons0 HwfΘ Hmi
            NM Δρ Ψρ (msubst_uskl_syn κ (R')) ψa α
            ltac:(eapply uskl_rsubst_weaken; [ exact Hrho0 | exact HΘs ])
            Hψaap Hαρ Htskψa HαT)
  as (τψ & Hτψmono & Heqψ & Hτψwf).

assert (HΨ'e : Ψ' [=] empty).
{ pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as HΨ't.
  rewrite Heqψ in HΨ't. rewrite ftag_ptyp_to_uskl_syn in HΨ't.
  exact HΨ't. }
assert (HΨie : Ψi [=] empty) by (clear - Hsub HΨ'e; fsetdec).
assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
pick fresh α1 for
  (add α (dom Θ0 `union` dom Θ) `union` dom Θ `union` dom κ `union` ftvar_in_pskl Pi
     `union` ftvar_in_uskl ψa
     `union` ftvar_in_aenv Θ0 `union` singleton β0
     `union` ftvar_in_pskl ⌊ R' ⌋ˢ).
assert (Hγdom0 : α1 `notin` dom Θ0) by auto.

assert (Hbγ : binds α1 abind_flex_mono (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0))
  by (simpl_env; auto).
assert (Hτψwfw : a_wf_ptyp Θw τψ).
{ eapply a_wf_ptyp_mono_strengthen_dom;
    [ exact HwfΘ | exact Hmon | exact Hτψmono | exact Hτψwf | ].
  rewrite Heqψ in Hψaw.
  rewrite ftvar_ptyp_to_uskl_syn in Hψaw. exact Hψaw. }

assert (HgΘ : ftvar_in_aenv (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0)
                [<=] add α1 (L `union` ftvar_in_aenv Θ0))
  by (simpl_env; simpl; clear; fsetdec).
assert (WIT : forall Pi0 τw,
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi0 }}a ->
  α1 `notin` ftvar_in_pskl Pi0 ->
  mono_ptyp τw -> a_wf_ptyp Θw τw ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi0) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τw) }}ad ->
  nonghost_pskl Pi0 -> (forall a, Pi0 <> pskl_var_f a) ->
  (forall κ' P, {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ' P) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τw) }}ad ->
     {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ' P) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad) ->
  exists Ξg Pa κg,
    {{ (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0) ⊢ₑ Pi0 ∼ (pskl_var_f α1)
       ⤳ Ξg ⨾ Pa }}a /\
    all_flex_mono Ξg /\ uniq Ξg /\ keys κg = keys Ξg /\
    (forall α2, α2 `in` dom Ξg -> α2 `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κg /\
    {{ Θ ⨟ Δ ⊢ˢ msubst_pskl (κg ++ ((α1, τψ) :: κ)) Pa
        ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad).
{ intros Pi0 τw HwfPi0 Hα1Pi0 Hm0 Hwf0 Hpre0 Hng Hnv Hpost.
  assert (Hprefix : msubst_pskl ((α1, τψ) :: κ) Pi0
                    = msubst_pskl κ Pi0).
  { change ((α1, τψ) :: κ) with (((α1, τψ) :: nil) ++ κ).
    apply msubst_pskl_prepend_fresh.
    intros α2 Hα2; cbn in Hα2.
    assert (α2 = α1) by (clear - Hα2; fsetdec); subst α2.
    exact Hα1Pi0. }
  destruct (@a_guess_ty_witness_mono (size_pskl Pi0) Θ0 Θ Θw
              ((α1, τψ) :: κ) Δ Ψi τw Pi0
              ltac:(reflexivity) HwfΘ HwfΘw Hmon Hdefs HwfPi0
              Hm0 Hwf0
              ltac:(rewrite Hprefix; exact Hpre0)
              (add α1 (L `union` ftvar_in_aenv Θ0)))
    as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
  exists Ξg, (ptyp_to_pskl Ag), κg.
  refine (conj _ (conj Hfmg (conj Hug (conj Hkg (conj _ (conj HFg (Hpost _ _ Hqg))))))).
  - apply a_solve_eq__flex_r.
    + left; exact Hbγ.
    + split; [ eapply a_wf_pskl_lc; exact HwfPi0 | ].
      intros Hf; inversion Hf; subst; eapply Hnv; reflexivity.
    + exact Hng.
    + apply Hgu; exact HgΘ.
  - intros α2 Hα2; pose proof (Hfrg α2 Hα2) as Hnf2; clear - Hnf2; fsetdec. }
assert (HPa : exists Ξs Pa κs,
  {{ (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0) ⊢ₑ Pi ∼ (pskl_var_f α1)
     ⤳ Ξs ⨾ Pa }}a /\
  all_flex_mono Ξs /\ uniq Ξs /\ keys κs = keys Ξs /\
  (forall α2, α2 `in` dom Ξs -> α2 `notin` L) /\
  Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
  {{ Θ ⨟ Δ ⊢ˢ msubst_pskl (κs ++ ((α1, τψ) :: κ)) Pa
      ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad).
{ assert (Hlcpi : lc_pskl Pi) by (eapply a_wf_pskl_lc; exact HwfPi).
  assert (Hα1Pi : α1 `notin` ftvar_in_pskl Pi) by (clear - Fr; solve_notin).
  assert (Hflexpa : {{ Θ ⨟ Δ ⊢ˢ msubst_pskl (nil ++ ((α1, τψ) :: κ))
                              (pskl_var_f α1)
                      ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad).
  { cbn [app].
    replace (msubst_pskl ((α1, τψ) :: κ) (pskl_var_f α1))
      with (ptyp_to_pskl τψ)
      by (cbn [msubst_pskl msubst_lookup];
          match goal with |- context [if ?c then _ else _] => destruct c end;
          [ reflexivity | contradiction ]).
    rewrite Heqψ.
    eapply ad_partial_precise_psi_cong;
      [ apply ad_ppre_mono_refl; exact Hτψmono
      | clear - HΨie HΨae; fsetdec ]. }
  assert (Hpreψ : {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ]
                     (ptyp_to_uskl_syn τψ) }}ad)
    by (rewrite <- Heqψ; exact Hpre).
  assert (Hpost : forall κ' P,
            {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ' P) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τψ) }}ad ->
            {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ' P) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad)
    by (intros κ' P Hq; rewrite Heqψ;
        eapply ad_partial_precise_psi_cong; [ exact Hq | clear - HΨae; fsetdec ]).
  destruct Pi as [ | nbi | α0 | Pi1 Pi2 | Pib | | Pit ].
  -
    refine (WIT pskl_unit τψ HwfPi Hα1Pi Hτψmono Hτψwfw Hpreψ
              nonghost_pskl__unit _ Hpost).
    intros a; discriminate.
  -  inversion HwfPi.
  -
    exists nil, (pskl_var_f α0), (@nil (atom * ptyp)).
    split; [ apply a_solve_eq__var | ].
    split; [ apply Forall_nil | ]. split; [ apply uniq_nil | ].
    split; [ reflexivity | ].
    split; [ intros α2 Hα2; cbn in Hα2; exfalso; clear - Hα2; fsetdec | ].
    split; [ apply Forall_nil | ].
    assert (Hα0γ : α0 <> α1)
      by (intro Hc; subst α1; clear - Hα1Pi; cbn in Hα1Pi; fsetdec).
    cbn [app].
    replace (msubst_pskl ((α1, τψ) :: κ) (pskl_var_f α0))
      with (msubst_pskl κ (pskl_var_f α0))
      by (cbn [msubst_pskl msubst_lookup];
          match goal with |- context [if ?c then _ else _] => destruct c end;
          [ contradiction | reflexivity ]).
    eapply ad_partial_precise_psi_cong;
      [ exact Hpre | clear - HΨae; fsetdec ].
  -
    refine (WIT (pskl_arrow Pi1 Pi2) τψ HwfPi Hα1Pi Hτψmono Hτψwfw Hpreψ
              (nonghost_pskl__arrow _ _) _ Hpost).
    intros a; discriminate.
  -
    refine (WIT (pskl_all_syn Pib) τψ HwfPi Hα1Pi Hτψmono Hτψwfw Hpreψ
              (nonghost_pskl__all _) _ Hpost).
    intros a; discriminate.
  -
    exists nil, (pskl_var_f α1), (@nil (atom * ptyp)).
    split; [ apply a_solve_eq__ghost_l | ].
    split; [ apply Forall_nil | ]. split; [ apply uniq_nil | ].
    split; [ reflexivity | ].
    split; [ intros α2 Hα2; cbn in Hα2; exfalso; clear - Hα2; fsetdec | ].
    split; [ apply Forall_nil | ].
    exact Hflexpa.
  -
    assert (Hg : guarded_pskl Pit /\ ({{ Θ0 ⨟ empty ⊢ₚₛ Pit }}a))
      by (exact (a_wf_pskl_univ_ghost_inv HwfPi)).
    destruct Hg as [HgPit HwfPit].
    assert (Hα1Pit : α1 `notin` ftvar_in_pskl Pit)
      by (clear - Hα1Pi; cbn in Hα1Pi; exact Hα1Pi).
    destruct (@ad_ppre_univ_ghost_subject_chain_inv Θ Δ Ψi
                (msubst_pskl κ (pskl_univ_ghost Pit)) ψa HwfΘ Hpre
                (msubst_pskl κ Pit) eq_refl τψ Heqψ Hτψmono)
      as (τe & Hchain & Hmτe & Hpree).
    assert (Hτewfw : a_wf_ptyp Θw τe)
      by (eapply a_def_chain_wf_at;
            [ exact Hchain | exact HwfΘw | exact Hdefs | exact Hτψwfw ]).

    assert (Hpostc : forall κ' P,
              {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ' P) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τe) }}ad ->
              {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ' P) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad).
    { intros κ' P Hq. rewrite Heqψ.
      eapply ad_partial_precise_psi_cong;
        [ eapply ad_ppre_chain_fold; [ exact Hchain | exact Hq ]
        | clear - HΨae; fsetdec ]. }
    destruct HgPit as [ | α0 | Pit1 Pit2 ].
    +
      assert (Hnv : forall a, pskl_unit <> pskl_var_f a) by (intros a; discriminate).
      destruct (WIT pskl_unit τe HwfPit Hα1Pit Hmτe Hτewfw Hpree
                  nonghost_pskl__unit Hnv Hpostc) as (Ξg & Pg & κg & Hsol & Hpk).
      exists Ξg, Pg, κg. refine (conj _ Hpk).
      apply a_solve_eq__univ_ghost_l_guarded; [ apply guarded_pskl__var | exact Hsol ].
    +
      exists nil, (pskl_var_f α0), (@nil (atom * ptyp)).
      split; [ apply a_solve_eq__univ_ghost_l_guarded;
                 [ apply guarded_pskl__var | apply a_solve_eq__var ] | ].
      split; [ apply Forall_nil | ]. split; [ apply uniq_nil | ].
      split; [ reflexivity | ].
      split; [ intros α2 Hα2; cbn in Hα2; exfalso; clear - Hα2; fsetdec | ].
      split; [ apply Forall_nil | ].
      assert (Hα0γ : α0 <> α1)
        by (intro Hc; subst α1; clear - Hα1Pit; cbn in Hα1Pit; fsetdec).
      cbn [app].
      replace (msubst_pskl ((α1, τψ) :: κ) (pskl_var_f α0))
        with (msubst_pskl κ (pskl_var_f α0))
        by (cbn [msubst_pskl msubst_lookup];
            match goal with |- context [if ?c then _ else _] => destruct c end;
            [ contradiction | reflexivity ]).
      rewrite Heqψ.
      eapply ad_partial_precise_psi_cong;
        [ eapply ad_ppre_chain_fold; [ exact Hchain | exact Hpree ]
        | clear - HΨae; fsetdec ].
    +
      assert (Hnv : forall a, pskl_arrow Pit1 Pit2 <> pskl_var_f a)
        by (intros a; discriminate).
      destruct (WIT (pskl_arrow Pit1 Pit2) τe HwfPit Hα1Pit Hmτe Hτewfw Hpree
                  (nonghost_pskl__arrow _ _) Hnv Hpostc)
        as (Ξg & Pg & κg & Hsol & Hpk).
      exists Ξg, Pg, κg. refine (conj _ Hpk).
      apply a_solve_eq__univ_ghost_l_guarded; [ apply guarded_pskl__var | exact Hsol ]. }
destruct HPa as (Ξs & Pa & κs & Hsolve_eq & Hfms & Hus & Hks & Hfrs
                 & HFs & Hprec).
exists (a_cstr_eq (pskl_var_f α1) :: nil),
       ((α1 ~ abind_flex_mono) ++ nil), Ξs, Pa,
       ((α1, τψ) :: nil), κs.
repeat split.
--
   apply a_lookeq__flex_r;
     solve [ cbn; clear - Fr; solve_notin
           | exact Hflx | exact HPnα | exact Hin ].
--
   apply a_solve_cstr__eq with (Ξ1 := Ξs)
        (Ξ2 := (@nil (atom * abind))) (P'' := Pa);
     [ exact Hsolve_eq | apply a_solve_cstr__empty ].
--  exact Hfms.
--  exact Hus.
--  exact Hks.
--  exact Hfrs.
--  exact HFs.
--
   eapply a_solve_eq_wf;
     [ exact Hsolve_eq
     | apply a_wf_pskl_weaken with (Θ := Θ0);
         [ intros x b Hb; apply binds_app_3; exact Hb | exact HwfPi ]
     | apply a_wf_pskl__var; right; left; exact Hbγ ].
--
   simpl_env. apply a_wf_aenv__flex; [ exact Hγdom0 | exact HwfΘ0 ].
--  simpl; clear - Fr; fsetdec.

--
   apply Forall_cons; [ | apply Forall_nil ].
   simpl. rewrite Heqψ. rewrite ftvar_ptyp_to_uskl_syn.
   clear; fsetdec.
--
   simpl; clear; fsetdec.
--
   apply a_inc_flex_prefix_build;
     [ exact Hfms | exact Hks | apply HFw; exact HFs | ].
   cbn [app]. simpl_env.
   apply a_inc__flex; [ exact Hκ | exact Hτψwf | exact Hτψmono ].
--  apply a_inc_equiv_refl; exact Hκ.
--
   intros α0 Hα0; simpl in Hα0.
   assert (α0 = α1) by (clear - Hα0; fsetdec); subst α0.
   clear - Fr; fsetdec.
--  cbn [app]. exact Hprec.
--
   intros α2 Hα2. simpl.
   pose proof (a_solve_eq_generated_fresh Hsolve_eq Hα2) as Hf.
   simpl in Hf. clear - Hf. fsetdec.
Qed.

Ltac lc_tgt :=
  match goal with
  | |- lc_bskl _ =>
      first
        [ assumption
        | solve [ eauto ]
        | match goal with
          | H : lc_bskl _ |- _ => solve [ inversion H; subst; eauto ]
          end ]
  end.

Definition lookeq_solve_result
    (Θ0 Θ Θw : aenv) (κ : metasubst) (Δ Ψi Ψa : atoms)
    (ψa : uskl) (α : atom) (P P0 Pi : pskl) (L : atoms) : Prop :=
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
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
    ftvar_in_a_cstrs 𝒞 [<=] ftvar_in_uskl ψa
                          `union` dom Ξc `union` dom κ
                          `union` def_ftv Θ /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞).

Lemma lookeq_solve_strip_tvar :
  forall Θ0 Θ Θw κ Δ Ψi Ψa ψa α P P0 Pi L Pβ P0β β,
  κ ∷ Θ0 ⊑ Θ -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  β `notin` dom Θ -> β `notin` dom Θ0 -> β `notin` dom Θw ->
  β `notin` dom κ -> β `notin` ftvar_in_uskl ψa -> β `notin` def_ftv Θ ->
  (forall Ξc 𝒞, {{ ((β ~ abind_tvar) ++ Θ0) ⊢ Pβ ∼[ α ] P0β ⤳ Ξc ⨾ 𝒞 }}a ->
     {{ Θ0 ⊢ P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 }}a) ->
  lookeq_solve_result ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) Θw κ
    Δ Ψi Ψa ψa α Pβ P0β Pi (add β L) ->
  lookeq_solve_result Θ0 Θ Θw κ Δ Ψi Ψa ψa α P P0 Pi L.
Proof.
  intros Θ0 Θ Θw κ Δ Ψi Ψa ψa α P P0 Pi L Pβ P0β β
    Hκ HwfPi HβΘ HβΘ0 HβΘw Hβκ Hβψa Hβdef Hlook REC.
  destruct REC as (𝒞 & Ξc & Ξs & Pa & κc & κs
                   & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
                   & HwfPa & HwfΞ & HαΞ
                   & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec
                   & Hapart).
  pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
  assert (HβΞc : β `notin` dom Ξc).
  { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
    apply Hκfresh. simpl; clear; fsetdec. }
  assert (HβΞs : β `notin` dom Ξs)
    by (intro Hc; pose proof (Hfrs β Hc) as Hf; clear - Hf; fsetdec).
  cbn [def_ftv] in HftvC.
  assert (HβC : β `notin` ftvar_in_a_cstrs 𝒞)
    by (clear - HftvC HβΞc Hβκ Hβψa Hβdef; fsetdec).
  assert (HβPa : β `notin` ftvar_in_pskl Pa).
  { pose proof (a_solve_cstr_ftv_eq HSolve (a_lookeq_cstr_eq HLK)) as Hpf.
    pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi.
    clear - Hpf Hfi HβC HβΘ0 HβΞs; fsetdec. }
  assert (Hfmc : all_flex_mono Ξc) by (eapply a_lookeq_all_flex_mono; exact HLK).
  destruct (solve_outputs_strip_tvar Hfms Hfmc Hks Hmapfst HFs Himg
              HβΘw Hβψa HβΘ HβPa HwfPa HwfΞ Hinc)
    as (HwfPa' & HwfΞ' & Hinc').
  exists 𝒞, Ξc, Ξs, Pa, κc, κs.
  repeat split.
  -  exact (Hlook _ _ HLK).
  -  eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
  -  exact Hfms.
  -  exact Hus.
  -  exact Hks.
  -
    intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
  -
    exact HFs.
  - exact HwfPa'.
  - exact HwfΞ'.
  -  exact HαΞ.
  -  exact Hmapfst.
  -  exact Himg.
  -  exact HftvC.
  - exact Hinc'.
  -  apply a_inc_equiv_refl; exact Hκ.
  -
    intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
    clear - Hκfresh; fsetdec.
  -
    eapply ad_partial_precise_strengthen_tvar; exact Hprec.
  -
    exact Hapart.
Qed.

Lemma a_lookeq_solve_complete_forall : forall n,
  (forall NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α Θs Δρ Ψρ Rsub,
    size_uskl R' + size_pskl P0 <= n ->
    {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
    {{ ⊢ Θw }}a ->
    (forall x b, binds x b Θw -> binds x b Θ) ->
    (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
    κ ∷ Θ0 ⊑ Θ ->
    (forall α0, a_flex_tvar Θ0 α0 ->
       ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw) ->
    ftvar_in_uskl ψa [<=] dom Θw ->
    α `notin` dom Θ -> α `notin` dom Θ0 ->
    ⌊ R' ⌋ˢ = P ->
    ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
    lc_uskl R' ->
    a_tags_sort NM Ψ' ψa ->
    (ftag_in_uskl R') ∩ Ψ' [=] empty ->
    Ψi `union` Ψa [<=] Ψ' ->
    delta_def_fresh Δ Θ ->
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
    Ψsub [<=] ftag_in_uskl R' `union` Ψρ `union` Ψa ->
    Ψa [<=] Ψsub ->

    {{ Ψsub ⨟ Θ ⊢ˢ Rsub ∼ Q }}ad ->
    lc_bskl Q ->
    {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl Rsub) }}a ->
    {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->

    uskl_rsubst NM Θs Δρ Ψρ Rsub
      (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ->
    (forall x b, binds x b Θs -> binds x b Θ) ->
    Ψρ ∩ Ψ' [=] empty ->
    rsubst_fresh Δρ Θ κ ->
    Δρ [<=] Δ ->
    Δρ ∩ dom Θw [=] empty ->
    (forall α0, α0 `in` Δρ ->
       α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi) ->
    (forall α0, α0 `in` Δρ ->
       α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
    (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
    forall L, ftvar_in_aenv Θ0 [<=] L ->
    exists 𝒞 Ξc Ξs Pa κc κs,
      ({{ Θ0 ⊢ P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
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
      ftvar_in_a_cstrs 𝒞 [<=] ftvar_in_uskl ψa
                            `union` dom Ξc `union` dom κ
                            `union` def_ftv Θ /\
      (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
      a_inc_equiv Θ0 κ κ Θ /\
      (forall α0, α0 `in` dom κc ->
         α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
      {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
      (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞)) ->
  forall NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa ψa P0 Pi α Θs Δρ Ψρ L
    R0 Rsub0 Ψbody Lρ Ls0 Lcof Q0,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a -> {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α0, a_flex_tvar Θ0 α0 ->
     ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw) ->
  ftvar_in_uskl ψa [<=] dom Θw ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  (forall x b, binds x b Θs -> binds x b Θ) ->
  Ψρ ∩ Ψ' [=] empty ->
  rsubst_fresh Δρ Θ κ ->
  Δρ [<=] Δ -> Δρ ∩ dom Θw [=] empty ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi) ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  ftvar_in_aenv Θ0 [<=] L ->
  P0 <> pskl_ghost ->
  size_uskl R0 + size_pskl P0 <= n ->
  ftvar_in_uskl R0 [<=] add α (dom Θ0 `union` dom Θ) ->
  (ftag_in_uskl R0) ∩ Ψ' [=] empty ->
  Ψbody [<=] ftag_in_uskl R0 `union` Ψρ `union` Ψa ->
  Ψa [<=] Ψbody ->
  (forall β, lc_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) ->
  (forall β, β `notin` Ls0 ->
    {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β empty) ⊢ₚₛ
       open_pskl_wrt_pskl (uskl_to_pskl Rsub0) (pskl_var_f β) }}a) ->
  (forall β, β `notin` Lρ ->
    uskl_rsubst NM Θs Δρ Ψρ
      (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
      (open_uskl_wrt_uskl
        (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R0)) (uskl_var_f β))) ->
  (forall β, β `notin` Lcof ->
    {{ Ψbody ⨟ ((β ~ abind_tvar) ++ Θ) ⊢ˢ
       open_uskl_wrt_uskl Rsub0 (uskl_var_f β) ∼
       open_bskl_wrt_bskl Q0 (bskl_var_f β) }}ad) ->
  (forall β, lc_bskl (open_bskl_wrt_bskl Q0 (bskl_var_f β))) ->
  ({{ Θ ⨟ empty ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0) ⊳
       bskl_all_inh Q0 }}ad \/
   {{ Θ ⨟ empty ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0) ⊳
       bskl_all_syn Q0 }}ad) ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ (pskl_all_syn (uskl_to_pskl R0)) ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
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
    ftvar_in_a_cstrs 𝒞 [<=] ftvar_in_uskl ψa
                          `union` dom Ξc `union` dom κ
                          `union` def_ftv Θ /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞).
Proof.
  intros n IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa ψa P0 Pi α Θs Δρ Ψρ L
    R0 Rsub0 Ψbody Lρ Ls0 Lcof Q0
    HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0 HwfPi Hκ Hκw Hψaw HαΘ HαΘ0
    Htags Hsub Hdfresh Hpre HΘs HΨρ Hrfr HΔρΔ HΔρw HΔρftv HΔρPi
    Hψaap HL HP0nh Hbodymeas HscopeS Hdisj HΨs1 HΨs2
    Hlcbody Hsbody Hrhobody Hcof HlcQ0 Hrefs.
  assert (Hακdom : α `notin` dom κ)
    by (intro Hc; apply (a_inc_dom_sub Hκ) in Hc; contradiction).
  assert (HΔρΘ : Δρ [<=] dom Θ).
  { intros x Hx. destruct (Hrfr x Hx) as (Hb & _ & _).
    eapply binds_In; exact Hb. }
  assert (Hlcψa : lc_uskl ψa) by (apply is_dskl_lc; inversion Htags; assumption).

  assert (HP0ng : ~ guarded_pskl P0).
  { intros Hg.
    destruct Hrefs as [Href | Href].
    - exact (proj1 (ad_refine_syn_msubst_guarded_not_all HwfΘ Hκ Hg Href Q0)
                   eq_refl).
    - exact (proj2 (ad_refine_syn_msubst_guarded_not_all HwfΘ Hκ Hg Href Q0)
                   eq_refl). }
  assert (Hbody : forall β P0β,
            β `notin` Lcof `union` Lρ `union` dom Θ `union` dom Θ0
                `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
                `union` ftvar_in_uskl R0 `union` def_ftv Θ `union` Ls0 ->
            {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ P0β }}a ->
            {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
               (pskl_to_bskl_inh (msubst_pskl κ P0β))
               ⊳ (open_bskl_wrt_bskl Q0 (bskl_var_f β)) }}ad ->
            size_uskl R0 + size_pskl P0β <= n ->
            (forall α0, α0 `in` Δρ ->
               α0 `notin` ftvar_in_pskl P0β `union` ftvar_in_pskl Pi) ->
            (forall Ξc 𝒞,
               {{ ((β ~ abind_tvar) ++ Θ0)
                  ⊢ (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                  ∼[ α ] P0β ⤳ Ξc ⨾ 𝒞 }}a ->
               {{ Θ0 ⊢ (pskl_all_syn (uskl_to_pskl R0)) ∼[ α ] P0
                  ⤳ Ξc ⨾ 𝒞 }}a) ->
            lookeq_solve_result Θ0 Θ Θw κ Δ Ψi Ψa ψa α
              (pskl_all_syn (uskl_to_pskl R0)) P0 Pi L).
  { intros β P0β Fr HwfP0β Hrefβ Hmeas HΔρftvβ Hlook.
    assert (HβΘ : β `notin` dom Θ) by auto.
    assert (HβΘ0 : β `notin` dom Θ0) by auto.
    assert (Hβα : β <> α) by auto.
    assert (Hβκ : β `notin` dom κ) by auto.
    destruct (solve_context_open_tvar
                HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 Hβα HβΘ HβΘ0)
      as (_ & _ & Hwfβ & Hwfβ0 & HαΘβ & HαΘ0β & Hκβ & _ & HwfPiβ).
    assert (HscopeSβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
              [<=] add α (dom ((β ~ abind_tvar) ++ Θ0)
                            `union` dom ((β ~ abind_tvar) ++ Θ))).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β)) as Hup.
      simpl in Hup, HscopeS |- *. clear - Hup HscopeS; fsetdec. }
    assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
              ∩ Ψ' [=] empty).
    { rewrite ftag_in_uskl_open_var. simpl in Hdisj. exact Hdisj. }
    assert (HΨs1β : Ψbody [<=] union
              (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) (union Ψρ Ψa)).
    { rewrite ftag_in_uskl_open_var. simpl in HΨs1. exact HΨs1. }
    assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ))
      by (eapply delta_def_fresh_weaken_tvar; eassumption).
    assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ Δ
              ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad)
      by (eapply ad_partial_precise_weaken;
            [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
    assert (Hconsβ : {{ Ψbody ⨟ ((β ~ abind_tvar) ++ Θ) ⊢ˢ
              (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
              ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f β)) }}ad)
      by (apply Hcof; auto).
    assert (Hrhoβ : uskl_rsubst NM Θs Δρ Ψρ
              (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
              (subst_uskl_in_uskl ψa α
                 (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β))))).
    { rewrite (@subst_msubst_uskl_syn_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
      apply Hrhobody; auto. }
    assert (HΘsβ : forall x b, binds x b Θs -> binds x b ((β ~ abind_tvar) ++ Θ))
      by (intros x b Hb; apply binds_app_3; apply HΘs; exact Hb).
    assert (Hrfrβ : rsubst_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ)
      by (apply rsubst_fresh_weaken_tvar; exact Hrfr).
    assert (HwfSubβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
              (uskl_to_pskl (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))) }}a).
    { rewrite uskl_to_pskl_open.
      eapply a_wf_pskl_delta_mono;
        [ apply (Hsbody β ltac:(auto)) | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
    assert (Hmeasβ : size_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                       + size_pskl P0β <= n)
      by (rewrite size_uskl_open_uskl_wrt_uskl_var; exact Hmeas).
    destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HβΘ)
      as (HβΘw & Hmonβ & Hnrβ & Hκwβ).
    assert (HLβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β L)
      by (rewrite ftvar_in_aenv_cons_tvar; clear - HL; fsetdec).
    assert (Hβψa : β `notin` ftvar_in_uskl ψa) by auto.
    assert (Hβdef : β `notin` def_ftv Θ) by auto.

    apply (@lookeq_solve_strip_tvar Θ0 Θ Θw κ Δ Ψi Ψa ψa α _ _ Pi L
             (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) P0β β
             Hκ HwfPi HβΘ HβΘ0 HβΘw Hβκ Hβψa Hβdef Hlook).
    exact (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) Θw
             κ Δ Ψ' Ψi Ψa Ψbody ψa (open_bskl_wrt_bskl Q0 (bskl_var_f β))
             (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) P0β Pi
             (open_uskl_wrt_uskl R0 (uskl_var_f β)) α
             Θs Δρ Ψρ (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
             Hmeasβ Hwfβ Hwfβ0 HwfΘw Hmonβ Hnrβ HwfP0β HwfPiβ Hκβ Hκwβ
             Hψaw HαΘβ HαΘ0β eq_refl
             HscopeSβ (Hlcbody β) Htags Hdisjβ Hsub Hdfreshβ Hpreβ
             HΨs1β HΨs2 Hconsβ (HlcQ0 β) HwfSubβ Hrefβ
             Hrhoβ HΘsβ HΨρ Hrfrβ HΔρΔ HΔρw HΔρftvβ HΔρPi Hψaap
             (add β L) HLβ). }
  destruct Hrefs as [HrefInh | HrefSyn].
  +
    destruct P0 as [ | n0 | β0 | P01 P02 | P0' | | P0s ].
    *  contradiction (HP0ng guarded_pskl__unit).
    *  inversion HwfP0.
    *  contradiction (HP0ng (guarded_pskl__var _)).
    *  contradiction (HP0ng (a_wf_pskl_arrow_guarded HwfP0)).
    *
      cbn [msubst_pskl pskl_to_bskl_inh] in HrefInh.
      inversion HrefInh; subst.
      match goal with H : forall α0, α0 `notin` ?Lr -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
        rename H into Hrbody; remember Lr as Lr0 eqn:HeqLr; clear HeqLr end.
      inversion HwfP0; subst.
      match goal with H : forall α0, α0 `notin` ?L0 -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
        rename H into Hw0body; remember L0 as Lw0 eqn:HeqLw0; clear HeqLw0 end.
      pick fresh β for
        (Lcof `union` Lρ `union` Lr0 `union` Lw0 `union` dom Θ `union` dom Θ0
           `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
           `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
           `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0'
           `union` def_ftv Θ

           `union` ftvar_in_aenv Θ0
              `union` Ls0).
      assert (HβΘ : β `notin` dom Θ) by auto.
      assert (Hβκ : β `notin` dom κ) by auto.
      apply (Hbody β (open_pskl_wrt_pskl P0' (pskl_var_f β))).
      -- clear - Fr; solve_notin.
      -- eapply a_wf_pskl_delta_mono;
           [ apply (Hw0body β ltac:(auto)) | intros γ _ Hγ; clear - Hγ; fsetdec ].
      -- rewrite (@msubst_pskl_open Θ0 κ Θ P0' β Hκ Hβκ).
         rewrite pskl_to_bskl_inh_open.
         eapply ad_refine_syn_delta_mono;
           [ apply (Hrbody β ltac:(auto)) | clear; fsetdec ].
      -- rewrite size_pskl_open_pskl_wrt_pskl_var. cbn in Hbodymeas |- *; lia.
      -- intros α0 Hα0.
         pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0'
                       (pskl_var_f β)) as Hup.
         pose proof (HΔρftv α0 Hα0) as Hd0. pose proof (HΔρΘ α0 Hα0) as Hd1.
         cbn [ftvar_in_pskl] in Hup, Hd0.
         clear - Hup Hd0 Hd1 HβΘ; fsetdec.
      --
         intros Ξc 𝒞 HLK. rewrite uskl_to_pskl_open in HLK.
         apply a_lookeq_forall_inh_adm with (β := β).
         ++ clear - Fr; solve_notin.
         ++ exact HLK.
    *  exfalso; apply HP0nh; reflexivity.
    *
      exfalso.
      destruct (a_wf_pskl_univ_ghost_inv HwfP0) as [HgP0s HwfP0s].
      assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
        by (apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
      cbn [msubst_pskl pskl_to_bskl_inh] in HrefInh.
      inversion HrefInh; subst.
      match goal with
        H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ bskl_all_inh _ }}ad |- _ =>
          pose proof (ad_refine_syn_guarded_r_all HwfΘ H HgL
                        ltac:(eexists; (left + right); reflexivity)) as Hbad end.
      inversion Hbad.
  +
    destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
    *
      contradiction (HP0ng guarded_pskl__unit).
    *  inversion HwfP0.
    *  contradiction (HP0ng (guarded_pskl__var _)).
    *
      contradiction (HP0ng (a_wf_pskl_arrow_guarded HwfP0)).
    *
      exfalso. cbn [msubst_pskl pskl_to_bskl_inh] in HrefSyn.
      inversion HrefSyn.
    *  exfalso; apply HP0nh; reflexivity.
    *
      destruct (a_wf_pskl_univ_ghost_inv HwfP0) as [HgP0s HwfP0s].
      assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
        by (apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
      cbn [msubst_pskl pskl_to_bskl_inh] in HrefSyn.
      inversion HrefSyn; subst.
      --
         exfalso.
         match goal with
           H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ bskl_all_syn _ }}ad |- _ =>
             pose proof (ad_refine_syn_guarded_r_all HwfΘ H HgL
                        ltac:(eexists; (left + right); reflexivity)) as Hbad end.
         inversion Hbad.
      --
         match goal with H : forall α0, α0 `notin` ?Lf -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
           rename H into Hfill end.
         match goal with H : forall α0, α0 `notin` ?Lf -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
           let Lf' := fresh "Lf" in
           remember Lf as Lf' eqn:HeqLf; clear HeqLf end.
         pick fresh β for
           (Lcof `union` Lρ `union` Lf `union` dom Θ `union` dom Θ0
              `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
              `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
              `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0s
              `union` def_ftv Θ

              `union` ftvar_in_aenv Θ0
              `union` Ls0).
         apply (Hbody β (pskl_univ_ghost P0s)).
         ++ clear - Fr; solve_notin.
         ++ eapply a_wf_pskl_weaken;
              [ intros x b Hb; apply binds_app_3; exact Hb | exact HwfP0 ].
         ++ cbn [msubst_pskl pskl_to_bskl_inh]; apply Hfill; auto.
         ++ cbn in Hbodymeas |- *; lia.
         ++ exact HΔρftv.
         ++
            intros Ξc 𝒞 HLK. rewrite uskl_to_pskl_open in HLK.
            apply a_lookeq_forall_syn_adm with (β := β).
            ** clear - Fr; solve_notin.
            ** exact HLK.
Qed.

Theorem a_lookeq_solve_complete_gen :
  forall n NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α Θs Δρ Ψρ Rsub,
  size_uskl R' + size_pskl P0 <= n ->
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α0, a_flex_tvar Θ0 α0 ->
     ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw) ->
  ftvar_in_uskl ψa [<=] dom Θw ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->
  Ψi `union` Ψa [<=] Ψ' ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->

  {{ Ψsub ⨟ Θ ⊢ˢ Rsub ∼ Q }}ad ->
  lc_bskl Q ->
  {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl Rsub) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->

  uskl_rsubst NM Θs Δρ Ψρ Rsub
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ->
  (forall x b, binds x b Θs -> binds x b Θ) ->
  Ψρ ∩ Ψ' [=] empty ->
  rsubst_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  Δρ ∩ dom Θw [=] empty ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi) ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
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
    ftvar_in_a_cstrs 𝒞 [<=] ftvar_in_uskl ψa
                          `union` dom Ξc `union` dom κ
                          `union` def_ftv Θ /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞).
Proof.
  induction n as [ | n IHn ];
    intros NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α Θs Δρ Ψρ Rsub Hn.
  { exfalso. pose proof (size_uskl_min R'). pose proof (size_pskl_min P0). lia. }
  intros HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0 HwfPi Hκ Hκw Hψaw
         HαΘ HαΘ0 HeraseR HscopeS HlcS Htags Hdisj Hsub
         Hdfresh Hpre HΨs1 HΨs2 Hconsis HlcQ HwfSub Hrefine
         Hrho HΘs HΨρ Hrfr HΔρΔ HΔρw HΔρftv HΔρPi Hψaap L HL.
  assert (HΔρΘ : Δρ [<=] dom Θ).
  { intros α0 Hα0. destruct (Hrfr α0 Hα0) as (Hb & _ & _).
    apply binds_In in Hb; exact Hb. }
  assert (HΔρΘ0 : Δρ [<=] dom Θ0).
  { intros α0 Hα0. destruct (Hrfr α0 Hα0) as (Hb & _ & _).
    apply binds_In with (a := abind_tvar).
    eapply a_inc_binds_tvar_rev; [ exact Hκ | exact Hb ]. }
  assert (HFw : forall κ0,
            Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ0 ->
            Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ0)
    by (intros κ0 HF0; eapply forall_wf_mono_weaken; [ exact Hmon | exact HF0 ]).

  assert (Hdefs : forall α0 τ0, binds α0 (abind_flex_mono_def τ0) Θ ->
                    binds α0 (abind_flex_mono_def τ0) Θw)
    by (intros α0 τ0 Hb; destruct (Hnr _ _ Hb) as [Hb' | Hc];
        [ exact Hb' | discriminate Hc ]).

  destruct (pskl_eq_var_dec P α) as [-> | HPnα].
  {
    assert (Hlk : msubst_lookup κ α = ptyp_var_f α).
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
    assert (Htskψa : is_dskl ψa) by (inversion Htags; assumption).
    assert (HtskRs : is_dskl Rsub) by (eapply uskl_rsubst_is_dskl; eassumption).
    assert (Hcv : exists Ξ Pa κ',
                    {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a /\
                    all_flex_mono Ξ /\ uniq Ξ /\
                    keys κ' = keys Ξ /\
                    (forall α0, α0 `in` dom Ξ -> α0 `notin` L) /\
                    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ' /\
                    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa)
                        ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad).
    { eapply a_solve_eq_complete_var_at
        with (Δρ := Δρ) (Ψρ := Ψρ) (ψsub := Rsub) (Ψsub := Ψsub);
      [ exact HwfΘ | exact HwfΘ0 | exact HwfΘw | exact Hmon | exact Hnr
      | exact HwfPi | exact HwfP0 | exact Hκ | exact Hκw
      | eapply uskl_rsubst_weaken; [ exact Hrho | exact HΘs ]
      | exact Htags | exact Hsub | exact HΨρ
      | exact Hrfr
      | exact HΔρΔ
      | exact HΔρPi
      | exact Hdfresh
      | exact Hpre
      | clear - HΨs1; fsetdec
      | exact HΨs2 | exact Hconsis | exact Hrefine | exact HL ]. }
    destruct Hcv as (Ξs & Pa & κs & Hsolve & Hfms & Hus & Hks & Hfrs & HFs
                     & Hprec).
    exists (a_cstr_eq P0 :: nil), nil, Ξs, Pa, (@nil (atom * ptyp)), κs.
    repeat split.
    - apply a_lookeq__var.
    - simpl. apply a_solve_cstr__eq
        with (Ξ1 := Ξs) (Ξ2 := (@nil (atom * abind))) (P'' := Pa);
        [ exact Hsolve | apply a_solve_cstr__empty ].
    - exact Hfms.
    - exact Hus.
    - exact Hks.
    - exact Hfrs.
    - exact HFs.
    - cbn [app].
      eapply a_solve_eq_wf; [ exact Hsolve | exact HwfPi | exact HwfP0 ].
    - simpl. exact HwfΘ0.
    - simpl; clear; fsetdec.
    - apply Forall_nil.
    -
      simpl.
      pose proof (ad_refine_syn_src_ftv Hrefine HwfΘ) as Hrf.
      rewrite ftvar_in_bskl_inh in Hrf.
      pose proof (ad_pat_consis_target_ftv Hconsis HwfΘ HtskRs) as Hcf.
      pose proof (uskl_rsubst_ftv_apart Hrho ltac:(clear - Hψaap; solve_notin_auto))
        as Hbnd.
      pose proof (msubst_pskl_ftv_dom_lower κ P0) as Hlow.
      clear - Hrf Hcf Hbnd Hlow; fsetdec.
    - cbn [app].
      apply a_inc_flex_prefix_build;
        [ exact Hfms | exact Hks | apply HFw; exact HFs | exact Hκ ].
    - simpl. apply a_inc_equiv_refl; exact Hκ.
    - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    - cbn [app]. exact Hprec.
    -
      intros α0 Hα0. simpl.
      pose proof (a_wf_pskl_ftv_dom HwfP0) as Hfd. simpl in Hfd.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      pose proof (Hfrs α0 Hα0) as Hf.
      clear - Hfd Hds HL Hf. fsetdec. }

  destruct (pskl_ghost_dec P0) as [-> | HP0nh].
  {
    simpl in Hrefine.
    assert (Hsk : is_sskl Q)
      by (eapply ad_refine_syn_ghost_sskl; [ exact Hrefine | reflexivity
                 | exact HlcQ ]).
    assert (HΨe : Ψsub [=] empty)
      by (eapply ad_pat_consis_sskl_tags; [ exact Hconsis | exact HwfΘ | exact Hsk ]).
    assert (HΨa0 : Ψa [=] empty) by (clear - HΨs2 HΨe; fsetdec).
    exists nil, nil, nil, Pi, (@nil (atom * ptyp)), (@nil (atom * ptyp)).
    repeat split.
    -
      apply a_lookeq__vacuous; exact HPnα.
    - simpl. apply a_solve_cstr__empty.
    - apply Forall_nil.
    - apply uniq_nil.
    - intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec.
    - apply Forall_nil.
    - simpl. exact HwfPi.
    - simpl. exact HwfΘ0.
    - simpl; clear; fsetdec.
    - apply Forall_nil.
    -  simpl; clear; fsetdec.
    - simpl. exact Hκ.
    - simpl. apply a_inc_equiv_refl; exact Hκ.
    - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    - simpl. eapply ad_partial_precise_psi_cong; [ exact Hpre | clear - HΨa0; fsetdec ].
    -
      intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec. }

  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P)) as [Hin | Hnin].
  2:{
    assert (Hκav : forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)).
    { intros p Hp. pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb.
      clear - HαΘ Hb; fsetdec. }
    assert (HαMS : α `notin` ftvar_in_uskl (msubst_uskl_syn κ R')).
    { rewrite <- ftvar_in_pskl_uskl_to_pskl. rewrite uskl_to_pskl_msubst_uskl_syn.
      rewrite HeraseR. apply msubst_pskl_ftv_avoid; [ exact Hκav | exact Hnin ]. }
    rewrite (subst_uskl_in_uskl_fresh_eq (msubst_uskl_syn κ R') ψa α HαMS) in Hrho.
    assert (HΨsR : Ψsub [<=] ftag_in_uskl Rsub)
      by (apply (ad_pat_consis_ftag_sub Hconsis)).
    pose proof (uskl_rsubst_ftag_sub Hrho) as Hftr.
    rewrite ftag_in_uskl_msubst_uskl_syn in Hftr.
    assert (HΨa0 : Ψa [=] empty)
      by (clear - HΨs2 HΨsR Hftr Hdisj Hsub HΨρ; fsetdec).
    exists nil, nil, nil, Pi, (@nil (atom * ptyp)), (@nil (atom * ptyp)).
    repeat split.
    - apply a_lookeq__absent; exact Hnin.
    - simpl. apply a_solve_cstr__empty.
    - apply Forall_nil.
    - apply uniq_nil.
    - intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec.
    - apply Forall_nil.
    - simpl. exact HwfPi.
    - simpl. exact HwfΘ0.
    - simpl; clear; fsetdec.
    - apply Forall_nil.
    -  simpl; clear; fsetdec.
    - simpl. exact Hκ.
    - simpl. apply a_inc_equiv_refl; exact Hκ.
    - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    - simpl. eapply ad_partial_precise_psi_cong; [ exact Hpre | clear - HΨa0; fsetdec ].
    -
      intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec. }

  assert (Hακdom : α `notin` dom κ)
    by (intro Hc; apply (a_inc_dom_sub Hκ) in Hc; contradiction).
  assert (Hκav : forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)).
  { intros p Hp. pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb.
    clear - HαΘ Hb; fsetdec. }
  assert (HαR : α `in` ftvar_in_uskl R').
  { rewrite <- HeraseR in Hin. rewrite ftvar_in_pskl_uskl_to_pskl in Hin. exact Hin. }
  destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
    simpl in HαR.
  -  clear - HαR; fsetdec.
  -  clear - HαR; fsetdec.
  -
    assert (β = α) by (clear - HαR; fsetdec); subst β.
    simpl in HeraseR. contradiction (HPnα (eq_sym HeraseR)).
  -
    pose proof Hrho as Hrho0.
    cbn [msubst_uskl_syn subst_uskl_in_uskl] in Hrho.
    destruct (uskl_rsubst_arrow_r_inv Hrho)
      as (Ra' & Rb' & Ψρ1 & Ψρ2 & HRs & Hrhoa & Hrhob & HΨρeq).
    subst Rsub.
    destruct (lc_uskl_arrow_inv HlcS) as [HlcSa HlcSb].

    cbn [uskl_to_pskl] in HeraseR; subst P.
    cbn [uskl_to_pskl] in HwfSub.
    destruct (a_wf_pskl_arrow_inv HwfSub) as [HwfSubA HwfSubB].
    destruct (ad_pat_consis_arrow_refine_unify HwfΘ Hconsis eq_refl
                (delta_def_fresh_empty Θ) Hrefine HlcQ)
      as (Ψ1 & Ψ2 & Q1 & Q2 & H6 & H1 & H4 & Href0 & Hcons0 & HlcQ12).
    clear Hconsis Hrefine.
    rename Href0 into Hrefine.
    +
      destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
      *
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine; inversion Hrefine.
      *
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine; inversion Hrefine.
      *
        assert (Hbt0 : a_binds_tvar β0 Θ0).
        { inversion HwfP0; subst; assumption. }
        destruct Hbt0 as [Hrig | Hflx].
        {
          exfalso.
          assert (Hmid : msubst_pskl κ (pskl_var_f β0) = pskl_var_f β0)
            by (eapply msubst_pskl_tvar_id;
                [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
          rewrite Hmid in Hrefine; cbn [pskl_to_bskl_inh] in Hrefine.
          eapply (ad_refine_syn_rigid_var_nonvar_absurd Hrefine);
            [ intros x b Hb; exact Hb | apply a_wf_aenv_uniq; exact HwfΘ
            | eapply a_inc_binds_tvar; eauto | intros βx Hcc; discriminate Hcc ]. }
        eapply (@a_lookeq_flex_p0_complete NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa
                  (bskl_arrow Q1 Q2) Pi (uskl_arrow Ra Rb) α Θs Δρ Ψρ
                  (uskl_arrow Ra' Rb') β0 L);
          solve [ eassumption | reflexivity | right; exact Hflx
                | assumption | cbn; assumption ].
      *
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        destruct (ad_refine_arrow_arrow_inv Hrefine) as [Href1 Href2].
        destruct (a_wf_pskl_arrow_inv HwfP0) as [HwfP01 HwfP02].
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.

        assert (HΨa : Ψa [=] union (Ψ1 ∩ Ψ') (Ψ2 ∩ Ψ'))
          by (clear - HΨs1 HΨs2 Hsub H6 Hdisj HΨρ; fsetdec).

        pose proof (rsubst_component_tags (ad_pat_consis_ftag_sub H1) Hrhoa Hψatag)
          as HΨs1L.
        pose proof (rsubst_component_tags (ad_pat_consis_ftag_sub H4) Hrhob Hψatag)
          as HΨs1R.
        assert (HΨρ1e : Ψρ1 ∩ Ψ' [=] empty) by (clear - HΨρ HΨρeq; fsetdec).
        assert (HΨρ2e : Ψρ2 ∩ Ψ' [=] empty) by (clear - HΨρ HΨρeq; fsetdec).
        assert (HscopeSa : ftvar_in_uskl Ra [<=] add α (dom Θ0 `union` dom Θ))
          by (clear - HscopeS; simpl in HscopeS; fsetdec).
        assert (HscopeSb : ftvar_in_uskl Rb [<=] add α (dom Θ0 `union` dom Θ))
          by (clear - HscopeS; simpl in HscopeS; fsetdec).
        assert (HdisjSa : (ftag_in_uskl Ra) ∩ Ψ' [=] empty)
          by (clear - Hdisj; simpl in Hdisj; fsetdec).
        assert (HdisjSb : (ftag_in_uskl Rb) ∩ Ψ' [=] empty)
          by (clear - Hdisj; simpl in Hdisj; fsetdec).
        assert (Hml : size_uskl Ra + size_pskl P01 <= n) by (cbn in Hn; lia).
        assert (Hmr : size_uskl Rb + size_pskl P02 <= n) by (cbn in Hn; lia).
        assert (HsubL : union Ψi (Ψ1 ∩ Ψ') [<=] Ψ')
          by (clear - Hsub; fsetdec).
        assert (HΨs2L : Ψ1 ∩ Ψ' [<=] Ψ1) by (clear; fsetdec).
        assert (HL1 : ftvar_in_aenv Θ0 [<=] add α (union L (dom Θ)))
          by (clear - HL; fsetdec).

        edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi (Ψ1 ∩ Ψ') Ψ1 ψa Q1
                     (uskl_to_pskl Ra) P01 Pi Ra α Θs Δρ Ψρ1 Ra'
                     Hml HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP01 HwfPi Hκ Hκw Hψaw
                     HαΘ HαΘ0 eq_refl
                     HscopeSa HlcSa Htags HdisjSa HsubL Hdfresh Hpre HΨs1L HΨs2L H1 ltac:(lc_tgt) HwfSubA Href1
                     Hrhoa HΘs HΨρ1e Hrfr HΔρΔ HΔρw
                     ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap
                     (add α (union L (dom Θ))) HL1)
          as (C1 & Ξc1 & Ξs1 & Pa1 & κc1 & κs1
                & HLK1 & HSolve1 & Hfms1 & Hus1 & Hks1 & Hfrs1 & HFs1
                & HwfPa1 & HwfΞ1 & HαΞ1
                & Hmap1 & Himg1 & HftvC1 & Hinc1 & Hinceq1 & Hκf1
                & Hpre1 & Hapart1).

        pose proof (a_lookeq_all_flex_mono HLK1) as HfmΞ1.
        pose proof (@keys_eq_dom _ _ κc1 Ξc1 Hmap1) as Hd1'.
        assert (Hd_s1 : dom κs1 [=] dom Ξs1) by (apply keys_eq_dom; exact Hks1).
        assert (Hfrs1κ : forall α0, α0 `in` dom κs1 ->
                  α0 `notin` add α (union L (dom Θ)))
          by (intros α0 Hα0; apply Hfrs1; clear - Hα0 Hd_s1; fsetdec).
        assert (HαΞs1 : α `notin` dom Ξs1)
          by (intro Hc; pose proof (Hfrs1 α Hc) as Hf; clear - Hf; fsetdec).
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdf0.
        pose proof (a_wf_aenv_solve_block HwfΞ1 HSolve1 Hfms1 Hus1) as HwfΞs1.

        destruct (solve_scope_arrow_prefix (conj Hmon (conj Hnr Hκw)) Hψaw
                    Hmap1 Himg1 Hks1 HFs1) as (_ & _ & HκwR).
        pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd02.
        assert (Htr_c : msubst_uskl_syn (κs1 ++ κc1 ++ κ) Rb
                        = msubst_uskl_syn κ Rb).
        { apply msubst_uskl_syn_prepend_fresh2; intros α0 Hα0.
          - pose proof (Hfrs1κ α0 Hα0) as Hf.
            clear - Hf HscopeSb Hdf0 HL; fsetdec.
          - specialize (Hκf1 α0 Hα0). clear - Hκf1 HscopeSb; fsetdec. }
        assert (Htr_r : msubst_pskl (κs1 ++ κc1 ++ κ) P02 = msubst_pskl κ P02).
        { apply msubst_pskl_prepend_fresh2; intros α0 Hα0.
          - pose proof (Hfrs1κ α0 Hα0) as Hf.
            clear - Hf Hfd02 Hdf0 HL; fsetdec.
          - specialize (Hκf1 α0 Hα0). clear - Hκf1 Hfd02; fsetdec. }
        rewrite <- Htr_c in Hrhob.
        rewrite <- Htr_r in Href2.
        assert (Hαr : α `notin` dom (Ξs1 ++ Ξc1 ++ Θ0))
          by (repeat rewrite dom_app; clear - HαΞs1 HαΞ1 HαΘ0; fsetdec).
        assert (HscopeSbR : ftvar_in_uskl Rb
                  [<=] add α (dom (Ξs1 ++ Ξc1 ++ Θ0) `union` dom Θ))
          by (repeat rewrite dom_app; clear - HscopeSb; fsetdec).
        assert (HsubR : union (union Ψi (Ψ1 ∩ Ψ'))
                              (Ψ2 ∩ Ψ') [<=] Ψ')
          by (clear - Hsub; fsetdec).
        assert (HΨs2R : Ψ2 ∩ Ψ' [<=] Ψ2) by (clear; fsetdec).
        assert (HwfP02R : {{ (Ξs1 ++ Ξc1 ++ Θ0) ⨟ empty ⊢ₚₛ P02 }}a)
          by (eapply a_wf_pskl_weaken;
                [ intros x b Hb; apply binds_app_3; apply binds_app_3; exact Hb
                | exact HwfP02 ]).
        assert (HΔρΞc1 : forall α0, α0 `in` Δρ -> α0 `notin` dom Ξc1).
        { intros α0 Hα0 Hc. rewrite <- Hd1' in Hc. specialize (Hκf1 α0 Hc).
          specialize (HΔρΘ α0 Hα0). clear - Hκf1 HΔρΘ; fsetdec. }
        assert (HΔρPa1ftv : forall α0, α0 `in` Δρ ->
                  α0 `notin` ftvar_in_pskl Pa1).
        { intros α0 Hα0.
          pose proof (a_solve_cstr_ftv_eq HSolve1 (a_lookeq_cstr_eq HLK1))
            as Hs1.
          pose proof (HΔρftv α0 Hα0) as Hd0. cbn [ftvar_in_pskl] in Hd0.
          pose proof (HΔρΞc1 α0 Hα0) as HΞ.
          assert (Hc1 : α0 `notin` ftvar_in_a_cstrs C1).
          { eapply a_lookeq_ftv_ctx;
              [ exact HLK1 | clear - HΔρΘ0 Hα0; fsetdec
              | clear - Hd0; fsetdec | exact HΞ ]. }
          assert (HΞs : α0 `notin` dom Ξs1).
          { intro Hc. pose proof (Hfrs1 α0 Hc) as Hf.
            pose proof (HΔρΘ0 α0 Hα0) as Hd00.
            pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdf.
            clear - Hf Hd00 Hdf HL; fsetdec. }
          clear - Hs1 Hc1 Hd0 HΞ HΞs; fsetdec. }
        assert (HΔρftvR : forall α0, α0 `in` Δρ ->
                  α0 `notin` ftvar_in_pskl P02 `union` ftvar_in_pskl Pa1).
        { intros α0 Hα0. pose proof (HΔρftv α0 Hα0) as Hd0.
          cbn [ftvar_in_pskl] in Hd0.
          pose proof (HΔρPa1ftv α0 Hα0) as Hp1. clear - Hd0 Hp1; fsetdec. }
        pose proof (rsubst_fresh_arrow_prefix Hrfr HΔρw Hψaap HFs1 Himg1)
          as HrfrR.
        pose proof (rsubst_fresh_shielded HrfrR HΔρPa1ftv) as HΔρPa1.
        assert (HfrP02Ξ : (ftvar_in_pskl P02) ∩ (dom Ξc1) [=] empty).
        { apply inter_dom_empty_of_forall. intros x Hx. rewrite <- Hd1' in Hx.
          specialize (Hκf1 x Hx). clear - Hκf1 Hfd02; fsetdec. }
        assert (HfrP02Ξs : (ftvar_in_pskl P02) ∩ (dom Ξs1) [=] empty).
        { apply inter_dom_empty_of_forall. intros x Hx.
          pose proof (Hfrs1 x Hx) as Hf. clear - Hf Hfd02 HL Hdf0; fsetdec. }
        assert (HL2 : ftvar_in_aenv (Ξs1 ++ Ξc1 ++ Θ0)
                  [<=] add α (union (union (union L (dom Θ))
                                    (union (dom Ξs1) (dom Ξc1)))
                                    (ftvar_in_a_cstrs C1))).
        { repeat rewrite ftvar_in_aenv_app.
          pose proof (all_flex_mono_ftvar_in_aenv Hfms1) as Hfs.
          pose proof (all_flex_mono_ftvar_in_aenv HfmΞ1) as Hfc.
          clear - Hfs Hfc HL; fsetdec. }
        edestruct (IHn NM (Ξs1 ++ Ξc1 ++ Θ0) Θ Θw (κs1 ++ κc1 ++ κ) Δ Ψ'
                     (union Ψi (Ψ1 ∩ Ψ')) (Ψ2 ∩ Ψ')
                     Ψ2 ψa Q2 (uskl_to_pskl Rb) P02 Pa1 Rb α Θs Δρ Ψρ2 Rb'
                     Hmr HwfΘ HwfΞs1 HwfΘw Hmon Hnr HwfP02R HwfPa1 Hinc1 HκwR Hψaw
                     HαΘ Hαr eq_refl
                     HscopeSbR HlcSb Htags HdisjSb HsubR Hdfresh Hpre1 HΨs1R HΨs2R H4 ltac:(lc_tgt) HwfSubB Href2
                     Hrhob HΘs HΨρ2e HrfrR HΔρΔ HΔρw HΔρftvR HΔρPa1 Hψaap
                     (add α (union (union (union L (dom Θ))
                                   (union (dom Ξs1) (dom Ξc1)))
                                   (ftvar_in_a_cstrs C1))) HL2)
          as (C2 & Ξc2 & Ξs2 & Pa2 & κc2 & κs2
                & HLK2 & HSolve2 & Hfms2 & Hus2 & Hks2 & Hfrs2 & HFs2
                & HwfPa2 & HwfΞ2 & HαΞ2
                & Hmap2 & Himg2 & HftvC2 & Hinc2 & Hinceq2 & Hκf2
                & Hpre2 & Hapart2).
        pose proof (a_lookeq_all_flex_mono HLK2) as HfmΞ2.
        pose proof (@keys_eq_dom _ _ κc2 Ξc2 Hmap2) as Hd2.
        assert (Hmapc : keys (κc1 ++ κc2) = keys (Ξc1 ++ Ξc2))
          by (rewrite !keys_app; rewrite Hmap1, Hmap2; reflexivity).
        assert (Hmaps : keys (κs2 ++ κs1) = keys (Ξs2 ++ Ξs1))
          by (rewrite !keys_app; rewrite Hks1, Hks2; reflexivity).
        assert (HΞ2disj : forall x, x `in` dom Ξc2 ->
                  x `notin` dom (Ξs1 ++ Ξc1 ++ Θ0)).
        { intros x Hx. rewrite <- Hd2 in Hx. pose proof (Hκf2 x Hx) as Hf.
          clear - Hf; fsetdec. }
        assert (Hdisj12 : forall β0, β0 `in` dom κc1 -> β0 `notin` dom κc2).
        { intros β0 Hβ0 Hin2. pose proof (Hκf2 β0 Hin2) as Hf2.
          repeat rewrite dom_app in Hf2. rewrite Hd1' in Hβ0.
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
        { intros x Hx. eapply a_lookeq_ftv_ctx;
            [ exact HLK2
            | repeat rewrite dom_app; clear - Hx; fsetdec
            | pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd;
              pose proof (Hfrs1 x Hx) as Hf;
              clear - Hfd Hf Hdf0 HL; fsetdec
            | intro Hc; rewrite <- Hd2 in Hc;
              pose proof (Hκf2 x Hc) as Hf2;
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
             destruct ((proj2 a_looksub_lookeq_ftv) _ _ _ _ _ _ HLK2 x Hx1)
               as [Hlft | Hrgt]; [ | clear - Hrgt Hxin; contradiction ].
             assert (HxΞ2 : x `notin` dom Ξc2).
             { intro Hc. rewrite <- Hd2 in Hc. rewrite <- Hd1' in Hx2.
               exact (Hdisj12 x Hx2 Hc). }
             clear - Hlft HxΞ2 HfrP02Ξ Hx2; fsetdec. }
           apply a_lookeq__arrow;
             [ exact Hgc1 | exact Hgc2
             | exact HLK1
             | eapply a_lookeq_ctx_ftv_mono;
                 [ exact HLK2
                 | repeat rewrite ftvar_in_aenv_app; clear; fsetdec
                 |
                   intros β0 Hβ0;
                   assert (Hns : β0 `notin` dom Ξs1)
                     by (clear - HfrP02Ξs Hβ0; fsetdec);
                   assert (Hnc : β0 `notin` dom Ξc1)
                     by (clear - HfrP02Ξ Hβ0; fsetdec);
                   rewrite (@a_flex_tvar_app_notin Ξs1 (Ξc1 ++ Θ0) β0 Hns);
                   rewrite (@a_flex_tvar_app_notin Ξc1 Θ0 β0 Hnc);
                   reflexivity ] ].
        --
           exact (a_solve_cstr_arrow_merge (a_lookeq_cstr_eq HLK1) HSolve1
                    HSolve2 HwfPi HfmΞ2 HΞ2disj HΞ2C1).
        --
           apply all_flex_mono_app; assumption.
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
           assert (HC2s1' : ftvar_in_a_cstrs C2 ∩ dom Ξs1 [<=] empty).
           { intros x Hx.
             assert (Hx1 : x `in` dom Ξs1) by (clear - Hx; fsetdec).
             assert (Hx2 : x `in` ftvar_in_a_cstrs C2) by (clear - Hx; fsetdec).
             exfalso; apply (HC2s1 x Hx1); exact Hx2. }
           rewrite ftvar_in_a_cstrs_app. rewrite dom_app.
           repeat rewrite dom_app in HftvC2.
           rewrite Hd1' in HftvC2. rewrite Hd_s1 in HftvC2.
           clear - HftvC1 HftvC2 HC2s1'; fsetdec.
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
           eapply ad_partial_precise_psi_cong; [ exact Hpre2 | clear - HΨa; fsetdec ].
        --
           exact Hapart.
      *
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine; inversion Hrefine.
      *
        exfalso; apply HP0nh; reflexivity.
      *
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        inversion Hrefine; subst.
        match goal with
          H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh _ ⊳ bskl_arrow _ _ }}ad |- _ =>
            rename H into Href' end.
        assert (Hmeas : size_uskl (uskl_arrow Ra Rb) + size_pskl P0s <= n)
          by (cbn in Hn |- *; lia).
        pose proof (proj2 (a_wf_pskl_univ_ghost_inv HwfP0)) as HwfP0s.
        edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa (bskl_arrow Q1 Q2)
                     (pskl_arrow (uskl_to_pskl Ra) (uskl_to_pskl Rb)) P0s Pi
                     (uskl_arrow Ra Rb) α Θs Δρ Ψρ (uskl_arrow Ra' Rb')
                     Hmeas HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0s HwfPi Hκ Hκw Hψaw
                     HαΘ HαΘ0
                     (eq_refl : ⌊ uskl_arrow Ra Rb ⌋ˢ
                                = pskl_arrow (uskl_to_pskl Ra) (uskl_to_pskl Rb))
                     HscopeS HlcS Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hcons0 ltac:(lc_tgt) HwfSub Href'
                     Hrho0 HΘs HΨρ Hrfr HΔρΔ HΔρw
                     ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap L HL)
          as (𝒞 & Ξc & Ξs & Pa & κc & κs & HLK & Hrest).
        exists 𝒞, Ξc, Ξs, Pa, κc, κs.
        refine (conj _ Hrest).
        apply a_lookeq__univ_ghost_r;
          [ exact HPnα
          | apply guarded_pskl__arrow; apply lc_uskl_to_pskl; assumption
          | exact HLK ].

  -
    cbn [uskl_to_pskl] in HeraseR; subst P.
    cbn [msubst_uskl_syn subst_uskl_in_uskl] in Hrho.
    destruct (uskl_rsubst_all_syn_r_inv Hrho) as (Lρ & Rsub0 & HRs & Hrhobody).
    subst Rsub.
    cbn [uskl_to_pskl] in HwfSub.
    inversion HwfSub; subst.
    match goal with H : forall α0, α0 `notin` ?Ls -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
      rename H into Hsbody; remember Ls as Ls0 eqn:HeqLs; clear HeqLs end.
    inversion HlcS; subst.
    match goal with H : forall α0, lc_uskl _ |- _ => rename H into Hlcbody end.
    destruct (ad_pat_consis_all_syn_refine_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HlcQ)
      as (Lcof & Q0 & Hcof & HlcQ0 & Hrefs).
    eapply a_lookeq_solve_complete_forall with
      (n := n) (NM := NM) (Θs := Θs) (Δρ := Δρ) (Ψρ := Ψρ)
      (Rsub0 := Rsub0) (Ψbody := Ψsub)
      (Lρ := Lρ) (Ls0 := Ls0) (Lcof := Lcof) (Q0 := Q0); eauto.
    cbn in Hn |- *; lia.
  -
    cbn [uskl_to_pskl] in HeraseR; subst P.

    cbn [msubst_uskl_syn subst_uskl_in_uskl] in Hrho.
    destruct (uskl_rsubst_all_tag_r_inv Hrho) as (Lρ & Rsub0 & HRs & Hrhobody).
    subst Rsub.
    cbn [uskl_to_pskl] in HwfSub.
    inversion HwfSub; subst.
    match goal with H : forall α0, α0 `notin` ?Ls -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
      rename H into Hsbody; remember Ls as Ls0 eqn:HeqLs; clear HeqLs end.
    inversion HlcS; subst.
    match goal with H : forall α0, lc_uskl _ |- _ => rename H into Hlcbody end.
    destruct (ad_pat_consis_all_tag_refine_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HlcQ)
      as (Lcof & Q0 & Ψ0 & Hcof & HlcQ0 & Hrefs).
    assert (HΨ0sub : Ψ0 [<=] Ψsub).
    { destruct Hrefs as [[_ HΨeq] | [_ HΨeq]]; clear - HΨeq; fsetdec. }
    assert (HΨa0 : Ψa [<=] Ψ0).
    { destruct Hrefs as [[_ HΨeq] | [_ HΨeq]];
        simpl in Hdisj; clear - HΨeq HΨs2 Hsub Hdisj; fsetdec. }
    assert (HΨbody : Ψ0 [<=] ftag_in_uskl R0 `union` Ψρ `union` Ψa).
    { pick fresh β for (Lcof `union` Lρ).
      assert (Hβcof : β `notin` Lcof) by auto.
      assert (Hβρ : β `notin` Lρ) by auto.
      pose proof (ad_pat_consis_ftag_sub (Hcof β Hβcof)) as Hfb.
      pose proof (uskl_rsubst_ftag_sub (Hrhobody β Hβρ)) as Hrft.
      rewrite ftag_in_uskl_open_var in Hfb.
      rewrite !ftag_in_uskl_open_var in Hrft.
      pose proof (ftag_in_uskl_subst_uskl_in_uskl ψa α
                    (msubst_uskl_syn κ R0)) as Hsb.
      rewrite ftag_in_uskl_msubst_uskl_syn in Hsb.
      pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
      simpl in HΨs1, Hdisj.
      rewrite <- Hψatag in Hsb.
      intros x Hx.
      pose proof (HΨs1 x (HΨ0sub x Hx)) as Houter.
      pose proof (Hrft x (Hfb x Hx)) as Himage.
      apply union_1 in Himage; destruct Himage as [Hρ | Himage];
        [ clear - Hρ; fsetdec | ].
      pose proof (Hsb x Himage) as Hbody.
      clear - Houter Hbody Hdisj; fsetdec. }
    assert (Hbodydisj : (ftag_in_uskl R0) ∩ Ψ' [=] empty)
      by (simpl in Hdisj; clear - Hdisj; fsetdec).
    assert (Hbodyref :
      {{ Θ ⨟ empty ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0) ⊳ bskl_all_inh Q0 }}ad \/
      {{ Θ ⨟ empty ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0) ⊳ bskl_all_syn Q0 }}ad)
      by (destruct Hrefs as [[H _] | [H _]]; auto).
    eapply a_lookeq_solve_complete_forall with
      (n := n) (NM := NM) (Θs := Θs) (Δρ := Δρ) (Ψρ := Ψρ)
      (Rsub0 := Rsub0) (Ψbody := Ψ0)
      (Lρ := Lρ) (Ls0 := Ls0) (Lcof := Lcof) (Q0 := Q0); eauto.
    cbn in Hn |- *; lia.
  -  clear - HαR; fsetdec.
  -
    cbn [uskl_to_pskl] in HeraseR; subst P.
    pose proof (lc_uskl_univ_ghost_inv HlcS) as HlcS0.

    pose proof Hrho as Hrho0.
    cbn [msubst_uskl_syn subst_uskl_in_uskl] in Hrho.
    destruct (uskl_rsubst_univ_ghost_r_inv Hrho) as (Rsub0 & HRs & Hrhobody).
    subst Rsub.
    cbn [uskl_to_pskl] in HwfSub.
    destruct (a_wf_pskl_univ_ghost_inv HwfSub) as [HgSub0 HwfSub0].
    assert (Hmeas0 : forall P0', size_pskl P0' <= size_pskl P0 ->
                     size_uskl R0 + size_pskl P0' <= n)
      by (intros P0' HP0'; cbn in Hn; lia).
    assert (Hdrop : guarded_pskl P0 -> flex_r_off Θ0 P0 ->
              lookeq_solve_result Θ0 Θ Θw κ Δ Ψi Ψa ψa α
                (pskl_univ_ghost (uskl_to_pskl R0)) P0 Pi L).
    { intros HgP0 Hoff.
      assert (HgQ : guarded_bskl Q).
      { eapply ad_refine_syn_guarded_r;
        [ exact HwfΘ | exact Hrefine | | lc_tgt ].
        apply guarded_pskl_to_bskl_inh;
          eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
      destruct (ad_pat_consis_univ_ghost_guarded_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HgQ HlcQ)
        as (Q0 & Hc0 & Href0 & HgQ0 & HlcQ0).
      destruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                  (uskl_to_pskl R0) P0 Pi R0 α Θs Δρ Ψρ Rsub0
                  (Hmeas0 P0 (le_n _))
                  HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0 HwfPi Hκ Hκw Hψaw HαΘ HαΘ0
                  eq_refl HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2
                  Hc0 HlcQ0 HwfSub0 Href0 Hrhobody HΘs HΨρ Hrfr HΔρΔ HΔρw
                  HΔρftv HΔρPi Hψaap L HL)
        as (𝒞 & Ξc & Ξs & Pa & κc & κs & HLK & Hrest).
      exists 𝒞, Ξc, Ξs, Pa, κc, κs.
      exact (conj (a_lookeq__univ_ghost2 HgP0 Hoff HLK) Hrest). }
    destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
    +
      apply Hdrop.
      * apply guarded_pskl__unit.
      * apply flex_r_off_nonvar; intros ?; discriminate.
    +  inversion HwfP0.
    +
      assert (Hbt0 : a_binds_tvar β0 Θ0).
      { inversion HwfP0; subst; assumption. }
      destruct Hbt0 as [Hrig | Hflx].
      2:{
        eapply (@a_lookeq_flex_p0_complete NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa
                  Q Pi (uskl_univ_ghost R0) α Θs Δρ Ψρ (uskl_univ_ghost Rsub0)
                  β0 L);
          solve [ eassumption | reflexivity | right; exact Hflx
                | assumption | cbn; assumption ]. }

      apply Hdrop.
      * apply guarded_pskl__var.
      * apply flex_r_off_rigid; intro Hf;
          pose proof (a_wf_aenv_uniq HwfΘ0) as Huq;
          destruct Hf as [Hb2 | [τx Hb2]];
          [ assert (Hc : abind_tvar = abind_flex_mono)
              by (eapply binds_unique; [ exact Hrig | exact Hb2 | exact Huq ])
          | assert (Hc : abind_tvar = abind_flex_mono_def τx)
              by (eapply binds_unique; [ exact Hrig | exact Hb2 | exact Huq ]) ];
          discriminate Hc.
    +
      apply Hdrop.
      * exact (a_wf_pskl_arrow_guarded HwfP0).
      * apply flex_r_off_nonvar; intros ?; discriminate.
    +
      cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
      inversion Hrefine; subst.
      *
        match goal with
          H : forall α0, α0 `notin` ?Lr -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ open_bskl_wrt_bskl ?Qb _ }}ad |- _ =>
            rename H into Hrbody;
            remember Lr as Lr0 eqn:HeqLr; clear HeqLr;
            remember Qb as Qb0 eqn:HeqQb; clear HeqQb
        end.
        inversion HwfP0; subst.
        match goal with H : forall α0, α0 `notin` ?L0 -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
          rename H into Hw0body; remember L0 as Lw0 eqn:HeqLw0; clear HeqLw0 end.
        inversion Hconsis; subst.
        --
           match goal with H : forall α0, α0 `notin` ?Lc -> {{ _ ⨟ _ ⊢ˢ _ ∼ _ }}ad |- _ =>
             rename H into Hcbody; remember Lc as Lc0 eqn:HeqLc; clear HeqLc end.
           pick fresh β for
             (Lr0 `union` Lw0 `union` Lc0 `union` dom Θ `union` dom Θ0
                `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
                `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
                `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0s

                `union` ftvar_in_aenv Θ0
                `union` def_ftv Θ).
           assert (HβΘ : β `notin` dom Θ) by auto.
           assert (HβΘ0 : β `notin` dom Θ0) by auto.
           assert (Hβα : β <> α) by auto.
           assert (Hβκ : β `notin` dom κ) by auto.
           assert (Hβψa : β `notin` ftvar_in_uskl ψa) by auto.
           assert (Hβdef : β `notin` def_ftv Θ) by auto.
           destruct (solve_context_open_tvar
                       HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 Hβα HβΘ HβΘ0)
             as (Hweak & _ & Hwfβ & Hwfβ0 & HαΘβ & HαΘ0β & Hκβ & _ & HwfPiβ).
           assert (HwfP0β : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                     ⊢ₚₛ (open_pskl_wrt_pskl P0s (pskl_var_f β)) }}a).
           { eapply a_wf_pskl_delta_mono;
               [ apply (Hw0body β ltac:(auto)) | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
           assert (HscopeSβ : ftvar_in_uskl (uskl_univ_ghost R0)
                     [<=] add α (dom ((β ~ abind_tvar) ++ Θ0) `union` dom ((β ~ abind_tvar) ++ Θ))).
           { simpl in HscopeS |- *. clear - HscopeS; fsetdec. }
           assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ))
             by (eapply delta_def_fresh_weaken_tvar; eassumption).
           assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                     ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad)
             by (eapply ad_partial_precise_weaken;
                   [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
           assert (HwfSubβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
                     (uskl_to_pskl (uskl_univ_ghost Rsub0)) }}a)
             by (eapply a_wf_pskl_weaken;
                   [ intros x b Hb; apply binds_app_3; exact Hb | exact HwfSub ]).

           assert (HΘsβ : forall x b, binds x b Θs -> binds x b ((β ~ abind_tvar) ++ Θ))
             by (intros x b Hb; apply binds_app_3; apply HΘs; exact Hb).
           assert (Hrfrβ : rsubst_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ)
             by (apply rsubst_fresh_weaken_tvar; exact Hrfr).
           assert (HΔρftvβ : forall α0, α0 `in` Δρ ->
                     α0 `notin` ftvar_in_pskl
                          (open_pskl_wrt_pskl P0s (pskl_var_f β))
                        `union` ftvar_in_pskl Pi).
           { intros α0 Hα0.
             pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0s
                           (pskl_var_f β)) as Hup.
             pose proof (HΔρftv α0 Hα0) as Hd0. pose proof (HΔρΘ α0 Hα0) as Hd1.
             cbn [ftvar_in_pskl] in Hup, Hd0.
             clear - Hup Hd0 Hd1 HβΘ; fsetdec. }
           assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                     (pskl_to_bskl_inh (msubst_pskl κ (open_pskl_wrt_pskl P0s
                                                         (pskl_var_f β))))
                     ⊳ (open_bskl_wrt_bskl Qb0 (bskl_var_f β)) }}ad).
           { rewrite (@msubst_pskl_open Θ0 κ Θ P0s β Hκ Hβκ).
             rewrite pskl_to_bskl_inh_open.
             eapply ad_refine_syn_delta_mono;
               [ apply (Hrbody β ltac:(auto)) | clear; fsetdec ]. }
           assert (Hmeas : size_uskl (uskl_univ_ghost R0)
                             + size_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β))
                             <= n).
           { rewrite size_pskl_open_pskl_wrt_pskl_var. cbn in Hn |- *; lia. }
           destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HβΘ)
             as (HβΘw & Hmonβ & Hnrβ & Hκwβ).
           assert (HLβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β L)
             by (rewrite ftvar_in_aenv_cons_tvar; clear - HL; fsetdec).
           apply (@lookeq_solve_strip_tvar Θ0 Θ Θw κ Δ Ψi Ψa ψa α _ _ Pi L
                    (pskl_univ_ghost (uskl_to_pskl R0))
                    (open_pskl_wrt_pskl P0s (pskl_var_f β)) β
                    Hκ HwfPi HβΘ HβΘ0 HβΘw Hβκ Hβψa Hβdef).
           ++
              intros Ξc 𝒞 HLK.
              apply a_lookeq_univ_ghost1_adm with (β := β).
              ** clear - Fr; solve_notin.
              ** exact HLK.
           ++ exact (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) Θw κ Δ
                       Ψ' Ψi Ψa Ψsub ψa (open_bskl_wrt_bskl Qb0 (bskl_var_f β))
                       (pskl_univ_ghost (uskl_to_pskl R0))
                       (open_pskl_wrt_pskl P0s (pskl_var_f β)) Pi
                       (uskl_univ_ghost R0) α Θs Δρ Ψρ (uskl_univ_ghost Rsub0)
                       Hmeas Hwfβ Hwfβ0 HwfΘw Hmonβ Hnrβ HwfP0β HwfPiβ Hκβ Hκwβ
                       Hψaw HαΘβ HαΘ0β eq_refl
                       HscopeSβ HlcS Htags Hdisj Hsub Hdfreshβ Hpreβ
                       HΨs1 HΨs2 (Hcbody β ltac:(auto)) ltac:(lc_tgt) HwfSubβ Hrefβ
                       Hrho0 HΘsβ HΨρ Hrfrβ HΔρΔ HΔρw HΔρftvβ HΔρPi Hψaap
                       (add β L) HLβ).
        --
           exfalso.
           pose proof (guarded_uskl_head
                         (@guarded_uskl_of_uskl_to_pskl
                            (Rsub0) HgSub0))
             as Hghsub.
           match goal with
             H : {{ _ ⨟ _ ⊢ˢ Rsub0
                   ∼ bskl_all_inh _ }}ad |- _ =>
               pose proof (ad_pat_consis_guarded_head_target H HwfΘ Hghsub) as Hgh
           end.
           destruct Hgh as [Habs | [[α0 Habs] | [Q1 [Q2 Habs]]]];
             discriminate Habs.
      *
        exfalso.
        eapply ad_refine_syn_all_inh_guarded_absurd;
          [ exact HwfΘ | exact Hrefine | apply guarded_bskl__var ].
    +  exfalso; apply HP0nh; reflexivity.
    +
      destruct (a_wf_pskl_univ_ghost_inv HwfP0) as [HgP0s HwfP0s].
      assert (Hkeep : forall Q0,
                {{ Ψsub ⨟ Θ ⊢ˢ Rsub0 ∼ Q0 }}ad -> lc_bskl Q0 ->
                {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0s)) ⊳ Q0 }}ad ->
                lookeq_solve_result Θ0 Θ Θw κ Δ Ψi Ψa ψa α
                  (pskl_univ_ghost (uskl_to_pskl R0)) (pskl_univ_ghost P0s) Pi L).
      { intros Q0 Hc0 HlcQ0 Href1.
        destruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                    (uskl_to_pskl R0) P0s Pi R0 α Θs Δρ Ψρ Rsub0
                    (Hmeas0 P0s ltac:(cbn; lia))
                    HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0s HwfPi Hκ Hκw Hψaw HαΘ HαΘ0
                    eq_refl HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2
                    Hc0 HlcQ0 HwfSub0 Href1 Hrhobody HΘs HΨρ Hrfr HΔρΔ HΔρw
                    ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap L HL)
          as (𝒞 & Ξc & Ξs & Pa & κc & κs & HLK & Hrest).
        exists 𝒞, Ξc, Ξs, Pa, κc, κs.
        refine (conj _ Hrest). apply a_lookeq__univ_ghost; exact HLK. }
      assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
        by (apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
      cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
      inversion Hrefine; subst.
      *
        match goal with
          H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ Q }}ad |- _ =>
            rename H into Href1 end.
        assert (HgQ : guarded_bskl Q)
          by (eapply ad_refine_syn_guarded_r;
              [ exact HwfΘ | exact Href1 | exact HgL
              | lc_tgt ]).
        destruct (ad_pat_consis_univ_ghost_guarded_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HgQ HlcQ)
          as (Q0 & Hc0 & Href0 & HgQ0 & HlcQ0).
        assert (Href2 : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0s)) ⊳ Q0 }}ad)
          by (eapply ad_refine_syn_univ_ghost_guarded_inv;
                [ exact HwfΘ | exact Href0 | exact HgQ0 ]).
        exact (Hkeep Q0 Hc0 HlcQ0 Href2).
      *
        exfalso.
        inversion Hconsis; subst.
        pose proof (guarded_uskl_head
                      (@guarded_uskl_of_uskl_to_pskl
                         (Rsub0) HgSub0))
          as Hghsub.
        match goal with
          H : {{ _ ⨟ _ ⊢ˢ Rsub0
                ∼ bskl_all_syn _ }}ad |- _ =>
            pose proof (ad_pat_consis_guarded_head_target H HwfΘ Hghsub) as Hgh
        end.
        destruct Hgh as [Habs | [[α0 Habs] | [Q1 [Q2 Habs]]]]; discriminate Habs.
      *
        match goal with
          H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ ?Q0' }}ad |- _ =>
            rename H into Href1 end.
        inversion Hconsis; subst.
        --
           match goal with
             H : {{ _ ⨟ _ ⊢ˢ Rsub0 ∼ _ }}ad |- _ =>
               rename H into Hc0 end.
           apply (Hkeep _ Hc0).
           ++ lc_tgt.
           ++ exact Href1.
        --
           exfalso.
           pose proof (guarded_uskl_head
                         (@guarded_uskl_of_uskl_to_pskl
                            (Rsub0) HgSub0))
             as Hghsub.
           match goal with
             H : {{ _ ⨟ _ ⊢ˢ Rsub0
                   ∼ bskl_univ_ghost _ }}ad |- _ =>
               pose proof (ad_pat_consis_guarded_head_target H HwfΘ Hghsub) as Hgh
           end.
           destruct Hgh as [Habs | [[α0 Habs] | [Q1 [Q2 Habs]]]];
             discriminate Habs.
      *
        match goal with H : binds ?αf (abind_flex_mono_def ?τ) Θ |- _ =>
          rename H into Hbf end.
        assert (HgQ : guarded_bskl (bskl_var_f α0)) by apply guarded_bskl__var.
        destruct (ad_pat_consis_univ_ghost_guarded_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HgQ HlcQ)
          as (Q0 & Hc0 & Href0 & HgQ0 & HlcQ0).
        assert (Href2 : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0s)) ⊳ Q0 }}ad)
          by (eapply ad_refine_syn_univ_ghost_guarded_inv;
                [ exact HwfΘ | exact Href0 | exact HgQ0 ]).
        exact (Hkeep Q0 Hc0 HlcQ0 Href2).
  -  clear - HαR; fsetdec.
  -
    cbn [uskl_to_pskl] in HeraseR; subst P.
    pose proof (lc_uskl_dot_univ_ghost_inv HlcS) as HlcS0.

    cbn [msubst_uskl_syn subst_uskl_in_uskl] in Hrho.
    destruct (uskl_rsubst_dot_univ_ghost_r_inv Hrho) as (Rsub0 & HRs & Hrhobody).
    subst Rsub.
    cbn [uskl_to_pskl] in HwfSub.
    destruct (a_wf_pskl_univ_ghost_inv HwfSub) as [HgSub0 HwfSub0].
    destruct (ad_pat_consis_dot_univ_ghost_refine_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HlcQ)
      as (Q0 & Hc0 & Href0 & HlcQ0).
    clear Hconsis Hrefine.
    assert (Hsrc : (exists L0, pskl_to_bskl_inh (msubst_pskl κ P0) = bskl_univ_ghost L0)
                   \/ pskl_to_bskl_inh (msubst_pskl κ P0) = bskl_ghost)
      by (eapply ad_refine_syn_univ_ghost_rhs_src;
            [ exact HwfΘ | exact Href0 | reflexivity ]).
    destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
    +
      exfalso; destruct Hsrc as [[L0 HL0] | HL0]; cbn in HL0; discriminate.
    +  inversion HwfP0.
    +
      exfalso; destruct Hsrc as [[L0 HL0] | HL0];
        cbn [msubst_pskl] in HL0; destruct (msubst_lookup κ β0);
        cbn in HL0; discriminate.
    +
      exfalso; destruct Hsrc as [[L0 HL0] | HL0]; cbn in HL0; discriminate.
    +
      exfalso; destruct Hsrc as [[L0 HL0] | HL0]; cbn in HL0; discriminate.
    +  exfalso; apply HP0nh; reflexivity.
    +
      clear Hsrc.
      destruct (a_wf_pskl_univ_ghost_inv HwfP0) as [HgP0s HwfP0s].
      cbn [msubst_pskl pskl_to_bskl_inh] in Href0.
      assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
        by (apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
      pose proof (ad_refine_syn_univ_ghost_keep_inv HwfΘ HgL Href0) as Href1.
      assert (Hmeas : size_uskl R0 + size_pskl P0s <= n) by (cbn in Hn; lia).
      edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                   (uskl_to_pskl R0) P0s Pi R0 α Θs Δρ Ψρ Rsub0
                   Hmeas HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0s HwfPi Hκ Hκw Hψaw HαΘ HαΘ0 eq_refl
                   HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0
                   ltac:(lc_tgt) HwfSub0 Href1
                   Hrhobody HΘs HΨρ Hrfr HΔρΔ HΔρw ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap L HL)
        as (𝒞 & Ξc & Ξs & Pa & κc & κs & HLK & Hrest).
      exists 𝒞, Ξc, Ξs, Pa, κc, κs.
      refine (conj _ Hrest).
      apply a_lookeq__univ_ghost; exact HLK.
Qed.

Theorem a_lookeq_solve_complete :
  forall NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->

  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->
  Ψi `union` Ψa [<=] Ψ' ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψa ->
  Ψa [<=] Ψsub ->
  ftvar_in_uskl ψa [<=] dom Θ ->
  {{ Ψsub ⨟ Θ ⊢ˢ (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ∼ Q }}ad ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R'))) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
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
    ftvar_in_a_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc `union` dom κ
                          `union` def_ftv Θ /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad.
Proof.
  intros NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α.
  intros HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 HeraseR HscopeS HlcS Htags Hdisj
         Hsub Hdfresh Hpre HΨs1 HΨs2 Hψaw Hconsis HwfQ HwfSub Hrefine L HL.
  edestruct (@a_lookeq_solve_complete_gen
               (size_uskl R' + size_pskl P0)
               NM Θ0 Θ Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α
               nil empty empty
               (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')))
    as (𝒞 & Ξc & Ξs & Pa & κc & κs
        & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
        & HwfPa & HwfΞ & HαΞ & Hmapfst
        & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart);
    [ exact (le_n _) | exact HwfΘ | exact HwfΘ0
    | exact HwfΘ | intros x b Hb; exact Hb | intros x b Hb; left; exact Hb
    | exact HwfP0 | exact HwfPi | exact Hκ
    | intros α0 Hf; eapply a_inc_lookup_flex_ftv_dom; [ exact Hκ | exact Hf ]
    | exact Hψaw
    | exact HαΘ | exact HαΘ0 | exact HeraseR | exact HscopeS
    | exact HlcS | exact Htags | exact Hdisj | exact Hsub | exact Hdfresh
    | exact Hpre | clear - HΨs1; fsetdec | exact HΨs2 | exact Hconsis
    | apply lc_bskl_of_bskl_to_pskl; exact (a_wf_pskl_lc HwfQ)
    | exact HwfSub | exact Hrefine
    | apply ursubst__refl;
        [ apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact HwfSub
        | clear; fsetdec ]
    | intros x b Hb; inversion Hb
    | clear; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | clear; fsetdec
    | clear; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | clear; fsetdec
    | exact HL
    | ].
  exists 𝒞, Ξc, Ξs, Pa, κc, κs.
  repeat split; assumption.
Qed.
