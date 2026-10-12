Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.prop_shapes.

Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.subtyping.prop_sub_msubst_equiv.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_gen.

Set Implicit Arguments.

Lemma ptyp_to_uskl_syn_shape : forall τ,
  (exists n, ptyp_to_uskl_syn τ = uskl_var_b n)
  \/ ptyp_to_uskl_syn τ = uskl_unit
  \/ (exists α, ptyp_to_uskl_syn τ = uskl_var_f α)
  \/ (exists A B, ptyp_to_uskl_syn τ = uskl_arrow A B)
  \/ (exists A, ptyp_to_uskl_syn τ = uskl_all_syn A).
Proof.
  intros τ; destruct τ; unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; cbn.
  - right; left; reflexivity.
  - left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; right; left; do 2 eexists; reflexivity.
  - right; right; right; right; eexists; reflexivity.
Qed.

Lemma ptyp_to_uskl_syn_not_tag : forall τ ε R,
  ptyp_to_uskl_syn τ <> uskl_all_tag ε R.
Proof.
  intros τ ε R.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

Lemma ptyp_to_uskl_syn_not_univ_ghost : forall τ R,
  ptyp_to_uskl_syn τ <> uskl_univ_ghost R.
Proof.
  intros τ R.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

Lemma ptyp_to_uskl_syn_not_dot_univ_ghost : forall τ R,
  ptyp_to_uskl_syn τ <> uskl_dot_univ_ghost R.
Proof.
  intros τ R.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

Lemma msubst_uskl_syn_all_tag_inv : forall κ R ε X,
  msubst_uskl_syn κ R = uskl_all_tag ε X ->
  exists R0, R = uskl_all_tag ε R0 /\ msubst_uskl_syn κ R0 = X.
Proof.
  intros κ R ε X He; destruct R; cbn in He; try discriminate He.
  - exfalso; eapply ptyp_to_uskl_syn_not_tag; exact He.
  - injection He as <- <-. eexists; split; reflexivity.
Qed.

Lemma msubst_uskl_syn_all_syn_inv : forall κ R X,
  msubst_uskl_syn κ R = uskl_all_syn X ->
  (exists R0, R = uskl_all_syn R0 /\ msubst_uskl_syn κ R0 = X)
  \/ (exists α, R = uskl_var_f α).
Proof.
  intros κ R X He; destruct R; cbn in He; try discriminate He.
  - right; eexists; reflexivity.
  - left; injection He as <-; eexists; split; reflexivity.
Qed.

Lemma msubst_uskl_syn_univ_ghost_inv : forall κ R X,
  msubst_uskl_syn κ R = uskl_univ_ghost X ->
  exists R0, R = uskl_univ_ghost R0 /\ msubst_uskl_syn κ R0 = X.
Proof.
  intros κ R X He; destruct R; cbn in He; try discriminate He.
  - exfalso; eapply ptyp_to_uskl_syn_not_univ_ghost; exact He.
  - injection He as <-. eexists; split; reflexivity.
Qed.

Lemma msubst_uskl_syn_dot_univ_ghost_inv : forall κ R X,
  msubst_uskl_syn κ R = uskl_dot_univ_ghost X ->
  exists R0, R = uskl_dot_univ_ghost R0 /\ msubst_uskl_syn κ R0 = X.
Proof.
  intros κ R X He; destruct R; cbn in He; try discriminate He.
  - exfalso; eapply ptyp_to_uskl_syn_not_dot_univ_ghost; exact He.
  - injection He as <-. eexists; split; reflexivity.
Qed.

Lemma msubst_uskl_syn_arrow_inv : forall κ R X Y,
  msubst_uskl_syn κ R = uskl_arrow X Y ->
  (exists Ra Rb, R = uskl_arrow Ra Rb /\
     msubst_uskl_syn κ Ra = X /\ msubst_uskl_syn κ Rb = Y)
  \/ (exists α, R = uskl_var_f α).
Proof.
  intros κ R X Y He; destruct R; cbn in He; try discriminate He.
  - right; eexists; reflexivity.
  - left; injection He as <- <-. do 2 eexists; repeat split.
Qed.

Lemma a_uskl_tyequiv_univ_ghost_l_inv : forall Θ R X,
  {{ Θ ⊢ (uskl_univ_ghost R) ≡ᵘ X }}a ->
  exists X0, X = uskl_univ_ghost X0 /\ {{ Θ ⊢ R ≡ᵘ X0 }}a.
Proof.
  intros Θ R X H; inversion H; subst;
    [ exfalso; eapply ptyp_to_uskl_syn_not_univ_ghost; eassumption
    | eexists; split; [ reflexivity | assumption ] ].
Qed.

Lemma a_uskl_tyequiv_dot_univ_ghost_l_inv : forall Θ R X,
  {{ Θ ⊢ (uskl_dot_univ_ghost R) ≡ᵘ X }}a ->
  exists X0, X = uskl_dot_univ_ghost X0 /\ {{ Θ ⊢ R ≡ᵘ X0 }}a.
Proof.
  intros Θ R X H; inversion H; subst;
    [ exfalso; eapply ptyp_to_uskl_syn_not_dot_univ_ghost; eassumption
    | eexists; split; [ reflexivity | assumption ] ].
Qed.

Lemma a_uskl_tyequiv_arrow_l_inv : forall Θ R1 R2 X,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ (uskl_arrow R1 R2) ≡ᵘ X }}a ->
  (exists X1 X2, X = uskl_arrow X1 X2) \/ (exists β, X = uskl_var_f β).
Proof.
  intros Θ R1 R2 X Hwf H; inversion H; subst;
    [ | left; do 2 eexists; reflexivity ].

  match goal with
  | Hm1 : mono_ptyp ?t1, He1 : ptyp_to_uskl_syn ?t1 = uskl_arrow R1 R2,
    Hm2 : mono_ptyp ?t2, Heq : {{ _ ⊢ ?t1 ≡ᵗ ?t2 }}a |- _ =>
      destruct Hm1; cbn in He1; try discriminate He1;
      pose proof (a_tyequiv_downarrow Hwf Heq) as Hdn;
      destruct Hm2; cbn in Hdn |- *;
        [  exfalso; discriminate Hdn
        | right; eexists; reflexivity
        | left; do 2 eexists; reflexivity ]
  end.
Qed.

Lemma msubst_uskl_syn_var_inv : forall κ R β,
  msubst_uskl_syn κ R = uskl_var_f β ->
  exists α, R = uskl_var_f α.
Proof.
  intros κ R β He; destruct R; cbn in He; try discriminate He.
  eexists; reflexivity.
Qed.

Lemma msubst_uskl_syn_all_syn_inv_mono : forall Θ0 κ Θ R X,
  κ ∷ Θ0 ⊑ Θ ->
  msubst_uskl_syn κ R = uskl_all_syn X ->
  exists R0, R = uskl_all_syn R0 /\ msubst_uskl_syn κ R0 = X.
Proof.
  intros Θ0 κ Θ R X Hinc He.
  destruct (@msubst_uskl_syn_all_syn_inv κ R X He) as [Hall | [α ->]];
    [ exact Hall | exfalso ].
  cbn in He.
  pose proof (@a_inc_lookup_mono Θ0 κ Θ α Hinc) as Hm.
  destruct (msubst_lookup κ α); cbn in He; try discriminate He.
  inversion Hm.
Qed.

Lemma downarrow_rigid : forall Θ α,
  uniq Θ ->
  binds α abind_tvar Θ ->
  ⇓ᵗ[Θ] (ptyp_var_f α) = ptyp_var_f α.
Proof.
  intros Θ α Huq Hb. cbn.
  apply msubst_lookup_notin.
  intro Hin.
  destruct (@aenv_msubst_dom_inv Θ α Hin) as [Hbf | [τ Hbf]];
    pose proof (binds_unique _ _ _ _ _ Hb Hbf Huq) as Hc; discriminate Hc.
Qed.

Lemma tyequiv_arrow_rigid_absurd : forall Θ α τ1 τ2,
  {{ ⊢ Θ }}a ->
  binds α abind_tvar Θ ->
  {{ Θ ⊢ (ptyp_arrow τ1 τ2) ≡ᵗ (ptyp_var_f α) }}a ->
  False.
Proof.
  intros Θ α τ1 τ2 Hwf Hb Heq.
  pose proof (a_tyequiv_downarrow Hwf Heq) as Hdn.
  rewrite (@downarrow_rigid Θ α (a_wf_aenv_uniq Hwf) Hb) in Hdn.
  cbn in Hdn. discriminate Hdn.
Qed.

Lemma slack_arrow_rigid_absurd : forall Θ0 κ Θ α R1' R2',
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  binds α abind_tvar Θ0 ->
  {{ Θ ⊢ (uskl_arrow R1' R2') ≡ᵘ (msubst_uskl_syn κ (uskl_var_f α)) }}a ->
  False.
Proof.
  intros Θ0 κ Θ α R1' R2' Hwf0 Hwf Hinc Hb Hslack.
  assert (Hnd : α `notin` dom κ)
    by (eapply a_inc_tvar_notin_dom; eassumption).
  assert (HbΘ : binds α abind_tvar Θ)
    by (eapply a_inc_binds_tvar; eassumption).
  cbn in Hslack. rewrite (msubst_lookup_notin κ Hnd) in Hslack.
  destruct (@a_uskl_tyequiv_mono_r_inv Θ _ _ Hslack (ptyp_var_f α) eq_refl
              (mono_ptyp__var α) (@a_wf_ptyp__var Θ α (or_introl HbΘ)))
    as [τ' [Heqτ' [Hm' [Hwf' Heq']]]].
  destruct τ'; cbn in Heqτ'; try discriminate Heqτ'.
  eapply tyequiv_arrow_rigid_absurd; eassumption.
Qed.

Lemma sub_flex_rigid_head_absurd :
  forall n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q,
  a_decls Ξ ->
  dom Ξ [<=] ftvar_in_pskl P0 ->
  {{ ⊢ (Ξ ++ (β ~ abind_tvar) ++ Θ0) }}a ->
  {{ ⊢ Θ }}a ->
  {{ (Ξ ++ (β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_flex_tvar Θ0 α ->
  β `in` ftvar_in_pskl P0 ->
  κ ∷ (Ξ ++ (β ~ abind_tvar) ++ Θ0) ⊑ Θ ->
  {{ Θ ⊢ R' ≡ᵘ (ptyp_to_uskl_syn (msubst_lookup κ α)) }}a ->
  ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ R' Q ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  False.
Proof.
  intros n NM M Θ0 Ξ α β P0 R' Ψ Θ κ Q
         HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα Hβin Hinc Hslack HD Hrs.

  assert (Huq : uniq (Ξ ++ (β ~ abind_tvar) ++ Θ0))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
  assert (Hwf' : {{ ⊢ (Ξ ++ Θ0) }}a)
    by (eapply a_wf_aenv_strip_mid; eassumption).
  assert (HwfΘ0 : {{ ⊢ Θ0 }}a) by (eapply a_wf_aenv_strip_prefix; exact Hwf').
  assert (Hαb0 : a_binds_tvar α Θ0)
    by (destruct Hfα as [h | [τ0 h]];
        [ right; left; exact h | right; right; exists τ0; exact h ]).
  assert (Hαbfull : a_binds_tvar α (Ξ ++ (β ~ abind_tvar) ++ Θ0)).
  { destruct (a_flex_tvar_weaken_app (Ξ ++ (β ~ abind_tvar)) Hfα)
      as [h | [τ0 h]];
      [ right; left | right; right; exists τ0 ]; simpl_env in h; exact h. }
  assert (Hbβ : binds β abind_tvar (Ξ ++ (β ~ abind_tvar) ++ Θ0))
    by (simpl_env; apply binds_app_3; apply binds_app_2;
        unfold binds; simpl; left; reflexivity).

  destruct (@a_inc_strip_decls_prefix Ξ ((β ~ abind_tvar) ++ Θ0) κ Θ HdeclsΞ
              Hinc)
    as [κa [κb [Heqκ [Hdκa Hincxb]]]].
  destruct (a_inc_tvar_inv Hincxb) as [Ξv [Θ' [HeqΘ [HsufΞv Hincb]]]].
  assert (HwfΘ' : {{ ⊢ Θ' }}a).
  { rewrite HeqΘ in Hwfth.
    eapply a_wf_aenv_strip_prefix with (Ξ := Ξv ++ (β ~ abind_tvar)).
    simpl_env. simpl_env in Hwfth. exact Hwfth. }
  assert (HeqW : (Ξv ++ (β ~ abind_tvar)) ++ Θ' = Θ)
    by (rewrite HeqΘ; simpl_env; reflexivity).
  assert (HβΘ' : β `notin` dom Θ').
  { rewrite HeqΘ in HuqΘ. clear - HuqΘ. simpl_env in HuqΘ. solve_uniq. }

  assert (Hmκα : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact Hinc).
  assert (Hwfκα : a_wf_ptyp Θ (msubst_lookup κ α))
    by (eapply a_inc_lookup_wf; eassumption).
  destruct (a_uskl_tyequiv_mono_r_inv Hslack
              (eq_refl (ptyp_to_uskl_syn (msubst_lookup κ α))) Hmκα Hwfκα)
    as [τ' [HeqR' [Hmτ' [Hwfτ' Heqττ']]]].
  subst R'.
  assert (Hddτ' : ⇓ᵗ[ Θ ] τ' = ⇓ᵗ[ Θ ] (msubst_lookup κ α))
    by (apply a_tyequiv_downarrow; eassumption).

  assert (Hακa : α `notin` dom κa).
  { rewrite Hdκa.
    assert (hd : α `in` dom Θ0)
      by (destruct Hfα as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
    clear - Huq hd. simpl_env in Huq. solve_uniq. }
  assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup κ α)).
  { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb Hακa).
    eapply a_inc_lookup_wf; eassumption. }
  assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ')
    by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
  assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup κ α) = ⇓ᵗ[ Θ' ] (msubst_lookup κ α)).
  { rewrite <- HeqW.
    apply downarrow_app_agree_ptyp; [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
  assert (HO1 : ftvar_in_ptyp (⇓ᵗ[ Θ ] τ') [<=] dom Θ').
  { rewrite Hddτ'. rewrite Hddα. apply a_wf_ptyp_ftv_dom.
    apply a_wf_ptyp_downarrow_mono; eassumption. }

  assert (Hmono_img : forall γ, mono_ptyp (msubst_lookup (aenv_msubst Θ) γ))
    by (intros; apply aenv_msubst_image_mono; exact Hwfth).
  assert (HO2 : ftvar_in_bskl (⇓ᵇ[ Θ ] Q) [<=] dom Θ').
  { eapply sub_gv_bskl_downarrow_mono_scoped;
      [ exact HD | exact Hwfth | reflexivity | exact Hmτ' | exact HO1 ]. }
  assert (Heqinh : ⇓ᵇ[ Θ ] (pskl_to_bskl_inh (msubst_pskl κ P0))
                   = pskl_to_bskl_inh (⇓ˢ[ Θ ] (msubst_pskl κ P0)))
    by (apply msubst_bskl_pskl_to_bskl_inh; exact Hmono_img).
  assert (HO3 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P0)) [<=] dom Θ').
  { pose proof (refine_syn_downarrow_source_ftv Hrs Hwfth) as h.
    rewrite Heqinh in h. rewrite ftvar_in_bskl_inh in h.
    clear - h HO2. fsetdec. }

  assert (HβκP0 : β `in` ftvar_in_pskl (msubst_pskl κ P0))
    by (eapply rigid_survives_solution; eassumption).
  assert (HβΘdn : β `notin` dom (aenv_msubst Θ)).
  { intro Hin.
    assert (HbβΘ : binds β abind_tvar Θ)
      by (eapply a_inc_binds_tvar; [ exact Hinc | exact Hbβ ]).
    destruct (@aenv_msubst_dom_inv Θ β Hin) as [Hbf | [τ0 Hbf]];
      pose proof (binds_unique _ _ _ _ _ HbβΘ Hbf HuqΘ) as Hc; discriminate Hc. }
  assert (Hβdn : β `in` ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P0)))
    by (apply msubst_pskl_ftv_keep; eassumption).
  clear - Hβdn HO3 HβΘ'. fsetdec.
Qed.

Definition sub_complete_arrow (n : nat) : Prop :=
  forall NM M Θ0 P0 P Ra Rb R' Ψ Θ κ Q,
    sub_complete_concl n NM M Θ0 P0 P (uskl_arrow Ra Rb) R' Ψ Θ κ Q.

Definition sub_complete_ctx_lt (n k : nat) : Prop :=
  forall NM M Θ0 P0 P R R' Ψ Θ κ Q,
    length Θ0 < k ->
    sub_complete_concl n NM M Θ0 P0 P R R' Ψ Θ κ Q.

Lemma sub_flex_complete_holds : forall n k,
  sub_complete_arrow n ->
  sub_complete_ctx_lt n k ->
  forall NM M Θ0 Ξ α P0 R' Ψ Θ κ Q,
    length Ξ + length Θ0 <= k ->
    sub_flex_complete_concl n NM M Θ0 Ξ α P0 R' Ψ Θ κ Q.
Proof.
  intros n k Harrow Hmain NM M Θ0.
  induction Θ0 as [ | [β b] Θ0' IHΘ0 ];
    intros Ξ α P0 R' Ψ Θ κ Q Hlen.
  -
    unfold sub_flex_complete_concl.
    intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD Hrs
           HwfQ.
    exfalso. destruct Hfα as [Hb | [τ Hb]]; inversion Hb.
  -
    assert (IH' : forall Ξ' α' P0' R'' Ψ' Θ'' κ' Q',
              length Ξ' <= S (length Ξ) ->
              sub_flex_complete_concl n NM M Θ0' Ξ' α' P0' R'' Ψ' Θ'' κ' Q').
    { intros Ξ' α' P0' R'' Ψ' Θ'' κ' Q' HlenΞ.
      apply IHΘ0; simpl in Hlen; lia. }
    destruct b as [ | A | P | | τ ].
    +
      destruct (α == β) as [-> | Hne].
      *
        unfold sub_flex_complete_concl.
        intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack HD
               Hrs HwfQ.
        exfalso.
        assert (Huq : uniq (Ξ ++ (β ~ abind_tvar) ++ Θ0'))
          by (apply a_wf_aenv_uniq; exact Hwf).
        destruct Hfα as [Hb | [τ0 Hb]];
          (apply binds_cons_1 in Hb as [[_ Hc] | Hb];
           [ discriminate Hc
           | apply binds_In in Hb; simpl_env in Huq; solve_uniq ]).
      * destruct (AtomSetProperties.In_dec β (ftvar_in_pskl P0))
          as [Hβin | Hβni].
        --
           unfold sub_flex_complete_concl.
           intros HdeclsΞ HdomΞ Hwf Hwfth HwfP0 Hfα HmodSK HmodTY Hinc Hslack
                  HD Hrs HwfQ.
           exfalso.
           assert (Hfα0 : a_flex_tvar Θ0' α)
             by (eapply (proj1 (a_flex_tvar_cons_other _ _ Hne)); exact Hfα).
           eapply sub_flex_rigid_head_absurd with (Θ0 := Θ0') (β := β);
             eassumption.
        -- apply (a_sub_flex_complete_skip_rigid IH' Hne Hβni).
    +
      apply (a_sub_flex_complete_skip_tm_var IH').
    +
      apply (a_sub_flex_complete_skip_tm_skl IH').
    +
      destruct (β == α) as [-> | Hne].
      * apply (a_sub_flex_complete_solve Harrow).
      * destruct (AtomSetProperties.In_dec β (ftvar_in_pskl P0))
          as [Hβin | Hβni].
        -- apply (a_sub_flex_complete_depend IH' (not_eq_sym Hne) Hβin).
        -- apply (a_sub_flex_complete_skip IH' (not_eq_sym Hne) Hβni).
    +
      apply (a_sub_flex_complete_assign (n := n) (Ξ := Ξ) (Θ0 := Θ0')).
      intros NM' M' Θ0'' P0' P' R'' T'' Ψ' Θ' κ' Q' Hle.
      apply (Hmain NM' M' Θ0'' P0' P' R'' T'' Ψ' Θ' κ' Q').
      simpl in Hlen. lia.
Qed.

Lemma ad_refine_syn_all_inh_l_shape : forall Θ Δ A Qt,
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_all_inh A) ⊳ Qt }}ad ->
  exists B, Qt = bskl_all_inh B.
Proof.
  intros Θ Δ A Qt H.
  remember (bskl_all_inh A) as S eqn:HS. revert A HS.
  induction H; intros A0 HS; try discriminate HS.
  -  eexists; reflexivity.
  -
    exfalso.
    destruct (IHad_refine_syn _ HS) as [B HB].
    destruct τ; cbn in HB; discriminate HB.
Qed.

Lemma check_row_guarded_p0 : forall Θ0 κ Θ P0 B,
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  guarded_pskl B ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (pskl_to_bskl_inh B) }}ad ->
  guarded_pskl P0.
Proof.
  intros Θ0 κ Θ P0 B Hinc HwfP0 Hmod HgB Hrs.
  pose proof (a_wf_pskl_lc HwfP0) as Hlc.
  inversion Hmod as [ | A HeqP0 | ]; subst.
  destruct A; cbn in *.
  - apply guarded_pskl__unit.
  -  inversion Hlc.
  - apply guarded_pskl__var.
  - inversion Hlc; subst. apply guarded_pskl__arrow; assumption.
  -
    exfalso.
    destruct (ad_refine_syn_all_inh_l_shape Hrs) as [B0 HB0].
    destruct (@pskl_to_bskl_inh_all_inh_inv B B0 HB0) as [X [HX _]].
    subst B. inversion HgB.
Qed.

Lemma sub_gv_all_inh_forall_r_family : forall n NM M Ψ Θ R Qt,
  ad_pat_sub_fuel n NM M Ψ Θ R Qt ->
  forall B, NM = a_sub_mode_ty -> M = mode_tc -> Qt = bskl_all_inh B ->
  exists L m, m < n /\
    forall α, α `notin` L ->
      ad_pat_sub_fuel m a_sub_mode_ty mode_tc Ψ ((α ~ abind_tvar) ++ Θ) R
        (open_bskl_wrt_bskl B (bskl_var_f α)).
Proof.
  intros n NM M Ψ Θ R Qt H; induction H; intros B0 HNM HM HQ;
    try discriminate.
  -
    exfalso.
    destruct (@pskl_to_bskl_inh_all_inh_inv _ _ HQ) as [X [HX _]].
    subst B. match goal with Hg : guarded_pskl _ |- _ => inversion Hg end.
  -
    inversion HQ; subst.
    exists L, n. split; [ lia | ].
    intros α Hα.
    match goal with
    | Hf : forall α, α `notin` L -> ad_pat_sub_fuel _ _ _ _ _ _ _ |- _ =>
        exact (Hf α Hα)
    end.
  -
    subst.
    match goal with
    | IHx : forall B, _ -> _ -> _ -> _ |- _ =>
        destruct (IHx B0 eq_refl eq_refl eq_refl) as [L [m [Hlt Hfam]]]
    end.
    exists L, (S m). split; [ lia | ].
    intros α Hα.
    eapply ad_pat_sub_fuel__forall_l_tagged;
      [ eassumption | eassumption | eassumption | eassumption
      | eapply a_wf_pskl_weaken;
          [ intros y c Hb; simpl_env; apply binds_app_3; exact Hb
          | eassumption ]
      | exact (Hfam α Hα) ].
  -
    subst.
    match goal with
    | IHx : forall B, _ -> _ -> _ -> _ |- _ =>
        destruct (IHx B0 eq_refl eq_refl eq_refl) as [L [m [Hlt Hfam]]]
    end.
    exists L, (S m). split; [ lia | ].
    intros α Hα.
    eapply ad_pat_sub_fuel__forall_l_untagged;
      [ eassumption | eassumption | eassumption | eassumption
      | eapply a_wf_pskl_weaken;
          [ intros y c Hb; simpl_env; apply binds_app_3; exact Hb
          | eassumption ]
      | exact (Hfam α Hα) ].
Qed.

Lemma sub_complete_all_inh_counterpart : forall n Θ0 P0 P R R' Ψ Θ κ B,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->
  sub_complete_concl (S n) a_sub_mode_ty mode_tc Θ0 P0 P R R' Ψ Θ κ
    (bskl_all_inh B).
Proof.
  intros n Θ0 P0 P R R' Ψ Θ κ B IH.
  intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
         Hgf.
  destruct (@sub_gv_all_inh_forall_r_family _ _ _ _ _ _ _ HDj B
              eq_refl eq_refl eq_refl)
    as [L [m [Hlt Hfam]]].
  refine (@a_sub_complete_forall_r n Θ0 P0 P R R' Ψ Θ κ B L IH _
            Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
            HwfQ Hgf).
  intros α Hα.
  eapply ad_pat_sub_fuel_le; [ exact (Hfam α Hα) | lia ].
Qed.

Lemma p0_wlog_trichotomy : forall NM M P0,
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  lc_pskl P0 ->
  guarded_pskl P0 \/ P0 = pskl_ghost \/
  (NM = a_sub_mode_ty /\ M = mode_tc /\ exists Pb, P0 = pskl_all_syn Pb).
Proof.
  intros NM M P0 Hsk Hty Hlc; destruct NM.
  -
    specialize (Hty eq_refl).
    inversion Hty as [ HeqM HeqP | A HeqM HeqP | M0 Pd Pc Hc HeqM HeqP ]; subst.
    + right; left; reflexivity.
    + destruct A; cbn in *.
      * left; apply guarded_pskl__unit.
      * inversion Hlc.
      * left; apply guarded_pskl__var.
      * left; inversion Hlc; subst; apply guarded_pskl__arrow; assumption.
      * right; right; repeat split; eexists; reflexivity.
    + left; inversion Hlc; subst; apply guarded_pskl__arrow; assumption.
  -
    specialize (Hsk eq_refl).
    inversion Hsk as [ HeqM HeqP | HeqM HeqP | M0 Pd Pc Hc HeqM HeqP ]; subst.
    + right; left; reflexivity.
    + right; left; reflexivity.
    + left; inversion Hlc; subst; apply guarded_pskl__arrow; assumption.
Qed.

Definition sub_complete (n : nat) : Prop :=
  forall NM M Θ0 P0 P R R' Ψ Θ κ Q,
    sub_complete_concl n NM M Θ0 P0 P R R' Ψ Θ κ Q.

Definition sub_flex_complete (n : nat) (Θ0 : aenv) : Prop :=
  forall NM M α P0 R' Ψ Θ κ Q,
    sub_flex_complete_concl n NM M Θ0 nil α P0 R' Ψ Θ κ Q.

Lemma sub_complete_assemble : forall n NM M Ψ Θ R' Q,
  ad_pat_sub_fuel n NM M Ψ Θ R' Q ->
  (forall n', n' < n -> sub_complete n') ->
  forall Θ0 (PIH : uskl -> Prop),
    (forall R0, PIH (uskl_univ_ghost R0) -> PIH R0) ->
    (forall R0, PIH (uskl_dot_univ_ghost R0) -> PIH R0) ->
    (forall α, PIH (uskl_var_f α) -> sub_flex_complete n Θ0) ->
    forall P0 P R κ, PIH R ->
      sub_complete_concl n NM M Θ0 P0 P R R' Ψ Θ κ Q.
Proof.
  intros n NM M Ψ Θ R' Q HD.
  induction HD as
    [ n0 NM0 Ψ0 Θa Ra Qa HΨ Hj Hss
    | n0 Ψ0 Θa Ta Ba HgT HgB Hj
    | n0 La Ψ0 Θa Ta Ba Hfam IHfam
    | n0 Ψ0 Θa Ra Qa HΨ HgR HgQ Hss Hj
    | n0 NM0 Ψ0 Ψ1 Ψ2 Θa Ma R1 R2 Q1 Q2 Hj1 Hsub2 IH2 HΨ
    | n0 NM0 Ψ0 Ψ' Θa Ma εa Rj ψj Qa HM HΨ1 HΨ2 Htg Hwfψ Hsub IHsub
    | n0 NM0 Ψ0 Ψ' Θa Ma Rj ψj Qa HM HΨ1 HΨ2 Htg Hwfψ Hsub IHsub
    | n0 Ψ0 Θa Ma Pa HΨ HwfPa Hmodg
    | n0 Ψ0 Θa Ma HΨ Hmodg
    | n0 Ψ0 Θa Ma Rg Qg HM Hsub IHsub
    | n0 Ψ0 Θa Ma Rg Qg HM Hsub IHsub
    | n0 NM0 Ψ0 Θa Ma αd τd Qa Hbd Hsub IHsub ];
    intros Hfuel Θ0 PIH He1 He2 He3 P0 P R κ HPIH.
  -
    apply a_sub_complete_infer.
  -
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    assert (HwfB : {{ Θa ⨟ empty ⊢ₚₛ Ba }}a)
      by (rewrite bskl_to_pskl_pskl_to_bskl_inh in HwfQ; exact HwfQ).
    assert (HgP0 : guarded_pskl P0)
      by (eapply check_row_guarded_p0;
          [ exact Hinc | exact HwfP0 | apply Hmodty; reflexivity
          | exact HgB | exact Hrs ]).
    exact (@a_sub_complete_check n0 Θ0 P0 P R Ta Ψ0 Θa κ Ba
             HgT HgB Hj HgP0 HwfB
             Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
             HwfQ Hgf).
  -
    exact (@a_sub_complete_forall_r n0 Θ0 P0 P R Ta Ψ0 Θa κ Ba La
             (Hfuel n0 ltac:(lia)) Hfam).
  -
    exact (@a_sub_complete_univ_ghost_r n0 Θ0 P0 P R Ra Ψ0 Θa κ Qa
             HgR HgQ Hj).
  -
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    assert (Hsh : (exists Rx Ry, R = uskl_arrow Rx Ry)
                  \/ (exists γ, R = uskl_var_f γ)).
    { destruct (@a_uskl_tyequiv_arrow_l_inv Θa R1 R2 _ Hwfth Hslack)
        as [[X1 [X2 HX]] | [γ HX]].
      - destruct (@msubst_uskl_syn_arrow_inv κ R X1 X2 HX)
          as [[Rx [Ry [HR _]]] | [γ HR]];
          [ left; exists Rx, Ry; exact HR | right; exists γ; exact HR ].
      - destruct (@msubst_uskl_syn_var_inv κ R γ HX) as [γ0 HR].
        right; exists γ0; exact HR. }
    destruct Hsh as [[Rx [Ry HR]] | [γ HR]]; subst R.
    + exact (@a_sub_complete_arrow n0 NM0 Ma Θ0 P0 P Rx Ry R1 R2 Ψ0 Θa κ
               Q1 Q2 (Hfuel n0 ltac:(lia))
               Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
               HwfQ Hgf).
    +
      cbn in HeqR. subst P.
      assert (Hbt : a_binds_tvar γ Θ0)
        by (inversion HwfP as [ | ? ? ? Hb | | | | ]; subst; exact Hb).
      destruct Hbt as [Hrig | Hfl].
      * exfalso.
        eapply slack_arrow_rigid_absurd;
          [ exact Hwf0 | exact Hwfth | exact Hinc | exact Hrig | exact Hslack ].
      * assert (Hfγ : a_flex_tvar Θ0 γ)
          by (destruct Hfl as [Hb | [τ0 Hb]];
              [ left; exact Hb | right; exists τ0; exact Hb ]).
        destruct (He3 γ HPIH NM0 Ma γ P0 (uskl_arrow R1 R2) Ψ0 Θa κ
                    (bskl_arrow Q1 Q2)
                    a_decls__nil ltac:(simpl; clear; solve_notin_auto)
                    Hwf0 Hwfth HwfP0 Hfγ Hmodsk Hmodty Hinc Hslack HDj Hrs
                    HwfQ)
          as [P1 [Θ1 [Hrun Hopt]]].
        exists P1, Θ1. split;
          [ apply a_sub__flex_mono; exact Hrun | exact Hopt ].
  -
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    assert (Hhd : exists R0, R = uskl_all_tag εa R0).
    { destruct (@a_uskl_tyequiv_all_tag_l_inv Θa εa Rj _ Hslack) as (X0 & _ & HX & _).
      destruct (@msubst_uskl_syn_all_tag_inv κ R εa X0 HX) as [R0 [HR _]].
      exists R0; exact HR. }
    destruct Hhd as [R0 HR0]. subst R.
    destruct (proj2 (or_assoc _ _ _)
                (p0_wlog_trichotomy Hmodsk Hmodty (a_wf_pskl_lc HwfP0)))
      as [Hwlog | [HeqNM [HeqM [Pb HeqP0]]]].
    + exact (@a_sub_complete_forall_l_tagged n0 NM0 Ma Θ0 P0 P R0 Rj Ψ0 Θa κ
               Qa εa Ψ' ψj (Hfuel n0 ltac:(lia)) HM HΨ1 HΨ2 Htg Hwfψ Hsub
               Hwlog Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj
               Hrs HwfQ Hgf).
    +
      subst NM0 Ma P0.
      cbn in Hrs.
      destruct (ad_refine_syn_all_inh_l_shape Hrs) as [B HB]. subst Qa.
      exact (@sub_complete_all_inh_counterpart n0 Θ0 (pskl_all_syn Pb) P
               (uskl_all_tag εa R0)
               (uskl_all_tag εa Rj) Ψ0 Θa κ B (Hfuel n0 ltac:(lia))
               Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
               HwfQ Hgf).
  -
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    assert (Hhd : exists R0, R = uskl_all_syn R0).
    { destruct (@a_uskl_tyequiv_all_syn_l_inv Θa Rj _ Hslack) as (X0 & _ & HX & _).
      destruct (@msubst_uskl_syn_all_syn_inv_mono Θ0 κ Θa R X0 Hinc HX)
        as [R0 [HR _]].
      exists R0; exact HR. }
    destruct Hhd as [R0 HR0]. subst R.
    destruct (proj2 (or_assoc _ _ _)
                (p0_wlog_trichotomy Hmodsk Hmodty (a_wf_pskl_lc HwfP0)))
      as [Hwlog | [HeqNM [HeqM [Pb HeqP0]]]].
    + exact (@a_sub_complete_forall_l_untagged n0 NM0 Ma Θ0 P0 P R0 Rj Ψ0 Θa κ
               Qa Ψ' ψj (Hfuel n0 ltac:(lia)) HM HΨ1 HΨ2 Htg Hwfψ Hsub
               Hwlog Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj
               Hrs HwfQ Hgf).
    + subst NM0 Ma P0.
      cbn in Hrs.
      destruct (ad_refine_syn_all_inh_l_shape Hrs) as [B HB]. subst Qa.
      exact (@sub_complete_all_inh_counterpart n0 Θ0 (pskl_all_syn Pb) P
               (uskl_all_syn R0)
               (uskl_all_syn Rj) Ψ0 Θa κ B (Hfuel n0 ltac:(lia))
               Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
               HwfQ Hgf).
  -
    exact (@a_sub_complete_ghost n0 Ma Θ0 P0 P R uskl_ghost Ψ0 Θa κ
             (pskl_to_bskl_inh Pa) eq_refl).
  -
    exact (@a_sub_complete_ghostg n0 Ma Θ0 P0 P R uskl_dot_ghost Ψ0 Θa κ
             bskl_ghost eq_refl).
  -
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    destruct (@a_uskl_tyequiv_univ_ghost_l_inv Θa Rg _ Hslack)
      as [X [HX Hslack0]].
    destruct (@msubst_uskl_syn_univ_ghost_inv κ R X HX) as [R00 [HR HmX]].
    subst R. cbn in HeqR. subst P.
    rewrite <- HmX in Hslack0.
    assert (HwfP' : {{ Θ0 ⨟ empty ⊢ₚₛ ⌊ R00 ⌋ˢ }}a)
      by (inversion HwfP; subst; rewrite <- (aenv_minus_empty Θ0);
          assumption).

    assert (Hgf0 : a_sub_mode_sk = a_sub_mode_ty -> uskl_ghost_free Rg)
      by (intro Habs; discriminate Habs).
    destruct (IHsub Hfuel Θ0 PIH He1 He2 He3 P0 (⌊ R00 ⌋ˢ) R00 κ
                (He1 R00 HPIH)
                Hwf0 Hwfth HwfP0 HwfP' Hmodsk Hmodty eq_refl Hinc Hslack0
                Hsub Hrs HwfQ Hgf0)
      as [P1 [Θ1 [Hrun Hopt]]].
    exists P1, Θ1. split;
      [ apply a_sub__univ_ghost_l; eassumption | exact Hopt ].
  -
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    destruct (@a_uskl_tyequiv_dot_univ_ghost_l_inv Θa Rg _ Hslack)
      as [X [HX Hslack0]].
    destruct (@msubst_uskl_syn_dot_univ_ghost_inv κ R X HX) as [R00 [HR HmX]].
    subst R. cbn in HeqR. subst P.
    rewrite <- HmX in Hslack0.
    assert (HwfP' : {{ Θ0 ⨟ empty ⊢ₚₛ ⌊ R00 ⌋ˢ }}a)
      by (inversion HwfP; subst; rewrite <- (aenv_minus_empty Θ0);
          assumption).

    assert (Hgf0 : a_sub_mode_sk = a_sub_mode_ty -> uskl_ghost_free Rg)
      by (intro Habs; discriminate Habs).
    destruct (IHsub Hfuel Θ0 PIH He1 He2 He3 P0 (⌊ R00 ⌋ˢ) R00 κ
                (He2 R00 HPIH)
                Hwf0 Hwfth HwfP0 HwfP' Hmodsk Hmodty eq_refl Hinc Hslack0
                Hsub Hrs HwfQ Hgf0)
      as [P1 [Θ1 [Hrun Hopt]]].
    exists P1, Θ1. split;
      [ apply a_sub__univ_ghost_l; eassumption | exact Hopt ].
  -
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    assert (Hslack' : {{ Θa ⊢ (ptyp_to_uskl_syn τd) ≡ᵘ (msubst_uskl_syn κ R) }}a).
    { eapply a_uskl_tyequiv_trans;
        [ apply flex_def_paint_tyequiv; eassumption
        | exact Hslack ]. }

    assert (Hgfd : NM0 = a_sub_mode_ty ->
              uskl_ghost_free (ptyp_to_uskl_syn τd))
      by (intros _; apply mono_ptyp_to_uskl_syn_ghost_free;
          eapply a_wf_aenv_binds_def_mono; eassumption).
    exact (IHsub Hfuel Θ0 PIH He1 He2 He3 P0 P R κ HPIH
             Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack'
             Hsub Hrs HwfQ Hgfd).
Qed.

Lemma sub_complete_arrow_holds : forall n,
  (forall n', n' < n -> sub_complete n') ->
  sub_complete_arrow n.
Proof.
  intros n Hfuel NM M Θ0 P0 P Ra Rb R' Ψ Θ κ Q.
  intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
         Hgf.
  exact (@sub_complete_assemble n NM M Ψ Θ R' Q HDj Hfuel Θ0
           (fun R0 => exists Rx Ry, R0 = uskl_arrow Rx Ry)
           ltac:(intros R0 [Rx [Ry HH]]; discriminate HH)
           ltac:(intros R0 [Rx [Ry HH]]; discriminate HH)
           ltac:(intros γ [Rx [Ry HH]]; discriminate HH)
           P0 P (uskl_arrow Ra Rb) κ
           (ex_intro _ Ra (ex_intro _ Rb eq_refl))
           Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf).
Qed.

Theorem a_sub_complete_bundle_holds : a_sub_complete_bundle.
Proof.
  intros n.
  induction n as [n IHfuel] using lt_wf_ind.
  assert (Hfuel : forall n', n' < n -> sub_complete n')
    by (intros n' Hn'; exact (proj1 (IHfuel n' Hn'))).
  assert (Harrow : sub_complete_arrow n)
    by (apply sub_complete_arrow_holds; exact Hfuel).

  assert (Hbelow : forall k, sub_complete_ctx_lt n k).
  { intro k. induction k as [k IHk] using lt_wf_ind.
    intros NM M Θ0 P0 P R R' Ψ Θ κ Q Hlen.
    intros Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs HwfQ
           Hgf.
    refine (@sub_complete_assemble n NM M Ψ Θ R' Q HDj Hfuel Θ0
              (fun _ => True) _ _ _ P0 P R κ I
              Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty HeqR Hinc Hslack HDj Hrs
              HwfQ Hgf);
      [ intros; exact I | intros; exact I | ].
    intros γ _ NM' M' α' P0' R'' Ψ' Θ' κ' Q'.
    apply (@sub_flex_complete_holds n (length Θ0) Harrow
             (IHk (length Θ0) Hlen) NM' M' Θ0 nil α' P0' R'' Ψ' Θ' κ' Q').
    simpl. lia. }
  split.
  - intros NM M Θ0 P0 P R R' Ψ Θ κ Q.
    apply (Hbelow (S (length Θ0)) NM M Θ0 P0 P R R' Ψ Θ κ Q). lia.
  - intros NM M Θ0 Ξ α P0 R' Ψ Θ κ Q.
    apply (@sub_flex_complete_holds n (length Ξ + length Θ0) Harrow
             (Hbelow (length Ξ + length Θ0))
             NM M Θ0 Ξ α P0 R' Ψ Θ κ Q). lia.
Qed.

Theorem a_sub_complete :
  forall n NM M Θ0 P0 P R' Θ κ Q,
    {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
    (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
    (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
    κ ∷ Θ0 ⊑ Θ ->
    {{ Θ ⊢ R' ≡ᵘ (msubst_uskl_syn κ (pskl_to_uskl P)) }}a ->
    ad_pat_sub_fuel n NM M empty Θ R' Q ->
    {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
    {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
    (NM = a_sub_mode_ty -> uskl_ghost_free R') ->
    exists P1 Θ1,
      a_sub NM M P0 Θ0 P P1 Θ1 /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           {{ Θ ⨟ empty ⊢ₚᵣ
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Q) }}ad).
Proof.
  intros n NM M Θ0 P0 P R' Θ κ Q
    Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty Hinc Hslack HDj Hrs HwfQ Hgf.
  exact (proj1 (a_sub_complete_bundle_holds n)
           NM M Θ0 P0 P (pskl_to_uskl P) R' empty Θ κ Q
           Hwf0 Hwfth HwfP0 HwfP Hmodsk Hmodty
           (uskl_to_pskl_pskl_to_uskl P) Hinc Hslack HDj
           Hrs HwfQ Hgf).
Qed.
