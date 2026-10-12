Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_mod_compat.
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
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_consis_rename.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_gen.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.basic.prop_wf_preservation.
Require Import src.fresco.deco_algo.prop_soundness_sub.

Set Implicit Arguments.

Open Scope fresco_a_scope.

Reserved Notation "{{ Θ ⊢ᵉ e }}a"
  (at level 0, e at level 74, format "'{{'  Θ  ⊢ᵉ  e  '}}a'").

Inductive a_wf_exp : aenv -> exp -> Prop :=
| a_wf_exp__unit : forall Θ,
    {{ Θ ⊢ᵉ exp_unit }}a
| a_wf_exp__var : forall Θ x,
    {{ Θ ⊢ᵉ (exp_var_f x) }}a
| a_wf_exp__anno : forall Θ e A,
    a_wf_ptyp Θ A ->
    {{ Θ ⊢ᵉ e }}a ->
    {{ Θ ⊢ᵉ (exp_anno e A) }}a
| a_wf_exp__freeze : forall Θ e,
    {{ Θ ⊢ᵉ e }}a ->
    {{ Θ ⊢ᵉ (exp_freeze e) }}a
| a_wf_exp__abs : forall L Θ e,
    (forall x, x `notin` L ->
       {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a) ->
    {{ Θ ⊢ᵉ (exp_abs e) }}a
| a_wf_exp__abs_anno : forall L Θ A e,
    a_wf_ptyp Θ A ->
    (forall x, x `notin` L ->
       {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a) ->
    {{ Θ ⊢ᵉ (exp_abs_anno A e) }}a
| a_wf_exp__app : forall Θ e1 e2,
    {{ Θ ⊢ᵉ e1 }}a ->
    {{ Θ ⊢ᵉ e2 }}a ->
    {{ Θ ⊢ᵉ (exp_app e1 e2) }}a
where "{{ Θ ⊢ᵉ e }}a" := (a_wf_exp Θ e) : fresco_a_scope.

Lemma a_wf_exp_transport : forall (R : aenv -> aenv -> Prop),
  (forall Θ Θ' A, R Θ Θ' -> a_wf_ptyp Θ A -> a_wf_ptyp Θ' A) ->
  forall Θ e, {{ Θ ⊢ᵉ e }}a -> forall Θ', R Θ Θ' -> {{ Θ' ⊢ᵉ e }}a.
Proof.
  intros R HR Θ e H; induction H; intros Θ' Hle.
  - apply a_wf_exp__unit.
  - apply a_wf_exp__var.
  - apply a_wf_exp__anno; eauto.
  - apply a_wf_exp__freeze; auto.
  - apply a_wf_exp__abs with (L := L). intros x Hx. eauto.
  - apply a_wf_exp__abs_anno with (L := L); eauto.
  - apply a_wf_exp__app; eauto.
Qed.

Lemma a_wf_exp_mono : forall Θ e,
  {{ Θ ⊢ᵉ e }}a ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Θ' ⊢ᵉ e }}a.
Proof. apply a_wf_exp_transport. intros; eapply a_wf_ptyp_mono; eauto. Qed.

Lemma a_wf_exp_isub : forall Θ e,
  {{ Θ ⊢ᵉ e }}a ->
  forall Θ', Θ ⊴ Θ' -> {{ Θ' ⊢ᵉ e }}a.
Proof. apply a_wf_exp_transport. intros; eapply a_wf_ptyp_isub; eauto. Qed.

Lemma abind_to_pskl_is_tm : forall (b : abind) P,
  abind_to_pskl b = Some P -> abind_is_tm b.
Proof. intros [] P H; simpl in *; congruence || exact I. Qed.

Lemma ad_pat_isub_tm : forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall Θ', Θ ⊴ Θ' -> aenv_tm_le Θ Θ' ->
  {{ Θ' ⊢ˢ[ M ] e ⦂ Q }}ad.
Proof.
  intros M Θ e Q H; induction H; intros Θ' Hle Htm.
  -
    apply ad_pat__unit;
      [ eapply a_wf_pskl_isub; eauto | eapply ad_pat_sub_isub; eauto ].
  -
    eapply ad_pat__var;
      [ apply Htm; [ eapply abind_to_pskl_is_tm; eauto | exact H ]
      | eassumption
      | eapply a_wf_pskl_isub; eauto
      | eapply ad_pat_sub_isub; eauto ].
  -
    apply ad_pat__anno;
      [ eapply a_wf_pskl_isub; eauto | eapply ad_pat_sub_isub; eauto ].
  -  apply ad_pat__freeze; auto.
  -
    apply ad_pat__abs with (L := L);
      [ assumption | eapply a_wf_pskl_isub; eauto | assumption | ].
    intros x Hx. apply H3;
      [ exact Hx
      | apply a_isub_cons_var_skl;
          [ exact Hle | eapply a_wf_pskl_lc; eauto ]
      | apply aenv_tm_le_cons; exact Htm ].
  -
    eapply ad_pat__abs_anno with (L := L);
      [ assumption | eapply a_wf_ptyp_isub; eauto | eassumption
      | assumption | ].
    intros x Hx. apply H4;
      [ exact Hx
      | apply a_isub_cons_var_typ;
          [ exact Hle | eapply a_wf_ptyp_lc; eauto ]
      | apply aenv_tm_le_cons; exact Htm ].
  -
    eapply ad_pat__app;
      [ auto | eapply ad_refine_syn_isub; eauto | auto ].
  -
    apply ad_pat__abs_check with (L := L). intros x Hx.
    apply H0;
      [ exact Hx
      | apply a_isub_cons_var_skl; [ exact Hle | apply lc_pskl_ghost ]
      | apply aenv_tm_le_cons; exact Htm ].
  -
    apply ad_pat__abs_anno_check with (L := L);
      [ eapply a_wf_ptyp_isub; eauto | ].
    intros x Hx. apply H1;
      [ exact Hx
      | apply a_isub_cons_var_typ;
          [ exact Hle | eapply a_wf_ptyp_lc; eauto ]
      | apply aenv_tm_le_cons; exact Htm ].
Qed.

Lemma binds_tm_cons_inv' : forall x (b : abind) y (c : abind) Θ,
  abind_is_tm b -> binds x b ((y ~ c) ++ Θ) -> ~ abind_is_tm c -> binds x b Θ.
Proof. intros; eapply binds_tm_cons_inv; eauto. Qed.

Lemma aenv_tm_le_mid_intro : forall Ξ (mid : aenv) Θ,
  aenv_tm_le (Ξ ++ Θ) (Ξ ++ mid ++ Θ).
Proof. intros Ξ mid Θ y b _ H. apply binds_weaken; exact H. Qed.

Lemma aenv_tm_le_src_strip_suffix : forall Ξs Θ Θ',
  a_suffix Ξs ->
  aenv_tm_le Θ Θ' -> aenv_tm_le (Ξs ++ Θ) Θ'.
Proof.
  intros * Hsuf Hle y b Htm Hb.
  apply Hle; [ exact Htm | eapply binds_tm_strip_suffix; eauto ].
Qed.

Lemma aenv_tm_le_cons_mid : forall (x : atom) (c : abind) Ξ Θ Θ0,
  aenv_tm_le Θ (Ξ ++ Θ0) ->
  aenv_tm_le ((x ~ c) ++ Θ) (Ξ ++ (x ~ c) ++ Θ0).
Proof.
  intros * Hle y b Htm Hb.
  apply binds_app_1 in Hb as [Hb | Hb].
  - apply binds_app_3; apply binds_app_2; exact Hb.
  - specialize (Hle y b Htm Hb).
    apply binds_app_1 in Hle as [Hle | Hle];
      [ apply binds_app_2; exact Hle
      | apply binds_app_3; apply binds_app_3; exact Hle ].
Qed.

Lemma a_assign_unify_consis_tm_ge :
  (forall Θ0 Ξ α P Θ1, {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> aenv_tm_le Θ1 (Ξ ++ Θ0)) /\
  (forall Θ0 α β Θ1, {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> aenv_tm_le Θ1 Θ0) /\
  (forall Δ1 Δ2 Θ0 P0 P Q Θ1,
     a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 -> aenv_tm_le Θ1 Θ0).
Proof.
  apply a_assign_unify_consis_mutind.

  -  intros; apply aenv_tm_le_refl.
  -
    intros Θ0 Ξ α P βs τ Hαn Hg Hm Hu Hfr.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    apply aenv_tm_le_src_strip_suffix;
      [ apply a_decls_suffix; eapply a_guess_mono_decls; eauto | ].
    apply aenv_tm_le_mid_intro.
  -
    intros Θ0 Θ1 Ξ α β τ P Q Hflex Hβ Hc IH.
    apply aenv_tm_le_cons_mid; exact IH.
  -
    intros Θ0 Θ1 Ξ α β P Hne Hβ Ha IH.
    simpl_env in IH; exact IH.
  -  intros; apply aenv_tm_le_cons_mid; assumption.
  -  intros; apply aenv_tm_le_cons_mid; assumption.
  -  intros; apply aenv_tm_le_cons_mid; assumption.
  -  intros; apply aenv_tm_le_cons_mid; assumption.

  -  intros; apply aenv_tm_le_refl.
  -
    intros Θ0 α β Hne Hβ.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    apply aenv_tm_le_weaken_r; apply aenv_tm_le_refl.
  -
    intros Θ0 α β Hne Hα.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    apply aenv_tm_le_weaken_r; apply aenv_tm_le_refl.
  -
    intros Θ0 Θ1 α1 τ α β Q Hfα Hfβ Hα1 Hc IH.
    apply aenv_tm_le_cons; exact IH.
  -  intros; apply aenv_tm_le_cons; assumption.
  -  intros; apply aenv_tm_le_cons; assumption.

  -  intros; apply aenv_tm_le_refl.
  -  intros; apply aenv_tm_le_refl.
  -  intros; apply aenv_tm_le_refl.
  -
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2.
    eapply aenv_tm_le_trans; [ exact IH2 | exact IH1 ].
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar);
      [ intros [] | exact IH ].
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar);
      [ intros [] | exact IH ].
  -  intros; assumption.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar);
      [ intros [] | exact IH ].
  -  intros; assumption.
  -  intros; assumption.
  -  intros; assumption.
  -  intros; assumption.
  -  intros; apply aenv_tm_le_refl.
  -  intros; assumption.
Qed.

Lemma a_consis_tm_ge : forall Δ1 Δ2 Θ0 P0 P Q Θ1,
  a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 -> aenv_tm_le Θ1 Θ0.
Proof. intros; eapply (proj2 (proj2 a_assign_unify_consis_tm_ge)); eauto. Qed.

Lemma a_consis_chk_tm_ge : forall Θ0 P P0 Θ1,
  a_consis_chk Θ0 P P0 Θ1 -> aenv_tm_le Θ1 Θ0.
Proof. intros * [Q Hc]; eapply a_consis_tm_ge; eauto. Qed.

Lemma a_sub_sub_flex_tm_ge :
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 -> aenv_tm_le Θ1 Θ0) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 -> aenv_tm_le Θ1 (Ξ ++ Θ0)).
Proof.
  apply a_sub_sub_flex_tm_mutind.

  -  intros; apply aenv_tm_le_refl.
  -
    intros Θ0 Θ1 A B Hgf1 Hgf2 Hg1 Hg2 Hchk.
    eapply a_consis_chk_tm_ge; exact Hchk.
  -
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huniq Hnotin Hrun IH.
    intros y b Htm Hb.
    assert (Hb1 : binds y b (Ξ ++ (α ~ abind_tvar) ++ Θ1))
      by (apply binds_app_3; apply binds_app_3; exact Hb).
    assert (Hb2 : binds y b ((α ~ abind_tvar) ++ Θ0))
      by (apply IH; [ exact Htm | exact Hb1 ]).
    eapply binds_tm_cons_inv'; [ exact Htm | exact Hb2 | intros [] ].
  -  intros; apply aenv_tm_le_refl.
  -  intros; assumption.
  -
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IH.
    eapply aenv_tm_le_trans; [ exact IH | eapply a_consis_tm_ge; exact Hc ].
  -
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hm Hg Hα Hext Huniq Hwf Hs IH.
    eapply aenv_tm_le_strip_suffix_tgt;
      [ apply a_decls_suffix; eapply a_extract_decls; eauto | exact IH ].
  -  intros; apply aenv_tm_le_refl.
  -  intros; assumption.

  -
    intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hα Hβ Hs IH.
    intros y b Htm Hb.
    specialize (IH y b Htm Hb).
    apply binds_app_1 in IH as [IH | IH];
      [ apply binds_app_2; exact IH | ].
    assert (IH1 : binds y b ((β ~ abind_flex_mono)
                              ++ (α ~ abind_flex_mono) ++ Θ0))
      by (eapply binds_tm_cons_inv'; [ exact Htm | exact IH | intros [] ]).
    assert (IH2 : binds y b ((α ~ abind_flex_mono) ++ Θ0))
      by (eapply binds_tm_cons_inv'; [ exact Htm | exact IH1 | intros [] ]).
    assert (IH3 : binds y b Θ0)
      by (eapply binds_tm_cons_inv'; [ exact Htm | exact IH2 | intros [] ]).
    apply binds_app_3; apply binds_app_3; exact IH3.
  -
    intros NM M P0 Θ0 Θ1 Ξ α β τ Q Hβ Hs IH.
    apply aenv_tm_le_cons_mid; exact IH.
  -
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hβ Hs IH.
    simpl_env in IH; exact IH.
  -  intros; apply aenv_tm_le_cons_mid; assumption.
  -  intros; apply aenv_tm_le_cons_mid; assumption.
  -  intros; apply aenv_tm_le_cons_mid; assumption.
  -  intros; apply aenv_tm_le_cons_mid; assumption.
Qed.

Lemma a_sub_tm_ge : forall NM M P0 Θ0 P Q Θ1,
  a_sub NM M P0 Θ0 P Q Θ1 -> aenv_tm_le Θ1 Θ0.
Proof. intros; eapply (proj1 a_sub_sub_flex_tm_ge); eauto. Qed.

Lemma a_split_tm_ge : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a -> aenv_tm_le Θ1 Θ0.
Proof.
  intros * H; inversion H; subst; try apply aenv_tm_le_refl.
  match goal with
  | Hc : a_consis _ _ _ _ _ _ _ |- _ => apply a_consis_tm_ge in Hc
  end.
  eapply aenv_tm_le_strip_cons_tgt with (c := abind_flex_mono);
    [ intros [] | ].
  eapply aenv_tm_le_strip_cons_tgt with (c := abind_flex_mono);
    [ intros [] | ].
  eassumption.
Qed.

Lemma aenv_tm_le_via_binder_ge : forall Ξ x (bx : abind) Θ Θ',
  aenv_tm_le (Ξ ++ (x ~ bx) ++ Θ') ((x ~ bx) ++ Θ) ->
  forall y b, abind_is_tm b -> y <> x -> binds y b (Ξ ++ Θ') -> binds y b Θ.
Proof.
  intros * Hle y b Htm Hne Hb.
  assert (Hb1 : binds y b ((x ~ bx) ++ Θ))
    by (apply Hle; [ exact Htm | apply binds_weaken; exact Hb ]).
  destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[Heq _] | Hb2];
    [ subst; contradiction | exact Hb2 ].
Qed.

Lemma a_pat_tm_ge : forall m Θ0 P0 e P Θ1,
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ P ⊣ Θ1 }}a -> aenv_tm_le Θ1 Θ0.
Proof.
  intros m Θ0 P0 e P Θ1 H; induction H.
  -  eapply a_sub_tm_ge; eassumption.
  -  eapply a_sub_tm_ge; eassumption.
  -  eapply a_sub_tm_ge; eassumption.
  -  eapply a_sub_tm_ge; eassumption.
  -  assumption.
  -
    intros y b Htm Hb.
    apply a_split_tm_ge in H0.
    apply H0; [ exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ exact IHa_pat | exact Htm
      | intros Heq; subst; apply binds_In in Hb; clear - H2 Hb;
        simpl_env in *; fsetdec
      | exact Hb ].
  -
    intros y b Htm Hb.
    apply a_split_tm_ge in H0.
    apply a_consis_chk_tm_ge in H1.
    apply H0; [ exact Htm | ]. apply H1; [ exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ exact IHa_pat | exact Htm
      | intros Heq; subst; apply binds_In in Hb; clear - H3 Hb;
        simpl_env in *; fsetdec
      | exact Hb ].
  -
    intros y b Htm Hb.
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ exact IHa_pat | exact Htm
      | intros Heq; subst; apply binds_In in Hb; clear - H0 Hb;
        simpl_env in *; fsetdec
      | exact Hb ].
  -
    intros y b Htm Hb.
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ exact IHa_pat | exact Htm
      | intros Heq; subst; apply binds_In in Hb; clear - H0 Hb;
        simpl_env in *; fsetdec
      | exact Hb ].
  -
    eapply aenv_tm_le_trans; [ exact IHa_pat2 | exact IHa_pat1 ].
Qed.

Lemma pskl_to_uskl_via_bskl_syn : forall P,
  bskl_to_uskl (pskl_to_bskl_syn P) = pskl_to_uskl P.
Proof. induction P; simpl; congruence. Qed.

Lemma a_split_sk_shape : forall m Θ0 P0 P Q0 Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}a ->
  a_sk_mode_compat m P0 ->
  Θ1 = Θ0 /\
  ((P0 = pskl_ghost /\ P = pskl_ghost /\ Q0 = pskl_ghost) \/
   P0 = pskl_arrow P Q0).
Proof.
  intros * Hs Hm; inversion Hs; subst.
  - split; [ reflexivity | right; reflexivity ].
  - split; [ reflexivity | left; auto ].
  - inversion Hm.
Qed.

Lemma a_split_sk_pieces : forall m Θ0 P0 P Q0 Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}a ->
  a_sk_mode_compat m P0 ->
  m <> mode_tc ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  ({{ Θ0 ⨟ empty ⊢ₚₛ P }}a) /\ ({{ Θ0 ⨟ empty ⊢ₚₛ Q0 }}a) /\
  a_sk_mode_compat (decr_mode m) Q0.
Proof.
  intros m Θ0 P0 P Q0 Θ1 Hs Hmod Hne HwfP0.
  destruct (a_split_sk_shape Hs Hmod) as [_ [[HP0 [HP HQ0]] | HP0]]; subst.
  - repeat split; try apply a_wf_pskl__ghost.
    destruct (a_sk_mode_compat_ghost_inv Hmod) as [Hm | Hm]; subst m;
      [ apply a_sk_mode_compat__ti | congruence ].
  - inversion HwfP0; subst.
    destruct (a_sk_mode_compat_arrow_inv Hmod) as [m' [Hm Hm']]; subst m.
    repeat split; assumption.
Qed.

Lemma a_split_ty_shape : forall m Θ0 P0 P Q0 Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}a ->
  a_ty_mode_compat m P0 ->
  m <> mode_tc ->
  Θ1 = Θ0 /\
  ((P0 = pskl_ghost /\ P = pskl_ghost /\ Q0 = pskl_ghost) \/
   P0 = pskl_arrow P Q0).
Proof.
  intros * Hs Hm Hne; inversion Hs; subst.
  - split; [ reflexivity | right; reflexivity ].
  - split; [ reflexivity | left; auto ].
  - exfalso.
    match goal with
    | |- False =>
        remember (pskl_var_f α) as Ps eqn:HPs;
        destruct Hm; [ discriminate | apply Hne; reflexivity | discriminate ]
    end.
Qed.

Lemma a_split_ty_pieces : forall m Θ0 P0 P Q0 Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}a ->
  a_ty_mode_compat m P0 ->
  m <> mode_tc ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  ({{ Θ0 ⨟ empty ⊢ₚₛ P }}a) /\ ({{ Θ0 ⨟ empty ⊢ₚₛ Q0 }}a) /\
  a_ty_mode_compat (decr_mode m) Q0.
Proof.
  intros m Θ0 P0 P Q0 Θ1 Hs Hmod Hne HwfP0.
  destruct (a_split_ty_shape Hs Hmod Hne) as [_ [[HP0 [HP HQ]] | HP0]]; subst.
  - repeat split; try apply a_wf_pskl__ghost.
    rewrite (a_ty_mode_compat_ghost_inv Hmod). apply a_ty_mode_compat__ti.
  - inversion HwfP0; subst.
    destruct (a_ty_mode_compat_arrow_inv Hmod Hne) as [m' [Hm Hm']];
      subst m. repeat split; assumption.
Qed.

Lemma ad_pat_sub_mod_comp_sk : forall M Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] R ⩽ Q }}ad ->
  mod_comp_sk Q M.
Proof.
  intros M Ψ Θ R Q H.
  remember a_sub_mode_sk as NM eqn:HNM.
  induction H; subst; try discriminate.
  -  apply mod_comp_sk__ti; assumption.
  -
    apply mod_comp_sk__tc. apply is_sskl__univ_ghost; assumption.
  -  apply mod_comp_sk__fn; auto.
  -  auto.
  -  auto.
  -  assumption.
  -  assumption.
  -  auto.
  -  auto.
  -  auto.
Qed.

Lemma abind_is_tm_not_ty : forall b : abind,
  abind_is_tm b -> ~ abind_is_ty b.
Proof. intros [] Htm; simpl in *; auto. Qed.

Lemma aenv_tbinds_le_rename_tm : forall Θa x y (b : abind) Θ0,
  ~ abind_is_ty b ->
  aenv_tbinds_le (Θa ++ (x ~ b) ++ Θ0) (Θa ++ (y ~ b) ++ Θ0).
Proof.
  intros * Hb α c Hc H.
  apply binds_weaken.
  eapply aenv_tbinds_le_strip_tm; eauto.
Qed.

Lemma ad_pat_subst_tm : forall M Θ' e Q,
  {{ Θ' ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall Θa x (b : abind) Θ0 y,
  Θ' = Θa ++ (x ~ b) ++ Θ0 ->
  abind_is_tm b ->
  x `notin` dom Θa `union` dom Θ0 ->
  {{ (Θa ++ (y ~ b) ++ Θ0) ⊢ˢ[ M ] (subst_exp_in_exp (exp_var_f y) x e) ⦂ Q }}ad.
Proof.
  intros M Θ' e Q H; induction H;
    intros Θa x0 b0 Θb y Heq Htm Hx0; subst; simpl;
  assert (Hren : aenv_tbinds_le (Θa ++ (x0 ~ b0) ++ Θb) (Θa ++ (y ~ b0) ++ Θb))
    by (apply aenv_tbinds_le_rename_tm; apply abind_is_tm_not_ty; exact Htm).
  -
    apply ad_pat__unit;
      [ eapply a_wf_pskl_mono;
          [ eassumption | exact Hren ]
      | eapply ad_pat_sub_mono;
          [ eassumption | exact Hren ] ].
  -
    destruct_if as [Heq | Hne].
    +
      subst x.
      assert (Hb0 : b = b0).
      { apply binds_app_1 in H as [H | H];
          [ exfalso; apply binds_In in H; clear - H Hx0; fsetdec | ].
        apply binds_app_1 in H as [H | H];
          [ | exfalso; apply binds_In in H; clear - H Hx0; fsetdec ].
        destruct H as [Hp | []]. inversion Hp; reflexivity. }
      subst b.
      eapply ad_pat__var with (b := b0);
        [ apply binds_app_3; unfold binds; simpl; left; reflexivity
        | eassumption
        | eapply a_wf_pskl_mono;
            [ eassumption | exact Hren ]
        | eapply ad_pat_sub_mono;
            [ eassumption | exact Hren ] ].
    +
      eapply ad_pat__var with (b := b);
        [ | eassumption
        | eapply a_wf_pskl_mono;
            [ eassumption | exact Hren ]
        | eapply ad_pat_sub_mono;
            [ eassumption | exact Hren ] ].
      apply binds_app_1 in H as [H | H];
        [ apply binds_app_2; exact H | ].
      apply binds_app_1 in H as [H | H];
        [ destruct H as [Hp | []]; inversion Hp; subst; exfalso; auto | ].
      apply binds_app_3; unfold binds; simpl; right; exact H.
  -
    apply ad_pat__anno;
      [ eapply a_wf_pskl_mono;
          [ eassumption | exact Hren ]
      | eapply ad_pat_sub_mono;
          [ eassumption | exact Hren ] ].
  -
    apply ad_pat__freeze. apply IHad_pat; auto.
  -
    apply ad_pat__abs with (L := L `union` singleton x0 `union` singleton y);
      [ assumption
      | eapply a_wf_pskl_mono;
          [ eassumption | exact Hren ]
      | assumption | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H3 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_skl P) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | ].
    simpl. clear - Hx0 Hz. fsetdec.
  -
    apply ad_pat__abs_anno
      with (L := L `union` singleton x0 `union` singleton y) (B := B);
      [ assumption
      | eapply a_wf_ptyp_mono;
          [ eassumption | exact Hren ]
      | reflexivity | assumption | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H4 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_typ (btyp_to_ptyp B)) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | ].
    simpl. clear - Hx0 Hz. fsetdec.
  -
    eapply ad_pat__app;
      [ apply IHad_pat1; auto
      | eapply ad_refine_syn_mono;
          [ eassumption | exact Hren ]
      | apply IHad_pat2; auto ].
  -
    apply ad_pat__abs_check
      with (L := L `union` singleton x0 `union` singleton y).
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H0 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_skl pskl_ghost) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | ].
    simpl. clear - Hx0 Hz. fsetdec.
  -
    apply ad_pat__abs_anno_check
      with (L := L `union` singleton x0 `union` singleton y);
      [ eapply a_wf_ptyp_mono;
          [ eassumption | exact Hren ] | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H1 z ltac:(clear - Hz; solve_notin_auto)
             ((z ~ abind_var_typ A) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | ].
    simpl. clear - Hx0 Hz. fsetdec.
Qed.

Lemma a_wf_aenv_binds_var_typ_wf : forall Θ x A,
  {{ ⊢ Θ }}a ->
  binds x (abind_var_typ A) Θ ->
  a_wf_ptyp Θ A.
Proof.
  intros Θ x A Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
    try discriminate;
    try (eapply a_wf_ptyp_weaken;
         [ intros y b Hby; unfold binds; right; exact Hby | ];
         first [ apply IHHwf; exact Hb'
               | inversion Heqb; subst; assumption ]).
Qed.

Lemma a_wf_aenv_strip_tm_mid : forall Ξ x (b : abind) Θ,
  ~ abind_is_ty b ->
  {{ ⊢ (Ξ ++ (x ~ b) ++ Θ) }}a ->
  {{ ⊢ (Ξ ++ Θ) }}a.
Proof.
  intros Ξ; induction Ξ as [ | [y c] Ξ' IH ]; intros x b Θ Hb Hwf.
  - rewrite app_nil_l in *. inversion Hwf; subst; assumption.
  - assert (Htail : {{ ⊢ (Ξ' ++ (x ~ b) ++ Θ) }}a)
      by (inversion Hwf; subst; assumption).
    assert (Hrest : {{ ⊢ (Ξ' ++ Θ) }}a) by (apply (IH x b Θ Hb Htail)).
    assert (Hy : y `notin` dom (Ξ' ++ Θ)).
    { assert (Hy0 : y `notin` dom (Ξ' ++ (x ~ b) ++ Θ))
        by (inversion Hwf; subst; assumption).
      simpl_env in Hy0. simpl_env. clear - Hy0. fsetdec. }
    assert (Hle : aenv_tbinds_le (Ξ' ++ (x ~ b) ++ Θ) (Ξ' ++ Θ))
      by (apply aenv_tbinds_le_strip_tm; exact Hb).
    inversion Hwf; subst.
    + apply a_wf_aenv__flex; assumption.
    + apply a_wf_aenv__flex_def; try assumption.
      eapply a_wf_ptyp_mono; eassumption.
    + apply a_wf_aenv__var; try assumption.
      eapply a_wf_pskl_mono; eassumption.
    + apply a_wf_aenv__var_typ; try assumption.
      eapply a_wf_ptyp_mono; eassumption.
    + apply a_wf_aenv__tvar; assumption.
Qed.

Lemma uniq_mid_eq : forall (Ξ1 : aenv) x (b1 : abind) Θ1 Ξ2 (b2 : abind) Θ2,
  Ξ1 ++ (x ~ b1) ++ Θ1 = Ξ2 ++ (x ~ b2) ++ Θ2 ->
  uniq (Ξ1 ++ (x ~ b1) ++ Θ1) ->
  Ξ1 = Ξ2 /\ b1 = b2 /\ Θ1 = Θ2.
Proof.
  intros Ξ1; induction Ξ1 as [ | [y c] Ξ1' IH ];
    intros x b1 Θ1 Ξ2 b2 Θ2 Heq Hu.
  - destruct Ξ2 as [ | [z d] Ξ2' ].
    + inversion Heq; subst; auto.
    +
      exfalso.
      assert (Hnot : x `notin` dom Θ1)
        by (inversion Hu; subst; assumption).
      assert (HeqΘ : Θ1 = Ξ2' ++ (x ~ b2) ++ Θ2)
        by (inversion Heq; subst; first [ reflexivity | assumption ]).
      rewrite HeqΘ in Hnot. simpl_env in Hnot. clear - Hnot. fsetdec.
  - destruct Ξ2 as [ | [z d] Ξ2' ].
    + exfalso.
      assert (Hnot : y `notin` dom (Ξ1' ++ (x ~ b1) ++ Θ1))
        by (inversion Hu; subst; assumption).
      assert (Hyx : y = x) by (inversion Heq; reflexivity).
      rewrite Hyx in Hnot. simpl_env in Hnot. clear - Hnot. fsetdec.
    + assert (Hu' : uniq (Ξ1' ++ (x ~ b1) ++ Θ1))
        by (inversion Hu; subst; assumption).
      assert (Heq' : Ξ1' ++ (x ~ b1) ++ Θ1 = Ξ2' ++ (x ~ b2) ++ Θ2)
        by (inversion Heq; subst; first [ reflexivity | assumption ]).
      assert (Hyz : y = z) by (inversion Heq; reflexivity).
      assert (Hcd : c = d) by (inversion Heq; reflexivity).
      destruct (IH _ _ _ _ _ _ Heq' Hu') as [HΞ [Hb HΘ]]; subst.
      auto.
Qed.

Lemma a_isub_strip_var_typ_mid : forall x A Ξ Θ0 Θ1,
  uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ1) ->
  uniq (Ξ ++ Θ0) ->
  ((x ~ abind_var_typ A) ++ Θ0) ⊴ (Ξ ++ (x ~ abind_var_typ A) ++ Θ1) ->
  Θ0 ⊴ Θ1.
Proof.
  intros x A Ξ Θ0 Θ1 Huq HuqΞ [[κ [Hid Hinc]] Hdef].
  destruct (a_inc_var_inv Hinc) as [Ξ0 [A' [Θ2 [Heq [_ [_ Hinc']]]]]].
  destruct (@uniq_mid_eq _ _ _ _ _ _ _ Heq Huq) as [-> [Heqb ->]]. inversion Heqb; subst.
  split.
  - exists κ. split; [ exact Hid | exact Hinc' ].
  - intros β τ Hb.
    assert (HβΘ0 : β `in` dom Θ0) by (eapply binds_In; eauto).
    assert (Hbw : binds β (abind_flex_mono_def τ)
                    (Ξ0 ++ (x ~ abind_var_typ A') ++ Θ2))
      by (apply Hdef; unfold binds; simpl; right;
          unfold binds in Hb; exact Hb).
    unfold binds in Hbw. apply in_app_or in Hbw.
    destruct Hbw as [Hbw | Hbw].
    { exfalso.
      assert (HβΞ : β `in` dom Ξ0) by (eapply binds_In; exact Hbw).
      clear - HuqΞ HβΘ0 HβΞ.
      destruct_uniq. unfold disjoint in *. fsetdec. }
    simpl in Hbw. destruct Hbw as [Heqp | Hbw].
    { exfalso. inversion Heqp. }
    exact Hbw.
Qed.

Arguments uniq_mid_eq {Ξ1 x b1 Θ1 Ξ2 b2 Θ2} _ _.

Lemma a_inc_weaken_suffix_target : forall Θ κ Θ' Ξ,
  κ ∷ Θ ⊑ Θ' ->
  is_id_msubst κ ->
  lc_aenv Θ' ->
  a_suffix Ξ ->
  exists κ', is_id_msubst κ' /\ κ' ∷ Θ ⊑ (Ξ ++ Θ').
Proof.
  intros * Hinc Hid Hlc HΞ.
  destruct (a_inc_refl_gen (Ξ0 := Ξ) Hlc HΞ) as [κ2 [Hid2 Hinc2]].
  eapply a_inc_trans; eassumption.
Qed.

Lemma a_isub_peel_tm_mid : forall x b Θ1 Ξ Θ2,
  abind_is_tm b ->
  a_suffix Ξ ->
  uniq (Ξ ++ (x ~ b) ++ Θ2) ->
  lc_aenv Θ2 ->
  ((x ~ b) ++ Θ1) ⊴ (Ξ ++ (x ~ b) ++ Θ2) ->
  Θ1 ⊴ (Ξ ++ Θ2).
Proof.
  intros x b Θ1 Ξ Θ2 Htm HΞ Hu Hlc [[κ [Hid Hinc]] Hd].
  assert (Hinc' : exists κ', κ' ∷ Θ1 ⊑ Θ2 /\ is_id_msubst κ').
  { destruct b; try contradiction Htm;
      [ destruct (a_inc_var_inv Hinc) as [Ξ0 [b' [Θ0 [Heq [_ [_ Hinc']]]]]]
      | destruct (a_inc_var_skl_inv Hinc) as [Ξ0 [b' [Θ0 [Heq [_ [_ Hinc']]]]]] ];
      destruct (uniq_mid_eq Heq Hu) as [-> [_ ->]]; eauto. }
  destruct Hinc' as [κ' [Hinc' Hid']].
  split.
  - eapply a_inc_weaken_suffix_target; eassumption.
  - intros α τ Hb.
    assert (Hb1 : binds α (abind_flex_mono_def τ) (Ξ ++ (x ~ b) ++ Θ2))
      by (apply Hd; apply binds_app_3; exact Hb).
    apply binds_app_1 in Hb1 as [Hb1 | Hb1];
      [ apply binds_app_2; exact Hb1 | ].
    apply binds_app_3.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[_ Heqd] | Hb2];
      [ subst b; contradiction Htm | exact Hb2 ].
Qed.

Lemma a_isub_wf_peel_tm_mid : forall x b Θ1 Ξ Θ2,
  a_suffix Ξ ->
  ((x ~ b) ++ Θ1) ⊴ (Ξ ++ (x ~ b) ++ Θ2) ->
  {{ ⊢ (Ξ ++ (x ~ b) ++ Θ2) }}a ->
  abind_is_tm b ->
  Θ1 ⊴ (Ξ ++ Θ2) /\ {{ ⊢ (Ξ ++ Θ2) }}a.
Proof.
  intros x b Θ1 Ξ Θ2 Hsuf Hle Hwf Htm. split.
  - eapply a_isub_peel_tm_mid;
      [ exact Htm | exact Hsuf | apply a_wf_aenv_uniq; exact Hwf | | exact Hle ].
    apply a_wf_aenv_lc_aenv in Hwf.
    apply lc_aenv_app_inv in Hwf as [_ Hwf].
    apply lc_aenv_app_inv in Hwf as [_ Hwf]. exact Hwf.
  - eapply a_wf_aenv_strip_tm_mid;
      [ apply abind_is_tm_not_ty; exact Htm | exact Hwf ].
Qed.

Corollary ad_pat_rename_tm : forall M x (b : abind) Θ0 e Q y,
  {{ ((x ~ b) ++ Θ0) ⊢ˢ[ M ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q }}ad ->
  abind_is_tm b ->
  x `notin` dom Θ0 `union` fvar_in_exp e ->
  {{ ((y ~ b) ++ Θ0) ⊢ˢ[ M ] (open_exp_wrt_exp e (exp_var_f y)) ⦂ Q }}ad.
Proof.
  intros * Hd Htm Hx.
  rewrite (subst_exp_in_exp_intro x); [ | clear - Hx; fsetdec ].
  change ((y ~ b) ++ Θ0) with (nil ++ (y ~ b) ++ Θ0).
  eapply ad_pat_subst_tm;
    [ exact Hd | reflexivity | exact Htm | simpl; clear - Hx; fsetdec ].
Qed.

Lemma btyp_to_bskl_ptyp_to_btyp_syn : forall A,
  btyp_to_bskl (ptyp_to_btyp_syn A) = pskl_to_bskl_syn (ptyp_to_pskl A).
Proof. induction A; simpl; congruence. Qed.

Lemma bskl_to_pskl_arrow_inv : forall Q P1 P2,
  bskl_to_pskl Q = pskl_arrow P1 P2 ->
  exists Q1 Q2, Q = bskl_arrow Q1 Q2 /\
                bskl_to_pskl Q1 = P1 /\ bskl_to_pskl Q2 = P2.
Proof.
  intros [ | | | Q1 Q2 | | | | ] P1 P2 Heq; simpl in Heq; try discriminate.
  inversion Heq; subst; eauto.
Qed.

Arguments bskl_to_pskl_arrow_inv {Q P1 P2} _.

Lemma a_wf_pskl_weaken_cons : forall Θ Δ P x (b : abind),
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> {{ ((x ~ b) ++ Θ) ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros * H. eapply a_wf_pskl_mono;
    [ exact H | apply aenv_tbinds_le_of_binds_le; apply aenv_binds_le_weaken_l ].
Qed.

Lemma a_wf_exp_weaken_cons : forall Θ e x (b : abind),
  {{ Θ ⊢ᵉ e }}a -> {{ ((x ~ b) ++ Θ) ⊢ᵉ e }}a.
Proof.
  intros * H. eapply a_wf_exp_mono;
    [ exact H | apply aenv_tbinds_le_of_binds_le; apply aenv_binds_le_weaken_l ].
Qed.

Lemma a_wf_exp_anno_inv : forall Θ e A,
  {{ Θ ⊢ᵉ (exp_anno e A) }}a -> a_wf_ptyp Θ A /\ {{ Θ ⊢ᵉ e }}a.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_exp_freeze_inv : forall Θ e,
  {{ Θ ⊢ᵉ (exp_freeze e) }}a -> {{ Θ ⊢ᵉ e }}a.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_exp_app_inv : forall Θ e1 e2,
  {{ Θ ⊢ᵉ (exp_app e1 e2) }}a -> {{ Θ ⊢ᵉ e1 }}a /\ {{ Θ ⊢ᵉ e2 }}a.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_exp_abs_anno_inv : forall Θ A e,
  {{ Θ ⊢ᵉ (exp_abs_anno A e) }}a -> a_wf_ptyp Θ A.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma a_wf_exp_subst_var : forall Θ e x z,
  {{ Θ ⊢ᵉ e }}a ->
  {{ Θ ⊢ᵉ (subst_exp_in_exp (exp_var_f x) z e) }}a.
Proof.
  intros Θ e x z H; induction H; simpl.
  - apply a_wf_exp__unit.
  - destruct_if; apply a_wf_exp__var.
  - apply a_wf_exp__anno; auto.
  - apply a_wf_exp__freeze; auto.
  - apply a_wf_exp__abs with (L := L `union` singleton z `union` singleton x).
    intros y Hy.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hy; fsetdec | apply lc_exp_var_f ].
    apply H0. clear - Hy; fsetdec.
  - apply a_wf_exp__abs_anno
      with (L := L `union` singleton z `union` singleton x);
      [ assumption | ].
    intros y Hy.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hy; fsetdec | apply lc_exp_var_f ].
    apply H1. clear - Hy; fsetdec.
  - apply a_wf_exp__app; auto.
Qed.

Lemma a_wf_exp_family_pick : forall Θ L e x,
  (forall y, y `notin` L -> {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f y)) }}a) ->
  {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a.
Proof.
  intros Θ L e x Hf.
  destruct (atom_fresh (L `union` fvar_in_exp e `union` singleton x))
    as [z Hz].
  rewrite (subst_exp_in_exp_intro z e (exp_var_f x));
    [ | clear - Hz; fsetdec ].
  apply a_wf_exp_subst_var, Hf. clear - Hz; fsetdec.
Qed.

Lemma a_wf_exp_abs_pick : forall Θ e x,
  {{ Θ ⊢ᵉ (exp_abs e) }}a ->
  {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a.
Proof.
  intros Θ e x H; inversion H; subst; eapply a_wf_exp_family_pick; eassumption.
Qed.

Lemma a_wf_exp_abs_anno_pick : forall Θ A e x,
  {{ Θ ⊢ᵉ (exp_abs_anno A e) }}a ->
  {{ Θ ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a.
Proof.
  intros Θ A e x H; inversion H; subst; eapply a_wf_exp_family_pick; eassumption.
Qed.

Lemma ad_pat_mod_comp_sk : forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad -> mod_comp_sk Q M.
Proof.
  intros M Θ e Q H; induction H.
  -  eapply ad_pat_sub_mod_comp_sk; eassumption.
  -  eapply ad_pat_sub_mod_comp_sk; eassumption.
  -  eapply ad_pat_sub_mod_comp_sk; eassumption.
  -  apply mod_comp_sk__tc. apply mod_comp_sk_ti_inv; assumption.
  -  assumption.
  -  assumption.
  -  eapply mod_comp_sk_fn_inv; eassumption.
  -
    destruct (atom_fresh L) as [x Hx]. specialize (H0 x Hx).
    apply mod_comp_sk__tc. apply is_sskl__univ_ghost. apply is_sskl__arrow;
      [ apply is_sskl__ghost | apply mod_comp_sk_tc_inv; exact H0 ].
  -
    destruct (atom_fresh L) as [x Hx]. specialize (H1 x Hx).
    apply mod_comp_sk__tc. apply is_sskl__univ_ghost. apply is_sskl__arrow.
    + rewrite btyp_to_bskl_ptyp_to_btyp_syn.
      apply is_sskl_pskl_to_bskl_syn.
      apply ptyp_to_pskl_lc. eapply a_wf_ptyp_lc; eassumption.
    + apply mod_comp_sk_tc_inv; exact H1.
Qed.

Corollary a_consis_chk_sound : forall Θ0 P P0 Θ1,
  a_consis_chk Θ0 P P0 Θ1 ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  exists Qt, ({{ empty ⨟ Θ1 ⊢ˢ (pskl_to_uskl P) ∼ Qt }}ad) /\
             {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad.
Proof.
  intros * [Q Hc] Hwf HwfP0 HwfP.
  destruct (a_consis_isub_wf_nil Hc Hwf HwfP0 HwfP) as [Hle Hwf1].
  destruct (a_consis_sound Hc Hwf HwfP0 HwfP) as [_ [[Qt [_ [Hcons Hrs]]] _]].
  eauto 6.
Qed.

Lemma ad_refine_syn_arrow_inv : forall Θ Δ Q1 Q2 P1 P2,
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow P1 P2) }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Q1 ⊳ P1 }}ad /\ {{ Θ ⨟ Δ ⊢ᵣ Q2 ⊳ P2 }}ad.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma ptyp_to_uskl_syn_via_pskl : forall A,
  ptyp_to_uskl_syn A = pskl_to_uskl (ptyp_to_pskl A).
Proof.
  intros A. unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  apply pskl_to_uskl_via_bskl_syn.
Qed.

Lemma btyp_to_ptyp_close_rec : forall B α k,
  btyp_to_ptyp (close_btyp_wrt_btyp_rec k α B)
  = close_ptyp_wrt_ptyp_rec k α (btyp_to_ptyp B).
Proof.
  intros B; induction B; intros α0 k; default_simp.
Qed.

Lemma btyp_to_ptyp_close : forall B α,
  btyp_to_ptyp (close_btyp_wrt_btyp α B)
  = close_ptyp_wrt_ptyp α (btyp_to_ptyp B).
Proof.
  intros. unfold close_btyp_wrt_btyp, close_ptyp_wrt_ptyp.
  apply btyp_to_ptyp_close_rec.
Qed.

Lemma btyp_to_bskl_close_rec : forall B α k,
  btyp_to_bskl (close_btyp_wrt_btyp_rec k α B)
  = close_bskl_wrt_bskl_rec k α (btyp_to_bskl B).
Proof.
  intros B; induction B; intros α0 k; default_simp.
Qed.

Lemma btyp_to_bskl_close : forall B α,
  btyp_to_bskl (close_btyp_wrt_btyp α B)
  = close_bskl_wrt_bskl α (btyp_to_bskl B).
Proof.
  intros. unfold close_btyp_wrt_btyp, close_bskl_wrt_bskl.
  apply btyp_to_bskl_close_rec.
Qed.

Lemma btyp_to_bskl_mono_syn : forall B,
  mono_ptyp (btyp_to_ptyp B) ->
  btyp_to_bskl B = ptyp_to_bskl_syn (btyp_to_ptyp B).
Proof.
  unfold ptyp_to_bskl_syn.
  intros B; induction B; intros Hm; simpl in *; try inversion Hm; subst; auto.
  f_equal; auto.
Qed.

Lemma ptyp_to_uskl_syn_open : forall A α,
  ptyp_to_uskl_syn (open_ptyp_wrt_ptyp A (ptyp_var_f α))
  = open_uskl_wrt_uskl (ptyp_to_uskl_syn A) (uskl_var_f α).
Proof.
  intros A α. unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  rewrite ptyp_to_pskl_open, pskl_to_bskl_syn_open, bskl_to_uskl_open.
  reflexivity.
Qed.

Local Ltac subject_ftv_forall_row L Q A0 H0 γ Hγ Θ HeqA :=
  inversion HeqA; subst;
  let β := fresh "β" in let Hβ := fresh "Hβ" in
  let Hopen := fresh "Hopen" in let Hlow := fresh "Hlow" in
  let Hl := fresh "Hl" in let Hm := fresh "Hm" in let Hr := fresh "Hr" in
  destruct (atom_fresh (L `union` singleton γ `union` dom Θ
                          `union` ftvar_in_ptyp A0 `union` ftvar_in_bskl Q))
    as [β Hβ];
  assert (Hopen : γ `in` ftvar_in_ptyp (open_ptyp_wrt_ptyp A0 (ptyp_var_f β)))
    by (pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A0 (ptyp_var_f β))
          as Hlow; clear - Hγ Hlow; fsetdec);
  destruct (H0 β ltac:(clear - Hβ; solve_notin_auto)
              (open_ptyp_wrt_ptyp A0 (ptyp_var_f β))
              ltac:(rewrite ptyp_to_uskl_syn_open; reflexivity)
              γ Hopen) as [Hl | [Hm | Hr]];
  [ left; simpl;
    let Hup := fresh "Hup" in
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β)) as Hup;
    simpl in Hup; clear - Hl Hup Hβ; fsetdec
  | right; left;
    let Hb := fresh "Hb" in let τ := fresh "τ" in
    let Hc := fresh "Hc" in let Hb' := fresh "Hb'" in
    destruct Hm as [Hb | [τ Hb]]; [ left | right; exists τ ];
      (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
       [ discriminate | exact Hb' ])
  | right; right;
    let β' := fresh "β'" in let τ := fresh "τ" in let Hb := fresh "Hb" in
    let Hin := fresh "Hin" in let Hc := fresh "Hc" in let Hb' := fresh "Hb'" in
    destruct Hr as [β' [τ [Hb Hin]]]; exists β', τ;
    split; [ | exact Hin ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
      [ discriminate | exact Hb' ] ].

Lemma ad_pat_consis_subject_ftv : forall Ψ Θ R Qt,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Qt }}ad ->
  forall A, R = ptyp_to_uskl_syn A ->
  forall γ, γ `in` ftvar_in_ptyp A ->
  γ `in` ftvar_in_bskl Qt \/ a_flex_tvar Θ γ \/
  (exists β τ, binds β (abind_flex_mono_def τ) Θ /\ γ `in` ftvar_in_ptyp τ).
Proof.
  intros Ψ Θ R Qt H; induction H; intros A HeqA γ Hγ;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in HeqA.
  -
    destruct A; simpl in HeqA, Hγ; try discriminate.
    clear - Hγ; fsetdec.
  -
    destruct A; simpl in HeqA, Hγ; try discriminate;
      try solve [ clear - Hγ; fsetdec ].
    inversion HeqA; subst. left. simpl. exact Hγ.
  -
    destruct A; simpl in HeqA, Hγ; try discriminate;
      try solve [ clear - Hγ; fsetdec ].
    inversion HeqA; subst.
    assert (Hd : γ `in` ftvar_in_ptyp A1 \/ γ `in` ftvar_in_ptyp A2)
      by (clear - Hγ; fsetdec).
    destruct Hd as [Hd | Hd];
      [ destruct (IHad_pat_consis1 _ eq_refl γ Hd) as [Hl | [Hm | Hr]]
      | destruct (IHad_pat_consis2 _ eq_refl γ Hd) as [Hl | [Hm | Hr]] ];
      solve [ left; simpl; clear - Hl; fsetdec
            | right; left; exact Hm
            | right; right; exact Hr ].
  -
    destruct A; simpl in HeqA, Hγ; try discriminate;
      try solve [ clear - Hγ; fsetdec ].
  -
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA, Hγ;
      try discriminate; try solve [ clear - Hγ; fsetdec ].
    subject_ftv_forall_row L Q A0 H0 γ Hγ Θ HeqA.
  -
    destruct A; simpl in HeqA, Hγ; try discriminate;
      try solve [ clear - Hγ; fsetdec ].
  -
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA, Hγ;
      try discriminate; try solve [ clear - Hγ; fsetdec ].
    subject_ftv_forall_row L Q A0 H0 γ Hγ Θ HeqA.
  -
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  -
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  -
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  -
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  -
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  -
    destruct A; simpl in HeqA, Hγ; try discriminate; clear - Hγ; fsetdec.
  -
    destruct A; simpl in HeqA, Hγ; try discriminate;
      try solve [ clear - Hγ; fsetdec ].
    inversion HeqA; subst.
    apply singleton_1 in Hγ; subst.
    right; left; right; exists τ. assumption.
  -
    destruct (IHad_pat_consis A ltac:(exact HeqA) γ Hγ) as [Hl | [Hm | Hr]].
    + right; right. exists α, τ. split; [ exact H | ].
      rewrite ftvar_ptyp_to_bskl_syn in Hl. exact Hl.
    + right; left; exact Hm.
    + right; right; exact Hr.
Qed.

Lemma transport_ghost_answer : forall Ψ Θc A Qt Θr Δ P,
  {{ Ψ ⨟ Θc ⊢ˢ (ptyp_to_uskl_syn A) ∼ Qt }}ad ->
  (forall γ, γ `in` Δ -> ~ a_flex_tvar Θc γ) ->
  (forall γ β τ, γ `in` Δ -> binds β (abind_flex_mono_def τ) Θc ->
                 γ `notin` ftvar_in_ptyp τ) ->
  Qt = pskl_to_bskl_syn P ->
  Δ ∩ ftvar_in_pskl P [=] empty ->
  exists B, btyp_to_ptyp B = A /\ {{ Θr ⨟ Δ ⊢ᵣ bskl_ghost ⊳ (btyp_to_bskl B) }}ad.
Proof.
  intros Ψ Θc A Qt Θr Δ P Hc HnfΔ HdfΔ HQt HfrP.
  exists (ptyp_to_btyp_syn A). split; [ apply btyp_to_ptyp_ptyp_to_btyp_syn | ].
  rewrite btyp_to_bskl_ptyp_to_btyp_syn.
  apply ad_refine_syn__ghost.
  assert (Hfree : forall γ, γ `in` Δ -> γ `notin` ftvar_in_ptyp A).
  { intros γ HΔ Hγ.
    destruct (ad_pat_consis_subject_ftv Hc A eq_refl Hγ) as [Hl | [Hm | Hr]].
    - subst Qt. rewrite ftvar_in_bskl_syn in Hl.
      assert (Hin : γ `in` Δ ∩ ftvar_in_pskl P) by (clear - HΔ Hl; fsetdec).
      rewrite HfrP in Hin. clear - Hin; fsetdec.
    - exact (HnfΔ γ HΔ Hm).
    - destruct Hr as [β [τ [Hb Hin]]]. exact (HdfΔ γ β τ HΔ Hb Hin). }
  rewrite ftvar_ptyp_to_pskl.
  intros γ; split; intros Hγ; [ | clear - Hγ; fsetdec ].
  exfalso. apply (Hfree γ); clear - Hγ; fsetdec.
Qed.

Lemma transport_answer_univ_ghost_remove : forall {Θ Δ Q A},
  (exists B, btyp_to_ptyp B = A /\ {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ (btyp_to_bskl B) }}ad) ->
  exists B, btyp_to_ptyp B = A /\
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q) ⊳ (btyp_to_bskl B) }}ad.
Proof.
  intros Θ Δ Q A [B [HeqB Href]]. exists B.
  split; [ exact HeqB | apply ad_refine_syn_univ_ghost_remove_intro; exact Href ].
Qed.

Lemma transport_answer_flex_l : forall {Θ Δ α τ A},
  binds α (abind_flex_mono_def τ) Θ ->
  (exists B, btyp_to_ptyp B = A /\
     {{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn τ) ⊳ (btyp_to_bskl B) }}ad) ->
  exists B, btyp_to_ptyp B = A /\
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_var_f α) ⊳ (btyp_to_bskl B) }}ad.
Proof.
  intros Θ Δ α τ A Hb [B [HeqB Href]]. exists B.
  split; [ exact HeqB | eapply ad_refine_syn__flex_l; [ exact Hb | exact Href ] ].
Qed.

Lemma transport_flex_cons_tvar : forall α Θc Θr,
  (forall γ, a_flex_tvar Θc γ -> a_binds_tvar γ Θr) ->
  forall γ, a_flex_tvar ((α ~ abind_tvar) ++ Θc) γ ->
            a_binds_tvar γ ((α ~ abind_tvar) ++ Θr).
Proof.
  intros α Θc Θr Hflex γ Hfl.
  eapply a_binds_tvar_mono;
    [ apply aenv_tbinds_le_of_binds_le; apply aenv_binds_le_weaken_l | ].
  apply Hflex. apply (a_flex_tvar_cons_tvar_any α Θc γ). exact Hfl.
Qed.

Lemma ad_refine_syn_target_transport : forall Ψ Θc R Qt,
  {{ Ψ ⨟ Θc ⊢ˢ R ∼ Qt }}ad ->
  {{ ⊢ Θc }}a ->
  forall A, R = ptyp_to_uskl_syn A -> lc_ptyp A ->
  forall Θr Δ Qb,
  {{ ⊢ Θr }}a ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θc ->
               binds β (abind_flex_mono_def τ) Θr) ->
  (forall γ, a_flex_tvar Θc γ -> a_binds_tvar γ Θr) ->
  (forall γ, γ `in` ftvar_in_ptyp A -> γ `in` Δ \/ a_binds_tvar γ Θr) ->
  (forall γ, γ `in` Δ -> ~ a_flex_tvar Θc γ) ->
  (forall γ β τ, γ `in` Δ -> binds β (abind_flex_mono_def τ) Θc ->
                 γ `notin` ftvar_in_ptyp τ) ->
  {{ Θr ⨟ Δ ⊢ᵣ Qb ⊳ Qt }}ad ->
  exists B, btyp_to_ptyp B = A /\ {{ Θr ⨟ Δ ⊢ᵣ Qb ⊳ (btyp_to_bskl B) }}ad.
Proof.
  intros Ψ Θc R Qt H; induction H;
    intros Hwfc A HeqA HlcA Θr Δ Qb Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ Href;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in HeqA.
  -
    destruct A; simpl in HeqA; try discriminate.
    exists btyp_unit. split; [ reflexivity | exact Href ].
  -
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA; try discriminate.
    assert (Heqv : α1 = α) by (inversion HeqA; reflexivity). subst α1.
    exists (btyp_var_f α). split; [ reflexivity | exact Href ].
  -
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA; try discriminate.
    inversion HeqA; subst. clear HeqA.
    inversion HlcA; subst.
    revert Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ.
    remember (bskl_arrow Q1 Q2) as Qt0 eqn:HQt.
    assert (Hc : {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn (ptyp_arrow A1 A2))
                   ∼ (bskl_arrow Q1 Q2) }}ad)
      by (unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl;
          eapply ad_pat_consis__arrow; eassumption).
    revert HQt.
    induction Href as
      [ Θx Δx
      | Θx Δx αx
      | Θx Δx Qs1 Qs2 Pt1 Pt2 HiA HrA IHA HrB IHB
      | Lx Θx Δx Qs Pt Hi Hfam IHfam
      | Θx Δx Pf Hwff
      | Θx Δx Qs Pt Hi Hr IHr
      | Lx Θx Δx Qs Pt Hi Hfam IHfam
      | Θx Δx Qs Pt Hi Hr IHr
      | Θx Δx αx τx Pt Hb Hr IHr
      | Θx Δx αx τx Qs Hb Hr IHr ];
      intros HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ; try discriminate HQt.
    +
      inversion HQt; subst.
      destruct (IHad_pat_consis1 Hwfc A1 eq_refl ltac:(assumption)
                  Θx Δx Qs1 Hwfr Hdefs Hflex
                  ltac:(intros γ Hγ; apply Hvis; simpl; clear - Hγ; solve_notin_auto)
                  HnfΔ HdfΔ HrA) as [B1 [HeqB1 HrA']].
      destruct (IHad_pat_consis2 Hwfc A2 eq_refl ltac:(assumption)
                  Θx Δx Qs2 Hwfr Hdefs Hflex
                  ltac:(intros γ Hγ; apply Hvis; simpl; clear - Hγ; solve_notin_auto)
                  HnfΔ HdfΔ HrB) as [B2 [HeqB2 HrB']].
      exists (btyp_arrow B1 B2). split;
        [ simpl; rewrite HeqB1, HeqB2; reflexivity
        | simpl; apply ad_refine_syn_arrow_intro; assumption ].
    +
      eapply transport_ghost_answer;
        [ exact Hc | exact HnfΔ | exact HdfΔ | symmetry; exact HQt
        | exact Hwff ].
    +
      apply transport_answer_univ_ghost_remove.
      exact (IHr HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ).
    +
      apply (transport_answer_flex_l Hb).
      exact (IHr HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ).
  -
    destruct A; simpl in HeqA; discriminate.
  -
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA; try discriminate.
    inversion HeqA; subst. clear HeqA.
    revert Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ.
    remember (bskl_all_inh Q) as Qt0 eqn:HQt.
    assert (Hc : {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn (ptyp_all A0)) ∼ (bskl_all_inh Q) }}ad)
      by (unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl;
          eapply ad_pat_consis__forall_inh_untagged with (L := L); eassumption).
    revert HQt.
    induction Href as
      [ Θx Δx
      | Θx Δx αx
      | Θx Δx Qs1 Qs2 Pt1 Pt2 HiA HrA IHA HrB IHB
      | Lx Θx Δx Qs Pt Hi Hfam IHfam
      | Θx Δx Pf Hwff
      | Θx Δx Qs Pt Hi Hr IHr
      | Lx Θx Δx Qs Pt Hi Hfam IHfam
      | Θx Δx Qs Pt Hi Hr IHr
      | Θx Δx αx τx Pt Hb Hr IHr
      | Θx Δx αx τx Qs Hb Hr IHr ];
      intros HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ; try discriminate HQt.
    +
      inversion HQt; subst.
      destruct (atom_fresh (L `union` Lx `union` dom Θ `union` dom Θx
                              `union` Δx `union` ftvar_in_ptyp A0
                              `union` ftvar_in_bskl Q `union` ftvar_in_bskl Qs))
        as [α Hα].
      assert (HnfΔ' : forall γ, γ `in` add α Δx ->
                        ~ a_flex_tvar ((α ~ abind_tvar) ++ Θ) γ).
      { intros γ Hγ Hfl.
        apply (a_flex_tvar_cons_tvar_any α Θ γ) in Hfl as Hfl0.
        destruct (γ == α) as [-> | Hne].
        - destruct Hfl0 as [Hb | [τ Hb]]; apply binds_In in Hb;
            clear - Hb Hα; destruct_notin; fsetdec.
        - apply (HnfΔ γ); [ clear - Hγ Hne; fsetdec | exact Hfl0 ]. }
      assert (HdfΔ' : forall γ β τ, γ `in` add α Δx ->
                        binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ) ->
                        γ `notin` ftvar_in_ptyp τ).
      { intros γ β τ Hγ Hbd.
        destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hcx] | Hb'];
          [ discriminate | ].
        destruct (γ == α) as [-> | Hne].
        - intros Hin.
          assert (Hwfτ : a_wf_ptyp Θ τ)
            by (eapply a_wf_aenv_binds_def_wf; eassumption).
          assert (Ht : a_binds_tvar α Θ)
            by (eapply a_wf_ptyp_ftv_tvarish; eassumption).
          destruct Ht as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb;
            clear - Hb Hα; destruct_notin; fsetdec.
        - apply (HdfΔ γ β τ); [ clear - Hγ Hne; fsetdec | exact Hb' ]. }
      assert (Hwfr' : {{ ⊢ ((α ~ abind_tvar) ++ Θx) }}a)
        by (apply a_wf_aenv__tvar; [ clear - Hα; solve_notin_auto | exact Hwfr ]).
      destruct (H0 α ltac:(clear - Hα; solve_notin_auto)
                  ltac:(apply a_wf_aenv__tvar; [ clear - Hα; solve_notin_auto | exact Hwfc ])
                  (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))
                  ltac:(rewrite ptyp_to_uskl_syn_open; reflexivity)
                  ltac:(inversion HlcA; subst; auto)
                  ((α ~ abind_tvar) ++ Θx) (add α Δx)
                  (open_bskl_wrt_bskl Qs (bskl_var_f α))
                  Hwfr'
                  (@flex_defs_cons_tvar α _ _ Hdefs)
                  (@transport_flex_cons_tvar α _ _ Hflex)
                  ltac:(intros γ Hγ;
                        pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper
                                      A0 (ptyp_var_f α)) as Hup;
                        simpl in Hup;
                        destruct (γ == α) as [Heγ | Hne];
                        [ left; subst; clear; fsetdec
                        | assert (Hγ0 : γ `in` ftvar_in_ptyp A0)
                            by (clear - Hγ Hup Hne; fsetdec);
                          destruct (Hvis γ ltac:(simpl; exact Hγ0)) as [Hd | Ht];
                          [ left; clear - Hd; fsetdec
                          | right; eapply a_binds_tvar_mono;
                              [ apply aenv_tbinds_le_of_binds_le;
                                apply aenv_binds_le_weaken_l | exact Ht ] ] ])
                  HnfΔ' HdfΔ'
                  (Hfam α ltac:(clear - Hα; solve_notin_auto)))
        as [B0 [HeqB0 Href0]].
      exists (btyp_all_inh (close_btyp_wrt_btyp α B0)). split.
      * simpl. rewrite btyp_to_ptyp_close, HeqB0.
        rewrite close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp;
          [ reflexivity | clear - Hα; fsetdec ].
      * simpl. apply ad_refine_syn_all_intro
          with (L := L `union` Lx `union` dom Θx `union` Δx
                       `union` singleton α `union` ftvar_in_bskl Qs
                       `union` ftvar_in_bskl (btyp_to_bskl B0)).
        intros β Hβ.
        pose proof (@ad_refine_syn_rename_gen _ _ _ _ Href0
                      ((β ~ abind_tvar) ++ Θx) α β
                      ltac:(clear; fsetdec)
                      ltac:(clear - Hβ; solve_notin_auto)
                      ltac:(intros β0 τ Hbd;
                            destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                              as [[_ Hcx] | Hb']; [ discriminate | ];
                            pose proof (@a_wf_aenv_def_ftv_dom _ _ _ Hwfr Hb') as Hsc;
                            pose proof (binds_In _ _ _ _ Hb') as Hin;
                            split; [ apply binds_cons_3; exact Hb' | ];
                            split; [ intros ->; clear - Hin Hα; destruct_notin; fsetdec | ];
                            split; intro Hc0; apply Hsc in Hc0;
                              [ clear - Hc0 Hα; destruct_notin; fsetdec
                              | clear - Hc0 Hβ; destruct_notin; fsetdec ])) as Hren.
        apply ad_refine_syn_delta_mono with (Δ := add β Δx) in Hren;
          [ | clear; fsetdec ].
        rewrite <- subst_bskl_in_bskl_intro in Hren;
          [ | clear - Hα; fsetdec ].
        rewrite subst_bskl_in_bskl_spec in Hren.
        rewrite <- btyp_to_bskl_close in Hren.
        exact Hren.
    +
      eapply transport_ghost_answer;
        [ exact Hc | exact HnfΔ | exact HdfΔ | symmetry; exact HQt
        | exact Hwff ].
    +
      apply transport_answer_univ_ghost_remove.
      exact (IHr HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ).
    +
      apply (transport_answer_flex_l Hb).
      exact (IHr HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ).
  -
    destruct A; simpl in HeqA; discriminate.
  -
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA; try discriminate.
    inversion HeqA; subst. clear HeqA.
    revert Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ.
    remember (bskl_all_syn Q) as Qt0 eqn:HQt.
    assert (Hc : {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn (ptyp_all A0)) ∼ (bskl_all_syn Q) }}ad)
      by (unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; simpl;
          eapply ad_pat_consis__forall_syn with (L := L); eassumption).
    revert HQt.
    induction Href as
      [ Θx Δx
      | Θx Δx αx
      | Θx Δx Qs1 Qs2 Pt1 Pt2 HiA HrA IHA HrB IHB
      | Lx Θx Δx Qs Pt Hi Hfam IHfam
      | Θx Δx Pf Hwff
      | Θx Δx Qs Pt Hi Hr IHr
      | Lx Θx Δx Qs Pt Hi Hfam IHfam
      | Θx Δx Qs Pt Hi Hr IHr
      | Θx Δx αx τx Pt Hb Hr IHr
      | Θx Δx αx τx Qs Hb Hr IHr ];
      intros HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ; try discriminate HQt.
    +
      eapply transport_ghost_answer;
        [ exact Hc | exact HnfΔ | exact HdfΔ | symmetry; exact HQt
        | exact Hwff ].
    +
      apply transport_answer_univ_ghost_remove.
      exact (IHr HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ).
    +
      inversion HQt; subst.
      destruct (atom_fresh (L `union` Lx `union` dom Θ `union` dom Θx
                              `union` Δx `union` ftvar_in_ptyp A0
                              `union` ftvar_in_bskl Q `union` ftvar_in_bskl Qs))
        as [α Hα].
      destruct (H0 α ltac:(clear - Hα; solve_notin_auto)
                  ltac:(apply a_wf_aenv__tvar; [ clear - Hα; solve_notin_auto | exact Hwfc ])
                  (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))
                  ltac:(rewrite ptyp_to_uskl_syn_open; reflexivity)
                  ltac:(inversion HlcA; subst; auto)
                  ((α ~ abind_tvar) ++ Θx) Δx (bskl_univ_ghost Qs)
                  ltac:(apply a_wf_aenv__tvar; [ clear - Hα; solve_notin_auto | exact Hwfr ])
                  (@flex_defs_cons_tvar α _ _ Hdefs)
                  (@transport_flex_cons_tvar α _ _ Hflex)
                  ltac:(intros γ Hγ;
                        pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper
                                      A0 (ptyp_var_f α)) as Hup;
                        simpl in Hup;
                        destruct (γ == α) as [Heγ | Hne];
                        [ right; left; subst;
                          unfold binds; simpl; left; reflexivity
                        | assert (Hγ0 : γ `in` ftvar_in_ptyp A0)
                            by (clear - Hγ Hup Hne; fsetdec);
                          destruct (Hvis γ ltac:(simpl; exact Hγ0)) as [Hd | Ht];
                          [ left; exact Hd
                          | right; eapply a_binds_tvar_mono;
                              [ apply aenv_tbinds_le_of_binds_le;
                                apply aenv_binds_le_weaken_l | exact Ht ] ] ])
                  (fun γ Hγ Hfl =>
                     HnfΔ γ Hγ (proj1 (a_flex_tvar_cons_tvar_any α Θ γ) Hfl))
                  ltac:(intros γ β τ Hγ Hbd;
                        destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hcx] | Hb'];
                        [ discriminate | exact (HdfΔ γ β τ Hγ Hb') ])
                  (Hfam α ltac:(clear - Hα; solve_notin_auto)))
        as [B0 [HeqB0 Href0]].
      exists (btyp_all_syn (close_btyp_wrt_btyp α B0)). split.
      * simpl. rewrite btyp_to_ptyp_close, HeqB0.
        rewrite close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp;
          [ reflexivity | clear - Hα; fsetdec ].
      * simpl. apply ad_refine_syn_univ_ghost_fill_intro
          with (L := L `union` Lx `union` dom Θx `union` Δx
                       `union` singleton α `union` ftvar_in_bskl Qs
                       `union` ftvar_in_bskl (btyp_to_bskl B0)).
        intros β Hβ.
        pose proof (@ad_refine_syn_rename_ctx_gen nil α Θx _ _ _ β Href0
                      ltac:(simpl_env; clear - Hα; solve_notin_auto)
                      ltac:(intros β0 τ Hbd; simpl_env in Hbd;
                            pose proof (@a_wf_aenv_def_ftv_dom _ _ _ Hwfr Hbd) as Hsc;
                            intro Hc0; apply Hsc in Hc0; clear - Hc0 Hα; destruct_notin; fsetdec)
                      ltac:(clear - Hβ; solve_notin_auto)) as Hren.
        simpl_env in Hren. simpl in Hren.
        rewrite subst_bskl_in_bskl_fresh_eq in Hren;
          [ | clear - Hα; simpl; fsetdec ].
        rewrite subst_bskl_in_bskl_spec in Hren.
        rewrite <- btyp_to_bskl_close in Hren.
        exact Hren.
    +
      apply (transport_answer_flex_l Hb).
      exact (IHr HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ).
  -
    destruct A; simpl in HeqA; discriminate.
  -
    destruct A; simpl in HeqA; discriminate.
  -
    destruct A; simpl in HeqA; discriminate.
  -
    destruct A; simpl in HeqA; discriminate.
  -
    destruct A; simpl in HeqA; discriminate.
  -
    destruct A; simpl in HeqA; discriminate.
  -
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqA; try discriminate.
    assert (Heqv : α1 = α) by (inversion HeqA; reflexivity). subst α1.
    assert (Hbr : binds α (abind_flex_mono_def τ) Θr) by (apply Hdefs; exact H).
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfr | exact Hbr ]).
    assert (Hwfτ : a_wf_ptyp Θr τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwfr | exact Hbr ]).
    destruct (IHad_pat_consis Hwfc τ eq_refl
                ltac:(eapply a_wf_ptyp_lc; exact Hwfτ)
                Θr Δ Qb Hwfr Hdefs Hflex
                ltac:(intros γ Hγ; right;
                      eapply a_wf_ptyp_ftv_tvarish; eassumption)
                HnfΔ HdfΔ Href) as [B [HeqB Href']].
    exists (btyp_var_f α). split; [ reflexivity | ].
    eapply ad_refine_syn__flex_r; [ exact Hbr | ].
    rewrite <- HeqB.
    rewrite <- btyp_to_bskl_mono_syn; [ exact Href' | rewrite HeqB; exact Hmono ].
  -
    assert (Hbr : binds α (abind_flex_mono_def τ) Θr) by (apply Hdefs; exact H).
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfr | exact Hbr ]).
    assert (Hwfτ : a_wf_ptyp Θr τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwfr | exact Hbr ]).
    subst R.
    revert Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ Hbr Hmono Hwfτ.
    remember (bskl_var_f α) as Qt0 eqn:HQt.
    assert (Hc : {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ (bskl_var_f α) }}ad)
      by (unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn;
          eapply ad_pat_consis__flex_r; eassumption).
    revert HQt.
    induction Href as
      [ Θx Δx
      | Θx Δx αx
      | Θx Δx Qs1 Qs2 Pt1 Pt2 HiA HrA IHA HrB IHB
      | Lx Θx Δx Qs Pt Hi Hfam IHfam
      | Θx Δx Pf Hwff
      | Θx Δx Qs Pt Hi Hr IHr
      | Lx Θx Δx Qs Pt Hi Hfam IHfam
      | Θx Δx Qs Pt Hi Hr IHr
      | Θx Δx αx τx Pt Hb Hr IHr
      | Θx Δx αx τx Qs Hb Hr IHr ];
      intros HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ Hbr Hmono Hwfτ; try discriminate HQt.
    +
      inversion HQt; subst.
      destruct (IHad_pat_consis Hwfc A eq_refl HlcA Θx Δx
                  (ptyp_to_bskl_syn τ) Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ
                  ltac:(rewrite <- !(ptyp_to_bskl_inh_syn_eq Hmono);
                        apply ad_refine_syn_refl_inh;
                        apply a_wf_ptyp_to_wf_pskl; exact Hwfτ))
        as [B [HeqB Href']].
      exists B. split; [ exact HeqB | ].
      eapply ad_refine_syn__flex_l; [ exact Hbr | exact Href' ].
    +
      eapply transport_ghost_answer;
        [ exact Hc | exact HnfΔ | exact HdfΔ | symmetry; exact HQt
        | exact Hwff ].
    +
      apply transport_answer_univ_ghost_remove.
      exact (IHr HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ Hbr Hmono Hwfτ).
    +
      apply (transport_answer_flex_l Hb).
      exact (IHr HQt Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ Hbr Hmono Hwfτ).
    +
      inversion HQt; subst.
      assert (Hτ : τx = τ)
        by (pose proof (binds_unique _ _ _ _ _ Hb Hbr
                          (a_wf_aenv_uniq Hwfr)) as Heq2;
            inversion Heq2; reflexivity).
      subst τx.
      destruct (IHad_pat_consis Hwfc A eq_refl HlcA Θx Δx Qs
                  Hwfr Hdefs Hflex Hvis HnfΔ HdfΔ Hr) as [B [HeqB Href']].
      exists B. split; [ exact HeqB | exact Href' ].
Qed.

Lemma a_consis_chk_annot_refine : forall Θ0 A P Θ1,
  a_consis_chk Θ0 (ptyp_to_pskl A) P Θ1 ->
  {{ ⊢ Θ0 }}a ->
  a_wf_ptyp Θ0 A ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  exists B, btyp_to_ptyp B = A /\
    {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B) }}ad.
Proof.
  intros Θ0 A P Θ1 Hchk Hwf HwfA HwfP.
  destruct (a_consis_chk_sound Hchk Hwf HwfP
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA))
    as [Hle [Hwf1 [Qt [Hcons Href]]]].
  assert (HwfA1 : a_wf_ptyp Θ1 A) by (eapply a_wf_ptyp_isub; eassumption).
  rewrite <- ptyp_to_uskl_syn_via_pskl in Hcons.
  eapply ad_refine_syn_target_transport;
    [ exact Hcons | exact Hwf1 | reflexivity
    | eapply a_wf_ptyp_lc; exact HwfA
    | exact Hwf1
    | intros β τ Hb; exact Hb
    | intros γ [Hb | [τ Hb]]; [ right; left | right; right; exists τ ]; exact Hb
    | intros γ Hγ; right; eapply a_wf_ptyp_ftv_tvarish; eassumption
    | intros γ Hγ; clear - Hγ; fsetdec
    | intros γ β τ Hγ; clear - Hγ; fsetdec
    | exact Href ].
Qed.

Lemma ad_pat_target_wf : forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a.
Proof.
  intros M Θ e Q H; induction H; intros Hwf.
  -  exact H.
  -  exact H1.
  -  exact H.
  -  apply IHad_pat; exact Hwf.
  -
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_skl P) ++ Θ) }}a).
    { apply a_wf_aenv__var;
        [ clear - Hx; fsetdec
        | exact H0
        | exact Hwf ]. }
    pose proof (H3 x ltac:(clear - Hx; solve_notin_auto) Hwfx) as HwfQ.
    simpl. apply a_wf_pskl__arrow.
    + rewrite bskl_to_pskl_pskl_to_bskl_inh. exact H0.
    + eapply a_wf_pskl_mono;
        [ exact HwfQ
        | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_skl P) Θ);
          intros [] ].
  -
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a).
    { apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H0 | exact Hwf ]. }
    pose proof (H4 x ltac:(clear - Hx; solve_notin_auto) Hwfx) as HwfQ.
    simpl. apply a_wf_pskl__arrow.
    + rewrite bskl_to_pskl_btyp_to_bskl. rewrite H1.
      apply a_wf_ptyp_to_wf_pskl. exact H0.
    + eapply a_wf_pskl_mono;
        [ exact HwfQ
        | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ A) Θ);
          intros [] ].
  -
    pose proof (IHad_pat2 Hwf) as Hwfarr.
    simpl in Hwfarr.
    inversion Hwfarr as [ | | Θz Δz Pa Pb Hwa Hwb | | | ]; subst.
    exact Hwb.
  -
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_skl pskl_ghost) ++ Θ) }}a).
    { apply a_wf_aenv__var;
        [ clear - Hx; fsetdec | apply a_wf_pskl__ghost | exact Hwf ]. }
    pose proof (H0 x ltac:(clear - Hx; solve_notin_auto) Hwfx) as HwfQ.
    assert (HwfQ' : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (pskl_to_bskl_syn P)) }}a)
      by (eapply a_wf_pskl_mono;
          [ exact HwfQ
          | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_skl pskl_ghost) Θ);
            intros [] ]).
    rewrite bskl_to_pskl_pskl_to_bskl_syn in HwfQ'.
    simpl. apply a_wf_pskl__univ_ghost.
    + apply guarded_pskl__arrow;
        [ apply lc_pskl_ghost | ].
      rewrite bskl_to_pskl_pskl_to_bskl_syn.
      eapply a_wf_pskl_lc; exact HwfQ'.
    + rewrite aenv_minus_empty. apply a_wf_pskl__arrow;
        [ apply a_wf_pskl__ghost | ].
      rewrite bskl_to_pskl_pskl_to_bskl_syn. exact HwfQ'.
  -
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a).
    { apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H | exact Hwf ]. }
    pose proof (H1 x ltac:(clear - Hx; solve_notin_auto) Hwfx) as HwfQ.
    assert (HwfQ' : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (pskl_to_bskl_syn P)) }}a)
      by (eapply a_wf_pskl_mono;
          [ exact HwfQ
          | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ A) Θ);
            intros [] ]).
    rewrite bskl_to_pskl_pskl_to_bskl_syn in HwfQ'.
    assert (HwfpA : {{ Θ ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
      by (apply a_wf_ptyp_to_wf_pskl; exact H).
    simpl. apply a_wf_pskl__univ_ghost.
    + apply guarded_pskl__arrow;
        [ eapply a_wf_pskl_lc;
          rewrite btyp_to_bskl_ptyp_to_btyp_syn,
                  bskl_to_pskl_pskl_to_bskl_syn; exact HwfpA
        | rewrite bskl_to_pskl_pskl_to_bskl_syn;
          eapply a_wf_pskl_lc; exact HwfQ' ].
    + rewrite aenv_minus_empty. apply a_wf_pskl__arrow;
        [ rewrite btyp_to_bskl_ptyp_to_btyp_syn,
                  bskl_to_pskl_pskl_to_bskl_syn; exact HwfpA
        | rewrite bskl_to_pskl_pskl_to_bskl_syn; exact HwfQ' ].
Qed.

Theorem a_pat_sound : forall m Θ0 P0 e P Θ1,
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ P ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat m P0 ->
  {{ Θ0 ⊢ᵉ e }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  exists Qt, bskl_to_pskl Qt = P /\
    ({{ Θ1 ⊢ˢ[ m ] e ⦂ Qt }}ad) /\
    ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad).
Proof.
  intros m Θ0 P0 e P Θ1 H; induction H; intros Hwf HwfP0 Hmod Hexp;
    pose proof (fun y Ps Hb => @a_wf_aenv_binds_var_skl_wf _ y Ps Hwf Hb)
      as Hskl.
  -
    destruct (a_sub_sound H Hwf HwfP0
                ltac:(apply a_wf_pskl__unit)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    assert (HwfQt : {{ Θ1 ⨟ empty ⊢ₚₛ (bskl_to_pskl Qt) }}a)
      by (rewrite HeQt; eapply a_sub_output_wf;
          [ exact H | exact Hwf | exact HwfP0 | apply a_wf_pskl__unit ]).
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ].
    split; [ apply ad_pat__unit; [ exact HwfQt | exact Hjoin ] | exact Href ].
  -
    assert (HwfA : a_wf_ptyp Θ0 A)
      by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
    destruct (a_sub_sound H0 Hwf HwfP0
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    assert (HwfQt : {{ Θ1 ⨟ empty ⊢ₚₛ (bskl_to_pskl Qt) }}a)
      by (rewrite HeQt; eapply a_sub_output_wf;
          [ exact H0 | exact Hwf | exact HwfP0
          | apply a_wf_ptyp_to_wf_pskl; exact HwfA ]).
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ]. split; [ | exact Href ].
    eapply ad_pat__var with (b := abind_var_typ A);
      [ apply (a_sub_tm_le H0); [ exact I | exact H ]
      | reflexivity
      | exact HwfQt
      | rewrite pskl_to_uskl_via_bskl_syn; exact Hjoin ].
  -
    destruct (a_sub_sound H0 Hwf HwfP0 (Hskl _ _ H)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    assert (HwfQt : {{ Θ1 ⨟ empty ⊢ₚₛ (bskl_to_pskl Qt) }}a)
      by (rewrite HeQt; eapply a_sub_output_wf;
          [ exact H0 | exact Hwf | exact HwfP0 | exact (Hskl _ _ H) ]).
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ]. split; [ | exact Href ].
    eapply ad_pat__var with (b := abind_var_skl P);
      [ apply (a_sub_tm_le H0); [ exact I | exact H ]
      | reflexivity
      | exact HwfQt
      | rewrite pskl_to_uskl_via_bskl_syn; exact Hjoin ].
  -
    destruct (a_wf_exp_anno_inv Hexp) as [HwfA Hexp0].
    destruct (a_sub_sound H Hwf HwfP0
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA)
                ltac:(intros _; exact Hmod)
                ltac:(intros Hd; discriminate))
      as [Hle [Hwf1 [Qt [HeQt [Hjoin Href]]]]].
    assert (HwfQt : {{ Θ1 ⨟ empty ⊢ₚₛ (bskl_to_pskl Qt) }}a)
      by (rewrite HeQt; eapply a_sub_output_wf;
          [ exact H | exact Hwf | exact HwfP0
          | apply a_wf_ptyp_to_wf_pskl; exact HwfA ]).
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ]. split; [ | exact Href ].
    apply ad_pat__anno;
      [ exact HwfQt
      | rewrite pskl_to_uskl_via_bskl_syn; exact Hjoin ].
  -
    destruct (IHa_pat Hwf ltac:(apply a_wf_pskl__ghost)
                a_sk_mode_compat__ti (a_wf_exp_freeze_inv Hexp))
      as [Hle [Hwf1 [Qt [HeQt [Hpat Href]]]]].
    destruct (ad_refine_syn_syn_l Href pskl_ghost eq_refl) as [P' HQt].
    subst Qt.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists (pskl_to_bskl_syn P'). split; [ exact HeQt | ].
    split; [ apply ad_pat__freeze; exact Hpat | exact Href ].
  -
    destruct (a_split_sk_shape H0 Hmod) as [HeqΘ Hshape]; subst Θ1.
    destruct (a_split_sk_pieces H0 Hmod H HwfP0) as [HwfPP [HwfQ0 Hmod']].
    assert (Hxd : x `notin` dom Θ0) by (clear - H2; simpl_env in *; fsetdec).
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_skl P) ++ Θ0) }}a).
    { apply a_wf_aenv__var; [ exact Hxd | exact HwfPP | exact Hwf ]. }
    destruct (IHa_pat Hwfx
                (a_wf_pskl_weaken_cons x (abind_var_skl P) HwfQ0) Hmod'
                (a_wf_exp_weaken_cons x (abind_var_skl P)
                   (@a_wf_exp_abs_pick _ _ x Hexp)))
      as [Hle [Hwfout [Qt [HeQt [Hpat Href]]]]].
    destruct (@a_isub_wf_peel_tm_mid _ _ _ _ _ ltac:(eassumption) Hle Hwfout I)
      as [Hisub Hwf2].
    assert (Hmc : mod_comp_sk (bskl_arrow (pskl_to_bskl_inh P) Qt) m).
    { pose proof (ad_pat_mod_comp_sk Hpat) as Hmq.
      destruct Hshape as [[HP0 [HP HQ0]] | HP0]; subst; simpl.
      - destruct (a_sk_mode_compat_ghost_inv Hmod) as [Hm | Hm]; subst m;
          [ | congruence ].
        apply mod_comp_sk__ti. apply is_sskl__arrow;
          [ apply is_sskl__ghost | apply mod_comp_sk_ti_inv; exact Hmq ].
      - destruct (a_sk_mode_compat_arrow_inv Hmod) as [m' [Hm Hm']]; subst m.
        apply mod_comp_sk__fn; exact Hmq. }
    assert (Href2 : {{ (Ξ ++ Θ2) ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0)
                      ⊳ (bskl_arrow (pskl_to_bskl_inh P) Qt) }}ad).
    { destruct Hshape as [[HP0 [HP HQ0]] | HP0]; subst; simpl.
      - destruct (ad_refine_syn_syn_l Href pskl_ghost eq_refl) as [P' HQt].
        subst Qt.
        change (bskl_arrow bskl_ghost (pskl_to_bskl_syn P'))
          with (pskl_to_bskl_syn (pskl_arrow pskl_ghost P')).
        apply ad_refine_syn__ghost. clear; fsetdec.
      - apply ad_refine_syn_arrow_intro;
          [ apply ad_refine_syn_refl_inh;
              eapply a_wf_pskl_isub; [ exact HwfPP | exact Hisub ]
          | eapply ad_refine_syn_strip_tm_skl; exact Href ]. }
    split; [ exact Hisub | ]. split; [ exact Hwf2 | ].
    exists (bskl_arrow (pskl_to_bskl_inh P) Qt).
    split.
    { simpl. rewrite bskl_to_pskl_pskl_to_bskl_inh, HeQt. reflexivity. }
    split; [ | exact Href2 ].
    apply ad_pat__abs with (L := singleton x);
      [ exact H
      | eapply a_wf_pskl_isub; [ exact HwfPP | exact Hisub ]
      | exact Hmc
      | ].
    intros y Hy.
    apply ad_pat_rename_tm with (x := x);
      [ apply ad_pat_suffix_moving with (Ξ := Ξ) (Θ2 := (x ~ abind_var_skl P));
          exact Hpat
      | exact I
      | clear - H2; simpl_env in *; fsetdec ].
  -
    destruct (a_split_sk_shape H0 Hmod) as [HeqΘ Hshape]; subst Θ1.
    pose proof (a_wf_exp_abs_anno_inv Hexp) as HwfA.
    destruct (a_split_sk_pieces H0 Hmod H HwfP0) as [HwfPP [HwfQ0 Hmod']].
    destruct (a_consis_chk_sound H1 Hwf HwfPP
                ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA))
      as [Hlec [Hwfc _]].
    assert (Hxd : x `notin` dom Θ2) by (clear - H3; simpl_env in *; fsetdec).
    assert (HwfAc : a_wf_ptyp Θ2 A) by (eapply a_wf_ptyp_isub; eassumption).
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ2) }}a)
      by (apply a_wf_aenv__var_typ; [ exact Hxd | exact HwfAc | exact Hwfc ]).
    destruct (IHa_pat Hwfx
                (a_wf_pskl_weaken_cons x (abind_var_typ A)
                   ltac:(eapply a_wf_pskl_isub; [ exact HwfQ0 | exact Hlec ]))
                Hmod'
                (a_wf_exp_weaken_cons x (abind_var_typ A)
                   (a_wf_exp_isub (@a_wf_exp_abs_anno_pick _ _ _ x Hexp) Hlec)))
      as [Hle [Hwfout [Qt [HeQt [Hpat Href]]]]].
    destruct (@a_isub_wf_peel_tm_mid _ _ _ _ _ ltac:(eassumption) Hle Hwfout I)
      as [Hisub Hwf3].
    assert (Hisub0 : Θ0 ⊴ (Ξ ++ Θ3)) by (eapply a_isub_trans; eassumption).
    assert (Hbody : forall y,
              {{ ((y ~ abind_var_typ A) ++ (Ξ ++ Θ3)) ⊢ˢ[ decr_mode m ]
                (open_exp_wrt_exp e (exp_var_f y)) ⦂ Qt }}ad).
    { intros y. apply ad_pat_rename_tm with (x := x);
        [ apply ad_pat_suffix_moving with (Ξ := Ξ) (Θ2 := (x ~ abind_var_typ A));
            exact Hpat
        | exact I
        | clear - H3; simpl_env in *; fsetdec ]. }
    destruct Hshape as [[HP0 [HP HQ0]] | HP0].
    +
      subst P0 P Q0.
      destruct (ad_refine_syn_syn_l Href pskl_ghost eq_refl) as [P' HQt].
      subst Qt.
      split; [ exact Hisub0 | ]. split; [ exact Hwf3 | ].
      exists (bskl_arrow (btyp_to_bskl (ptyp_to_btyp_syn A))
                         (pskl_to_bskl_syn P')).
      split.
      { rewrite bskl_to_pskl_pskl_to_bskl_syn in HeQt.
        simpl. rewrite btyp_to_bskl_ptyp_to_btyp_syn.
        rewrite !bskl_to_pskl_pskl_to_bskl_syn. rewrite HeQt. reflexivity. }
      split.
      * eapply ad_pat__abs_anno with (L := singleton x)
                                     (B := ptyp_to_btyp_syn A);
          [ exact H
          | eapply a_wf_ptyp_isub; [ exact HwfA | exact Hisub0 ]
          | apply btyp_to_ptyp_ptyp_to_btyp_syn
          | | intros y Hy; apply Hbody ].
        destruct (a_sk_mode_compat_ghost_inv Hmod) as [Hm | Hm]; subst m;
          [ | congruence ].
        apply mod_comp_sk__ti. apply is_sskl__arrow.
        -- rewrite btyp_to_bskl_ptyp_to_btyp_syn.
           apply is_sskl_pskl_to_bskl_syn. apply ptyp_to_pskl_lc.
           eapply a_wf_ptyp_lc; exact HwfA.
        -- apply mod_comp_sk_ti_inv. apply (ad_pat_mod_comp_sk (Hbody x)).
      * simpl. rewrite btyp_to_bskl_ptyp_to_btyp_syn.
        change (bskl_arrow (pskl_to_bskl_syn (ptyp_to_pskl A))
                           (pskl_to_bskl_syn P'))
          with (pskl_to_bskl_syn (pskl_arrow (ptyp_to_pskl A) P')).
        apply ad_refine_syn__ghost. clear; fsetdec.
    +
      subst P0.
      destruct (a_consis_chk_annot_refine H1 Hwf HwfA HwfPP)
        as [B [HeqB HrefA]].
      destruct (a_sk_mode_compat_arrow_inv Hmod) as [m' [Hm Hm']]; subst m.
      split; [ exact Hisub0 | ]. split; [ exact Hwf3 | ].
      exists (bskl_arrow (btyp_to_bskl B) Qt).
      split.
      { simpl. rewrite bskl_to_pskl_btyp_to_bskl, HeqB, HeQt. reflexivity. }
      split.
      * eapply ad_pat__abs_anno with (L := singleton x) (B := B);
          [ exact H
          | eapply a_wf_ptyp_isub; [ exact HwfA | exact Hisub0 ]
          | exact HeqB
          | apply mod_comp_sk__fn; apply (ad_pat_mod_comp_sk (Hbody x))
          | intros y Hy; apply Hbody ].
      * simpl. apply ad_refine_syn_arrow_intro;
          [ eapply ad_refine_syn_isub; [ exact HrefA | exact Hisub ]
          | eapply ad_refine_syn_strip_tm_typ; exact Href ].
  -
    assert (Hxd : x `notin` dom Θ0) by (clear - H0; simpl_env in *; fsetdec).
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_skl pskl_ghost) ++ Θ0) }}a)
      by (apply a_wf_aenv__var;
          [ exact Hxd | apply a_wf_pskl__ghost | exact Hwf ]).
    destruct (IHa_pat Hwfx
                ltac:(apply a_wf_pskl__ghost) a_sk_mode_compat__tc
                (a_wf_exp_weaken_cons x (abind_var_skl pskl_ghost)
                   (@a_wf_exp_abs_pick _ _ x Hexp)))
      as [Hle [Hwfout [Qt [HeQt [Hpat Href]]]]].
    destruct (ad_refine_syn_syn_l Href pskl_ghost eq_refl) as [P' HQt].
    subst Qt.
    destruct (@a_isub_wf_peel_tm_mid _ _ _ _ _ ltac:(eassumption) Hle Hwfout I)
      as [Hisub Hwf1].
    split; [ exact Hisub | ]. split; [ exact Hwf1 | ].
    exists (bskl_univ_ghost (bskl_arrow bskl_ghost (pskl_to_bskl_syn P'))).
    split.
    { rewrite bskl_to_pskl_pskl_to_bskl_syn in HeQt.
      simpl. rewrite bskl_to_pskl_pskl_to_bskl_syn, HeQt. reflexivity. }
    split.
    + apply ad_pat__abs_check with (L := singleton x) (P := P').
      intros y Hy.
      apply ad_pat_rename_tm with (x := x);
        [ apply ad_pat_suffix_moving with (Ξ := Ξ)
                                          (Θ2 := (x ~ abind_var_skl pskl_ghost));
            exact Hpat
        | exact I
        | clear - H0; simpl_env in *; fsetdec ].
    + change (bskl_univ_ghost (bskl_arrow bskl_ghost (pskl_to_bskl_syn P')))
        with (pskl_to_bskl_syn (pskl_univ_ghost (pskl_arrow pskl_ghost P'))).
      apply ad_refine_syn__ghost. clear; fsetdec.
  -
    pose proof (a_wf_exp_abs_anno_inv Hexp) as HwfA.
    assert (Hxd : x `notin` dom Θ0) by (clear - H0; simpl_env in *; fsetdec).
    assert (Hwfx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ0) }}a)
      by (apply a_wf_aenv__var_typ;
          [ exact Hxd | exact HwfA | exact Hwf ]).
    destruct (IHa_pat Hwfx
                ltac:(apply a_wf_pskl__ghost) a_sk_mode_compat__tc
                (a_wf_exp_weaken_cons x (abind_var_typ A)
                   (@a_wf_exp_abs_anno_pick _ _ _ x Hexp)))
      as [Hle [Hwfout [Qt [HeQt [Hpat Href]]]]].
    destruct (ad_refine_syn_syn_l Href pskl_ghost eq_refl) as [P' HQt].
    subst Qt.
    destruct (@a_isub_wf_peel_tm_mid _ _ _ _ _ ltac:(eassumption) Hle Hwfout I)
      as [Hisub Hwf1].
    assert (HwfA1 : a_wf_ptyp (Ξ ++ Θ1) A)
      by (eapply a_wf_ptyp_isub; [ exact HwfA | exact Hisub ]).
    split; [ exact Hisub | ]. split; [ exact Hwf1 | ].
    exists (bskl_univ_ghost (bskl_arrow (btyp_to_bskl (ptyp_to_btyp_syn A))
                                     (pskl_to_bskl_syn P'))).
    split.
    { rewrite bskl_to_pskl_pskl_to_bskl_syn in HeQt.
      simpl. rewrite btyp_to_bskl_ptyp_to_btyp_syn.
      rewrite !bskl_to_pskl_pskl_to_bskl_syn, HeQt. reflexivity. }
    split.
    + apply ad_pat__abs_anno_check with (L := singleton x) (P := P');
        [ exact HwfA1 | ].
      intros y Hy.
      apply ad_pat_rename_tm with (x := x);
        [ apply ad_pat_suffix_moving with (Ξ := Ξ)
                                          (Θ2 := (x ~ abind_var_typ A));
            exact Hpat
        | exact I
        | clear - H0; simpl_env in *; fsetdec ].
    + rewrite btyp_to_bskl_ptyp_to_btyp_syn.
      change (bskl_univ_ghost (bskl_arrow (pskl_to_bskl_syn (ptyp_to_pskl A))
                                       (pskl_to_bskl_syn P')))
        with (pskl_to_bskl_syn
                (pskl_univ_ghost (pskl_arrow (ptyp_to_pskl A) P'))).
      apply ad_refine_syn__ghost. clear; fsetdec.
  -
    destruct (a_wf_exp_app_inv Hexp) as [Hexp1 Hexp2].
    destruct (IHa_pat1 Hwf ltac:(apply a_wf_pskl__ghost)
                a_sk_mode_compat__tc Hexp2)
      as [Hle1 [Hwf1 [Qt1 [HeQt1 [Hpat1 Href1]]]]].
    destruct (ad_refine_syn_syn_l Href1 pskl_ghost eq_refl) as [P' HQt1].
    subst Qt1.
    assert (HwfPin : {{ Θ1 ⨟ empty ⊢ₚₛ P' }}a).
    { pose proof (ad_pat_target_wf Hpat1 Hwf1) as Hw.
      rewrite bskl_to_pskl_pskl_to_bskl_syn in Hw. exact Hw. }
    rewrite bskl_to_pskl_pskl_to_bskl_syn in HeQt1. subst P0.
    destruct (IHa_pat2 Hwf1
                ltac:(apply a_wf_pskl__arrow;
                      [ exact HwfPin
                      | eapply a_wf_pskl_isub; [ exact HwfP0 | exact Hle1 ] ])
                ltac:(apply a_sk_mode_compat__fn; exact Hmod)
                (a_wf_exp_isub Hexp1 Hle1))
      as [Hle2 [Hwf2 [Qt2 [HeQt2 [Hpat2 Href2]]]]].
    destruct (bskl_to_pskl_arrow_inv HeQt2) as [Qa [Qb [HQt2 [HeQa HeQb]]]].
    subst Qt2. simpl in Href2.
    destruct (ad_refine_syn_arrow_inv Href2) as [HrefA HrefB].
    split; [ eapply a_isub_trans; eassumption | ]. split; [ exact Hwf2 | ].
    exists Qb. split; [ exact HeQb | ]. split; [ | exact HrefB ].
    eapply ad_pat__app with (P := P') (Q1 := Qa);
      [ eapply ad_pat_isub_tm;
          [ exact Hpat1 | exact Hle2 | eapply a_pat_tm_le; exact H0 ]
      | exact HrefA
      | exact Hpat2 ].
Qed.

Lemma a_split_dom_mono : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a -> dom Θ0 [<=] dom Θ1.
Proof.
  intros Θ0 P0 P Q Θ1 H;
    destruct H as [ Θa Pa Qa | Θa | Θa Θb α β α1 Qc Hβ Hα1 Hc ];
    try reflexivity.
  pose proof (auc_dom_mono_consis Hc) as Hd.
  simpl_env in Hd. clear - Hd. fsetdec.
Qed.

Lemma a_consis_chk_dom_mono : forall Θ0 P P0 Θ1,
  a_consis_chk Θ0 P P0 Θ1 -> dom Θ0 [<=] dom Θ1.
Proof. intros Θ0 P P0 Θ1 [Qc Hc]. exact (auc_dom_mono_consis Hc). Qed.

Lemma a_pat_dom_mono : forall m Θ0 P0 e Q Θ1,
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}a -> dom Θ0 [<=] dom Θ1.
Proof.
  intros m Θ0 P0 e Q Θ1 H; induction H as
    [ m0 Θa Θb P0a Pa Hsub
    | m0 Θa Θb P0a x A Qa Hb Hsub
    | m0 Θa Θb P0a x Ps Qa Hb Hsub
    | m0 Θa Θb P0a ea A Qa Hsub
    | Θa ea Qa Θb Hp IHp
    | x m0 Θa Θb Θc P0a Pa Q0 ea Qa Ξ Hne Hsp Hsuf Hxf Hp IHp
    | x m0 Θa Θb Θc Θd P0a Pa Q0 A ea Qa Ξ Hne Hsp Hchk Hsuf Hxf Hp IHp
    | x Θa Θb ea Qa Ξ Hsuf Hxf Hp IHp
    | x Θa Θb A ea Qa Ξ Hsuf Hxf Hp IHp
    | m0 Θa Θb Θc P0a Q0 Pa Qa e1 e2 Hp2 IHp2 Hp1 IHp1 ];
    try (exact ((proj1 a_sub_sub_flex_dom_mono) _ _ _ _ _ _ _ Hsub));
    try exact IHp.
  -
    pose proof (a_split_dom_mono Hsp) as Hd1.
    simpl_env in Hxf. simpl_env in IHp. simpl_env.
    intros a Ha.
    assert (Ha1 : a `in` dom Θb) by (clear - Ha Hd1; fsetdec).
    assert (Hax : a <> x) by (intros ->; clear - Ha1 Hxf; fsetdec).
    assert (Ha2 : a `in` union (singleton x) (dom Θb))
      by (clear - Ha1; fsetdec).
    apply IHp in Ha2. clear - Ha2 Hax. fsetdec.
  -
    pose proof (a_split_dom_mono Hsp) as Hd1.
    pose proof (a_consis_chk_dom_mono Hchk) as Hd2.
    simpl_env in Hxf. simpl_env in IHp. simpl_env.
    intros a Ha.
    assert (Ha1 : a `in` dom Θc) by (clear - Ha Hd1 Hd2; fsetdec).
    assert (Hax : a <> x) by (intros ->; clear - Ha1 Hxf; fsetdec).
    assert (Ha2 : a `in` union (singleton x) (dom Θc))
      by (clear - Ha1; fsetdec).
    apply IHp in Ha2. clear - Ha2 Hax. fsetdec.
  -
    simpl_env in Hxf. simpl_env in IHp. simpl_env.
    intros a Ha.
    assert (Hax : a <> x) by (intros ->; clear - Ha Hxf; fsetdec).
    assert (Ha2 : a `in` union (singleton x) (dom Θa))
      by (clear - Ha; fsetdec).
    apply IHp in Ha2. clear - Ha2 Hax. fsetdec.
  -
    simpl_env in Hxf. simpl_env in IHp. simpl_env.
    intros a Ha.
    assert (Hax : a <> x) by (intros ->; clear - Ha Hxf; fsetdec).
    assert (Ha2 : a `in` union (singleton x) (dom Θa))
      by (clear - Ha; fsetdec).
    apply IHp in Ha2. clear - Ha2 Hax. fsetdec.
  -
    clear - IHp1 IHp2. fsetdec.
Qed.
