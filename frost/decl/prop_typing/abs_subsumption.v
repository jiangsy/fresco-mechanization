(** Frost — declarative typing metatheory: SPLIT helpers for abs-value
    to-subsumption (the closure infrastructure used by D12). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.prop_typing.weakening.
Require Import src.frost.decl.prop_typing.gen.
Require Import src.frost.decl.prop_typing.mono_subsumption.

Set Implicit Arguments.

(** [d_typing_abs_value_to_subsumption_d_sub]: companion lemma for
    the d_sub-level closure of [d_typing_abs_value_to_subsumption]'s
    __embed case. Induction on d_sub: __check mirrors __check_gen
    (mono extraction + reconstruction); __forall_r recurses via the
    IH on the inner d_sub. Other cases vacuous via mode or shape
    mismatch. *)
Lemma d_typing_abs_value_to_subsumption_d_sub :
  forall Γ Δ T0 C0,
    d_sub mode_tc Δ Γ T0 C0 ->
    Δ = nil ->
    forall Lvar e Ahead Bhead m_orig,
      T0 = typ_arrow Ahead Bhead ->
      is_inh_typ Ahead ->
      d_wf_typ Γ Ahead ->
      (forall x, x `notin` Lvar ->
         d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ Ahead) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      decr_mode m_orig = mode_ti ->
      d_wf_denv Γ ->
      d_typing_gen mode_tc Γ (exp_abs e) C0.
Proof.
  intros Γ Δ T0 C0 Hs. dependent induction Hs; intros HΔ Lvar e Ahead Bhead m_orig HT0 HinhA HwfA Hbody Hdecr Hwfd; subst.
  - (* d_sub__check: LHS = syn_color T = typ_arrow Ahead Bhead. *)
    (* Mirror __check_gen mono-extraction chain. *)
    destruct T; simpl in HT0; try discriminate.
    inversion HT0; subst.
    assert (HmonoA : mono_typ (syn_color T1))
      by (eapply is_inh_typ_syn_color_mono_pre; eauto).
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H5 into Hcons1. rename H6 into Hcons2.
    (* Derive A = ctyp_arrow A1' A2' from H3 to expose A2 = inh_color A2',
       then apply d_consis_syn_inh_mono to Hcons2 for HmonoB.
       Do this BEFORE the HeqA2 subst that would consume A2. *)
    assert (HmonoB : mono_typ (syn_color T2)).
    { symmetry in H3. apply inh_color_eq_arrow_inv in H3.
      destruct H3 as [A1' [A2' [_ [_ HA2_eq]]]].
      (* HA2_eq : inh_color A2' = A2, so rewrite <- to replace A2 in Hcons2. *)
      rewrite <- HA2_eq in Hcons2.
      eapply d_consis_syn_inh_mono; exact Hcons2. }
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoA) Hcons1) as HeqA1.
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoB) Hcons2) as HeqA2.
    subst.
    pose proof (mono_typ_inh_color_erase HmonoA) as HeqA_inh.
    rewrite erase_syn_color in HeqA_inh.
    rewrite <- HeqA_inh at 1.
    (* Goal at this point: d_typing_gen mode_tc Γ (exp_abs e) (typ_arrow
       (syn_color T1) (syn_color T2)). We use HA2_eq (which after subst
       is syn_color T2 = inh_color A2') and HeqA_inh to map between
       inh_color and syn_color paintings. *)
    apply d_typing_gen__abs with (L := Lvar `union` dom Γ).
    + rewrite HeqA_inh. exact HwfA.
    + intros x0 Hx0.
      assert (Hwfd_x : d_wf_denv ((x0 ~ dbind_typ (syn_color T1)) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ (syn_color T1)) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_preserves_wf; eauto.
  - (* d_sub__forall_r: target = typ_all_col colour_inh A. Reconstruct
       via [d_typing_gen__forall] (value rule) + recursive IH at each X. *)
    apply d_typing_gen__forall with (L := L `union` Lvar `union` dom Γ).
    + apply is_value__abs.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      (* IH H0 takes: X, X∉L, then the same args as the lemma at (X∷Γ). *)
      eapply H0 with (Ahead := Ahead) (Bhead := Bhead) (m_orig := m_orig)
        (Lvar := Lvar); eauto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
  - (* d_sub__forall_l_tagged: LHS = typ_all_etag, contradicts typ_arrow. *)
    discriminate.
Qed.

(** [d_typing_abs_anno_value_to_subsumption_d_sub]: anno-variant
    companion. Same structure as the value variant's companion but
    with LHS [typ_arrow (syn_color_t Ahead) Bhead] and conclusion
    via [d_typing_gen__abs_anno]. No [is_inh_typ Ahead] precondition
    (mono on Ahead derived via [mono_typ_syn_color_t_inv]). *)
Lemma d_typing_abs_anno_value_to_subsumption_d_sub :
  forall Γ Δ T0 C0,
    d_sub mode_tc Δ Γ T0 C0 ->
    Δ = nil ->
    forall Lvar e Ahead Bhead m_orig,
      T0 = typ_arrow (syn_color_t Ahead) Bhead ->
      d_wf_typ Γ Ahead ->
      (forall x, x `notin` Lvar ->
         d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ Ahead) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      decr_mode m_orig = mode_ti ->
      d_wf_denv Γ ->
      d_typing_gen mode_tc Γ (exp_abs_anno Ahead e) C0.
Proof.
  intros Γ Δ T0 C0 Hs. dependent induction Hs;
    intros HΔ Lvar e Ahead Bhead m_orig HT0 HwfA Hbody Hdecr Hwfd; subst.
  - (* d_sub__check: parallel to anno helper's __check_gen case. *)
    destruct T; simpl in HT0; try discriminate.
    inversion HT0; subst.
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H6 into Hcons1. rename H7 into Hcons2.
    (* Derive mono via d_consis_syn_inh_mono (new helper). *)
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { symmetry in H4. apply inh_color_eq_arrow_inv in H4.
      destruct H4 as [A1' [_ [_ [HA1_eq _]]]].
      rewrite <- HA1_eq in Hcons1.
      eapply d_consis_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { symmetry in H4. apply inh_color_eq_arrow_inv in H4.
      destruct H4 as [_ [A2' [_ [_ HA2_eq]]]].
      rewrite <- HA2_eq in Hcons2.
      eapply d_consis_syn_inh_mono; exact Hcons2. }
    rename H2 into Heq_LHS.
    assert (HmonoA : mono_typ Ahead).
    { rewrite Heq_LHS in HmonoT1_syn.
      exact (mono_typ_syn_color_t_inv Ahead HmonoT1_syn). }
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in Heq_LHS.
    rewrite syn_color_t_syn_color_erase in Heq_LHS.
    rewrite !erase_syn_color in Heq_LHS.
    subst T1.
    rewrite <- (mono_typ_inh_color_erase HmonoA) at 1.
    apply d_typing_gen__abs_anno with (L := Lvar `union` dom Γ).
    + rewrite HsynA. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ Ahead) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ Ahead) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_preserves_wf; eauto.
  - (* d_sub__forall_r: recurse via IH. *)
    apply d_typing_gen__forall with (L := L `union` Lvar `union` dom Γ).
    + apply is_value__abs_anno.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      eapply H0 with (Ahead := Ahead) (Bhead := Bhead) (m_orig := m_orig)
        (Lvar := Lvar); eauto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
  - (* d_sub__forall_l_tagged: vacuous. *)
    discriminate.
Qed.

(** [is_inh_typ_inh_color]: any [inh_color C] for [C : ctyp] is
    [is_inh_typ] PROVIDED [d_wf_typ] (which rules out [ctyp_hole] /
    [ctyp_tophole] shapes). *)
Lemma is_inh_typ_inh_color : forall Γ C,
    d_wf_typ Γ (inh_color C) ->
    is_inh_typ (inh_color C).
Proof.
  intros Γ C Hwf. remember (inh_color C) as A in Hwf.
  revert C HeqA. induction Hwf; intros C HeqA.
  - destruct C; simpl in HeqA; try discriminate. apply is_inh_typ__unit.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_inh_typ__var.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_inh_typ__arrow.
    + eapply IHHwf1; reflexivity.
    + eapply IHHwf2; reflexivity.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst.
    inst_cofinites_for is_inh_typ__all.
    intros X HX.
    assert (HX' : X `notin` L) by fsetdec.
    rewrite <- inh_color_open_var.
    eapply H0; eauto.
    rewrite inh_color_open_var. reflexivity.
Qed.

(** [is_syn_typ_syn_color]: parallel to [is_inh_typ_inh_color] but for
    the [syn_color] painting. Same shape of proof. *)
Lemma is_syn_typ_syn_color : forall Γ C,
    d_wf_typ Γ (syn_color C) ->
    is_syn_typ (syn_color C).
Proof.
  intros Γ C Hwf. remember (syn_color C) as A in Hwf.
  revert C HeqA. induction Hwf; intros C HeqA.
  - destruct C; simpl in HeqA; try discriminate. apply is_syn_typ__unit.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_syn_typ__var.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_syn_typ__arrow.
    + eapply IHHwf1; reflexivity.
    + eapply IHHwf2; reflexivity.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst.
    inst_cofinites_for is_syn_typ__all.
    intros X HX.
    assert (HX' : X `notin` L) by fsetdec.
    rewrite <- syn_color_open_var.
    eapply H0; eauto.
    rewrite syn_color_open_var. reflexivity.
Qed.


(** [d_typing_abs_value_to_subsumption_split_d_sub]: d_sub companion
    for the SPLIT abs-value-to-subsumption helper. Parallels
    [d_typing_abs_anno_value_to_subsumption_d_sub] but:
    - LHS shape: [typ_arrow (inh_color_t Ahead) Bhead] (not
      [typ_arrow (syn_color_t Ahead) Bhead]).
    - Reconstruction via [d_typing_gen__abs] (not [__abs_anno]).

    [d_sub__check]'s LHS = [syn_color T] forces
    [syn_color T1 = inh_color_t Ahead], which is only satisfiable for
    Ahead mono (syn-painted on quantifiers vs inh-painted differ
    unless no quantifiers). Mono Ahead lets the binding [(x ~ Ahead)]
    coincide with the rule's [(x ~ syn_color A_rule)] for
    [A_rule := erase Ahead]. *)
Lemma d_typing_abs_value_to_subsumption_split_d_sub :
  forall Γ Δ T0 C0,
    d_sub mode_tc Δ Γ T0 C0 ->
    Δ = nil ->
    forall Lvar e Ahead Bhead m_orig,
      T0 = typ_arrow (inh_color_t Ahead) Bhead ->
      d_wf_typ Γ (inh_color_t Ahead) ->
      (forall x, x `notin` Lvar ->
         d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ Ahead) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      decr_mode m_orig = mode_ti ->
      d_wf_denv Γ ->
      d_typing_gen mode_tc Γ (exp_abs e) C0.
Proof.
  intros Γ Δ T0 C0 Hs. dependent induction Hs;
    intros HΔ Lvar e Ahead Bhead m_orig HT0 HwfA Hbody Hdecr Hwfd; subst.
  - (* d_sub__check: LHS = syn_color T = typ_arrow (inh_color_t Ahead) Bhead.
       Forces T = ctyp_arrow T1 T2, then syn_color T1 = inh_color_t Ahead. *)
    destruct T; simpl in HT0; try discriminate.
    inversion HT0; subst.
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H6 into Hcons1. rename H7 into Hcons2.
    (* Derive mono via d_consis_syn_inh_mono (post-refactor helper).
       The typ_arrow = inh_color A equation is in context (named H_eq
       via match); inh_color_eq_arrow_inv splits A. *)
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_syn_inh_mono; exact Hcons2. }
    rename H2 into Heq_LHS.
    (* Heq_LHS: syn_color T1 = inh_color_t Ahead. T1 mono ⇒ Ahead mono
       (since inh_color_t Ahead = inh_color (erase Ahead), and that's
       mono iff erase Ahead is colourless, iff Ahead is mono). *)
    assert (HmonoIH : mono_typ (inh_color_t Ahead))
      by (rewrite <- Heq_LHS; exact HmonoT1_syn).
    assert (HmonoA : mono_typ Ahead)
      by (apply mono_typ_inh_color_t_inv; exact HmonoIH).
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    (* HsynA: syn_color (erase Ahead) = Ahead.
       HinhA: inh_color (erase Ahead) = Ahead. *)
    (* Erase both sides of Heq_LHS to derive T1 = erase Ahead. *)
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs e) (typ_arrow (syn_color (erase Ahead)) (syn_color T2)).
       Rewrite syn_color (erase Ahead) ↦ inh_color (erase Ahead) (both = Ahead). *)
    rewrite HsynA.
    rewrite <- HinhA at 1.
    assert (HwfA_raw : d_wf_typ Γ Ahead).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    apply d_typing_gen__abs with (L := Lvar `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ Ahead) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ Ahead) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_preserves_wf; eauto.
  - (* d_sub__forall_r: recurse via IH. *)
    apply d_typing_gen__forall with (L := L `union` Lvar `union` dom Γ).
    + apply is_value__abs.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      eapply H0 with (Ahead := Ahead) (Bhead := Bhead) (m_orig := m_orig)
        (Lvar := Lvar); eauto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
  - (* d_sub__forall_l_tagged: vacuous (LHS not typ_arrow). *)
    discriminate.
Qed.

(** [d_typing_abs_value_to_subsumption_split]: abs value-to-subsumption
    helper with SPLIT binding/arrow-arg. Parallels
    [d_typing_abs_anno_value_to_subsumption] but for [exp_abs e] (not
    [exp_abs_anno A e]) with arrow arg [inh_color_t A] (not
    [syn_color_t A]). The split signature lets it apply at the D12
    __abs callsite where the rule's body binding is [syn_color A0]
    and the conclusion's arrow arg is [inh_color A0]. *)
Lemma d_typing_abs_value_to_subsumption_split :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ (inh_color_t A) ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_tc nil Γ (typ_arrow (inh_color_t A) B) C ->
    d_typing_gen mode_tc Γ (exp_abs e) C.
Proof.
  intros L Γ e A B m_orig C HwfA Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: dispatch to d_sub companion. *)
    eapply d_typing_abs_value_to_subsumption_split_d_sub
      with (Ahead := A) (Bhead := B) (m_orig := m_orig); eauto.
  - (* __check_gen: LHS = syn_color T forces T = ctyp_arrow T1 T2,
       then syn_color T1 = inh_color_t A — only satisfiable for A mono. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H6 into Hcons1. rename H7 into Hcons2.
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons2. }
    match goal with H : syn_color T1 = inh_color_t A |- _ =>
      rename H into Heq_LHS
    end.
    assert (HmonoIH : mono_typ (inh_color_t A))
      by (rewrite <- Heq_LHS; exact HmonoT1_syn).
    assert (HmonoA : mono_typ A)
      by (apply mono_typ_inh_color_t_inv; exact HmonoIH).
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    rewrite HsynA.
    rewrite <- HinhA at 1.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_gen_preserves_wf; eauto.
  - (* __refl_mono: target = typ_arrow (inh_color_t A) B forced mono. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmIH : mono_typ (inh_color_t A) |- _ =>
      assert (HmonoA : mono_typ A)
        by (apply mono_typ_inh_color_t_inv; auto)
    end.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- (mono_typ_inh_color_erase HmonoA).
      rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    rewrite inh_color_t_inh_color_erase.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite (mono_typ_inh_color_erase HmonoA). assumption.
    + intros x Hx.
      assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      rewrite (mono_typ_syn_color_erase HmonoA).
      apply d_typing_gen_lift_mono with (A := B); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
        -- rewrite_env ((x ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           match goal with H1 : d_wf_typ Γ (typ_arrow _ _) |- _ =>
             inversion H1; subst; assumption
           end.
  - (* __forall_r: target = typ_all_col colour_inh A_target. Recurse via
       [d_typing_gen__forall] + IH at each X. *)
    apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      apply H0 with (A := A) (B := B); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
Qed.

(** [d_typing_abs_value_to_subsumption_split_ti]: mode_ti variant of the
    SPLIT abs helper. Same shape, but Hsub_gen / conclusion at mode_ti
    (not mode_tc). At mode_ti, d_sub_gen rules are only __embed,
    __infer_gen, __refl_mono — no __forall_r recursion.

    Strengthened signature: added [d_wf_typ Γ B] premise so that the
    __embed/__infer_gen cases can derive [is_syn_typ (syn_color T2)]
    from [B = syn_color T2] (forced by [d_sub__infer]) + the wf premise.
    Without this strengthening, the LHS-rigidity lemma would need an
    inductive helper that fails on the [d_consis_gen__forall_syn] case. *)
Lemma d_typing_abs_value_to_subsumption_split_ti :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ (inh_color_t A) ->
    d_wf_typ Γ B ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_ti nil Γ (typ_arrow (inh_color_t A) B) C ->
    d_typing_gen mode_ti Γ (exp_abs e) C.
Proof.
  intros L Γ e A B m_orig C HwfA HwfB Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: d_sub mode_ti, only d_sub__infer applies. *)
    rename H into Hdsub. dependent destruction Hdsub.
    (* d_sub__infer: LHS = syn_color T, forces typ_arrow shape. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    match goal with H : syn_color T1 = inh_color_t A |- _ =>
      rename H into Heq_LHS
    end.
    (* Derive A mono from the equation [syn_color T1 = inh_color_t A]
       (rules out [typ_all_*] colour-mismatch + [hole]/[tophole] via wf). *)
    assert (HmonoA : mono_typ A).
    { symmetry in Heq_LHS. eapply inh_color_t_eq_syn_color_mono; eauto. }
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    (* Rigidity: derive [syn_color T2 = syn_color A2] from Hcons2 +
       [HwfB] giving [is_syn_typ (syn_color T2)] via [is_syn_typ_syn_color]
       (B = syn_color T2 after [inversion x; subst]). *)
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    assert (HwfsynA : d_wf_typ Γ (syn_color (erase A))).
    { rewrite HsynA. assumption. }
    assert (HsynT1 : is_syn_typ (syn_color (erase A)))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2 : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_lhs_syn_eq HsynT1 Hcons1) as HeqA1.
    pose proof (d_consis_lhs_syn_eq HsynT2 Hcons2) as HeqA2.
    subst.
    rewrite HsynA.
    rewrite <- HinhA at 1.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      (* Body Hbody already at mode_ti (decr_mode m_orig = mode_ti) with
         binding [(x ~ dbind_typ A) ++ Γ] and conclusion B = syn_color T2;
         no lift needed. *)
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __infer_gen: parallel to __embed __infer, with d_consis_gen. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis_gen _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis_gen _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis_gen _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    match goal with H : syn_color T1 = inh_color_t A |- _ =>
      rename H into Heq_LHS
    end.
    assert (HmonoA : mono_typ A).
    { symmetry in Heq_LHS. eapply inh_color_t_eq_syn_color_mono; eauto. }
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    assert (HwfsynA : d_wf_typ Γ (syn_color (erase A))).
    { rewrite HsynA. assumption. }
    assert (HsynT1 : is_syn_typ (syn_color (erase A)))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2 : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_gen_lhs_syn_eq HsynT1 Hcons1) as HeqA1.
    pose proof (d_consis_gen_lhs_syn_eq HsynT2 Hcons2) as HeqA2.
    subst.
    rewrite HsynA.
    rewrite <- HinhA at 1.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __refl_mono: target = typ_arrow (inh_color_t A) B forced mono. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmIH : mono_typ (inh_color_t A) |- _ =>
      assert (HmonoA : mono_typ A)
        by (apply mono_typ_inh_color_t_inv; auto)
    end.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- (mono_typ_inh_color_erase HmonoA).
      rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    rewrite inh_color_t_inh_color_erase.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite (mono_typ_inh_color_erase HmonoA). assumption.
    + intros x Hx.
      rewrite (mono_typ_syn_color_erase HmonoA).
      (* Body Hbody at mode_ti, binding (x ~ dbind_typ A), conclusion B;
         direct application — lift_mono would be a no-op. *)
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
Qed.

(** [d_typing_abs_anno_value_to_subsumption_split_d_sub]: d_sub
    companion for the SPLIT abs_anno helper. Conclusion's term is
    [exp_abs_anno (inh_color_t Ahead) e] to match the rule's
    [exp_abs_anno (inh_color A_rule) e] for [A_rule = erase Ahead]
    (in the mono case, [inh_color (erase Ahead) = inh_color_t Ahead]
    via [inh_color_t_inh_color_erase]). *)
Lemma d_typing_abs_anno_value_to_subsumption_split_d_sub :
  forall Γ Δ T0 C0,
    d_sub mode_tc Δ Γ T0 C0 ->
    Δ = nil ->
    forall Lvar e Ahead Bhead m_orig,
      T0 = typ_arrow Ahead Bhead ->
      d_wf_typ Γ Ahead ->
      (forall x, x `notin` Lvar ->
         d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ Ahead) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      decr_mode m_orig = mode_ti ->
      d_wf_denv Γ ->
      d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t Ahead) e) C0.
Proof.
  intros Γ Δ T0 C0 Hs. dependent induction Hs;
    intros HΔ Lvar e Ahead Bhead m_orig HT0 HwfA Hbody Hdecr Hwfd; subst.
  - (* d_sub__check: LHS = syn_color T = typ_arrow Ahead Bhead.
       After `inversion HT0; subst`, Ahead gets substituted with syn_color T1
       (and Bhead with syn_color T2). Work with syn_color T1 / T2 directly. *)
    destruct T; simpl in HT0; try discriminate.
    inversion HT0; subst.
    match goal with H : d_consis _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_syn_inh_mono; exact Hcons2. }
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t (syn_color T1)) e)
              (typ_arrow (syn_color T1) (syn_color T2)).
       Simplify: inh_color_t (syn_color T1) = inh_color T1
       (via inh_color_t_inh_color_erase + erase_syn_color).
       Apply d_typing_gen__abs_anno with A_rule := T1. *)
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := Lvar `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ (syn_color T1)) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ (syn_color T1)) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_preserves_wf; eauto.
  - (* d_sub__forall_r: recurse via IH. *)
    apply d_typing_gen__forall with (L := L `union` Lvar `union` dom Γ).
    + apply is_value__abs_anno.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      eapply H0 with (Ahead := Ahead) (Bhead := Bhead) (m_orig := m_orig)
        (Lvar := Lvar); eauto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
  - (* d_sub__forall_l_tagged: vacuous (LHS not typ_arrow). *)
    discriminate.
Qed.

(** [d_typing_abs_anno_value_to_subsumption_split]: SPLIT abs_anno
    helper. Conclusion's term is [exp_abs_anno (inh_color_t A) e]. *)
Lemma d_typing_abs_anno_value_to_subsumption_split :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_tc nil Γ (typ_arrow A B) C ->
    d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t A) e) C.
Proof.
  intros L Γ e A B m_orig C HwfA Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: dispatch to d_sub companion. *)
    eapply d_typing_abs_anno_value_to_subsumption_split_d_sub
      with (Ahead := A) (Bhead := B) (m_orig := m_orig); eauto.
  - (* __check_gen: parallel to _d_sub __check. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis_gen _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis_gen _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis_gen _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons2. }
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t (syn_color T1)) e)
              (typ_arrow (syn_color T1) (syn_color T2)). *)
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ (syn_color T1)) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ (syn_color T1)) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_gen_preserves_wf; eauto.
  - (* __refl_mono: target = typ_arrow A B forced mono. Reconstruct via
       d_typing_gen__abs_anno with A_rule := erase A; the rule produces
       term [exp_abs_anno (inh_color (erase A)) e] and conclusion arg
       [syn_color (erase A)]. For mono A: inh_color (erase A) = A and
       syn_color (erase A) = A; also inh_color_t A = inh_color (erase A)
       via inh_color_t_inh_color_erase. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmA : mono_typ A |- _ => rename HmA into HmonoA end.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t A) e) (typ_arrow A B). *)
    replace (inh_color_t A) with (inh_color (erase A))
      by (symmetry; apply inh_color_t_inh_color_erase).
    rewrite <- HsynA at 2.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + rewrite HsynA. assumption.
    + intros x Hx.
      assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      rewrite HsynA.
      apply d_typing_gen_lift_mono with (A := B); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
        -- rewrite_env ((x ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           match goal with H1 : d_wf_typ Γ (typ_arrow _ _) |- _ =>
             inversion H1; subst; assumption
           end.
  - (* __forall_r: recurse via IH. *)
    apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs_anno.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      apply H0 with (A := A) (B := B); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
Qed.

(** [d_typing_abs_anno_value_to_subsumption_split_ti]: mode_ti variant of
    the SPLIT abs_anno helper. Strengthened with [d_wf_typ Γ B] premise
    (used to derive [is_syn_typ (syn_color T2)] in __embed/__infer_gen). *)
Lemma d_typing_abs_anno_value_to_subsumption_split_ti :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ A ->
    d_wf_typ Γ B ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_ti nil Γ (typ_arrow A B) C ->
    d_typing_gen mode_ti Γ (exp_abs_anno (inh_color_t A) e) C.
Proof.
  intros L Γ e A B m_orig C HwfA HwfB Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: d_sub mode_ti, only d_sub__infer applies. *)
    rename H into Hdsub. dependent destruction Hdsub.
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HsynT1' : is_syn_typ (syn_color T1))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2' : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_lhs_syn_eq HsynT1' Hcons1) as HeqA1.
    pose proof (d_consis_lhs_syn_eq HsynT2' Hcons2) as HeqA2.
    subst.
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __infer_gen: parallel to __embed __infer with d_consis_gen. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis_gen _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis_gen _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis_gen _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HsynT1 : is_syn_typ (syn_color T1))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2 : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_gen_lhs_syn_eq HsynT1 Hcons1) as HeqA1.
    pose proof (d_consis_gen_lhs_syn_eq HsynT2 Hcons2) as HeqA2.
    subst.
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __refl_mono: target = typ_arrow A B forced mono. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmA : mono_typ A |- _ => rename HmA into HmonoA end.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    replace (inh_color_t A) with (inh_color (erase A))
      by (symmetry; apply inh_color_t_inh_color_erase).
    rewrite <- HsynA at 2.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + rewrite HsynA. assumption.
    + intros x Hx.
      rewrite HsynA.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
Qed.

(** Mono-extraction helpers (used in __check_gen closure). *)

Lemma is_inh_typ_syn_color_mono : forall A C,
    is_inh_typ A ->
    A = syn_color C ->
    mono_typ A.
Proof.
  intros A C Hinh. revert C. induction Hinh; intros C HC.
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - destruct C; simpl in HC; inversion HC; subst.
    apply mono_typ__arrow.
    + eapply IHHinh1; reflexivity.
    + eapply IHHinh2; reflexivity.
  - (* A = typ_all_col colour_inh A_inner; syn_color C never has
       colour_inh at head — destructed C is ctyp_all giving
       colour_syn. Contradiction. *)
    destruct C; simpl in HC; discriminate.
Qed.

Lemma d_consis_gen_LHS_syn_color_mono : forall Δ Γ T A,
    d_consis_gen Δ Γ T A ->
    forall C, T = syn_color C ->
    mono_typ T.
Proof.
  intros Δ Γ T A Hc. induction Hc; intros C HC.
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - destruct C; simpl in HC; discriminate.
  - destruct C; simpl in HC; discriminate.
  - (* __forall_syn (post-refactor): T = typ_all_col colour_syn _ =
       syn_color (ctyp_all _). T is NOT mono. Lemma is FALSE here. *)
    admit.
  - destruct C; simpl in HC; discriminate.
  - destruct C; simpl in HC; try discriminate.
    inversion HC; subst.
    apply mono_typ__arrow.
    + eapply IHHc1; reflexivity.
    + eapply IHHc2; reflexivity.
Admitted.

(** [d_typing_abs_value_to_forall]: when Hty = __abs (a value), lifting
    to typ_all_col colour_inh via __forall_r requires nested recursion
    on the per-X premise.

    Stronger form: take an arbitrary [C] with [d_sub_gen mode_tc nil Γ
    (typ_arrow A B) C], so dependent induction on the d_sub_gen
    handles all target shapes (including nested [typ_all_col]). *)
Lemma d_typing_abs_value_to_subsumption :
  forall L Γ e A B m_orig C,
    is_inh_typ A ->
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_tc nil Γ (typ_arrow A B) C ->
    d_typing_gen mode_tc Γ (exp_abs e) C.
Proof.
  intros L Γ e A B m_orig C HinhA HwfA Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: route through [d_typing_abs_value_to_subsumption_d_sub]
       which inducts on the inner d_sub directly (so __forall_r recurses
       naturally). *)
    eapply d_typing_abs_value_to_subsumption_d_sub with
      (Ahead := A) (Bhead := B) (m_orig := m_orig); eauto.
  - (* __check_gen: T : ctyp with syn_color T = typ_arrow A B forces
       T = ctyp_arrow T1 T2, A = syn_color T1, B = syn_color T2.
       From [HinhA: is_inh_typ A] + syn-LHS ⟹ A mono.
       From inner d_consis_gen on syn LHS ⟹ T1, T2 mono.
       Then mirror __refl_mono with derived mono witnesses. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    (* A = syn_color T1, B = syn_color T2 now. *)
    assert (HmonoA : mono_typ (syn_color T1))
      by (eapply is_inh_typ_syn_color_mono; eauto).
    (* H0 : d_consis_gen nil Γ (typ_arrow (syn_color T1) (syn_color T2))
              (inh_color A0).  Inversion forces __arrow. *)
    inversion H0; subst.
    (* H6: d_consis_gen Δ1 Γ (syn_color T1) A1
       H7: d_consis_gen Δ2 Γ (syn_color T2) A2
       H1: Δ1 ++ Δ2 = nil
       Goal: d_typing_gen mode_tc Γ (exp_abs e) (typ_arrow A1 A2). *)
    apply app_eq_nil in H1. destruct H1 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    assert (HmonoB : mono_typ (syn_color T2))
      by (eapply d_consis_gen_LHS_syn_color_mono; eauto).
    (* By d_consis_gen_lhs_syn_eq, syn_color T1 = A1 and syn_color T2 = A2. *)
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoA) H6) as HeqA1.
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoB) H7) as HeqA2.
    subst A1 A2.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs e)
              (typ_arrow (syn_color T1) (syn_color T2)). *)
    (* Mirror __refl_mono: rewrite syn_color T1 ↦ inh_color T1 via the
       mono pinning [mono_typ (syn_color T1) ⇒ inh_color (erase (syn_color T1)) = syn_color T1
       ⇒ inh_color T1 = syn_color T1 (via erase_syn_color)]. *)
    pose proof (mono_typ_inh_color_erase HmonoA) as HeqA_inh.
    rewrite erase_syn_color in HeqA_inh.
    (* HeqA_inh : inh_color T1 = syn_color T1. *)
    rewrite <- HeqA_inh at 1.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite HeqA_inh. exact HwfA.
    + intros x0 Hx0.
      assert (Hwfd_x : d_wf_denv ((x0 ~ dbind_typ (syn_color T1)) ++ Γ)).
      { apply d_wf_denv__typ; auto. }
      (* Goal: d_typing_gen mode_tc ((x0:syn_color T1)∷Γ) (open e x0)
                (syn_color T2). *)
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ (syn_color T1)) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_gen_preserves_wf; eauto.
  - (* __refl_mono: target = typ_arrow A B forced mono ⇒ mono A and
       mono B. The ctyp base for [d_typing_gen__abs] is [erase A]; for
       mono A, [inh_color (erase A) = syn_color (erase A) = A], so the
       rule's body binding [(x ~ syn_color (erase A))] coincides with
       the lemma's [(x ~ A)]. Body lift from (decr_mode m_orig = mode_ti)
       to mode_tc via [d_typing_gen_lift_mono] (Qed except its __app
       case, which is the canonical mono-arg gap). *)
    match goal with Hm : mono_typ (typ_arrow A B) |- _ =>
      assert (HmonoA : mono_typ A) by (inversion Hm; auto);
      assert (HmonoB : mono_typ B) by (inversion Hm; auto)
    end.
    rewrite <- (mono_typ_inh_color_erase HmonoA) at 1.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite (mono_typ_inh_color_erase HmonoA). assumption.
    + intros x Hx.
      assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      rewrite (mono_typ_syn_color_erase HmonoA).
      apply d_typing_gen_lift_mono with (A := B); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
        -- rewrite_env ((x ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           match goal with Hw : d_wf_typ Γ (typ_arrow A B) |- _ =>
             inversion Hw; assumption
           end.
  - (* __forall_r: target = typ_all_col colour_inh A_target. Reconstruct
       via [d_typing_gen__forall] (value rule) + recursive IH at each X.
       The dependent-induction IH [H0] takes the body-sub at each X plus
       the helper's other premises threaded under the [(X ~ dbind_tvar)
       ++ Γ] extension; we supply those via weakening. *)
    apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      apply (H0 X ltac:(auto) Hwfd_X Hdecr B A); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
Qed.

(** [d_typing_abs_anno_value_to_subsumption]: same structure as
    [d_typing_abs_value_to_subsumption] but for [exp_abs_anno A e].
    The d_sub_gen __forall_r case recurses; __embed and __refl_any
    inherit the same circularity obstacle (body lift from
    [decr_mode m_orig] to [mode_tc]). *)
Lemma d_typing_abs_anno_value_to_subsumption :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_tc nil Γ (typ_arrow (syn_color_t A) B) C ->
    d_typing_gen mode_tc Γ (exp_abs_anno A e) C.
Proof.
  intros L Γ e A B m_orig C HwfA Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: invert the wrapped d_sub and handle __check / __forall_r. *)
    rename H into Hsub.
    inversion Hsub; subst.
    + (* d_sub__check: T : ctyp with syn_color T = typ_arrow (syn_color_t A) B
         forces T = ctyp_arrow T1 T2. *)
      destruct T; simpl in H; try discriminate.
      inversion H; subst.
      (* Now H : syn_color T1 = syn_color_t A (and syn_color T2 = B). *)
      rename H1 into Hcons.
      inversion Hcons; subst.
      apply app_eq_nil in H1. destruct H1 as [HΔ1 HΔ2]. subst Δ1 Δ2.
      rename H7 into Hcons1. rename H8 into Hcons2.
      assert (HmonoT1_syn : mono_typ (syn_color T1)).
      { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
          symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
          destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
          rewrite <- HA1_eq in Hcons1
        end.
        eapply d_consis_syn_inh_mono; exact Hcons1. }
      assert (HmonoT2_syn : mono_typ (syn_color T2)).
      { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
          symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
          destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
          rewrite <- HA2_eq in Hcons2
        end.
        eapply d_consis_syn_inh_mono; exact Hcons2. }
      (* H3: syn_color T1 = syn_color_t A. With T1 mono → A mono. *)
      rename H3 into Heq_LHS.
      assert (HmonoA : mono_typ A).
      { apply mono_typ_syn_color_t_inv.
        rewrite <- Heq_LHS. exact HmonoT1_syn. }
      pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
        as HeqA2.
      pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
        as HeqA1.
      subst.
      pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
      pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
      apply (f_equal erase) in Heq_LHS.
      rewrite syn_color_t_syn_color_erase in Heq_LHS.
      rewrite !erase_syn_color in Heq_LHS.
      subst T1.
      (* Goal: typ_arrow (syn_color (erase A)) (syn_color T2). *)
      rewrite <- (mono_typ_inh_color_erase HmonoA) at 1.
      apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
      * rewrite HsynA. exact HwfA.
      * intros x Hx.
        rewrite HsynA.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ))
          by (apply d_wf_denv__typ; auto).
        apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
        -- rewrite <- Hdecr. apply Hbody. auto.
        -- apply d_sub_gen_refl; auto.
           ++ apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
           ++ rewrite_env ((x ~ dbind_typ A) ++ Γ).
              apply d_wf_typ_weakening_head.
              eapply d_consis_preserves_wf; eauto.
    + (* d_sub__forall_r: route through anno-variant companion which
         recurses on the inner d_sub. *)
      eapply d_typing_abs_anno_value_to_subsumption_d_sub
        with (Ahead := A) (Bhead := B) (m_orig := m_orig); eauto.
  - (* __check_gen: T : ctyp with syn_color T = typ_arrow (syn_color_t A) B.
       Same mono extraction as the __embed __check sub-case above. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H6 into Hcons1. rename H7 into Hcons2.
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons2. }
    assert (HmonoA : mono_typ A).
    { rewrite H2 in HmonoT1_syn.
      exact (mono_typ_syn_color_t_inv A HmonoT1_syn). }
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in H2.
    rewrite syn_color_t_syn_color_erase in H2.
    rewrite !erase_syn_color in H2.
    subst T1.
    (* Goal: typ_arrow (syn_color (erase A)) (syn_color T2). *)
    rewrite <- (mono_typ_inh_color_erase HmonoA) at 1.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + rewrite HsynA. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_gen_preserves_wf; eauto.
  - (* __refl_mono: target = typ_arrow (syn_color_t A) B forced mono.
       From [mono_typ_syn_color_t_inv] we recover mono A; the [ctyp]
       base for [d_typing_gen__abs_anno] is [erase A], with conclusion
       arg [syn_color (erase A) = syn_color_t A] (via
       [syn_color_t_syn_color_erase]). For mono A the body's
       [(x ~ A)] matches the rule's [(x ~ syn_color (erase A))] via
       [mono_typ_syn_color_erase]. Body lift mode_ti → mode_tc via
       [d_typing_gen_lift_mono] (Qed except __app). *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmsA : mono_typ (syn_color_t A) |- _ =>
      assert (HmonoA : mono_typ A)
        by (apply mono_typ_syn_color_t_inv; auto)
    end.
    rewrite syn_color_t_syn_color_erase.
    rewrite <- (mono_typ_inh_color_erase HmonoA) at 1.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + rewrite (mono_typ_syn_color_erase HmonoA). assumption.
    + intros x Hx.
      assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      rewrite (mono_typ_syn_color_erase HmonoA).
      apply d_typing_gen_lift_mono with (A := B); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
        -- rewrite_env ((x ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           match goal with HwfA' : d_wf_typ Γ (typ_arrow _ _) |- _ =>
             inversion HwfA'; assumption
           end.
  - (* __forall_r: target = typ_all_col colour_inh A_target. Reconstruct
       via [d_typing_gen__forall] (value rule) + recursive IH at each X.
       [exp_abs_anno A e] is_value when [e] is — but the rule requires
       only [is_value (exp_abs_anno A e)], which holds unconditionally. *)
    apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs_anno.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      apply H0 with (A := A) (B := B); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
Qed.
