(** Auxiliary facts for declarative general subsumption, stated over the
    current split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.
From Hammer Require Export Tactics.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.typing.prop_weakening.
Require Import src.frost.decl.typing.def_gen.

Set Implicit Arguments.

Ltac nbauto := try sauto limit:30.

Lemma d_consis_gen_weakening : forall Γ1 Γ2 Γ3 Δ D1 D2,
    Δ ⨟ (Γ1 ++ Γ3) ⊨ᵍ D1 ≈ D2 ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊨ᵍ D1 ≈ D2.
Proof.
  intros Γ1 Γ2 Γ3 Δ D1 D2 H.
  dependent induction H; nbauto.
  - apply d_consis_gen__var.
    eapply binds_weaken; eauto.
  - apply d_consis_gen__arrow; nbauto.
  - apply d_consis_gen__forall_tag_inh with
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); nbauto.
    + intros X HX.
      rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
      eapply H0; eauto.
  - apply d_consis_gen__forall_syn_inh  with 
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); nbauto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_tag_syn with
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_syn with
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_tag_syn_erasure with
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_inh with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
Qed.

Lemma d_consis_gen_weakening_head : forall Γ Γ' Δ B1 B2,
    Δ ⨟ Γ ⊨ᵍ B1 ≈ B2 ->
    Δ ⨟ (Γ' ++ Γ) ⊨ᵍ B1 ≈ B2.
Proof.
  intros Γ Γ' Δ B1 B2 H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_consis_gen_weakening. simpl. exact H.
Qed.

Lemma d_sub_gen_weakening : forall Γ1 Γ2 Γ3 m Δ B1 B2,
    Δ ⨟ (Γ1 ++ Γ3) ⊢ᵍ[ m ] B1 ⊑ B2 ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ᵍ[ m ] B1 ⊑ B2.
Proof.
  intros Γ1 Γ2 Γ3 m Δ B1 B2 H.
  dependent induction H; try sauto limit:30 use:d_consis_weakening, d_consis_gen_weakening.
  - apply d_sub_gen__infer_gen; nbauto.
    + apply d_consis_weakening; nbauto.
  - apply d_sub_gen__check_gen; nbauto.
    + apply d_consis_weakening; nbauto.
  - apply d_sub_gen__forall_r with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); nbauto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3); nbauto.
    eapply H1; eauto.
  - apply d_sub_gen__arg.
    + apply d_consis_weakening. exact H.
    + eapply IHd_sub_gen; eauto.
    + exact H1.
  - apply d_sub_gen__forall_l_tagged with (Δ' := Δ') (ph := ph); nbauto.
    + apply d_wf_utyp_weakening. exact H1.
  - apply d_sub_gen__forall_l_untagged with (Δ' := Δ') (ph := ph); nbauto.
    + apply d_wf_utyp_weakening. exact H1.
Qed.

Lemma d_sub_gen_weakening_head : forall Γ Γ' m Δ D1 D2,
    Δ ⨟ Γ ⊢ᵍ[ m ] D1 ⊑ D2 ->
    Δ ⨟ (Γ' ++ Γ) ⊢ᵍ[ m ] D1 ⊑ D2.
Proof.
  intros Γ Γ' m Δ D1 D2 H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_sub_gen_weakening. simpl. exact H.
Qed.

Lemma d_consis_gen_trans : forall Δa Δb Γ D1 D2 B,
    Δa ⨟ Γ ⊨ᵍ D1 ≈ D2 ->
    Δb ⨟ Γ ⊨ᵍ D2 ≈ (btyp_to_gutyp B) ->
    list_disjoint Δa Δb ->
    (Δa ++ Δb) ⨟ Γ ⊨ᵍ D1 ≈ (btyp_to_gutyp B).
Proof.
  intros* H. revert B Δb. induction H; intros; nbauto.
  - dependent destruction H2; nbauto. rewrite <- x.
    econstructor; nbauto.
    assert (exists B1, btyp_to_gutyp B1 = G1'0) as [B1 IHB1] by admit.
    assert (exists B2, btyp_to_gutyp B2 = G2'0) as [B2 IHB2] by admit.
    rewrite <- IHB1 in *.
    admit. admit.
  - admit.
  - admit.
  -
Admitted.
Lemma d_consis_gen_refl_btyp : forall Γ B,
    Γ ⊢ᵦ B ->
    nil ⨟ Γ ⊨ᵍ (btyp_to_gutyp B) ≈ (btyp_to_gutyp B).
Proof.
  intros Γ B Hwf.
  dependent induction Hwf.
  - apply d_consis_gen__unit.
  - apply d_consis_gen__var. exact H.
  - simpl. replace (@nil atom) with (@nil atom ++ @nil atom) by reflexivity.
    apply d_consis_gen__arrow.
    + exact IHHwf1.
    + exact IHHwf2.
    + apply list_disjoint_nil_l.
  - simpl. apply d_consis_gen__forall_syn with (L := L).
    intros X HX.
    change (gutyp_var_f X) with (btyp_to_gutyp (btyp_var_f X)).
    repeat rewrite <- btyp_to_gutyp_open.
    apply H0. exact HX.
  - simpl. apply d_consis_gen__forall_inh with (L := L).
    intros X HX.
    change (gutyp_var_f X) with (btyp_to_gutyp (btyp_var_f X)).
    repeat rewrite <- btyp_to_gutyp_open.
    apply H0. exact HX.
Qed.

Lemma d_consis_gen_refl_styp_as_utyp : forall Γ B,
    Γ ⊢ᵦ B ->
    is_styp B ->
    nil ⨟ Γ ⊨ᵍ (utyp_to_gutyp (btyp_to_utyp_syn B)) ≈ (btyp_to_gutyp B).
Proof.
  intros Γ B Hwf Hst.
  generalize dependent Hst.
  dependent induction Hwf; intros Hst; inversion Hst; subst; simpl.
  - apply d_consis_gen__unit.
  - apply d_consis_gen__var. exact H.
  - replace (@nil atom) with (@nil atom ++ @nil atom) by reflexivity.
    apply d_consis_gen__arrow.
    + apply IHHwf1. exact H1.
    + apply IHHwf2. exact H2.
    + apply list_disjoint_nil_l.
  - apply d_consis_gen__forall_syn with (L := L `union` L0).
    intros X HX.
    change (gutyp_var_f X) with (utyp_to_gutyp (utyp_var_f X)).
    rewrite <- utyp_to_gutyp_open.
    change (utyp_var_f X) with (btyp_to_utyp_syn (btyp_var_f X)).
    rewrite <- btyp_to_utyp_syn_open.
    replace (open_gutyp_wrt_gutyp (btyp_to_gutyp B)
               (utyp_to_gutyp (btyp_to_utyp_syn (btyp_var_f X))))
      with (btyp_to_gutyp (open_btyp_wrt_btyp B (btyp_var_f X))).
    apply H0; auto.
    change (gutyp_var_f X) with (btyp_to_gutyp (btyp_var_f X)).
    simpl.
    apply btyp_to_gutyp_open.
Qed.

(** Paper B.2, native split form for a synthesized middle type. *)
Lemma d_consis_compose : forall Δa Δb Γ C A B,
    Δa ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    Δb ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B ->
    list_disjoint Δa Δb ->
    exists Δc, Permutation Δc (Δa ++ Δb) /\ Δc ⨟ Γ ⊨ C ≈ B.
Proof.
Admitted.

Lemma d_sub_gen_refl_styp_ti : forall Γ B,
    Γ ⊢ᵦ B ->
    is_styp B ->
    nil ⨟ Γ ⊢ᵍ[ mode_ti ] (utyp_to_gutyp (btyp_to_utyp_syn B)) ⊑ B.
Proof.
  intros Γ B Hwf Hst.
  apply d_sub_gen__infer_gen.
  - apply d_consis_gen_refl_styp_as_utyp; auto.
  - exact Hst.
Qed.

Lemma d_sub_gen_trans_ti_lhs : forall Γ B1 B2 B3 m2,
    Γ ⊢ᵦ B2 ->
    nil ⨟ Γ ⊢ᵍ[ mode_ti ] B1 ⊑ B2 ->
    nil ⨟ Γ ⊢ᵍ[ m2 ] (btyp_to_gutyp B2) ⊑ B3 ->
    nil ⨟ Γ ⊢ᵍ[ m2 ] B1 ⊑ B3.
Proof.
  intros Γ B1 B2 B3 m2 HwfB2 Hsub12 Hsub23.
  dependent destruction Hsub12.
  dependent destruction Hsub23.
  - apply d_sub_gen__infer_gen.
    + dependent destruction H.
      dependent destruction H0; try discriminate.
      * apply d_consis_gen__unit.
      * apply d_consis_gen__var. exact H.
      * apply d_consis_gen__arrow.
        -- admit.
        -- admit.
        -- apply list_disjoint_nil_l.
      * admit.
    + exact H1.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.

Lemma d_sub_gen_trans : forall m1 Γ B1 B2 B3 m2,
    nil ⨟ Γ ⊢ᵍ[ m1 ] B1 ⊑ B2 ->
    nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ] (btyp_to_gutyp B2) ⊑ B3 ->
    nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ] B1 ⊑ B3.
Proof.
  (** Closing this lemma now requires native generalized
      consistency/subtyping composition over [gutyp], especially through
      [Arg] and [ForallL].  The old shortcut through ordinary [d_sub]
      was removed because it was not a paper rule. *)
Admitted.
