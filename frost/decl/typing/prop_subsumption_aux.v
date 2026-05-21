(** Auxiliary facts for declarative general subsumption, stated over the
    current split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

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

Lemma d_consis_gen_weakening : forall Γ1 Γ2 Γ3 Δ B1 B2,
    Δ ⨟ (Γ1 ++ Γ3) ⊨ᵍ B1 ≈ B2 ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊨ᵍ B1 ≈ B2.
Proof.
  intros Γ1 Γ2 Γ3 Δ B1 B2 H.
  dependent induction H.
  - apply d_consis_gen__unit.
  - apply d_consis_gen__var.
    eapply binds_weaken; eauto.
  - apply d_consis_gen__arrow.
    + eapply IHd_consis_gen1; eauto.
    + eapply IHd_consis_gen2; eauto.
    + exact H1.
  - apply d_consis_gen__forall_tag_inh with
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    + intros X HX.
      rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
      eapply H0; eauto.
    + exact H1.
  - apply d_consis_gen__forall_tag_syn with
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_tag_syn_erasure with
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_syn with
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
  dependent induction H.
  - apply d_sub_gen__infer_gen.
    + apply d_consis_gen_weakening. exact H.
    + exact H0.
  - apply d_sub_gen__check_gen.
    + exact H.
    + apply d_consis_gen_weakening. exact H0.
    + exact H1.
  - apply d_sub_gen__forall_r with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_sub_gen__arg.
    + apply d_consis_gen_weakening. exact H.
    + eapply IHd_sub_gen; eauto.
    + exact H1.
  - apply d_sub_gen__forall_l_tagged with (Δ' := Δ') (ph := ph).
    + exact H.
    + exact H0.
    + apply d_wf_utyp_weakening. exact H1.
    + exact H2.
    + eapply IHd_sub_gen; eauto.
  - apply d_sub_gen__forall_l_untagged with (Δ' := Δ') (ph := ph).
    + exact H.
    + exact H0.
    + apply d_wf_utyp_weakening. exact H1.
    + exact H2.
    + eapply IHd_sub_gen; eauto.
Qed.

Lemma d_sub_gen_weakening_head : forall Γ Γ' m Δ B1 B2,
    Δ ⨟ Γ ⊢ᵍ[ m ] B1 ⊑ B2 ->
    Δ ⨟ (Γ' ++ Γ) ⊢ᵍ[ m ] B1 ⊑ B2.
Proof.
  intros Γ Γ' m Δ B1 B2 H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_sub_gen_weakening. simpl. exact H.
Qed.

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
