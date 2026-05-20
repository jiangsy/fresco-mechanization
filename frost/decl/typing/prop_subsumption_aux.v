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
  - apply d_consis_gen__embed.
    apply d_consis_weakening. exact H.
  - apply d_consis_gen__forall_inh with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__refl_plain.
    apply d_wf_ptyp_weakening. exact H.
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
  - apply d_sub_gen__embed.
    apply d_sub_weakening. exact H.
  - apply d_sub_gen__infer_gen.
    apply d_consis_gen_weakening. exact H.
  - apply d_sub_gen__check_gen.
    apply d_consis_gen_weakening. exact H.
  - apply d_sub_gen__refl_plain.
    apply d_wf_ptyp_weakening. exact H.
  - apply d_sub_gen__forall_r with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_sub_gen__arg.
    + apply d_consis_gen_weakening. exact H.
    + eapply IHd_sub_gen; eauto.
    + exact H1.
Qed.

Lemma d_sub_gen_weakening_head : forall Γ Γ' m Δ B1 B2,
    Δ ⨟ Γ ⊢ᵍ[ m ] B1 ⊑ B2 ->
    Δ ⨟ (Γ' ++ Γ) ⊢ᵍ[ m ] B1 ⊑ B2.
Proof.
  intros Γ Γ' m Δ B1 B2 H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_sub_gen_weakening. simpl. exact H.
Qed.

Lemma d_sub_gen_trans : forall m1 Γ B1 B2 B3 m2,
    nil ⨟ Γ ⊢ᵍ[ m1 ] B1 ⊑ B2 ->
    nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ] B2 ⊑ B3 ->
    nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ] B1 ⊑ B3.
Proof.
  (** The first real branch after the split-syntax repair is the
      [d_sub_gen__embed]/[d_sub_gen__embed] composition.  That branch is
      exactly ordinary subtyping transitivity for [d_sub] with an
      embeddable middle type.  The previous unified-syntax proof hid this
      behind [d_sub_gen_to_d_sub], but that bridge is not valid for the
      generalized [Arg] cases.  Closing this lemma natively therefore
      requires a split-syntax B.4/D11 proof or an equivalent generalized
      consistency/subtyping composition lemma. *)
Admitted.

Lemma d_typing_gen_lift_plain : forall Γ e A m,
    Γ ⊢ᵍ[ mode_ti ] e ⦂ ptyp_to_btyp_syn A ->
    d_wf_ptyp Γ A ->
    Γ ⊢ᵍ[ m ] e ⦂ ptyp_to_btyp_syn A.
Proof.
  intros Γ e A m Hty Hwf.
  eapply d_typing_gen__sub.
  - exact Hty.
  - apply d_sub_gen__refl_plain. exact Hwf.
Qed.
