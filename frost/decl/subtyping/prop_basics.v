(** Frost — declarative subtyping basics for the split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Set Implicit Arguments.

Lemma d_consis_refl_mono : forall Γ A,
    mono_ptyp A ->
    d_wf_ptyp Γ A ->
    empty ⨟ Γ ⊨ (ptyp_to_utyp_syn A) ≈ (ptyp_to_btyp_syn A).
Proof.
Admitted.

Lemma mono_ptyp_is_styp : forall A,
    mono_ptyp A -> is_styp (ptyp_to_btyp_syn A).
Proof.
Admitted.

Lemma mono_ptyp_is_ityp : forall A,
    mono_ptyp A -> is_ityp (ptyp_to_btyp_inh A).
Proof.
Admitted.

Lemma mono_ptyp_guarded : forall A,
    mono_ptyp A -> guarded_utyp (ptyp_to_utyp_syn A).
Proof.
Admitted.

Lemma d_sub_refl_mono : forall Γ A,
    mono_ptyp A ->
    d_wf_ptyp Γ A ->
    empty ⨟ Γ ⊢[ mode_ti ] (ptyp_to_utyp_syn A) ⊑ (ptyp_to_btyp_syn A).
Proof.
  intros Γ A Hmono Hwf.
  apply d_sub__infer.
  - apply d_consis_refl_mono; auto.
  - apply mono_ptyp_is_styp; auto.
  - reflexivity.
Qed.

Lemma d_consis_weakening : forall Γ1 Γ2 Γ3 Δ C B,
    Δ ⨟ (Γ1 ++ Γ3) ⊨ C ≈ B ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊨ C ≈ B.
Proof.
Admitted.

Lemma d_consis_weakening_head : forall Γ Γ' Δ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    Δ ⨟ (Γ' ++ Γ) ⊨ C ≈ B.
Proof.
  intros Γ Γ' Δ C B H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_consis_weakening. simpl. exact H.
Qed.

Lemma d_sub_weakening : forall Γ1 Γ2 Γ3 m Δ C B,
    Δ ⨟ (Γ1 ++ Γ3) ⊢[ m ] C ⊑ B ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢[ m ] C ⊑ B.
Proof.
Admitted.

Lemma d_sub_weakening_head : forall Γ Γ' m Δ C B,
    Δ ⨟ Γ ⊢[ m ] C ⊑ B ->
    Δ ⨟ (Γ' ++ Γ) ⊢[ m ] C ⊑ B.
Proof.
  intros Γ Γ' m Δ C B H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_sub_weakening. simpl. exact H.
Qed.

Lemma d_consis_empty_eq : forall Γ C B,
    empty ⨟ Γ ⊨ C ≈ B ->
    btyp_to_ptyp C = btyp_to_ptyp B.
Proof.
Admitted.
