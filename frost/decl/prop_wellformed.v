(** Frost — well-formedness preservation lemmas (Phase 2.B). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.

Set Implicit Arguments.

(** * Declarative context well-formedness.
    A [denv] is well-formed iff every binding's payload is well-formed
    in the prefix preceding it. The paper treats this as implicit; we
    state it explicitly to ground preservation proofs. *)

Inductive d_wf_denv : list (atom * dbind) -> Prop :=
| d_wf_denv__nil : d_wf_denv nil
| d_wf_denv__tvar : forall Γ X,
    d_wf_denv Γ ->
    X `notin` dom Γ ->
    d_wf_denv ((X ~ dbind_tvar) ++ Γ)
| d_wf_denv__typ : forall Γ x A,
    d_wf_denv Γ ->
    x `notin` dom Γ ->
    d_wf_typ Γ A ->
    d_wf_denv ((x ~ dbind_typ A) ++ Γ)
| d_wf_denv__skel : forall Γ x P,
    d_wf_denv Γ ->
    x `notin` dom Γ ->
    d_wf_skel nil Γ P ->
    d_wf_denv ((x ~ dbind_skel P) ++ Γ).

(** ** Inversion lemmas. *)

Lemma d_wf_denv_inv_tvar : forall Γ X,
    d_wf_denv ((X ~ dbind_tvar) ++ Γ) ->
    d_wf_denv Γ /\ X `notin` dom Γ.
Proof. intros Γ X H. inversion H; subst; split; auto. Qed.

Lemma d_wf_denv_inv_typ : forall Γ x A,
    d_wf_denv ((x ~ dbind_typ A) ++ Γ) ->
    d_wf_denv Γ /\ x `notin` dom Γ /\ d_wf_typ Γ A.
Proof. intros Γ x A H. inversion H; subst; auto. Qed.

Lemma d_wf_denv_inv_skel : forall Γ x P,
    d_wf_denv ((x ~ dbind_skel P) ++ Γ) ->
    d_wf_denv Γ /\ x `notin` dom Γ /\ d_wf_skel nil Γ P.
Proof. intros Γ x P H. inversion H; subst; auto. Qed.

(** * Weakening — inserting a fresh middle context preserves wf. *)

Lemma d_wf_typ_weakening : forall Γ1 Γ2 Γ3 A,
    d_wf_typ (Γ1 ++ Γ3) A ->
    d_wf_typ (Γ1 ++ Γ2 ++ Γ3) A.
Proof.
  intros Γ1 Γ2 Γ3 A H. dependent induction H.
  - apply d_wf_typ__unit.
  - apply d_wf_typ__var.
    apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_wf_typ__arrow; auto.
  - apply d_wf_typ__all with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.

Lemma d_wf_skel_weakening : forall Γ1 Γ2 Γ3 Ψ P,
    d_wf_skel Ψ (Γ1 ++ Γ3) P ->
    d_wf_skel Ψ (Γ1 ++ Γ2 ++ Γ3) P.
Proof.
  intros Γ1 Γ2 Γ3 Ψ P H. dependent induction H.
  - apply d_wf_skel__unit.
  - apply d_wf_skel__var. destruct H as [Hin | Hin].
    + left. exact Hin.
    + right. apply binds_app_iff in Hin. destruct Hin as [Hin | Hin].
      * apply binds_app_iff. auto.
      * apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_wf_skel__arrow; auto.
  - apply d_wf_skel__all_col with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. apply H0; auto.
  - apply d_wf_skel__all_plain with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. apply H0; auto.
  - apply d_wf_skel__hole.
  - apply d_wf_skel__tophole; auto.
Qed.

Lemma d_wf_ttyp_weakening : forall Γ1 Γ2 Γ3 Δ A,
    d_wf_ttyp Δ (Γ1 ++ Γ3) A ->
    d_wf_ttyp Δ (Γ1 ++ Γ2 ++ Γ3) A.
Proof.
  intros Γ1 Γ2 Γ3 Δ A H. dependent induction H.
  - apply d_wf_ttyp__unit.
  - apply d_wf_ttyp__var.
    apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_wf_ttyp__arrow; auto.
  - apply d_wf_ttyp__all with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.

Lemma d_wf_utyp_weakening : forall Γ1 Γ2 Γ3 Δ A,
    d_wf_utyp Δ (Γ1 ++ Γ3) A ->
    d_wf_utyp Δ (Γ1 ++ Γ2 ++ Γ3) A.
Proof.
  intros Γ1 Γ2 Γ3 Δ A H. dependent induction H.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var.
    apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_wf_utyp__arrow; auto.
  - apply d_wf_utyp__tall with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - apply d_wf_utyp__pall with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.

Lemma d_wf_tskel_weakening : forall Γ1 Γ2 Γ3 Δ P,
    d_wf_tskel Δ (Γ1 ++ Γ3) P ->
    d_wf_tskel Δ (Γ1 ++ Γ2 ++ Γ3) P.
Proof.
  intros Γ1 Γ2 Γ3 Δ P H. dependent induction H.
  - apply d_wf_tskel__unit.
  - apply d_wf_tskel__var.
    apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_wf_tskel__arrow; auto.
  - apply d_wf_tskel__all with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - apply d_wf_tskel__hole.
  - apply d_wf_tskel__tophole; auto.
Qed.

Lemma d_wf_uskel_weakening : forall Γ1 Γ2 Γ3 Δ P,
    d_wf_uskel Δ (Γ1 ++ Γ3) P ->
    d_wf_uskel Δ (Γ1 ++ Γ2 ++ Γ3) P.
Proof.
  intros Γ1 Γ2 Γ3 Δ P H. dependent induction H.
  - apply d_wf_uskel__unit.
  - apply d_wf_uskel__var.
    apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_wf_uskel__arrow; auto.
  - apply d_wf_uskel__tall with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - apply d_wf_uskel__pall with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - apply d_wf_uskel__hole.
  - apply d_wf_uskel__tophole; auto.
Qed.

(** ** Head-append convenience corollaries. *)

Lemma d_wf_typ_weakening_head : forall Γ Γ' A,
    d_wf_typ Γ A ->
    d_wf_typ (Γ' ++ Γ) A.
Proof.
  intros Γ Γ' A H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_typ_weakening. rewrite_env Γ. exact H.
Qed.

Lemma d_wf_skel_weakening_head : forall Γ Γ' Ψ P,
    d_wf_skel Ψ Γ P ->
    d_wf_skel Ψ (Γ' ++ Γ) P.
Proof.
  intros Γ Γ' Ψ P H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_skel_weakening. rewrite_env Γ. exact H.
Qed.

Lemma d_wf_ttyp_weakening_head : forall Γ Γ' Δ A,
    d_wf_ttyp Δ Γ A ->
    d_wf_ttyp Δ (Γ' ++ Γ) A.
Proof.
  intros Γ Γ' Δ A H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_ttyp_weakening. rewrite_env Γ. exact H.
Qed.

Lemma d_wf_utyp_weakening_head : forall Γ Γ' Δ A,
    d_wf_utyp Δ Γ A ->
    d_wf_utyp Δ (Γ' ++ Γ) A.
Proof.
  intros Γ Γ' Δ A H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_utyp_weakening. rewrite_env Γ. exact H.
Qed.

Lemma d_wf_tskel_weakening_head : forall Γ Γ' Δ P,
    d_wf_tskel Δ Γ P ->
    d_wf_tskel Δ (Γ' ++ Γ) P.
Proof.
  intros Γ Γ' Δ P H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_tskel_weakening. rewrite_env Γ. exact H.
Qed.

Lemma d_wf_uskel_weakening_head : forall Γ Γ' Δ P,
    d_wf_uskel Δ Γ P ->
    d_wf_uskel Δ (Γ' ++ Γ) P.
Proof.
  intros Γ Γ' Δ P H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_uskel_weakening. rewrite_env Γ. exact H.
Qed.
