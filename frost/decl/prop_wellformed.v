(** Frost — well-formedness lemmas for the current split syntax. *)

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

Set Implicit Arguments.

(** * Declarative contexts. *)

Inductive d_wf_denv : list (atom * dbind) -> Prop :=
| d_wf_denv__nil : d_wf_denv nil
| d_wf_denv__tvar : forall Γ X,
    d_wf_denv Γ ->
    X `notin` dom Γ ->
    d_wf_denv ((X ~ dbind_tvar) ++ Γ)
| d_wf_denv__typ : forall Γ x A,
    d_wf_denv Γ ->
    x `notin` dom Γ ->
    d_wf_ptyp Γ A ->
    d_wf_denv ((x ~ dbind_typ A) ++ Γ)
| d_wf_denv__skl : forall Γ x P,
    d_wf_denv Γ ->
    x `notin` dom Γ ->
    d_wf_pskl nil Γ P ->
    d_wf_denv ((x ~ dbind_skl P) ++ Γ).

Lemma d_wf_denv_inv_tvar : forall Γ X,
    d_wf_denv ((X ~ dbind_tvar) ++ Γ) ->
    d_wf_denv Γ /\ X `notin` dom Γ.
Proof.
  intros Γ X H. inversion H; subst; auto.
Qed.

Lemma d_wf_denv_inv_typ : forall Γ x A,
    d_wf_denv ((x ~ dbind_typ A) ++ Γ) ->
    d_wf_denv Γ /\ x `notin` dom Γ /\ d_wf_ptyp Γ A.
Proof.
  intros Γ x A H. inversion H; subst; auto.
Qed.

Lemma d_wf_denv_inv_skl : forall Γ x P,
    d_wf_denv ((x ~ dbind_skl P) ++ Γ) ->
    d_wf_denv Γ /\ x `notin` dom Γ /\ d_wf_pskl nil Γ P.
Proof.
  intros Γ x P H. inversion H; subst; auto.
Qed.

(** * Weakening. *)

Lemma d_wf_ptyp_weakening : forall Γ1 Γ2 Γ3 A,
    d_wf_ptyp (Γ1 ++ Γ3) A ->
    d_wf_ptyp (Γ1 ++ Γ2 ++ Γ3) A.
Proof.
  intros Γ1 Γ2 Γ3 A H. dependent induction H.
  - constructor.
  - constructor. apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff; auto.
    + apply binds_app_iff. right. apply binds_app_iff; auto.
  - constructor; auto.
  - inst_cofinites_for d_wf_ptyp__all.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.

Lemma d_wf_btyp_weakening : forall Γ1 Γ2 Γ3 B,
    d_wf_btyp (Γ1 ++ Γ3) B ->
    d_wf_btyp (Γ1 ++ Γ2 ++ Γ3) B.
Proof.
  intros Γ1 Γ2 Γ3 B H. dependent induction H.
  - constructor.
  - constructor. apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff; auto.
    + apply binds_app_iff. right. apply binds_app_iff; auto.
  - constructor; auto.
  - inst_cofinites_for d_wf_btyp__all_syn.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - inst_cofinites_for d_wf_btyp__all_inh.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.

Lemma d_wf_utyp_weakening : forall Γ1 Γ2 Γ3 Δ C,
    Δ ⨟ (Γ1 ++ Γ3) ⊢ᵤ C ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ᵤ C.
Proof.
  intros Γ1 Γ2 Γ3 Δ C H. dependent induction H.
  - constructor.
  - constructor. apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff; auto.
    + apply binds_app_iff. right. apply binds_app_iff; auto.
  - econstructor; eauto.
  - inst_cofinites_for d_wf_utyp__all_syn.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - inst_cofinites_for d_wf_utyp__all_etag; auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.

Lemma d_wf_pskl_weakening : forall Γ1 Γ2 Γ3 Ψ P,
    Ψ ⨟ (Γ1 ++ Γ3) ⊢ₚₛ P ->
    Ψ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ₚₛ P.
Proof.
  intros Γ1 Γ2 Γ3 Ψ P H. dependent induction H.
  - constructor.
  - constructor. destruct H as [Hin | Hin].
    + left; auto.
    + right. apply binds_app_iff in Hin. destruct Hin as [Hin | Hin].
      * apply binds_app_iff; auto.
      * apply binds_app_iff. right. apply binds_app_iff; auto.
  - constructor; auto.
  - inst_cofinites_for d_wf_pskl__all.
    intros X HX. apply H0; auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma d_wf_uskl_weakening : forall Γ1 Γ2 Γ3 Δ R,
    Δ ⨟ (Γ1 ++ Γ3) ⊢ᵤₛ R ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ᵤₛ R.
Proof.
  intros Γ1 Γ2 Γ3 Δ R H. dependent induction H.
  - constructor.
  - constructor. apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff; auto.
    + apply binds_app_iff. right. apply binds_app_iff; auto.
  - econstructor; eauto.
  - inst_cofinites_for d_wf_uskl__all_syn.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - inst_cofinites_for d_wf_uskl__all_etag; auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma d_wf_ptyp_weakening_head : forall Γ Γ' A,
    d_wf_ptyp Γ A ->
    d_wf_ptyp (Γ' ++ Γ) A.
Proof.
  intros Γ Γ' A H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_ptyp_weakening. rewrite_env Γ. exact H.
Qed.

Lemma d_wf_btyp_weakening_head : forall Γ Γ' B,
    d_wf_btyp Γ B ->
    d_wf_btyp (Γ' ++ Γ) B.
Proof.
  intros Γ Γ' B H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_btyp_weakening. rewrite_env Γ. exact H.
Qed.

(** * Preservation hooks.

    These are the shape-correct statements the later typing/subtyping
    ports should consume.  Some are currently left as axioms while the
    proof layer is being moved off the old unified syntax; they are
    intentionally stated over the latest categories. *)

Lemma d_wf_ptyp_to_btyp_syn : forall Γ A,
    d_wf_ptyp Γ A ->
    d_wf_btyp Γ (ptyp_to_btyp_syn A).
Proof.
Admitted.

Lemma d_wf_ptyp_to_btyp_inh : forall Γ A,
    d_wf_ptyp Γ A ->
    d_wf_btyp Γ (ptyp_to_btyp_inh A).
Proof.
Admitted.

Lemma d_wf_ptyp_to_utyp_syn : forall Γ A,
    d_wf_ptyp Γ A ->
    nil ⨟ Γ ⊢ᵤ (ptyp_to_utyp_syn A).
Proof.
Admitted.

Lemma d_typing_pat_preserves_wf :
  (forall m Γ e B, d_typing m Γ e B -> d_wf_btyp Γ B) /\
  (forall m Γ e Q, d_pat m Γ e Q -> d_wf_pskl nil Γ Q).
Proof.
Admitted.
