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
(* The [is_skel P] premise pins skeleton bindings to the [is_skel] grammar
   (as the paper intends — skeletons in [Γ] are patterns, which exclude the
   [typ_all_plain]/[typ_all_etag] cases that [d_wf_skel] technically admits).
   Every constructor of dbind_skel-extending rules in the typing system
   ([d_pat__abs] via [is_inh_skel], [d_pat__abs_check] via [typ_hole])
   already satisfies this premise. *)
| d_wf_denv__skel : forall Γ x P,
    d_wf_denv Γ ->
    x `notin` dom Γ ->
    is_skel P ->
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
  - inst_cofinites_for d_wf_typ__all.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.

Lemma d_wf_skel_weakening : forall Γ1 Γ2 Γ3 Ψ P,
    Ψ ⨟ (Γ1 ++ Γ3) ⊢ₛₖ P ->
    Ψ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ₛₖ P.
Proof.
  intros Γ1 Γ2 Γ3 Ψ P H. dependent induction H.
  - apply d_wf_skel__unit.
  - apply d_wf_skel__var. destruct H as [Hin | Hin].
    + left. exact Hin.
    + right. apply binds_app_iff in Hin. destruct Hin as [Hin | Hin].
      * apply binds_app_iff. auto.
      * apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_wf_skel__arrow; auto.
  - inst_cofinites_for d_wf_skel__all_col.
    intros X HX. apply H0; auto.
  - inst_cofinites_for d_wf_skel__all_plain.
    intros X HX. apply H0; auto.
  - apply d_wf_skel__hole.
  - apply d_wf_skel__tophole; auto.
Qed.

Lemma d_wf_ttyp_weakening : forall Γ1 Γ2 Γ3 Δ A,
    Δ ⨟ (Γ1 ++ Γ3) ⊢ₜₜ A ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ₜₜ A.
Proof.
  intros Γ1 Γ2 Γ3 Δ A H. dependent induction H.
  - apply d_wf_ttyp__unit.
  - apply d_wf_ttyp__var.
    apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_wf_ttyp__arrow; auto.
  - inst_cofinites_for d_wf_ttyp__all; auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.

Lemma d_wf_utyp_weakening : forall Γ1 Γ2 Γ3 Δ A,
    Δ ⨟ (Γ1 ++ Γ3) ⊢ᵤₜ A ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ᵤₜ A.
Proof.
  intros Γ1 Γ2 Γ3 Δ A H. dependent induction H.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var.
    apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_wf_utyp__arrow; auto.
  - inst_cofinites_for d_wf_utyp__tall; auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - inst_cofinites_for d_wf_utyp__pall.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
Qed.

Lemma d_wf_tskel_weakening : forall Γ1 Γ2 Γ3 Δ P,
    Δ ⨟ (Γ1 ++ Γ3) ⊢ₜₛ P ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ₜₛ P.
Proof.
  intros Γ1 Γ2 Γ3 Δ P H. dependent induction H.
  - apply d_wf_tskel__unit.
  - apply d_wf_tskel__var.
    apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_wf_tskel__arrow; auto.
  - inst_cofinites_for d_wf_tskel__all; auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - apply d_wf_tskel__hole.
  - apply d_wf_tskel__tophole; auto.
Qed.

Lemma d_wf_uskel_weakening : forall Γ1 Γ2 Γ3 Δ P,
    Δ ⨟ (Γ1 ++ Γ3) ⊢ᵤₛ P ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ᵤₛ P.
Proof.
  intros Γ1 Γ2 Γ3 Δ P H. dependent induction H.
  - apply d_wf_uskel__unit.
  - apply d_wf_uskel__var.
    apply binds_app_iff in H. destruct H as [Hin | Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_wf_uskel__arrow; auto.
  - inst_cofinites_for d_wf_uskel__tall; auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H0; auto.
  - inst_cofinites_for d_wf_uskel__pall.
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

(** [d_wf_typ] is preserved by any context morphism that preserves
    tvar bindings. Only [dbind_tvar] entries matter for [d_wf_typ]. *)
Lemma d_wf_typ_tvar_morph : forall Γ Γ' A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_wf_typ Γ A ->
    d_wf_typ Γ' A.
Proof.
  intros Γ Γ' A Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_wf_typ__unit.
  - apply d_wf_typ__var. apply Hmorph; auto.
  - apply d_wf_typ__arrow; auto.
  - apply d_wf_typ__all with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb].
    + apply binds_app_iff. left. auto.
    + apply binds_app_iff. right. auto.
Qed.

(** Same morphism property for [d_wf_ttyp]. *)
Lemma d_wf_ttyp_tvar_morph : forall Γ Γ' Δ A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    Δ ⨟ Γ ⊢ₜₜ A ->
    Δ ⨟ Γ' ⊢ₜₜ A.
Proof.
  intros Γ Γ' Δ A Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_wf_ttyp__unit.
  - apply d_wf_ttyp__var. apply Hmorph; auto.
  - apply d_wf_ttyp__arrow; auto.
  - inst_cofinites_for d_wf_ttyp__all; auto.
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb];
      apply binds_app_iff; [left | right]; auto.
Qed.

(** Same morphism property for [d_wf_utyp]. *)
Lemma d_wf_utyp_tvar_morph : forall Γ Γ' Δ A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    Δ ⨟ Γ ⊢ᵤₜ A ->
    Δ ⨟ Γ' ⊢ᵤₜ A.
Proof.
  intros Γ Γ' Δ A Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var. apply Hmorph; auto.
  - apply d_wf_utyp__arrow; auto.
  - inst_cofinites_for d_wf_utyp__tall; auto.
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb];
      apply binds_app_iff; [left | right]; auto.
  - inst_cofinites_for d_wf_utyp__pall.
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb];
      apply binds_app_iff; [left | right]; auto.
Qed.

(** Same morphism property for [d_wf_skel]. Note Ψ stays the same; the
    morphism only acts on Γ. *)
Lemma d_wf_skel_tvar_morph : forall Γ Γ' Ψ P,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    Ψ ⨟ Γ ⊢ₛₖ P ->
    Ψ ⨟ Γ' ⊢ₛₖ P.
Proof.
  intros Γ Γ' Ψ P Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_wf_skel__unit.
  - apply d_wf_skel__var. destruct H as [Hin | Hb]; [left|right]; auto.
  - apply d_wf_skel__arrow; auto.
  - apply d_wf_skel__all_col with (L := L `union` dom Γ'). auto.
  - apply d_wf_skel__all_plain with (L := L `union` dom Γ'). auto.
  - apply d_wf_skel__hole.
  - apply d_wf_skel__tophole; auto.
Qed.

(** Same morphism property for [d_wf_tskel]. *)
Lemma d_wf_tskel_tvar_morph : forall Γ Γ' Δ A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_wf_tskel Δ Γ A ->
    d_wf_tskel Δ Γ' A.
Proof.
  intros Γ Γ' Δ A Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_wf_tskel__unit.
  - apply d_wf_tskel__var. apply Hmorph; auto.
  - apply d_wf_tskel__arrow; auto.
  - apply d_wf_tskel__all with (L := L `union` dom Γ'); auto.
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb];
      apply binds_app_iff; [left | right]; auto.
  - apply d_wf_tskel__hole.
  - apply d_wf_tskel__tophole; auto.
Qed.

(** Same morphism property for [d_wf_uskel]. *)
Lemma d_wf_uskel_tvar_morph : forall Γ Γ' Δ A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_wf_uskel Δ Γ A ->
    d_wf_uskel Δ Γ' A.
Proof.
  intros Γ Γ' Δ A Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_wf_uskel__unit.
  - apply d_wf_uskel__var. apply Hmorph; auto.
  - apply d_wf_uskel__arrow; auto.
  - apply d_wf_uskel__tall with (L := L `union` dom Γ'); auto.
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb];
      apply binds_app_iff; [left | right]; auto.
  - apply d_wf_uskel__pall with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb];
      apply binds_app_iff; [left | right]; auto.
  - apply d_wf_uskel__hole.
  - apply d_wf_uskel__tophole; auto.
Qed.

Lemma d_wf_skel_weakening_head : forall Γ Γ' Ψ P,
    Ψ ⨟ Γ ⊢ₛₖ P ->
    Ψ ⨟ (Γ' ++ Γ) ⊢ₛₖ P.
Proof.
  intros Γ Γ' Ψ P H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_skel_weakening. rewrite_env Γ. exact H.
Qed.

Lemma d_wf_ttyp_weakening_head : forall Γ Γ' Δ A,
    Δ ⨟ Γ ⊢ₜₜ A ->
    Δ ⨟ (Γ' ++ Γ) ⊢ₜₜ A.
Proof.
  intros Γ Γ' Δ A H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_ttyp_weakening. rewrite_env Γ. exact H.
Qed.

Lemma d_wf_utyp_weakening_head : forall Γ Γ' Δ A,
    Δ ⨟ Γ ⊢ᵤₜ A ->
    Δ ⨟ (Γ' ++ Γ) ⊢ᵤₜ A.
Proof.
  intros Γ Γ' Δ A H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_utyp_weakening. rewrite_env Γ. exact H.
Qed.

Lemma d_wf_tskel_weakening_head : forall Γ Γ' Δ P,
    Δ ⨟ Γ ⊢ₜₛ P ->
    Δ ⨟ (Γ' ++ Γ) ⊢ₜₛ P.
Proof.
  intros Γ Γ' Δ P H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_tskel_weakening. rewrite_env Γ. exact H.
Qed.

Lemma d_wf_uskel_weakening_head : forall Γ Γ' Δ P,
    Δ ⨟ Γ ⊢ᵤₛ P ->
    Δ ⨟ (Γ' ++ Γ) ⊢ᵤₛ P.
Proof.
  intros Γ Γ' Δ P H. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_wf_uskel_weakening. rewrite_env Γ. exact H.
Qed.

(** * Locally-closed corollaries of wellformedness.
    Each wf judgment implies the type is locally closed. Used by the
    substitution-preservation proofs (the [open]-rewrite needs [lc_typ B]). *)

Lemma d_wf_typ_lc : forall Γ A, d_wf_typ Γ A -> lc_typ A.
Proof.
  intros Γ A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_col_exists with (X1 := X).
    apply H0. auto.
Qed.

Lemma d_wf_skel_lc : forall Ψ Γ P, Ψ ⨟ Γ ⊢ₛₖ P -> lc_typ P.
Proof.
  intros Ψ Γ P H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_col_exists with (X1 := X).
    apply H0. auto.
  - pick fresh X. apply lc_typ_all_plain_exists with (X1 := X).
    apply H0. auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma d_wf_ttyp_lc : forall Δ Γ A, Δ ⨟ Γ ⊢ₜₜ A -> lc_typ A.
Proof.
  intros Δ Γ A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_etag_exists with (X1 := X).
    apply H0. auto.
Qed.

Lemma d_wf_utyp_lc : forall Δ Γ A, Δ ⨟ Γ ⊢ᵤₜ A -> lc_typ A.
Proof.
  intros Δ Γ A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_etag_exists with (X1 := X).
    apply H0. auto.
  - pick fresh X. apply lc_typ_all_plain_exists with (X1 := X).
    apply H0. auto.
Qed.

Lemma d_wf_tskel_lc : forall Δ Γ P, Δ ⨟ Γ ⊢ₜₛ P -> lc_typ P.
Proof.
  intros Δ Γ P H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_etag_exists with (X1 := X).
    apply H0. auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma d_wf_uskel_lc : forall Δ Γ P, Δ ⨟ Γ ⊢ᵤₛ P -> lc_typ P.
Proof.
  intros Δ Γ P H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_etag_exists with (X1 := X).
    apply H0. auto.
  - pick fresh X. apply lc_typ_all_plain_exists with (X1 := X).
    apply H0. auto.
  - constructor.
  - constructor; auto.
Qed.

(** * Wellformedness preservation under typvar substitution.

    Substituting a wf [B] for a tvar [X] in a wf [A] yields a wf result
    in the same context with [X] removed. Each lemma requires [B] to be
    well-formed in the matching category (e.g., [d_wf_ttyp] for tagged
    substitution). *)

(** [d_wf_skel] is monotone in Ψ: enlarging Ψ to any super-list preserves
    wf. Stated as a "Ψ supersets Ψ'" inclusion via [incl]. *)
Lemma d_wf_skel_psi_incl : forall Ψ Ψ' Γ P,
    d_wf_skel Ψ Γ P -> incl Ψ Ψ' -> d_wf_skel Ψ' Γ P.
Proof.
  intros Ψ Ψ' Γ P H. revert Ψ'. induction H; intros Ψ' Hincl.
  - apply d_wf_skel__unit.
  - apply d_wf_skel__var. destruct H as [Hin | Hin].
    + left. apply Hincl. exact Hin.
    + right. exact Hin.
  - apply d_wf_skel__arrow; auto.
  - apply d_wf_skel__all_col with (L := L).
    intros X HX. apply H0; auto.
    intros y Hy. destruct Hy as [Heq | Htail]; [left; exact Heq | right; apply Hincl; exact Htail].
  - apply d_wf_skel__all_plain with (L := L).
    intros X HX. apply H0; auto.
    intros y Hy. destruct Hy as [Heq | Htail]; [left; exact Heq | right; apply Hincl; exact Htail].
  - apply d_wf_skel__hole.
  - apply d_wf_skel__tophole; auto.
Qed.

(** Weaken Ψ on the left. *)
Lemma d_wf_skel_psi_weakening : forall Ψ Ψ' Γ P,
    d_wf_skel Ψ Γ P -> d_wf_skel (Ψ' ++ Ψ) Γ P.
Proof.
  intros Ψ Ψ' Γ P H.
  apply d_wf_skel_psi_incl with (Ψ := Ψ); auto.
  intros x Hx. apply in_or_app. right. exact Hx.
Qed.

(** [d_wf_typ] only inhabits plain types (per the predicate hierarchy). *)
Lemma d_wf_typ_is_typ : forall Γ A,
    d_wf_typ Γ A -> is_typ A.
Proof.
  intros Γ A H. induction H.
  - apply is_typ__unit.
  - apply is_typ__var.
  - apply is_typ__arrow; auto.
  - apply is_typ__all with (L := L). auto.
Qed.

(** Drop a [(X ~ dbind_tvar)] entry from Γ when X is already in Ψ —
    i.e., the X has been "moved" from Γ to Ψ. Restricted to [is_typ P]
    so the [tophole]-case of [d_wf_skel] (which clears Ψ) never fires. *)
Lemma d_wf_skel_drop_tvar_in_psi : forall P,
    is_typ P ->
    forall Γ1 Γ2 X Ψ,
      List.In X Ψ ->
      Ψ ⨟ (Γ1 ++ (X ~ dbind_tvar) ++ Γ2) ⊢ₛₖ P ->
      Ψ ⨟ (Γ1 ++ Γ2) ⊢ₛₖ P.
Proof.
  intros P Hist. induction Hist; intros Γ1 Γ2 X1 Ψ HXin Hwf.
  - apply d_wf_skel__unit.
  - (* var *)
    inversion Hwf as [|? ? ? Hor| | | | |]; subst.
    apply d_wf_skel__var. destruct Hor as [Hin | Hbinds].
    + left. exact Hin.
    + apply binds_app_iff in Hbinds. destruct Hbinds as [Hb1 | Hb1].
      * right. apply binds_app_iff. left. exact Hb1.
      * apply binds_app_iff in Hb1. destruct Hb1 as [Hb1 | Hb1].
        -- apply binds_one_iff in Hb1. destruct Hb1 as [Hxeq _]. subst.
           left. exact HXin.
        -- right. apply binds_app_iff. right. exact Hb1.
  - (* arrow *)
    inversion Hwf as [| |? ? ? ? HA HB| | | |]; subst.
    apply d_wf_skel__arrow; eauto.
  - (* all_col c A *)
    inversion Hwf as [| | |L0 ? ? ? ? Hbody| | |]; subst.
    apply d_wf_skel__all_col
      with (L := L0 `union` L `union` dom (Γ1 ++ Γ2) `union` singleton X1).
    intros Y HY. apply (H0 Y) with (X := X1) (Ψ := Y :: Ψ).
    + auto.
    + simpl. right. exact HXin.
    + apply Hbody. auto.
Qed.

(** Bridge: a [d_wf_typ]-wellformed type is also a [d_wf_skel]-wellformed
    skeleton (with empty Ψ). Uses [d_wf_skel_drop_tvar_in_psi] in the
    all-case to convert the IH from "X in Γ" to "X in Ψ". *)
Lemma d_wf_typ_d_wf_skel : forall Γ A,
    d_wf_typ Γ A -> nil ⨟ Γ ⊢ₛₖ A.
Proof.
  intros Γ A H. induction H.
  - apply d_wf_skel__unit.
  - apply d_wf_skel__var. right. exact H.
  - apply d_wf_skel__arrow; auto.
  - apply d_wf_skel__all_col with (L := L `union` dom Γ).
    intros X HX.
    (* IH H1 X HX : d_wf_skel nil ((X~_)++Γ) (open A X) *)
    (* Goal     : d_wf_skel (X::nil) Γ (open A X) *)
    assert (Histyp : is_typ (open_typ_wrt_typ A (typ_var_f X)))
      by (apply d_wf_typ_is_typ with (Γ := (X ~ dbind_tvar) ++ Γ); auto).
    (* Step 1: psi-weaken nil → [X]. *)
    assert (Hsk : d_wf_skel (X :: nil) ((X ~ dbind_tvar) ++ Γ)
                            (open_typ_wrt_typ A (typ_var_f X))).
    { change (X :: nil) with ((X :: nil) ++ nil).
      apply d_wf_skel_psi_weakening. auto. }
    (* Step 2: drop X from Γ since X ∈ Ψ. *)
    rewrite_env (nil ++ Γ).
    eapply d_wf_skel_drop_tvar_in_psi with (X := X); eauto.
    simpl. left. reflexivity.
Qed.

(** Embed [d_wf_ttyp Δ Γ A] into [d_wf_utyp Δ Γ A]: the unresolved-type
    wf is more permissive (extra [pall] constructor). *)
Lemma d_wf_ttyp_is_utyp : forall Δ Γ A,
    d_wf_ttyp Δ Γ A -> d_wf_utyp Δ Γ A.
Proof.
  intros Δ Γ A H. induction H.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var; auto.
  - apply d_wf_utyp__arrow; auto.
  - apply d_wf_utyp__tall with (L := L); auto.
Qed.

(** Embed [d_wf_tskel Δ Γ P] into [d_wf_uskel Δ Γ P]. *)
Lemma d_wf_tskel_is_uskel : forall Δ Γ P,
    d_wf_tskel Δ Γ P -> d_wf_uskel Δ Γ P.
Proof.
  intros Δ Γ P H. induction H.
  - apply d_wf_uskel__unit.
  - apply d_wf_uskel__var; auto.
  - apply d_wf_uskel__arrow; auto.
  - apply d_wf_uskel__tall with (L := L); auto.
  - apply d_wf_uskel__hole.
  - apply d_wf_uskel__tophole; auto.
Qed.

Lemma d_wf_typ_subst : forall Γ1 Γ2 X A B,
    d_wf_typ (Γ1 ++ (X ~ dbind_tvar) ++ Γ2) A ->
    d_wf_typ Γ2 B ->
    d_wf_typ (Γ1 ++ Γ2) (subst_typ_in_typ B X A).
Proof.
  intros Γ1 Γ2 X A B HA HB. dependent induction HA; simpl.
  - apply d_wf_typ__unit.
  - destruct (X0 == X); subst.
    + replace (if X == X then B else typ_var_f X) with B
        by (destruct (X == X); [reflexivity | contradiction]).
      apply d_wf_typ_weakening_head. exact HB.
    + replace (if X0 == X then B else typ_var_f X0) with (typ_var_f X0)
        by (destruct (X0 == X); [contradiction | reflexivity]).
      apply binds_remove_mid in H; auto.
      apply d_wf_typ__var. apply binds_app_iff in H. destruct H; apply binds_app_iff; auto.
  - apply d_wf_typ__arrow; auto.
  - inst_cofinites_for d_wf_typ__all.
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_typ_lc HB)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
Qed.

(** [d_wf_skel] substitution requires the substituted-in [B] to be a
    well-formed skeleton in [nil] Ψ-context AND [guarded_typ B] so the
    [tophole] constructor's [guarded_skel] premise is preserved when the
    [typ_var_f X] sat under a tophole. In practice, the only call site
    (skeleton refinement / pattern subst) instantiates with a guarded type. *)
Lemma d_wf_skel_subst : forall Γ1 Γ2 Ψ X P B,
    d_wf_skel Ψ (Γ1 ++ (X ~ dbind_tvar) ++ Γ2) P ->
    d_wf_skel nil Γ2 B ->
    guarded_typ B ->
    d_wf_skel Ψ (Γ1 ++ Γ2) (subst_typ_in_typ B X P).
Proof.
  intros Γ1 Γ2 Ψ X P B HP HB HGuard. dependent induction HP; simpl.
  - apply d_wf_skel__unit.
  - destruct (X0 == X); subst.
    + replace (if X == X then B else typ_var_f X) with B
        by (destruct (X == X); [reflexivity | contradiction]).
      replace Ψ with (Ψ ++ (@nil atom)) by apply app_nil_r.
      apply d_wf_skel_psi_weakening.
      apply d_wf_skel_weakening_head. exact HB.
    + replace (if X0 == X then B else typ_var_f X0) with (typ_var_f X0)
        by (destruct (X0 == X); [contradiction | reflexivity]).
      apply d_wf_skel__var. destruct H as [Hin | Hin].
      * left. exact Hin.
      * right. eapply binds_remove_mid in Hin; [| exact n].
        apply binds_app_iff in Hin. destruct Hin as [Hin | Hin]; apply binds_app_iff; auto.
  - apply d_wf_skel__arrow; auto.
  - inst_cofinites_for d_wf_skel__all_col.
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_skel_lc HB)].
    apply H0; auto.
  - inst_cofinites_for d_wf_skel__all_plain.
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_skel_lc HB)].
    apply H0; auto.
  - apply d_wf_skel__hole.
  - apply d_wf_skel__tophole.
    + (* guarded_skel preserved by subst, given [guarded_typ B]. *)
      inversion H; subst; simpl.
      * apply guarded_skel__unit.
      * destruct (X0 == X); subst.
        -- replace (if X == X then B else typ_var_f X) with B
             by (destruct (X == X); [reflexivity | contradiction]).
           inversion HGuard; subst.
           ++ apply guarded_skel__unit.
           ++ apply guarded_skel__var.
           ++ apply guarded_skel__arrow.
        -- replace (if X0 == X then B else typ_var_f X0) with (typ_var_f X0)
             by (destruct (X0 == X); [contradiction | reflexivity]).
           apply guarded_skel__var.
      * apply guarded_skel__arrow.
    + apply IHHP; auto.
Qed.

Lemma d_wf_ttyp_subst : forall Γ1 Γ2 Δ X A B,
    d_wf_ttyp Δ (Γ1 ++ (X ~ dbind_tvar) ++ Γ2) A ->
    d_wf_ttyp nil Γ2 B ->
    d_wf_ttyp Δ (Γ1 ++ Γ2) (subst_typ_in_typ B X A).
Proof.
  intros Γ1 Γ2 Δ X A B HA HB. dependent induction HA; simpl.
  - apply d_wf_ttyp__unit.
  - destruct (X0 == X); subst.
    + replace (if X == X then B else typ_var_f X) with B
        by (destruct (X == X); [reflexivity | contradiction]).
      apply d_wf_ttyp_weakening_head. exact HB.
    + replace (if X0 == X then B else typ_var_f X0) with (typ_var_f X0)
        by (destruct (X0 == X); [contradiction | reflexivity]).
      apply binds_remove_mid in H; auto.
      apply d_wf_ttyp__var. apply binds_app_iff in H. destruct H; apply binds_app_iff; auto.
  - apply d_wf_ttyp__arrow; auto.
  - apply d_wf_ttyp__all with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)); auto.
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_ttyp_lc HB)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
Qed.

Lemma d_wf_utyp_subst : forall Γ1 Γ2 Δ X A B,
    d_wf_utyp Δ (Γ1 ++ (X ~ dbind_tvar) ++ Γ2) A ->
    d_wf_ttyp nil Γ2 B ->
    d_wf_utyp Δ (Γ1 ++ Γ2) (subst_typ_in_typ B X A).
Proof.
  intros Γ1 Γ2 Δ X A B HA HB. dependent induction HA; simpl.
  - apply d_wf_utyp__unit.
  - destruct (X0 == X); subst.
    + replace (if X == X then B else typ_var_f X) with B
        by (destruct (X == X); [reflexivity | contradiction]).
      apply d_wf_utyp_weakening_head. apply d_wf_ttyp_is_utyp. exact HB.
    + replace (if X0 == X then B else typ_var_f X0) with (typ_var_f X0)
        by (destruct (X0 == X); [contradiction | reflexivity]).
      apply binds_remove_mid in H; auto.
      apply d_wf_utyp__var. apply binds_app_iff in H. destruct H; apply binds_app_iff; auto.
  - apply d_wf_utyp__arrow; auto.
  - apply d_wf_utyp__tall with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)); auto.
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_ttyp_lc HB)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
  - apply d_wf_utyp__pall with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)).
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_ttyp_lc HB)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
Qed.

Lemma d_wf_tskel_subst : forall Γ1 Γ2 Δ X P B,
    d_wf_tskel Δ (Γ1 ++ (X ~ dbind_tvar) ++ Γ2) P ->
    d_wf_tskel nil Γ2 B ->
    d_wf_tskel Δ (Γ1 ++ Γ2) (subst_typ_in_typ B X P).
Proof.
  intros Γ1 Γ2 Δ X P B HP HB. dependent induction HP; simpl.
  - apply d_wf_tskel__unit.
  - destruct (X0 == X); subst.
    + replace (if X == X then B else typ_var_f X) with B
        by (destruct (X == X); [reflexivity | contradiction]).
      apply d_wf_tskel_weakening_head. exact HB.
    + replace (if X0 == X then B else typ_var_f X0) with (typ_var_f X0)
        by (destruct (X0 == X); [contradiction | reflexivity]).
      apply binds_remove_mid in H; auto.
      apply d_wf_tskel__var. apply binds_app_iff in H. destruct H; apply binds_app_iff; auto.
  - apply d_wf_tskel__arrow; auto.
  - apply d_wf_tskel__all with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)); auto.
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_tskel_lc HB)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
  - apply d_wf_tskel__hole.
  - apply d_wf_tskel__tophole; auto.
Qed.

Lemma d_wf_uskel_subst : forall Γ1 Γ2 Δ X P B,
    d_wf_uskel Δ (Γ1 ++ (X ~ dbind_tvar) ++ Γ2) P ->
    d_wf_tskel nil Γ2 B ->
    d_wf_uskel Δ (Γ1 ++ Γ2) (subst_typ_in_typ B X P).
Proof.
  intros Γ1 Γ2 Δ X P B HP HB. dependent induction HP; simpl.
  - apply d_wf_uskel__unit.
  - destruct (X0 == X); subst.
    + replace (if X == X then B else typ_var_f X) with B
        by (destruct (X == X); [reflexivity | contradiction]).
      apply d_wf_uskel_weakening_head. apply d_wf_tskel_is_uskel. exact HB.
    + replace (if X0 == X then B else typ_var_f X0) with (typ_var_f X0)
        by (destruct (X0 == X); [contradiction | reflexivity]).
      apply binds_remove_mid in H; auto.
      apply d_wf_uskel__var. apply binds_app_iff in H. destruct H; apply binds_app_iff; auto.
  - apply d_wf_uskel__arrow; auto.
  - apply d_wf_uskel__tall with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)); auto.
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_tskel_lc HB)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
  - apply d_wf_uskel__pall with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)).
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_tskel_lc HB)].
    rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    apply H0; auto.
  - apply d_wf_uskel__hole.
  - apply d_wf_uskel__tophole; auto.
Qed.

(** Opening preserves [guarded_skel]: opening only acts on bound variables,
    and [guarded_skel] only inspects the topmost constructor (unit, free
    var, or arrow), which is preserved by [open_typ_wrt_typ_rec]. *)
Lemma guarded_skel_open_preservation : forall Q X k,
    guarded_skel Q ->
    guarded_skel (open_typ_wrt_typ_rec k (typ_var_f X) Q).
Proof.
  intros Q X k H. inversion H; subst; simpl.
  - apply guarded_skel__unit.
  - apply guarded_skel__var.
  - apply guarded_skel__arrow.
Qed.

Lemma guarded_skel_open : forall Q X,
    guarded_skel Q ->
    guarded_skel (open_typ_wrt_typ Q (typ_var_f X)).
Proof.
  intros Q X H. unfold open_typ_wrt_typ. apply guarded_skel_open_preservation; auto.
Qed.

(** * Refinement preserves wellformedness.

    Paper Lemma at [declarative.tex:1380]. If [P ⊳ Q] (colour-respecting
    refinement) and [P] is wellformed under [Ψ ⨟ Γ], then [Q] is too. *)

(** Paper Lemma 3.4 (Refinement preserves well-formedness). [paper-ref: name:"Refinement preserves well-formedness"] *)
Lemma d_refine_preserves_wf : forall Ψ Γ P Q,
    Ψ ⨟ Γ ⊢ₛₖ P ->
    Ψ ⨟ Γ ⊢ᵣ P ▸ Q ->
    Ψ ⨟ Γ ⊢ₛₖ Q.
Proof.
  intros Ψ Γ P Q HwfP Href. induction Href.
  - exact HwfP.
  - exact HwfP.
  - inversion HwfP; subst.
    apply d_wf_skel__arrow; auto.
  - inversion HwfP; subst.
    apply d_wf_skel__all_plain with (L := L `union` L0).
    intros X HX. apply H0; auto.
  - (* hole: input typ_hole, output Q wf under nil; lift to Ψ. *)
    rewrite_env (Ψ ++ (@nil atom)). apply d_wf_skel_psi_weakening. exact H.
  - (* tophole_no_top: input P = typ_tophole P0; output Q = typ_all_plain Q0.
       Inversion on [d_wf_skel Ψ Γ (typ_tophole P0)] gives [guarded_skel P0]
       and [d_wf_skel nil Γ P0]. *)
    inversion HwfP; subst.
    apply d_wf_skel__all_plain with (L := L).
    intros X HX. apply H0; auto.
    apply d_wf_skel_psi_incl with (Ψ := nil); [exact H5 | intros y []].
  - (* tophole_with_top: Q = typ_all_plain (typ_tophole Q0). *)
    apply d_wf_skel__all_plain with (L := L).
    intros X HX.
    apply d_wf_skel__tophole.
    + apply guarded_skel_open. exact H.
    + apply H2; auto.
Qed.

(** [d_wf_typ] / [d_wf_skel] are insensitive to [dbind_typ] / [dbind_skel]
    bindings: only [dbind_tvar] bindings matter for the var-lookup case.
    Strengthening drops a single irrelevant term-binding. *)

Lemma d_wf_typ_strengthening_typ : forall Γ1 Γ2 x A B,
    d_wf_typ (Γ1 ++ (x ~ dbind_typ A) ++ Γ2) B ->
    d_wf_typ (Γ1 ++ Γ2) B.
Proof.
  intros Γ1 Γ2 x A B H. dependent induction H.
  - apply d_wf_typ__unit.
  - apply d_wf_typ__var. apply binds_app_iff in H.
    destruct H as [Hin | Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff in Hin.
      destruct Hin as [Hin | Hin].
      * apply binds_one_iff in Hin. destruct Hin as [_ Habs]. inversion Habs.
      * exact Hin.
  - apply d_wf_typ__arrow; eauto.
  - apply d_wf_typ__all with (L := L `union` dom (Γ1 ++ Γ2)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply H0; eauto.
Qed.

Lemma d_wf_typ_strengthening_skel : forall Γ1 Γ2 x P B,
    d_wf_typ (Γ1 ++ (x ~ dbind_skel P) ++ Γ2) B ->
    d_wf_typ (Γ1 ++ Γ2) B.
Proof.
  intros Γ1 Γ2 x P B H. dependent induction H.
  - apply d_wf_typ__unit.
  - apply d_wf_typ__var. apply binds_app_iff in H.
    destruct H as [Hin | Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff in Hin.
      destruct Hin as [Hin | Hin].
      * apply binds_one_iff in Hin. destruct Hin as [_ Habs]. inversion Habs.
      * exact Hin.
  - apply d_wf_typ__arrow; eauto.
  - apply d_wf_typ__all with (L := L `union` dom (Γ1 ++ Γ2)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply H0; eauto.
Qed.

Lemma d_wf_skel_strengthening_skel : forall Γ1 Γ2 Ψ x P B,
    Ψ ⨟ (Γ1 ++ (x ~ dbind_skel P) ++ Γ2) ⊢ₛₖ B ->
    Ψ ⨟ (Γ1 ++ Γ2) ⊢ₛₖ B.
Proof.
  intros Γ1 Γ2 Ψ x P B H. dependent induction H.
  - apply d_wf_skel__unit.
  - apply d_wf_skel__var. destruct H.
    + left. exact H.
    + right. apply binds_app_iff in H.
      destruct H as [Hin | Hin].
      * apply binds_app_iff. auto.
      * apply binds_app_iff. right. apply binds_app_iff in Hin.
        destruct Hin as [Hin | Hin].
        -- apply binds_one_iff in Hin. destruct Hin as [_ Habs]. inversion Habs.
        -- exact Hin.
  - apply d_wf_skel__arrow; eauto.
  - apply d_wf_skel__all_col with (L := L `union` dom (Γ1 ++ Γ2)).
    intros X HX. eapply H0; eauto.
  - apply d_wf_skel__all_plain with (L := L `union` dom (Γ1 ++ Γ2)).
    intros X HX. eapply H0; eauto.
  - apply d_wf_skel__hole.
  - apply d_wf_skel__tophole; eauto.
Qed.

Lemma d_wf_skel_strengthening_typ : forall Γ1 Γ2 Ψ x A B,
    Ψ ⨟ (Γ1 ++ (x ~ dbind_typ A) ++ Γ2) ⊢ₛₖ B ->
    Ψ ⨟ (Γ1 ++ Γ2) ⊢ₛₖ B.
Proof.
  intros Γ1 Γ2 Ψ x A B H. dependent induction H.
  - apply d_wf_skel__unit.
  - apply d_wf_skel__var. destruct H.
    + left. exact H.
    + right. apply binds_app_iff in H.
      destruct H as [Hin | Hin].
      * apply binds_app_iff. auto.
      * apply binds_app_iff. right. apply binds_app_iff in Hin.
        destruct Hin as [Hin | Hin].
        -- apply binds_one_iff in Hin. destruct Hin as [_ Habs]. inversion Habs.
        -- exact Hin.
  - apply d_wf_skel__arrow; eauto.
  - apply d_wf_skel__all_col with (L := L `union` dom (Γ1 ++ Γ2)).
    intros X HX. eapply H0; eauto.
  - apply d_wf_skel__all_plain with (L := L `union` dom (Γ1 ++ Γ2)).
    intros X HX. eapply H0; eauto.
  - apply d_wf_skel__hole.
  - apply d_wf_skel__tophole; eauto.
Qed.

(** * Context-lookup wellformedness.
    Looking up a binding in a wellformed [denv] returns a wf payload. *)

Lemma d_wf_denv_binds_typ : forall Γ x A,
    d_wf_denv Γ -> binds x (dbind_typ A) Γ -> d_wf_typ Γ A.
Proof.
  induction Γ as [|[y db] Γ' IH]; intros x A Hwf Hbinds.
  - inversion Hbinds.
  - inversion Hbinds as [Heq | Hin].
    + (* head match *)
      inversion Heq; subst.
      inversion Hwf; subst.
      apply d_wf_typ_weakening_head with (Γ' := (x ~ dbind_typ A)). exact H4.
    + (* tail binding *)
      inversion Hwf; subst;
        [ apply d_wf_typ_weakening_head with (Γ' := (y ~ dbind_tvar))
        | apply d_wf_typ_weakening_head with (Γ' := (y ~ dbind_typ A0))
        | apply d_wf_typ_weakening_head with (Γ' := (y ~ dbind_skel P)) ];
        eapply IH; eauto.
Qed.

Lemma d_wf_denv_binds_skel : forall Γ x P,
    d_wf_denv Γ -> binds x (dbind_skel P) Γ -> nil ⨟ Γ ⊢ₛₖ P.
Proof.
  induction Γ as [|[y db] Γ' IH]; intros x P Hwf Hbinds.
  - inversion Hbinds.
  - inversion Hbinds as [Heq | Hin].
    + inversion Heq; subst.
      inversion Hwf; subst.
      apply d_wf_skel_weakening_head with (Γ' := (x ~ dbind_skel P)). exact H5.
    + inversion Hwf; subst;
        [ apply d_wf_skel_weakening_head with (Γ' := (y ~ dbind_tvar))
        | apply d_wf_skel_weakening_head with (Γ' := (y ~ dbind_typ A))
        | apply d_wf_skel_weakening_head with (Γ' := (y ~ dbind_skel P0)) ];
        eapply IH; eauto.
Qed.

(** * Synthesised refinement preserves wellformedness.

    Analogue of [d_refine_preserves_wf] for the colour-aware synthesised
    refinement [Ψ ⨟ Γ ⊢ P ▸ Q]: the ∀ outputs are [typ_all_col colour_*]
    instead of [typ_all_plain], but the proof structure is identical. *)

(** Synthesised analogue of paper Lemma 3.4 (Refinement preserves
    well-formedness). [paper-ref: name:"Refinement preserves well-formedness"] *)
Lemma d_refine_syn_preserves_wf : forall Ψ Γ P Q,
    Ψ ⨟ Γ ⊢ₛₖ P ->
    Ψ ⨟ Γ ⊢ᵣ P ⊳ Q ->
    Ψ ⨟ Γ ⊢ₛₖ Q.
Proof.
  intros Ψ Γ P Q HwfP Href. induction Href.
  - exact HwfP.
  - exact HwfP.
  - inversion HwfP; subst.
    apply d_wf_skel__arrow; auto.
  - inversion HwfP; subst.
    apply d_wf_skel__all_col with (L := L `union` L0).
    intros X HX. apply H0; auto.
  - exact H0.
  - inversion HwfP; subst.
    apply d_wf_skel__all_col with (L := L).
    intros X HX. apply H0; auto.
    apply d_wf_skel_psi_incl with (Ψ := nil); [exact H5 | intros y []].
  - apply d_wf_skel__all_col with (L := L).
    intros X HX.
    apply d_wf_skel__tophole.
    + apply guarded_skel_open. exact H.
    + apply H2; auto.
Qed.

(** * Bridge: every wf type is a wf skeleton (defer).

    The direct bridge [d_wf_typ Γ A → d_wf_skel Ψ Γ A] is non-trivial:
    [d_wf_typ] extends Γ for ∀-binders while [d_wf_skel] extends Ψ. The
    recursive case for [typ_all_col c A] requires a "move from Γ to Ψ"
    lemma that respects the Ψ-scoping rules. Deferred to Phase 2.E's
    skeleton work, where the proof can sit alongside other Γ↔Ψ lemmas. *)

(** * Wellformedness preservation for [d_consis] and [d_sub].

    INTERNAL plumbing — these are not paper-stated lemmas. The paper
    only states wf-preservation for [d_refine] (Lemma 3.4) and [d_pat]
    (Lemma 3.7). We carry [d_consis_preserves_wf] / [d_sub_preserves_wf]
    here purely as plumbing for the [d_typing__sub] case of
    [d_typing_pat_preserves_wf] (which IS Lemma 3.7's d_typing analog
    in the mutual).

    Conclusion: the RHS of these judgments is [d_wf_typ Γ]. The
    var-case admit propagates through to [d_sub_preserves_wf] and
    onward to [d_typing_pat_preserves_wf]'s [d_typing__sub] case. *)

Lemma d_consis_preserves_wf : forall Δ Γ T A,
    Δ ⨟ Γ ⊨ T ≈ A ->
    d_wf_typ Γ A.
Proof.
  intros Δ Γ T A H. induction H.
  - apply d_wf_typ__unit.
  - (* d_consis__var now carries binds via the strengthened rule. *)
    apply d_wf_typ__var; auto.
  - inst_cofinites_for d_wf_typ__all. eauto.
  - inst_cofinites_for d_wf_typ__all. eauto.
  - inst_cofinites_for d_wf_typ__all. eauto.
  - inst_cofinites_for d_wf_typ__all. eauto.
  - apply d_wf_typ__arrow; auto.
Qed.

Lemma d_sub_preserves_wf : forall M Δ Γ T A,
    Γ ⊢[ M ; Δ ] T ⊑ A ->
    d_wf_typ Γ A.
Proof.
  intros M Δ Γ T A H. induction H.
  - eapply d_consis_preserves_wf; eauto.
  - eapply d_consis_preserves_wf; eauto.
  - inst_cofinites_for d_wf_typ__all. eauto.
  - apply d_wf_typ__arrow; auto.
    eapply d_consis_preserves_wf; eauto.
  - assumption.
  - assumption.
Qed.

(** * d_pat_consis / d_pat_sub preservation of wf and guardedness.
    These were originally in prop_skeleton.v; moved here so that
    d_typing_pat_preserves_wf's d_pat__sub case can use them. *)

Lemma d_pat_consis_preserves_guarded : forall Δ Γ SS P,
    d_pat_consis Δ Γ SS P ->
    guarded_skel SS ->
    guarded_skel P.
Proof.
  intros Δ Γ SS P H Hg. inversion H; subst.
  - apply guarded_skel__unit.
  - apply guarded_skel__var.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - apply guarded_skel__arrow.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
Qed.

(** Strengthened with [is_syn_skel P] precondition. This precondition
    holds at every call site that matters in the typing-context use of
    [d_pat_consis] — namely [d_pat_sub__infer] and [d_pat_sub__univ_ghost_r],
    both of which carry [is_syn_skel P] as an explicit rule premise.

    The strengthening closes the [__univ_ghost_inh1] case (RHS
    [typ_all_col colour_inh]) by inversion of [is_syn_skel P] — that
    constructor of [is_syn_skel typ_all_col] only accepts [colour_syn]. *)
Lemma d_pat_consis_preserves_wf : forall Δ Γ SS P,
    d_pat_consis Δ Γ SS P ->
    is_skel SS ->
    nil ⨟ Γ ⊢ₛₖ SS ->
    is_syn_skel P ->
    nil ⨟ Γ ⊢ₛₖ P.
Proof.
  intros Δ Γ SS P H. induction H; intros His_skel Hwf His_syn.
  - apply d_wf_skel__unit.
  - apply d_wf_skel__var. right. auto.
  - inversion His_skel.
  - inversion His_skel.
  - inversion His_skel.
  - inversion His_skel.
  - auto.
  - inversion His_skel; inversion Hwf; inversion His_syn; subst.
    apply d_wf_skel__arrow; auto.
  - inversion His_skel; inversion Hwf; inversion His_syn; subst.
    apply d_wf_skel__tophole.
    + eapply d_pat_consis_preserves_guarded; eauto.
    + apply IHd_pat_consis; auto.
  - (* __univ_ghost_inh1: RHS [typ_all_col colour_inh P] cannot be
       [is_syn_skel] (which only accepts [colour_syn] for [typ_all_col]).
       Case closes by inversion of [His_syn]. *)
    inversion His_syn.
  - inversion His_skel; inversion Hwf; subst.
    apply IHd_pat_consis; auto.
Qed.

(** Strengthened with [is_syn_skel P] precondition (same justification
    as [d_pat_consis_preserves_wf]). The [__arg] case unfolds
    [is_syn_skel (typ_arrow P1 P2)] to get [is_syn_skel P1] for the
    consistency-side appeal and [is_syn_skel P2] for the recursive IH.

    The [__univ_ghost_r] output is [typ_tophole P]; inversion of
    [is_syn_skel typ_tophole P] yields [is_syn_skel P], propagating
    through. The [__ghost] output [P] takes the [is_syn_skel P]
    premise directly. *)
Lemma d_pat_sub_preserves_wf : forall M Δ Γ SS P,
    d_pat_sub M Δ Γ SS P ->
    is_skel SS ->
    nil ⨟ Γ ⊢ₛₖ SS ->
    is_syn_skel P ->
    nil ⨟ Γ ⊢ₛₖ P.
Proof.
  intros M Δ Γ SS P H. induction H; intros His_skel Hwf His_syn.
  - eapply d_pat_consis_preserves_wf; eauto.
  - inversion His_syn; subst.
    apply d_wf_skel__tophole.
    + eapply d_pat_consis_preserves_guarded; eauto.
    + eapply d_pat_consis_preserves_wf; eauto.
  - auto.
  - inversion His_skel; inversion Hwf; subst.
    apply IHd_pat_sub; auto.
  - inversion His_skel; inversion Hwf; inversion His_syn; subst.
    apply d_wf_skel__arrow.
    + eapply d_pat_consis_preserves_wf; eauto.
    + apply IHd_pat_sub; auto.
  - inversion His_skel.
  - inversion His_skel.
Qed.

(** [d_wf_denv]-bound skeletons are is_skel (from the strengthened
    [d_wf_denv__skel] premise). *)
Lemma d_wf_denv_binds_skel_is_skel : forall Γ x P,
    d_wf_denv Γ ->
    binds x (dbind_skel P) Γ ->
    is_skel P.
Proof.
  induction Γ as [|[y db] Γ' IH]; intros x P Hwf Hbinds.
  - inversion Hbinds.
  - inversion Hbinds as [Heq | Hin].
    + inversion Heq; subst. inversion Hwf; subst. exact H4.
    + inversion Hwf; subst; eapply IH; eauto.
Qed.

(** d_pat_sub output is [is_syn_skel] at [mode_tc] / [mode_ti].
    At [mode_fn], d_pat_sub__arg can fire which gives [typ_arrow P1 P2]
    with [P1] from [d_pat_consis] — and we have no [is_syn_skel] guarantee
    on that. The lemma is therefore restricted to non-fn modes. *)
Lemma d_pat_sub_implies_is_syn_skel : forall M Δ Γ SS P,
    d_pat_sub M Δ Γ SS P ->
    (M = mode_tc \/ M = mode_ti) ->
    is_skel SS ->
    is_syn_skel P.
Proof.
  intros M Δ Γ SS P H. induction H; intros Hm Hskel; auto.
  - apply is_syn_skel__tophole. auto.
  - destruct Hm; subst; congruence.
  - apply IHd_pat_sub; auto. inversion Hskel; subst; auto.
  - destruct Hm; subst; congruence.
  - inversion Hskel.
  - inversion Hskel.
Qed.

(** d_pat at mode_ti for base terms outputs [is_skel]. Sufficient for
    the d_pat__sub case of Lemma 3.7 (the only context where we need
    [is_skel] of a d_pat output to feed [d_pat_sub_preserves_wf]). *)
Lemma d_pat_base_mode_ti_is_skel : forall Γ e P,
    is_base_term e ->
    d_pat mode_ti Γ e P ->
    d_wf_denv Γ ->
    is_skel P.
Proof.
  intros Γ e P Hbase Hpat Hwf.
  remember mode_ti as m eqn:Hm.
  induction Hpat; subst; try (inversion Hbase; fail); try discriminate.
  - apply is_skel__unit.
  - eapply d_wf_denv_binds_skel_is_skel; eauto.
  - apply is_typ_is_skel. eapply d_wf_typ_is_typ; eauto.
  - apply is_syn_skel_is_skel.
    eapply d_pat_sub_implies_is_syn_skel; eauto.
Qed.

(** * Paper Lemma 3.7 (Preservation of Skeleton Well-formedness).
    [paper-ref: name:"Preservation of Skeleton Well-formedness"]

    Mutual statement: well-typed terms yield wf result types
    (plumbing — not paper-stated), and well-patterned terms yield wf
    result skeletons (Lemma 3.7 proper, projected as
    [d_pat_preserves_skel_wf] in prop_skeleton.v).

    After the Phase 2.B rule strengthening (wf premises on
    abs/abs_anno/anno), most cases close cleanly. Closed cases:

      d_typing: __unit, __var, __anno, __sub (via d_sub_preserves_wf
        plumbing), __freeze, __forall, __abs, __abs_anno, __app
        (via the d_wf_typ → d_wf_skel bridge on the IH).

      d_pat: __unit, __var, __anno (via bridge), __freeze, __abs,
        __abs_anno (via bridge), __app (via bridge).

    THREE open inline admits remain, with distinct root causes:

    (P1) [d_pat__sub] (line ~975): blocked on
         [d_pat_sub_preserves_wf]. The narrowed form of that lemma is
         tautological (takes [d_wf_skel nil Γ P] AS a side hypothesis
         and returns the same). It needs to be strengthened to "from
         d_pat_sub Δ Γ SS P derive d_wf_skel nil Γ P" WITHOUT the side
         hypothesis. That strengthening requires a Γ↔Ψ "move" lemma
         (the input SS lives in [d_wf_uskel] kind while the output
         must be [d_wf_skel]) which is the same lemma deferred from
         the typ→skel bridge in Phase 2.B. STATUS: structural, not
         paper-level — closeable if move-lemma is proven.

    (P2) [d_pat__abs_check] (line ~989): the rule's conclusion
         produces the skeleton [typ_arrow (typ_tophole typ_hole) Q].
         The skeleton wf rule [d_wf_skel__tophole] requires the body
         to be [guarded_skel], but [typ_hole] is NOT guarded
         ([guarded_skel] excludes [typ_hole] / [typ_tophole]).
         Moreover, the paper explicitly forbids [typ_tophole typ_hole]
         at declarative.tex:1191 ("We also forbid TopHole.Hole").
         STATUS: PAPER-LEVEL TENSION — the d_pat rule produces a
         shape the wf predicate rejects. Closing requires either
         (a) restricting [d_pat__abs_check] to produce a different
         skeleton (changes the rule), or (b) loosening
         [d_wf_skel__tophole] to admit [typ_tophole typ_hole] (changes
         the wf predicate). Both are paper-level decisions.

    (P3) [d_pat__abs_anno_check] (line ~993): same shape as (P2) but
         with [typ_tophole A] where [A] is the user-written annotation.
         If [A] is unguarded (e.g., [A = ∀a. a → a]), the resulting
         skeleton [typ_tophole (∀a. a → a)] fails [guarded_skel].
         STATUS: PAPER-LEVEL TENSION — same as (P2). Conditional
         narrowing ("if [guarded_typ A] then conclusion is wf") works
         for guarded A; for non-guarded A the case is genuinely
         outside the wf predicate's image.

    Summary: 1 closeable structural admit (P1) + 2 paper-level
    tensions (P2, P3). To close 3.7 fully: prove the Γ↔Ψ move lemma,
    and resolve P2/P3 at the paper level.
*)

(** The mutual lemma conditions the d_pat side on [m ∈ {mode_tc, mode_ti}].
    This conditioning is internal — the paper-faithful Lemma 3.7 is
    extracted as [d_pat_preserves_skel_wf] below at mode_tc with no extra
    premises. The condition is needed because the [d_pat__sub] case at
    mode_fn can produce non-wf skeletons via [d_pat_sub__arg] (the
    counter-example: typ_arrow with consis-produced typ_all_col colour_inh
    left arm), and we want the lemma to hold without an additional
    [is_syn_skel] premise on the top-level. *)
Lemma d_typing_pat_preserves_wf :
    (forall m Γ e A,
        Γ ⊢[ m ] e ⇒ A ->
        d_wf_denv Γ ->
        d_wf_typ Γ A) /\
    (forall m Γ e P,
        Γ ⊢[ m ] e ⇨ P ->
        d_wf_denv Γ ->
        (m = mode_tc \/ m = mode_ti) ->
        nil ⨟ Γ ⊢ₛₖ P).
Proof.
  apply d_typing_pat_mut; intros.
  - (* d_typing__unit *) apply d_wf_typ__unit.
  - (* d_typing__var: A is the dbind_typ payload of x in Γ. Use the
       context-lookup wf lemma. *)
    eapply d_wf_denv_binds_typ; eauto.
  - (* d_typing__anno: IH gives d_wf_typ Γ A directly. *)
    apply H; auto.
  - (* d_typing__sub: d_sub_preserves_wf takes [d_wf_typ Γ A] as
       side hypothesis; we get it from the IH on [d_typing mode_ti Γ e A]. *)
    eapply d_sub_preserves_wf; eauto.
  - (* d_typing__freeze: IH gives d_wf_typ Γ A directly. *)
    apply H; auto.
  - (* d_typing__forall: IH gives d_wf_typ ((X~_)++Γ) (open A X) for each
       X. Goal: d_wf_typ Γ (typ_all_col colour_inh A). *)
    apply d_wf_typ__all with (L := L `union` dom Γ).
    intros X HX. apply H; auto.
    apply d_wf_denv__tvar; auto.
  - (* d_typing__abs: rule now carries d_wf_typ Γ A as a premise (the
       2026-05-11 rule-strengthening patch). Close: arrow wf from
       new premise + IH strengthening on B. *)
    apply d_wf_typ__arrow; auto.
    pick fresh x for (L `union` dom Γ).
    eapply d_wf_typ_strengthening_typ with (Γ1 := nil) (x := x) (A := A).
    eauto using d_wf_denv__typ.
  - (* d_typing__abs_anno: same pattern. *)
    apply d_wf_typ__arrow; auto.
    pick fresh x for (L `union` dom Γ).
    eapply d_wf_typ_strengthening_typ with (Γ1 := nil) (x := x) (A := A).
    eauto using d_wf_denv__typ.
  - (* d_typing__app: IH on the function gives d_wf_typ Γ (typ_arrow A B);
       invert to project B. Refinement side adds no new obligation. *)
    assert (Harr : d_wf_typ Γ (typ_arrow A B)) by (apply H0; auto).
    inversion Harr; subst. auto.
  - (* d_pat__unit *) apply d_wf_skel__unit.
  - (* d_pat__var: similar to d_typing__var, using d_wf_denv_binds_skel. *)
    eapply d_wf_denv_binds_skel; eauto.
  - (* d_pat__anno: bridge d_wf_typ → d_wf_skel using
       [d_wf_typ_d_wf_skel]. *)
    apply d_wf_typ_d_wf_skel. auto.
  - (* d_pat__sub: closed via the strengthened [d_pat_sub_preserves_wf]
       and the auxiliary [d_pat_base_mode_ti_is_skel] /
       [d_pat_sub_implies_is_syn_skel]. *)
    assert (Hskel_P : is_skel P) by (eapply d_pat_base_mode_ti_is_skel; eauto).
    assert (Hwf_P : nil ⨟ Γ ⊢ₛₖ P) by (apply H; auto).
    assert (Hsyn_Q : is_syn_skel Q)
      by (eapply d_pat_sub_implies_is_syn_skel; eauto).
    eapply d_pat_sub_preserves_wf; eauto.
  - (* d_pat__freeze: IH at mode_ti gives wf directly. *)
    apply H; auto.
  - (* d_pat__abs: rule now carries d_wf_skel nil Γ P as a premise.
       Goal: d_wf_skel nil Γ (typ_arrow P Q). Arrow from new premise +
       IH strengthening on Q. *)
    apply d_wf_skel__arrow; auto.
    pick fresh x for (L `union` dom Γ).
    eapply d_wf_skel_strengthening_skel with (Γ1 := nil) (x := x) (P := P).
    eapply H; eauto using d_wf_denv__skel, is_inh_skel_is_skel.
    (* decr_mode m at this case: outer m ∈ {tc, ti} and m ≠ tc so m = ti.
       decr_mode ti = ti. So inner mode_ti ∈ {tc, ti}. *)
    destruct H1 as [Habs | Hti]; [subst; contradiction|]. subst.
    simpl. right. reflexivity.
  - (* d_pat__abs_check: produces [typ_tophole (typ_arrow typ_hole Q)]. *)
    apply d_wf_skel__tophole.
    + apply guarded_skel__arrow.
    + apply d_wf_skel__arrow.
      * apply d_wf_skel__hole.
      * pick fresh x for (L `union` dom Γ).
        eapply d_wf_skel_strengthening_skel
          with (Γ1 := nil) (x := x) (P := typ_hole).
        eapply H;
          eauto using d_wf_denv__skel, is_skel__hole, d_wf_skel__hole.
  - (* d_pat__abs_anno: arrow wf via bridge for A and IH strengthening for Q. *)
    apply d_wf_skel__arrow.
    + apply d_wf_typ_d_wf_skel. auto.
    + pick fresh x for (L `union` dom Γ).
      eapply d_wf_skel_strengthening_typ with (Γ1 := nil) (x := x) (A := A).
      eapply H; eauto using d_wf_denv__typ.
      destruct H1 as [Habs | Hti]; [subst; contradiction|]. subst.
      simpl. right. reflexivity.
  - (* d_pat__abs_anno_check: produces [typ_tophole (typ_arrow A Q)]. *)
    apply d_wf_skel__tophole.
    + apply guarded_skel__arrow.
    + apply d_wf_skel__arrow.
      * apply d_wf_typ_d_wf_skel; auto.
      * pick fresh x for (L `union` dom Γ).
        eapply d_wf_skel_strengthening_typ
          with (Γ1 := nil) (x := x) (A := A).
        eapply H; eauto using d_wf_denv__typ.
  - (* d_pat__app: IH on the function (d_typing side) gives
       d_wf_typ Γ (typ_arrow P' Q); invert and bridge Q to a wf skeleton. *)
    assert (Harr : d_wf_typ Γ (typ_arrow P' Q)) by (apply H0; auto).
    inversion Harr; subst.
    apply d_wf_typ_d_wf_skel; auto.
Qed.

(** Paper Lemma 3.7 (Preservation of Skeleton Well-formedness) is
    extracted as [d_pat_preserves_skel_wf] in [prop_skeleton.v],
    specialising the mutual at [mode_tc] with no extra premises. *)
