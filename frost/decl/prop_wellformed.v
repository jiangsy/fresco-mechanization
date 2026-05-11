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

Lemma d_wf_skel_lc : forall Ψ Γ P, d_wf_skel Ψ Γ P -> lc_typ P.
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

Lemma d_wf_ttyp_lc : forall Δ Γ A, d_wf_ttyp Δ Γ A -> lc_typ A.
Proof.
  intros Δ Γ A H. induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - pick fresh X. apply lc_typ_all_etag_exists with (X1 := X).
    apply H0. auto.
Qed.

Lemma d_wf_utyp_lc : forall Δ Γ A, d_wf_utyp Δ Γ A -> lc_typ A.
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

Lemma d_wf_tskel_lc : forall Δ Γ P, d_wf_tskel Δ Γ P -> lc_typ P.
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

Lemma d_wf_uskel_lc : forall Δ Γ P, d_wf_uskel Δ Γ P -> lc_typ P.
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
  - apply d_wf_typ__all with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)).
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
  - apply d_wf_skel__all_col with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)).
    intros Y HY.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var; [| fsetdec | apply (d_wf_skel_lc HB)].
    apply H0; auto.
  - apply d_wf_skel__all_plain with (L := L `union` singleton X `union` dom (Γ1 ++ Γ2)).
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
