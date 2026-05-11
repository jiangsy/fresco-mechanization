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

Lemma d_refine_preserves_wf : forall Ψ Γ P Q,
    d_wf_skel Ψ Γ P ->
    d_refine Ψ Γ P Q ->
    d_wf_skel Ψ Γ Q.
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
    d_wf_skel Ψ (Γ1 ++ (x ~ dbind_skel P) ++ Γ2) B ->
    d_wf_skel Ψ (Γ1 ++ Γ2) B.
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
    d_wf_skel Ψ (Γ1 ++ (x ~ dbind_typ A) ++ Γ2) B ->
    d_wf_skel Ψ (Γ1 ++ Γ2) B.
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
    d_wf_denv Γ -> binds x (dbind_skel P) Γ -> d_wf_skel nil Γ P.
Proof.
  induction Γ as [|[y db] Γ' IH]; intros x P Hwf Hbinds.
  - inversion Hbinds.
  - inversion Hbinds as [Heq | Hin].
    + inversion Heq; subst.
      inversion Hwf; subst.
      apply d_wf_skel_weakening_head with (Γ' := (x ~ dbind_skel P)). exact H4.
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

Lemma d_refine_syn_preserves_wf : forall Ψ Γ P Q,
    d_wf_skel Ψ Γ P ->
    d_refine_syn Ψ Γ P Q ->
    d_wf_skel Ψ Γ Q.
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

(** * Skeleton wellformedness preservation under d_pat (paper:1970).

    The mutual claim: well-typed terms yield wf result types, and
    well-patterned terms yield wf result skeletons. After Phase 2.B's
    rule strengthening (wf premises on the abs/abs_anno rules), most
    cases close. Remaining admits:
    - [d_typing__sub] / [d_pat__sub] need [d_sub_preserves_wf] /
      [d_pat_sub_preserves_wf] (Phase 2.C, Phase 2.E).
    - [d_typing__app] / [d_pat__app] need refinement-side wf and the
      function-type IH projection (Phase 2.D / 2.E).
    - [d_pat__abs_check] / [d_pat__abs_anno_check] produce skeletons
      containing [typ_tophole typ_hole] / [typ_tophole A], which are
      NOT well-formed per the paper's own wf criteria (declarative.tex
      line 1191 explicitly forbids them). This is a paper-level
      tension — the rules produce shapes the wf predicate rejects.
      Documented in PROGRESS.md as a finding; cases admit until the
      paper-level resolution is settled.
*)

Lemma d_typing_pat_preserves_wf :
    (forall m Γ e A,
        d_typing m Γ e A ->
        d_wf_denv Γ ->
        d_wf_typ Γ A) /\
    (forall m Γ e P,
        d_pat m Γ e P ->
        d_wf_denv Γ ->
        d_wf_skel nil Γ P).
Proof.
  apply d_typing_pat_mut; intros.
  - (* d_typing__unit *) apply d_wf_typ__unit.
  - (* d_typing__var: A is the dbind_typ payload of x in Γ. Use the
       context-lookup wf lemma. *)
    eapply d_wf_denv_binds_typ; eauto.
  - (* d_typing__anno: IH gives d_wf_typ Γ A directly. *)
    apply H; auto.
  - (* d_typing__sub: needs d_sub_preserves_wf (Phase 2.C). *)
    admit.
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
  - (* d_typing__app: needs the function-type IH to give an arrow, then
       project the result component. Closure relies on d_refine_syn's wf
       interaction. Phase 2.D. *)
    admit.
  - (* d_pat__unit *) apply d_wf_skel__unit.
  - (* d_pat__var: similar to d_typing__var, using d_wf_denv_binds_skel. *)
    eapply d_wf_denv_binds_skel; eauto.
  - (* d_pat__anno: the pat rule gives A as the inferred type, but A
       isn't a wf'd skel premise; closure via Phase 2.D's anno regularity. *)
    admit.
  - (* d_pat__sub: needs d_pat_sub_preserves_wf (Phase 2.E). *)
    admit.
  - (* d_pat__freeze: IH gives directly. *)
    apply H; auto.
  - (* d_pat__abs: rule now carries d_wf_skel nil Γ P as a premise.
       Goal: d_wf_skel nil Γ (typ_arrow P Q). Arrow from new premise +
       IH strengthening on Q. *)
    apply d_wf_skel__arrow; auto.
    pick fresh x for (L `union` dom Γ).
    eapply d_wf_skel_strengthening_skel with (Γ1 := nil) (x := x) (P := P).
    eauto using d_wf_denv__skel.
  - (* d_pat__abs_check: Q = open output. P here is [typ_tophole typ_hole].
       The IH gives d_wf_skel nil ((x~skel typ_hole)++Γ) Q; close it. *)
    admit.
  - (* d_pat__abs_anno: regularity on the annotation A. *)
    admit.
  - (* d_pat__abs_anno_check: tophole wraps A; need d_wf_typ on A. *)
    admit.
  - (* d_pat__app: cross-track (Phase 2.E). *)
    admit.
Admitted.
