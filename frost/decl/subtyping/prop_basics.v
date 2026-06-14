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


(** The synthesised painting of any locally-closed [ptyp] is synthesised
    ([is_styp]): every ∀ becomes [btyp_all_syn].  (Induct on [lc_ptyp] so the
    ∀ body's [is_styp] follows from the per-instance IH.) *)
Lemma is_styp_ptyp_to_btyp_syn : forall A,
    lc_ptyp A -> is_styp (ptyp_to_btyp_syn A).
Proof.
  intros A H. induction H; simpl.
  - constructor.
  - constructor.
  - constructor; assumption.
  - apply is_styp__all with (L := empty). intros X _.
    change (btyp_var_f X) with (ptyp_to_btyp_syn (ptyp_var_f X)).
    rewrite <- ptyp_to_btyp_syn_open.
    match goal with H : forall _, is_styp _ |- _ => apply H end.
Qed.


Lemma d_consis_weakening : forall Γ1 Γ2 Γ3 Δ C B,
    Δ ⨟ (Γ1 ++ Γ3) ⊨ C ≈ B ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊨ C ≈ B.
Proof.
  intros Γ1 Γ2 Γ3 Δ C B H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst.
  - apply d_consis__unit. assumption.
  - apply d_consis__var; [ | assumption ].
    match goal with Hb : binds _ _ _ |- _ => analyze_binds Hb end.
  - eapply d_consis__arrow.
    + eapply IHd_consis1; reflexivity.
    + eapply IHd_consis2; reflexivity.
    + assumption.
  - eapply d_consis__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ3)); [ | eassumption ].
    intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_consis__forall_inh_untagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_consis__forall_syn with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
Qed.

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
  intros Γ1 Γ2 Γ3 m Δ C B H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst.
  - apply d_sub__infer; [ apply d_consis_weakening; assumption | assumption | assumption ].
  - apply d_sub__check;
      [ assumption | assumption | apply d_consis_weakening; assumption | assumption ].
  - apply d_sub__forall_r with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - eapply d_sub__arg.
    + apply d_consis_weakening; eassumption.
    + match goal with IH : forall _ _, _ -> d_sub _ _ _ _ _ |- _ => apply (IH Γ1 Γ3 eq_refl) end.
    + eassumption.
  - eapply d_sub__forall_l_tagged.
    + assumption.
    + eassumption.
    + eassumption.
    + apply d_wf_utyp_weakening; eassumption.
    + assumption.
    + match goal with IH : forall _ _, _ -> d_sub _ _ _ _ _ |- _ => apply (IH Γ1 Γ3 eq_refl) end.
  - eapply d_sub__forall_l_untagged.
    + assumption.
    + eassumption.
    + eassumption.
    + apply d_wf_utyp_weakening; eassumption.
    + assumption.
    + match goal with IH : forall _ _, _ -> d_sub _ _ _ _ _ |- _ => apply (IH Γ1 Γ3 eq_refl) end.
Qed.

Lemma d_sub_weakening_head : forall Γ Γ' m Δ C B,
    Δ ⨟ Γ ⊢[ m ] C ⊑ B ->
    Δ ⨟ (Γ' ++ Γ) ⊢[ m ] C ⊑ B.
Proof.
  intros Γ Γ' m Δ C B H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_sub_weakening. simpl. exact H.
Qed.

