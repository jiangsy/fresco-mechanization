(** Frost declarative typing weakening, native split-syntax form. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.

Set Implicit Arguments.

Lemma d_refine_syn_weakening : forall Γ1 Γ2 Γ3 Ψ Q P,
    d_refine_syn Ψ (Γ1 ++ Γ3) Q P ->
    d_refine_syn Ψ (Γ1 ++ Γ2 ++ Γ3) Q P.
Proof.
  intros Γ1 Γ2 Γ3 Ψ Q P H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var.
    match goal with H : _ \/ _ |- _ => destruct H as [HΨ | Hb] end;
      [ left; assumption | right; analyze_binds Hb ].
  - apply d_refine_syn__arrow; auto.
  - apply d_refine_syn__all with (L := L `union` dom (Γ1 ++ Γ3)). intros X HX.
    eapply (H0 X ltac:(fsetdec) Γ1 Γ3). reflexivity.
  - apply d_refine_syn__hole. apply d_wf_pskl_weakening. assumption.
  - apply d_refine_syn__tophole_remove; auto.
  - apply d_refine_syn__tophole_fill with (L := L `union` dom (Γ1 ++ Γ3)). intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 X ltac:(fsetdec) ((X ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_refine_syn__tophole_keep; [ assumption | auto ].
Qed.

Lemma d_refine_syn_weakening_head : forall Γ Γ' Ψ Q P,
    d_refine_syn Ψ Γ Q P ->
    d_refine_syn Ψ (Γ' ++ Γ) Q P.
Proof.
  intros Γ Γ' Ψ Q P H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_refine_syn_weakening. simpl. exact H.
Qed.

Lemma d_typing_weakening : forall Γ1 Γ2 Γ3 m e B,
    d_typing m (Γ1 ++ Γ3) e B ->
    d_typing m (Γ1 ++ Γ2 ++ Γ3) e B.
Proof.
Admitted.

Lemma d_pat_weakening : forall Γ1 Γ2 Γ3 m e Q,
    d_pat m (Γ1 ++ Γ3) e Q ->
    d_pat m (Γ1 ++ Γ2 ++ Γ3) e Q.
Proof.
Admitted.

Lemma d_typing_weakening_head : forall Γ Γ' m e B,
    d_typing m Γ e B ->
    d_typing m (Γ' ++ Γ) e B.
Proof.
  intros Γ Γ' m e B H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_typing_weakening. exact H.
Qed.

Lemma d_pat_weakening_head : forall Γ Γ' m e Q,
    d_pat m Γ e Q ->
    d_pat m (Γ' ++ Γ) e Q.
Proof.
  intros Γ Γ' m e Q H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_pat_weakening. exact H.
Qed.

