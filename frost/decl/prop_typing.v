(** Frost — declarative typing metatheory (Phase 2.D). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Set Implicit Arguments.

(** * Supporting weakening lemmas for non-mutual judgments. *)

Lemma d_consis_weakening : forall Γ1 Γ2 Γ3 Δ T A,
    d_consis Δ (Γ1 ++ Γ3) T A ->
    d_consis Δ (Γ1 ++ Γ2 ++ Γ3) T A.
Proof.
  intros Γ1 Γ2 Γ3 Δ T A H.
  dependent induction H.
  - apply d_consis__unit.
  - apply d_consis__var.
  - apply d_consis__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__forall_inh_untagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__forall_syn_untagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__arrow; eauto.
Qed.

Lemma d_sub_weakening : forall Γ1 Γ2 Γ3 M Δ T A,
    d_sub M Δ (Γ1 ++ Γ3) T A ->
    d_sub M Δ (Γ1 ++ Γ2 ++ Γ3) T A.
Proof.
  intros Γ1 Γ2 Γ3 M Δ T A H. dependent induction H.
  - apply d_sub__infer; auto. apply d_consis_weakening; auto.
  - apply d_sub__check; auto. apply d_consis_weakening; auto.
  - apply d_sub__forall_r with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_sub__arg; eauto. apply d_consis_weakening; auto.
  - eapply d_sub__forall_l_tagged; eauto.
    eapply d_wf_ttyp_weakening; eauto.
  - eapply d_sub__forall_l_untagged; eauto.
    eapply d_wf_ttyp_weakening; eauto.
Qed.
