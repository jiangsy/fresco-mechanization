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

Lemma d_pat_consis_weakening : forall Γ1 Γ2 Γ3 Δ R Q,
    d_pat_consis Δ (Γ1 ++ Γ3) R Q ->
    d_pat_consis Δ (Γ1 ++ Γ2 ++ Γ3) R Q.
Proof.
  intros Γ1 Γ2 Γ3 Δ R Q H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst.
  - apply d_pat_consis__unit.
  - apply d_pat_consis__var. analyze_binds H.
  - eapply d_pat_consis__arrow;
      [ eapply IHd_pat_consis1 | eapply IHd_pat_consis2 ]; reflexivity.
  - apply d_pat_consis__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__forall_inh_untagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__forall_syn with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__ghostg.
  - apply d_pat_consis__topholeg. eapply IHd_pat_consis; reflexivity.
  - apply d_pat_consis__hole. apply d_wf_pskl_weakening. assumption.
  - apply d_pat_consis__tophole. eapply IHd_pat_consis; reflexivity.
  - apply d_pat_consis__tophole_inh with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__tophole_drop. eapply IHd_pat_consis; reflexivity.
Qed.

Lemma d_pat_sub_weakening : forall Γ1 Γ2 Γ3 m Δ R Q,
    d_pat_sub m Δ (Γ1 ++ Γ3) R Q ->
    d_pat_sub m Δ (Γ1 ++ Γ2 ++ Γ3) R Q.
Proof.
  intros Γ1 Γ2 Γ3 m Δ R Q H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst.
  - apply d_pat_sub__infer; [ apply d_pat_consis_weakening; assumption | assumption ].
  - apply d_pat_sub__univ_ghost_r; try assumption.
    apply d_pat_consis_weakening; assumption.
  - eapply d_pat_sub__arg;
      [ apply d_pat_consis_weakening; eassumption | eapply IHd_pat_sub; reflexivity ].
  - eapply d_pat_sub__forall_l_tagged.
    + assumption.
    + eassumption.
    + eassumption.
    + apply d_wf_uskl_weakening; eassumption.
    + assumption.
    + eapply IHd_pat_sub; reflexivity.
  - eapply d_pat_sub__forall_l_untagged.
    + assumption.
    + eassumption.
    + eassumption.
    + apply d_wf_uskl_weakening; eassumption.
    + assumption.
    + eapply IHd_pat_sub; reflexivity.
  - apply d_pat_sub__ghost. apply d_wf_pskl_weakening. assumption.
  - apply d_pat_sub__univ_ghost_l; [ assumption | eapply IHd_pat_sub; reflexivity ].
  - apply d_pat_sub__ghostg.
  - apply d_pat_sub__univ_ghost_lg; [ assumption | eapply IHd_pat_sub; reflexivity ].
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

