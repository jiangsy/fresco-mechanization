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
Require Import src.frost.decl.prop_subtyping.

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
    apply binds_app_iff in H. destruct H as [Hin|Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_consis__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
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

(** Local copies of [d_consis_tvar_morph] / [d_sub_tvar_morph]
    (see [prop_subtyping.v]); duplicated here to avoid a cyclic import. *)
Lemma d_consis_tvar_morph : forall Γ Γ' Δ T A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_consis Δ Γ T A ->
    d_consis Δ Γ' T A.
Proof.
  intros Γ Γ' Δ T A Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_consis__unit.
  - apply d_consis__var. apply Hmorph; auto.
  - apply d_consis__forall_inh_tagged with (L := L `union` dom Γ'); auto.
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__forall_inh_untagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__forall_syn_tagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__forall_syn_untagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__arrow; auto.
Qed.

Lemma d_sub_tvar_morph : forall Γ Γ' M Δ T A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_sub M Δ Γ T A ->
    d_sub M Δ Γ' T A.
Proof.
  intros Γ Γ' M Δ T A Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_sub__infer; auto. eapply d_consis_tvar_morph; eauto.
  - apply d_sub__check; auto. eapply d_consis_tvar_morph; eauto.
  - apply d_sub__forall_r with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff; [left | right]; auto.
  - apply d_sub__arg.
    + eapply d_consis_tvar_morph; eauto.
    + apply IHd_sub; auto.
  - eapply d_sub__forall_l_tagged; eauto.
    eapply d_wf_ttyp_tvar_morph; eauto.
  - eapply d_sub__forall_l_untagged; eauto.
    eapply d_wf_ttyp_tvar_morph; eauto.
Qed.

Lemma d_refine_syn_weakening : forall Γ1 Γ2 Γ3 Ψ P Q,
    d_refine_syn Ψ (Γ1 ++ Γ3) P Q ->
    d_refine_syn Ψ (Γ1 ++ Γ2 ++ Γ3) P Q.
Proof.
  intros Γ1 Γ2 Γ3 Ψ P Q H. dependent induction H.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H.
    + left. auto.
    + right. apply binds_app_iff in H. destruct H as [HX | HX].
      * apply binds_app_iff. auto.
      * apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_refine_syn__arrow; eauto.
  - apply d_refine_syn__all_inh with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. eapply H0; eauto.
  - apply d_refine_syn__hole; auto. eapply d_wf_skel_weakening; eauto.
  - apply d_refine_syn__tophole_no_top with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. eapply H0; eauto.
  - apply d_refine_syn__tophole_with_top with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    + auto.
    + eapply d_wf_skel_weakening; eauto.
    + intros X HX. eapply H2; eauto.
Qed.

Lemma d_refine_weakening : forall Γ1 Γ2 Γ3 Ψ P Q,
    d_refine Ψ (Γ1 ++ Γ3) P Q ->
    d_refine Ψ (Γ1 ++ Γ2 ++ Γ3) P Q.
Proof.
  intros Γ1 Γ2 Γ3 Ψ P Q H. dependent induction H.
  - apply d_refine__unit.
  - apply d_refine__var. destruct H.
    + left. auto.
    + right. apply binds_app_iff in H. destruct H as [HX | HX].
      * apply binds_app_iff. auto.
      * apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_refine__arrow; eauto.
  - apply d_refine__all with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. eapply H0; eauto.
  - apply d_refine__hole; auto. eapply d_wf_skel_weakening; eauto.
  - apply d_refine__tophole_no_top with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. eapply H0; eauto.
  - apply d_refine__tophole_with_top with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    eapply d_wf_skel_weakening; eauto.
Qed.

Lemma d_refine_weakening_head : forall Γ Γ' Ψ P Q,
    d_refine Ψ Γ P Q ->
    d_refine Ψ (Γ' ++ Γ) P Q.
Proof. intros. rewrite_env (nil ++ Γ' ++ Γ). apply d_refine_weakening. simpl. auto. Qed.

Lemma d_refine_syn_weakening_head : forall Γ Γ' Ψ P Q,
    d_refine_syn Ψ Γ P Q ->
    d_refine_syn Ψ (Γ' ++ Γ) P Q.
Proof. intros. rewrite_env (nil ++ Γ' ++ Γ). apply d_refine_syn_weakening. simpl. auto. Qed.

(** Context tvar-morphism for [d_refine]. *)
Lemma d_refine_tvar_morph : forall Γ Γ' Ψ P Q,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_refine Ψ Γ P Q ->
    d_refine Ψ Γ' P Q.
Proof.
  intros Γ Γ' Ψ P Q Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_refine__unit.
  - apply d_refine__var. destruct H as [Hin | Hb]; [left|right]; auto.
  - apply d_refine__arrow; auto.
  - apply d_refine__all with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
  - apply d_refine__hole. eapply d_wf_skel_tvar_morph; eauto.
  - apply d_refine__tophole_no_top with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
  - apply d_refine__tophole_with_top with (L := L `union` dom Γ'); auto.
    eapply d_wf_skel_tvar_morph; eauto.
Qed.

(** Context tvar-morphism for [d_refine_syn]. *)
Lemma d_refine_syn_tvar_morph : forall Γ Γ' Ψ P Q,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_refine_syn Ψ Γ P Q ->
    d_refine_syn Ψ Γ' P Q.
Proof.
  intros Γ Γ' Ψ P Q Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [Hin | Hb]; [left|right]; auto.
  - apply d_refine_syn__arrow; auto.
  - apply d_refine_syn__all_inh with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
  - apply d_refine_syn__hole; auto. eapply d_wf_skel_tvar_morph; eauto.
  - apply d_refine_syn__tophole_no_top with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
  - apply d_refine_syn__tophole_with_top with (L := L `union` dom Γ'); auto.
    eapply d_wf_skel_tvar_morph; eauto.
Qed.

Lemma d_pat_consis_weakening : forall Γ1 Γ2 Γ3 Δ SS P,
    d_pat_consis Δ (Γ1 ++ Γ3) SS P ->
    d_pat_consis Δ (Γ1 ++ Γ2 ++ Γ3) SS P.
Proof.
  intros Γ1 Γ2 Γ3 Δ SS P H. dependent induction H.
  - apply d_pat_consis__unit.
  - apply d_pat_consis__var.
    apply binds_app_iff in H. destruct H as [Hin|Hin].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_pat_consis__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_pat_consis__forall_inh_untagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_pat_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_pat_consis__forall_syn_untagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_pat_consis__ghost; auto.
    apply d_wf_skel_weakening; auto.
  - apply d_pat_consis__arrow; eauto.
  - apply d_pat_consis__univ_ghost_arr; eauto.
  - apply d_pat_consis__univ_ghost_inh1 with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_pat_consis__univ_ghost_pass; eauto.
Qed.

Lemma d_pat_sub_weakening : forall Γ1 Γ2 Γ3 M Δ SS P,
    d_pat_sub M Δ (Γ1 ++ Γ3) SS P ->
    d_pat_sub M Δ (Γ1 ++ Γ2 ++ Γ3) SS P.
Proof.
  intros Γ1 Γ2 Γ3 M Δ SS P H. dependent induction H.
  - apply d_pat_sub__infer; auto. apply d_pat_consis_weakening; auto.
  - apply d_pat_sub__univ_ghost_r; auto. apply d_pat_consis_weakening; auto.
  - apply d_pat_sub__ghost; auto.
    apply d_wf_skel_weakening; auto.
  - apply d_pat_sub__univ_ghost_l; auto.
  - apply d_pat_sub__arg; auto. apply d_pat_consis_weakening; auto.
  - eapply d_pat_sub__forall_l_tagged; eauto.
    eapply d_wf_tskel_weakening; eauto.
  - eapply d_pat_sub__forall_l_untagged; eauto.
    eapply d_wf_tskel_weakening; eauto.
Qed.

Lemma d_pat_consis_weakening_head : forall Γ Γ' Δ SS P,
    d_pat_consis Δ Γ SS P ->
    d_pat_consis Δ (Γ' ++ Γ) SS P.
Proof.
  intros. rewrite_env (nil ++ Γ' ++ Γ). apply d_pat_consis_weakening. simpl. auto.
Qed.

Lemma d_pat_sub_weakening_head : forall Γ Γ' M Δ SS P,
    d_pat_sub M Δ Γ SS P ->
    d_pat_sub M Δ (Γ' ++ Γ) SS P.
Proof.
  intros. rewrite_env (nil ++ Γ' ++ Γ). apply d_pat_sub_weakening. simpl. auto.
Qed.

(** Context tvar-morphism for [d_pat_consis]. *)
Lemma d_pat_consis_tvar_morph : forall Γ Γ' Δ SS P,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_pat_consis Δ Γ SS P ->
    d_pat_consis Δ Γ' SS P.
Proof.
  intros Γ Γ' Δ SS P Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_pat_consis__unit.
  - apply d_pat_consis__var. apply Hmorph; auto.
  - apply d_pat_consis__forall_inh_tagged with (L := L `union` dom Γ'); auto.
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb];
      apply binds_app_iff; [left | right]; auto.
  - apply d_pat_consis__forall_inh_untagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb];
      apply binds_app_iff; [left | right]; auto.
  - apply d_pat_consis__forall_syn_tagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb];
      apply binds_app_iff; [left | right]; auto.
  - apply d_pat_consis__forall_syn_untagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb];
      apply binds_app_iff; [left | right]; auto.
  - apply d_pat_consis__ghost; auto. eapply d_wf_skel_tvar_morph; eauto.
  - apply d_pat_consis__arrow; auto.
  - apply d_pat_consis__univ_ghost_arr; auto.
  - apply d_pat_consis__univ_ghost_inh1 with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY. destruct HbY as [Hb | Hb];
      apply binds_app_iff; [left | right]; auto.
  - apply d_pat_consis__univ_ghost_pass; auto.
Qed.

(** Context tvar-morphism for [d_pat_sub]. *)
Lemma d_pat_sub_tvar_morph : forall Γ Γ' M Δ SS P,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_pat_sub M Δ Γ SS P ->
    d_pat_sub M Δ Γ' SS P.
Proof.
  intros Γ Γ' M Δ SS P Hmorph H. generalize dependent Γ'.
  induction H; intros Γ' Hmorph.
  - apply d_pat_sub__infer; auto. eapply d_pat_consis_tvar_morph; eauto.
  - apply d_pat_sub__univ_ghost_r; auto. eapply d_pat_consis_tvar_morph; eauto.
  - apply d_pat_sub__ghost; auto. eapply d_wf_skel_tvar_morph; eauto.
  - apply d_pat_sub__univ_ghost_l; auto.
  - apply d_pat_sub__arg; auto. eapply d_pat_consis_tvar_morph; eauto.
  - eapply d_pat_sub__forall_l_tagged; eauto.
    eapply d_wf_tskel_tvar_morph; eauto.
  - eapply d_pat_sub__forall_l_untagged; eauto.
    eapply d_wf_tskel_tvar_morph; eauto.
Qed.

(** * Weakening for the mutual d_typing / d_pat (Phase 2.D.1b). *)

Lemma d_typing_pat_weakening :
    (forall m Γ e A, d_typing m Γ e A ->
       forall Γ1 Γ2 Γ3, Γ = Γ1 ++ Γ3 ->
                         d_typing m (Γ1 ++ Γ2 ++ Γ3) e A) /\
    (forall m Γ e P, d_pat m Γ e P ->
       forall Γ1 Γ2 Γ3, Γ = Γ1 ++ Γ3 ->
                         d_pat m (Γ1 ++ Γ2 ++ Γ3) e P).
Proof.
  apply d_typing_pat_mut; intros; subst.
  - apply d_typing__unit; auto.
  - apply d_typing__var. apply binds_app_iff in b. destruct b.
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_typing__anno; auto.
  - apply d_typing__sub with (A := A); auto.
    apply d_sub_weakening; auto.
  - apply d_typing__freeze; auto.
  - apply d_typing__forall with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H; auto.
  - apply d_typing__abs with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_typ_weakening; eauto.
    + intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H; auto.
  - apply d_typing__abs_anno with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_typ_weakening; eauto.
    + intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H; auto.
  - apply d_typing__app with (P := P) (P' := P') (A := A); eauto.
    apply d_refine_syn_weakening; auto.
  - apply d_pat__unit.
  - apply d_pat__var. apply binds_app_iff in b. destruct b.
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_pat__anno. eapply d_wf_typ_weakening; eauto.
  - apply d_pat__sub with (P := P); eauto.
    apply d_pat_sub_weakening; auto.
  - apply d_pat__freeze; auto.
  - apply d_pat__abs with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_skel_weakening; eauto.
    + intros x Hx. rewrite_env (((x ~ dbind_skel P) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H; auto.
  - apply d_pat__abs_check with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros x Hx. rewrite_env (((x ~ dbind_skel typ_hole) ++ Γ1) ++ Γ2 ++ Γ3).
    apply H; auto.
  - apply d_pat__abs_anno with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_typ_weakening; eauto.
    + intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H; auto.
  - apply d_pat__abs_anno_check with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_typ_weakening; eauto.
    + intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H; auto.
  - apply d_pat__app with (P := P) (P' := P'); eauto.
    apply d_refine_syn_weakening; auto.
Qed.

Corollary d_typing_weakening : forall Γ1 Γ2 Γ3 m e A,
    d_typing m (Γ1 ++ Γ3) e A ->
    d_typing m (Γ1 ++ Γ2 ++ Γ3) e A.
Proof. intros. eapply (proj1 d_typing_pat_weakening); eauto. Qed.

Corollary d_pat_weakening : forall Γ1 Γ2 Γ3 m e P,
    d_pat m (Γ1 ++ Γ3) e P ->
    d_pat m (Γ1 ++ Γ2 ++ Γ3) e P.
Proof. intros. eapply (proj2 d_typing_pat_weakening); eauto. Qed.

Corollary d_typing_weakening_head : forall Γ Γ' m e A,
    d_typing m Γ e A ->
    d_typing m (Γ' ++ Γ) e A.
Proof. intros. rewrite_env (nil ++ Γ' ++ Γ). apply d_typing_weakening. simpl. auto. Qed.

Corollary d_pat_weakening_head : forall Γ Γ' m e P,
    d_pat m Γ e P ->
    d_pat m (Γ' ++ Γ) e P.
Proof. intros. rewrite_env (nil ++ Γ' ++ Γ). apply d_pat_weakening. simpl. auto. Qed.

(** Mutual context morphism for [d_typing] / [d_pat]: preserve ALL
    bindings (tvar, typ, skel). Stronger than [d_consis_tvar_morph]
    since the [d_typing__var] / [d_pat__var] rules look up
    [dbind_typ] / [dbind_skel] bindings. *)
Lemma d_typing_pat_ctx_morph :
    (forall m Γ e A, d_typing m Γ e A ->
       forall Γ', (forall X bn, binds X bn Γ -> binds X bn Γ') ->
                  d_typing m Γ' e A) /\
    (forall m Γ e P, d_pat m Γ e P ->
       forall Γ', (forall X bn, binds X bn Γ -> binds X bn Γ') ->
                  d_pat m Γ' e P).
Proof.
  apply d_typing_pat_mut.
  - (* d_typing__unit *)
    intros Γ Hcompat Γ' Hm. apply d_typing__unit; auto.
  - (* d_typing__var *)
    intros Γ x A Hbnd Γ' Hm. apply d_typing__var. apply Hm; auto.
  - (* d_typing__anno *)
    intros Γ e A Hinh Hty IH Γ' Hm. apply d_typing__anno; auto.
  - (* d_typing__sub *)
    intros Γ m e A B Hbase Hty IH Hsub Γ' Hm.
    apply d_typing__sub with (A := A); auto.
    eapply d_sub_tvar_morph; [|exact Hsub].
    intros Y HbY. eapply Hm; eauto.
  - (* d_typing__freeze *)
    intros Γ e A Hty IH Γ' Hm. apply d_typing__freeze; auto.
  - (* d_typing__forall *)
    intros L Γ e A Hval Hbody IH Γ' Hm.
    apply d_typing__forall with (L := L `union` dom Γ'); auto.
    intros X HX. apply IH; auto.
    intros Y bn HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff; [left; auto | right; auto].
  - (* d_typing__abs: no m≠mode_tc premise *)
    intros L Γ m e A B Hinh Hwf Hbody IH Γ' Hm.
    apply d_typing__abs with (L := L `union` dom Γ'); auto.
    + eapply d_wf_typ_tvar_morph; [|exact Hwf].
      intros Y HbY. eapply Hm; eauto.
    + intros x Hx. apply IH; auto.
      intros Y bn HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb]; apply binds_app_iff; [left; auto | right; auto].
  - (* d_typing__abs_anno *)
    intros L Γ m e A B Hwf Hbody IH Γ' Hm.
    apply d_typing__abs_anno with (L := L `union` dom Γ'); auto.
    + eapply d_wf_typ_tvar_morph; [|exact Hwf].
      intros Y HbY. eapply Hm; eauto.
    + intros x Hx. apply IH; auto.
      intros Y bn HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb]; apply binds_app_iff; [left; auto | right; auto].
  - (* d_typing__app *)
    intros Γ m e1 e2 P P' A B Hpat IHpat Href Hty1 IH1 Hty2 IH2 Γ' Hm.
    apply d_typing__app with (P := P) (P' := P') (A := A); auto.
    eapply d_refine_syn_tvar_morph; [|exact Href].
    intros Y HbY. eapply Hm; eauto.
  - (* d_pat__unit *)
    intros Γ Γ' Hm. apply d_pat__unit.
  - (* d_pat__var *)
    intros Γ x P Hbnd Γ' Hm. apply d_pat__var. apply Hm; auto.
  - (* d_pat__anno *)
    intros Γ e A Hwf Γ' Hm. apply d_pat__anno.
    eapply d_wf_typ_tvar_morph; [|exact Hwf].
    intros Y HbY. eapply Hm; eauto.
  - (* d_pat__sub *)
    intros Γ m e P Q Hbase Hpat IH Hsub Γ' Hm.
    apply d_pat__sub with (P := P); auto.
    eapply d_pat_sub_tvar_morph; [|exact Hsub].
    intros Y HbY. eapply Hm; eauto.
  - (* d_pat__freeze *)
    intros Γ e P Hpat IH Γ' Hm. apply d_pat__freeze; auto.
  - (* d_pat__abs *)
    intros L Γ m e P Q Hmne Hinh Hwf Hbody IH Γ' Hm.
    apply d_pat__abs with (L := L `union` dom Γ'); auto.
    + eapply d_wf_skel_tvar_morph; [|exact Hwf].
      intros Y HbY. eapply Hm; eauto.
    + intros x Hx. apply IH; auto.
      intros Y bn HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb]; apply binds_app_iff; [left; auto | right; auto].
  - (* d_pat__abs_check *)
    intros L Γ e Q Hbody IH Γ' Hm.
    apply d_pat__abs_check with (L := L `union` dom Γ').
    intros x Hx. apply IH; auto.
    intros Y bn HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff; [left; auto | right; auto].
  - (* d_pat__abs_anno *)
    intros L Γ m e A Q Hmne Hwf Hbody IH Γ' Hm.
    apply d_pat__abs_anno with (L := L `union` dom Γ'); auto.
    + eapply d_wf_typ_tvar_morph; [|exact Hwf].
      intros Y HbY. eapply Hm; eauto.
    + intros x Hx. apply IH; auto.
      intros Y bn HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb]; apply binds_app_iff; [left; auto | right; auto].
  - (* d_pat__abs_anno_check *)
    intros L Γ e A Q Hwf Hbody IH Γ' Hm.
    apply d_pat__abs_anno_check with (L := L `union` dom Γ'); auto.
    + eapply d_wf_typ_tvar_morph; [|exact Hwf].
      intros Y HbY. eapply Hm; eauto.
    + intros x Hx. apply IH; auto.
      intros Y bn HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb]; apply binds_app_iff; [left; auto | right; auto].
  - (* d_pat__app *)
    intros Γ m e1 e2 P P' Q Hpat2 IH2 Href Hty1 IH1 Γ' Hm.
    apply d_pat__app with (P := P) (P' := P'); auto.
    eapply d_refine_syn_tvar_morph; [|exact Href].
    intros Y HbY. eapply Hm; eauto.
Qed.

Corollary d_typing_ctx_morph : forall Γ Γ' m e A,
    (forall X bn, binds X bn Γ -> binds X bn Γ') ->
    d_typing m Γ e A ->
    d_typing m Γ' e A.
Proof. intros. eapply (proj1 d_typing_pat_ctx_morph); eauto. Qed.

Corollary d_pat_ctx_morph : forall Γ Γ' m e P,
    (forall X bn, binds X bn Γ -> binds X bn Γ') ->
    d_pat m Γ e P ->
    d_pat m Γ' e P.
Proof. intros. eapply (proj2 d_typing_pat_ctx_morph); eauto. Qed.

(** * Phase 2.D.2 — Term substitution (expvar) for d_typing / d_pat.

    HONEST status (audit 2026-05-12):
    - The paper does NOT state a term-substitution lemma anywhere
      (paper appendix proofs.tex has metasubstitution lemmas only).
    - Nothing else in our development currently calls this lemma; it
      was added in Phase 2.D as a standalone target.
    - Strategy is the standard 18-case mutual induction; closure
      needs auxiliary lemmas (d_sub strengthening, lc_exp regularity,
      is_base_term subst, possibly is_value preservation if we
      handle d_typing__forall via direct value-restriction reasoning;
      alternative: restructure that case via general subsumption).
    - Marked with [Abort] (not [Admitted]) so it does not pollute
      the development with an axiom. The statement is preserved in
      this file as a target. *)

Lemma d_typing_pat_subst_exp_mut :
    (forall m Γ e1 B, d_typing m Γ e1 B ->
       forall Γ1 Γ2 x A e2,
         Γ = Γ1 ++ (x ~ dbind_typ A) ++ Γ2 ->
         d_typing mode_ti Γ2 e2 A ->
         d_typing m (Γ1 ++ Γ2) (subst_exp_in_exp e2 x e1) B) /\
    (forall m Γ e1 P, d_pat m Γ e1 P ->
       forall Γ1 Γ2 x A e2,
         Γ = Γ1 ++ (x ~ dbind_typ A) ++ Γ2 ->
         d_typing mode_ti Γ2 e2 A ->
         d_pat m (Γ1 ++ Γ2) (subst_exp_in_exp e2 x e1) P).
Proof.
Abort.

(* Corollaries removed; would not type-check after Abort.
   d_typing_subst_exp and d_pat_subst_exp will be added once the
   mutual lemma is proven. *)

(** * Phase 2.D.3 — Type substitution (typvar) for d_typing + d_pat.

    Substituting a well-formed monotype B for a type variable X in
    both the expression and the result type preserves typing. The
    mutual statement threads B through Γ1 (which may mention X) and
    drops the X-binding.

    Caveats:
    - [d_typing__forall] introduces a new type variable; the cofinite
      framework permits choosing Y ∉ {X} ∪ ..., commuting subst with
      open via [subst_typ_in_exp_open_exp_wrt_typ_var].
    - [d_typing__anno] / [d_typing__abs] / [d_typing__abs_anno] carry
      [is_inh_typ A] / [d_wf_typ Γ A] premises — both transfer under
      subst provided B itself is inh and wf. We thread this as
      side hypotheses.
    - [d_pat__abs] / [d_pat__abs_anno] / [d_pat__abs_anno_check]
      similarly need [is_inh_skel P] / [d_wf_typ Γ A] / wf-skel under
      substitution. Skeleton side requires [guarded_typ B] like the
      [d_wf_skel_subst] lemma — same constraint as Phase 2.B.

    For now we state the lemma; the proof is large (18 cases) but
    mechanical, paralleling [d_typing_pat_weakening]. We admit with
    a documented rationale.
*)

Lemma d_typing_pat_subst_typ_mut :
    (forall m Γ e A,
        d_typing m Γ e A ->
        forall X B Γ1 Γ2,
          Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
          d_wf_typ Γ2 B ->
          guarded_typ B ->
          d_typing m (map (subst_typ_in_dbind B X) Γ1 ++ Γ2)
                     (subst_typ_in_exp B X e)
                     (subst_typ_in_typ B X A))
 /\ (forall m Γ e P,
        d_pat m Γ e P ->
        forall X B Γ1 Γ2,
          Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
          d_wf_typ Γ2 B ->
          guarded_typ B ->
          d_pat m (map (subst_typ_in_dbind B X) Γ1 ++ Γ2)
                  (subst_typ_in_exp B X e)
                  (subst_typ_in_typ B X P)).
Proof.
  (* Research-grade laborious 18-case proof — see file-level rationale
     above. The non-trivial cases all use the lngen subst-open commute
     lemma and the [d_wf_*_subst] family from prop_wellformed.v. *)
Admitted.

(** * Phase 2.D.4 — Narrowing.

    Replacing a typ-binding [x : A] in the context with [x : A'] where
    A' ≤ A preserves typing. The "≤" relation we use is the shallow
    polymorphic subtyping d_shallow_sub (paper line 1062), which is
    the right notion for context narrowing per the design doc.

    Sub-case: when A' = A (identity), narrowing is trivially weakening
    by identity replacement. Non-trivial when A' is strictly smaller.
*)

Lemma d_typing_narrowing : forall Γ1 x A A' Γ2 m e B,
    d_typing m (Γ1 ++ (x ~ dbind_typ A) ++ Γ2) e B ->
    d_shallow_sub Γ2 A' A ->
    d_wf_typ Γ2 A' ->
    d_typing m (Γ1 ++ (x ~ dbind_typ A') ++ Γ2) e B.
Proof.
  (* Induction on the typing derivation. The only delicate case is
     [d_typing__var] for the narrowed x: we need to produce a derivation
     of e=exp_var_f x with the narrowed type A. Per paper:574 (general
     subsumption), this requires invoking d_typing_general_subsumption
     (Task 6). Since Task 6 itself is research-grade, we admit. *)
Admitted.

(** * Phase 2.D.5 — Structural rules (SuffixMoving).

    Paper proofs.tex lemma:structural: commuting independent context
    entries. We use the simplest sufficient notion of "independent":
    the dom of Γ2 is disjoint from the free type-vars used by the
    bindings in Ξ, and vice versa.

    The strict statement requires defining a "free vars of context"
    function, which is essentially Metalib's fv on dbind. Rather than
    defining that here, we narrow to a clean special case: moving a
    single binding past a fresh suffix.
*)

(** Paper Lemma D.3 (Structural rules). [paper-ref: lemma:structural]
    Narrowed: a single-binding move past a fresh suffix.

    The hypothesis [y notin dom Γ1] is not actually needed for the
    morph-based proof (since [binds] is duplicate-tolerant), but we
    keep it in the statement to track the paper's preconditions. *)
Lemma d_typing_suffix_moving_singleton : forall Γ1 y b Γ2 m e A,
    d_typing m (Γ1 ++ (y ~ b) ++ Γ2) e A ->
    y `notin` dom Γ1 ->
    d_typing m (Γ1 ++ Γ2 ++ (y ~ b)) e A.
Proof.
  intros Γ1 y b Γ2 m e A Hty Hnotin.
  eapply d_typing_ctx_morph; [|exact Hty].
  intros X bn HbY. apply binds_app_iff in HbY.
  destruct HbY as [HbΓ1 | HbRest].
  - apply binds_app_iff. left. exact HbΓ1.
  - apply binds_app_iff in HbRest. destruct HbRest as [Hbyb | HbΓ2].
    + apply binds_app_iff. right. apply binds_app_iff. right. exact Hbyb.
    + apply binds_app_iff. right. apply binds_app_iff. left. exact HbΓ2.
Qed.

(** d_pat analogue. *)
Lemma d_pat_suffix_moving_singleton : forall Γ1 y b Γ2 m e P,
    d_pat m (Γ1 ++ (y ~ b) ++ Γ2) e P ->
    y `notin` dom Γ1 ->
    d_pat m (Γ1 ++ Γ2 ++ (y ~ b)) e P.
Proof.
  intros Γ1 y b Γ2 m e P Hpat Hnotin.
  eapply d_pat_ctx_morph; [|exact Hpat].
  intros X bn HbY. apply binds_app_iff in HbY.
  destruct HbY as [HbΓ1 | HbRest].
  - apply binds_app_iff. left. exact HbΓ1.
  - apply binds_app_iff in HbRest. destruct HbRest as [Hbyb | HbΓ2].
    + apply binds_app_iff. right. apply binds_app_iff. right. exact Hbyb.
    + apply binds_app_iff. right. apply binds_app_iff. left. exact HbΓ2.
Qed.

(** * Phase 2.D.6 — General subsumption (paper declarative.tex:574).

    The paper's restatable Lemma states that subsumption is admissible
    for ARBITRARY terms, not just base terms. The d_typing__sub rule
    in our calculus restricts the [is_base_term e] premise.

    Strategy (per the design doc): for non-base terms, the rule that
    introduced them can absorb the subsumption into its existing
    conclusion. This is genuinely research-grade — for several cases
    (notably [d_typing__app]) the result requires a transitivity
    lemma for d_sub which itself is not proven (paper:574 sub-lemma).

    We prove the base-term cases cleanly, and admit the non-base
    cases with documented rationale (per the design's strictification
    policy: "narrow to base + abs + freeze if hard").
*)

(** Paper Lemma 3.1 (General subsumption). [paper-ref: lemma:general-subsumption]

    Strategy: paper proof factors through a syntax-directed restatement
    of the type system, using [thm:typing-syn-soundness] / [_completeness]
    + [Generalised General Subsumption] on the syntax-directed system.
    The mech does not have a separate syntax-directed system, so we
    close directly on the bidirectional system. The direct closure
    requires [d_sub] transitivity (paper [thm:subtyping-transitivity] /
    [thm:consist-subtyping-transitivity]); see [d_consis_extends_d_sub_nil]
    in [prop_subtyping.v] which is the narrowed transitivity sufficient
    for the [__sub] case.

    Added precondition [d_wf_denv Γ]: needed for [d_typing_pat_preserves_wf]
    to extract [d_wf_typ Γ A0] for the intermediate type, which then
    discharges the [d_wf_typ] precondition of [d_consis_extends_d_sub_nil].

    Closure status — see the [D1 closure structure] comment below for the
    detailed map across Hsub × Hty cases. *)
(** D1 closure structure (this commit):

    Approach — induct on Hsub primarily, then dispatch on Hty's shape
    within each Hsub case. Key supporting facts that simplify the
    proof globally:

    - [d_typing_pat_preserves_wf] → [d_wf_typ Γ A] from Hty.
    - [d_sub_LHS_mono_wf] on Hsub + [d_wf_typ Γ A] → [mono_typ A].
    - For [Hsub = __infer / __check]: LHS is_typ (from mono) → by
      [d_consis_empty_eq], B = A. So both reduce to a mode-lift at the
      same mono type → discharged by [d_typing_lift_mono].
    - For [Hsub = __forall_r]: dispatch on Hty.
      * base terms (unit/var/anno/sub): use [d_typing__sub] with Hsub.
      * values (abs/abs_anno): use [d_typing__forall] + Hsub-IH at each X.
      * applications: NOT a value, NOT base — needs function-side lift
        (research-grade; admitted).
    - For [Hsub = __arg]: similar dispatch; the body-conversion path
      requires recursive general subsumption on the body (research-grade
      for the cases where the body's Hsub-inner is itself __arg /
      __forall_r). The mode-lift sub-case (inner __infer / __check) is
      closeable, but full closure needs an extended induction structure
      (paper's "FN^n" generalisation). Admitted for non-mode-lift cases.
    - For [Hsub = __forall_l_*]: A would be [typ_all_etag] /
      [typ_all_plain] (from Hsub's LHS shape), violating [d_wf_typ Γ A].
      Vacuous. *)
(** Strong form with [Γ_pre ++ Γ] split (following [d_sub_subst_mono]
    pattern): Hsub and Hty live at [(Γ_pre ++ Γ)], with Γ as the "base"
    context. After [dependent induction Hsub], the IH at a sub-Hsub
    abstracts over both Γ_pre and Γ — so we can apply it at a different
    Γ_pre'. This unlocks:

    - __arg + __abs body conversion: set Γ_pre' := (x ~ T1) ++ Γ_pre,
      then body's general subsumption is the IH.
    - __forall_r body via Hsub-IH at sub-Hsub_X (set Γ_pre' :=
      (X ~ tvar) ++ Γ_pre). *)
Theorem d_typing_general_subsumption_split : forall m Γ_pre Γ e A B,
    d_wf_denv (Γ_pre ++ Γ) ->
    d_typing mode_ti (Γ_pre ++ Γ) e A ->
    d_sub m nil (Γ_pre ++ Γ) A B ->
    d_typing m (Γ_pre ++ Γ) e B.
Proof.
  intros m Γ_pre Γ e A B Hwfd Hty Hsub.
  assert (HwfA : d_wf_typ (Γ_pre ++ Γ) A) by
    (eapply (proj1 d_typing_pat_preserves_wf); eauto).
  assert (HmonoA : mono_typ A) by (eapply d_sub_LHS_mono_wf; eauto).
  generalize dependent e.
  dependent induction Hsub; intros e Hty.
  - (* d_sub__infer: m = mode_ti, [d_consis nil Γ T A]. By
       d_consis_empty_eq on mono T, A = T. Goal becomes Hty. *)
    assert (Heq : T = A) by
      (eapply d_consis_empty_eq; eauto using mono_typ_is_typ).
    subst T. exact Hty.
  - (* d_sub__check: m = mode_tc. By d_consis_empty_eq, A = T (lemma's T).
       Need to lift Hty from mode_ti to mode_tc at the mono type T.
       d_typing_lift_mono handles this. *)
    rename T into A0.
    assert (Heq : A0 = A) by
      (eapply d_consis_empty_eq; eauto using mono_typ_is_typ).
    subst A0.
    apply d_typing_lift_mono with (m_target := mode_tc) in Hty; auto.
    apply d_sub__check; auto.
  - (* d_sub__forall_r: m = mode_tc, B = typ_all_col colour_inh A'.
       Dispatch on Hty's shape. *)
    rename T into A0. rename A into A'.
    inversion Hty; subst.
    + (* __unit *)
      apply d_typing__sub with (A := typ_unit).
      * apply is_base_term__unit.
      * apply d_typing__unit; auto.
      * apply d_sub__forall_r with (L := L); auto.
    + (* __var *)
      apply d_typing__sub with (A := A0).
      * apply is_base_term__var.
      * apply d_typing__var; auto.
      * apply d_sub__forall_r with (L := L); auto.
    + (* __anno *)
      apply d_typing__sub with (A := A0).
      * apply is_base_term__anno.
      * exact Hty.
      * apply d_sub__forall_r with (L := L); auto.
    + (* __sub: e base, inner d_typing mode_ti Γ e A_inner, inner sub at
         mode_ti. Compose inner d_consis (from inversion) with each Hsub_X
         via d_consis_extends_d_sub_nil. *)
      match goal with
      | Hsub_inner : d_sub mode_ti nil _ ?A_inner A0 |- _ =>
          apply d_typing__sub with (A := A_inner); auto;
          apply d_sub__forall_r with (L := L); intros X HX;
          inversion Hsub_inner; subst;
          try (match goal with H' : ?m0 <> ?m0 |- _ =>
                 exfalso; apply H'; reflexivity end);
          apply d_consis_extends_d_sub_nil with (A := A0); auto;
          [ apply d_consis_weakening_head; auto
          | apply d_wf_typ_weakening_head;
            eapply (proj1 d_typing_pat_preserves_wf); eauto ]
      end.
    + (* __abs: e = exp_abs e0. Apply d_typing__forall + Hsub-IH per X.
         Re-shape ((X~tvar) ++ Γ_pre ++ Γ) into the IH's expected
         (?Γ_pre' ++ ?Γ') pattern using rewrite_env. *)
      apply d_typing__forall with (L := L `union` dom (Γ_pre ++ Γ)).
      * apply is_value__abs.
      * intros X HX.
        rewrite_env (((X ~ dbind_tvar) ++ Γ_pre) ++ Γ).
        apply H0 with (X := X); auto.
        -- rewrite_env ((X ~ dbind_tvar) ++ (Γ_pre ++ Γ)).
           apply d_wf_denv__tvar; auto.
        -- rewrite_env ((X ~ dbind_tvar) ++ (Γ_pre ++ Γ)).
           apply d_wf_typ_weakening_head; auto.
        -- rewrite_env ((X ~ dbind_tvar) ++ (Γ_pre ++ Γ)).
           apply d_typing_weakening_head; auto.
    + (* __abs_anno *)
      apply d_typing__forall with (L := L `union` dom (Γ_pre ++ Γ)).
      * apply is_value__abs_anno.
      * intros X HX.
        rewrite_env (((X ~ dbind_tvar) ++ Γ_pre) ++ Γ).
        apply H0 with (X := X); auto.
        -- rewrite_env ((X ~ dbind_tvar) ++ (Γ_pre ++ Γ)).
           apply d_wf_denv__tvar; auto.
        -- rewrite_env ((X ~ dbind_tvar) ++ (Γ_pre ++ Γ)).
           apply d_wf_typ_weakening_head; auto.
        -- rewrite_env ((X ~ dbind_tvar) ++ (Γ_pre ++ Γ)).
           apply d_typing_weakening_head; auto.
    + (* __app: NOT a value, NOT base — research-grade. *)
      admit.
  - (* d_sub__arg: m = mode_fn m_inner, B = typ_arrow A1 A2.
       Dispatch on Hty's shape. Base-term Hty (unit/var/anno/sub) close
       via [d_typing__sub] using the outer __arg Hsub directly. Non-base
       Hty (abs/abs_anno/app) need body conversion — research-grade
       (admitted) for non-mode-lift sub-Hsubs.

       The outer Δ = nil destructures Δ1 ++ Δ2 = nil → both nil. *)
    apply app_eq_nil in x as [HΔ1 HΔ2]. subst Δ1 Δ2.
    inversion Hty; subst.
    + (* __var: Hty = d_typing__var, e = exp_var x with A = typ_arrow ...
         Wrap in d_typing__sub at (mode_fn m). *)
      apply d_typing__sub with (A := typ_arrow T1 T2).
      * apply is_base_term__var.
      * apply d_typing__var; auto.
      * rewrite_env (@nil atom ++ @nil atom).
        apply d_sub__arg; auto.
    + (* __anno: e = exp_anno e' A. Wrap. *)
      apply d_typing__sub with (A := typ_arrow T1 T2).
      * apply is_base_term__anno.
      * exact Hty.
      * rewrite_env (@nil atom ++ @nil atom).
        apply d_sub__arg; auto.
    + (* __sub: e base, compose inner sub with outer __arg via
         d_consis_extends_d_sub_nil. *)
      match goal with
      | Hsub_inner : d_sub mode_ti nil _ ?A_inner (typ_arrow T1 T2) |- _ =>
          apply d_typing__sub with (A := A_inner); auto;
          inversion Hsub_inner; subst;
          try (match goal with H' : ?m0 <> ?m0 |- _ =>
                 exfalso; apply H'; reflexivity end);
          apply d_consis_extends_d_sub_nil with (A := typ_arrow T1 T2); auto;
          [ rewrite_env (@nil atom ++ @nil atom);
            apply d_sub__arg; auto
          | eapply (proj1 d_typing_pat_preserves_wf); eauto ]
      end.
    + (* __abs: e = exp_abs e0, A = typ_arrow T1 T2. Apply d_typing__abs
         at (mode_fn m). Body conversion depends on inner Hsub's shape.

         Closure plan:
         - inner __infer / __check: A2 = T2 via d_consis_empty_eq on mono
           T2; body needs only mode lift via d_typing_lift_mono.
         - inner __forall_r / __arg: A2 != T2; body needs full D1.
           Requires parametric Γ_ext IH (paper's "FN^n"). Admitted. *)
      assert (HmonoT1 : mono_typ T1) by (inversion HmonoA; auto).
      assert (HmonoT2 : mono_typ T2) by (inversion HmonoA; auto).
      assert (HwfT1 : d_wf_typ (Γ_pre ++ Γ) T1) by (inversion HwfA; auto).
      assert (HwfT2 : d_wf_typ (Γ_pre ++ Γ) T2) by (inversion HwfA; auto).
      (* A1 = T1 via d_consis_empty_eq on mono T1. *)
      match goal with H : d_consis nil _ T1 ?A1 |- _ =>
        assert (HeqA1 : T1 = A1)
          by (apply d_consis_empty_eq with (Γ := (Γ_pre ++ Γ)); auto using mono_typ_is_typ);
        subst A1
      end.
      (* Save body forall by name. *)
      match goal with Hbody : forall y : atom, _ |- _ =>
        rename Hbody into Hty_body
      end.
      (* Pick L = (body's L) ∪ dom Γ so freshness derives both notins. *)
      match type of Hty_body with
      | forall y, y `notin` ?L_body -> _ =>
          apply d_typing__abs with (L := L_body `union` dom (Γ_pre ++ Γ))
      end.
      * apply mono_typ_is_inh_typ. exact HmonoT1.
      * exact HwfT1.
      * intros x Hx.
        simpl in Hty_body.   (* unfold decr_mode mode_ti = mode_ti *)
        inversion Hsub; subst.
        -- (* inner __infer (m = mode_ti, A2 = T2). *)
          match goal with H_c : d_consis nil _ T2 ?A2_var |- _ =>
            assert (HeqA2 : T2 = A2_var)
              by (apply d_consis_empty_eq with (Γ := (Γ_pre ++ Γ));
                  auto using mono_typ_is_typ);
            subst A2_var
          end.
          apply Hty_body; fsetdec.
        -- (* inner __check (m = mode_tc, A2 = T2). Body mode lift to tc. *)
          match goal with H_c : d_consis nil _ T2 ?A2_var |- _ =>
            assert (HeqA2 : T2 = A2_var)
              by (apply d_consis_empty_eq with (Γ := (Γ_pre ++ Γ));
                  auto using mono_typ_is_typ);
            subst A2_var
          end.
          apply d_typing_lift_mono with (A := T2); auto.
          ++ apply Hty_body; fsetdec.
          ++ apply d_wf_denv__typ; auto.
          ++ apply d_sub__check.
             ** intros ε T0 Heq. rewrite Heq in HmonoT2. inversion HmonoT2.
             ** intros T0 Heq. rewrite Heq in HmonoT2. inversion HmonoT2.
             ** apply mono_typ_is_inh_typ. exact HmonoT2.
             ** apply d_consis_refl_mono.
                --- exact HmonoT2.
                --- apply d_wf_typ_weakening_head. exact HwfT2.
        -- (* inner __forall_r: body needs full D1 (recursive). The IHHsub
             from `dependent induction Hsub` is fixed at outer Γ via a
             context equation; cannot lift body to (x~T1)++Γ_pre++Γ.
             Path: lex induction or Hty-induction. Admitted. *)
          admit.
        -- (* inner __arg: same. *) admit.
        -- (* inner __forall_l_tagged: T2 = typ_all_etag, contradicts mono. *)
          inversion HmonoT2.
        -- (* inner __forall_l_untagged: T2 = typ_all_plain, contradicts. *)
          inversion HmonoT2.
    + (* __abs_anno: e = exp_abs_anno T1 e0. Same proof as __abs but
         without is_inh_typ premise. *)
      assert (HmonoT1 : mono_typ T1) by (inversion HmonoA; auto).
      assert (HmonoT2 : mono_typ T2) by (inversion HmonoA; auto).
      assert (HwfT1 : d_wf_typ (Γ_pre ++ Γ) T1) by (inversion HwfA; auto).
      assert (HwfT2 : d_wf_typ (Γ_pre ++ Γ) T2) by (inversion HwfA; auto).
      match goal with H : d_consis nil _ T1 ?A1_var |- _ =>
        assert (HeqA1 : T1 = A1_var)
          by (apply d_consis_empty_eq with (Γ := (Γ_pre ++ Γ)); auto using mono_typ_is_typ);
        subst A1_var
      end.
      match goal with Hbody : forall y : atom, _ |- _ =>
        rename Hbody into Hty_body
      end.
      match type of Hty_body with
      | forall y, y `notin` ?L_body -> _ =>
          apply d_typing__abs_anno with (L := L_body `union` dom (Γ_pre ++ Γ))
      end.
      * exact HwfT1.
      * intros x Hx.
        simpl in Hty_body.
        inversion Hsub; subst.
        -- (* inner __infer (m = mode_ti, A2 = T2). *)
          match goal with H_c : d_consis nil _ T2 ?A2_var |- _ =>
            assert (HeqA2 : T2 = A2_var)
              by (apply d_consis_empty_eq with (Γ := (Γ_pre ++ Γ));
                  auto using mono_typ_is_typ);
            subst A2_var
          end.
          apply Hty_body; fsetdec.
        -- (* inner __check (m = mode_tc, A2 = T2). *)
          match goal with H_c : d_consis nil _ T2 ?A2_var |- _ =>
            assert (HeqA2 : T2 = A2_var)
              by (apply d_consis_empty_eq with (Γ := (Γ_pre ++ Γ));
                  auto using mono_typ_is_typ);
            subst A2_var
          end.
          apply d_typing_lift_mono with (A := T2); auto.
          ++ apply Hty_body; fsetdec.
          ++ apply d_wf_denv__typ; auto.
          ++ apply d_sub__check.
             ** intros ε T0 Heq. rewrite Heq in HmonoT2. inversion HmonoT2.
             ** intros T0 Heq. rewrite Heq in HmonoT2. inversion HmonoT2.
             ** apply mono_typ_is_inh_typ. exact HmonoT2.
             ** apply d_consis_refl_mono.
                --- exact HmonoT2.
                --- apply d_wf_typ_weakening_head. exact HwfT2.
        -- (* inner __forall_r: research-grade. *) admit.
        -- (* inner __arg: research-grade. *) admit.
        -- inversion HmonoT2.
        -- inversion HmonoT2.
    + (* __app: function-side conversion. *) admit.
  - (* d_sub__forall_l_tagged: A = typ_all_etag _ _, but [d_wf_typ Γ A]
       (from HwfA) doesn't admit typ_all_etag. Vacuous. *)
    inversion HwfA.
  - (* d_sub__forall_l_untagged: similar. *)
    inversion HwfA.
Admitted.

(** D1 = the strong form at Γ_pre := nil. *)
Theorem d_typing_general_subsumption : forall Γ e A B m,
    d_wf_denv Γ ->
    d_typing mode_ti Γ e A ->
    d_sub m nil Γ A B ->
    d_typing m Γ e B.
Proof.
  intros Γ e A B m Hwfd Hty Hsub.
  apply d_typing_general_subsumption_split with (Γ_pre := nil) (A := A); auto.
Qed.

(** * Phase 2.D.7 — Stability S1 (argument-permutation).

    Design doc §3.D anchor: [f : ∀a b. a → (a → a) → int] applied to
    e1 e2 should give the same int as some [f' : ∀a. (a → a) → a → int]
    applied to e2 e1.

    Per the design's strictification policy, we attempt the strongest
    form first and narrow if needed. Below we state the strongest
    formulation (transposition of two adjacent arguments at any type),
    and a narrowed monotype-only version.

    Status: the most-general form fails to typecheck because re-typing
    the swapped function [λ y x. f x y] requires a d_typing__app
    derivation that the current rules cannot construct without a
    d_typing_app_inversion lemma (which itself is research-grade).
    We document this and produce a counter-example in PROGRESS.md.

    Narrowed form: transposition of two adjacent monotype arguments.
    Even this is research-grade — admits with rationale.
*)

Lemma d_typing_swap_mono : forall Γ f e1 e2 A1 A2 C m,
    mono_typ A1 ->
    mono_typ A2 ->
    d_typing m Γ (exp_app (exp_app f e1) e2) C ->
    d_typing mode_ti Γ f (typ_arrow A1 (typ_arrow A2 C)) ->
    d_typing mode_tc Γ e1 A1 ->
    d_typing mode_tc Γ e2 A2 ->
    (* The swapped function: λ y:A2. λ x:A1. f x y, where the body
       is built using locally-nameless de Bruijn indices. *)
    exists f_swap,
      d_typing mode_ti Γ f_swap (typ_arrow A2 (typ_arrow A1 C)) /\
      d_typing m Γ (exp_app (exp_app f_swap e2) e1) C.
Proof.
  (* Constructive: f_swap := exp_abs_anno A2 (exp_abs_anno A1
                                  (exp_app (exp_app f
                                             (exp_var_b 0))
                                           (exp_var_b 1))).
     Typing f_swap reduces to typing the inner [f x y] under the
     extended context, then closing twice with d_typing__abs_anno.
     The application [f_swap e2 e1] then types by [d_typing__app]
     applied twice.

     The remaining obstacle: producing the inner [d_pat] derivation
     for the arguments under the typing__app rules requires either
     (a) a d_pat-from-d_typing lemma, or (b) the algorithmic side's
     skeleton inference (Phase 3). Neither is currently available,
     so this lemma is admitted with a documented research-grade
     status. *)
Admitted.

(** * Phase 2.D.8 — Stability S2 (application-restructuring).

    Typability invariant under β-equivalent restructurings:
        Γ ⊢_M f e1 e2 ⇒ B  iff  Γ ⊢_M (λx:A1. f x e2) e1 ⇒ B.

    Same caveats as S1: requires inverting and rebuilding application
    derivations through d_pat / d_refine_syn / d_typing__abs_anno.
*)

Lemma d_typing_app_restructure : forall Γ f e1 e2 A1 B m,
    d_typing m Γ (exp_app (exp_app f e1) e2) B ->
    d_typing mode_tc Γ e1 A1 ->
    (* The restructured term [(λ x:A1. f x e2) e1]. *)
    d_typing m Γ
      (exp_app (exp_abs_anno A1
                 (exp_app (exp_app f (exp_var_b 0))
                          e2))
               e1) B.
Proof.
  (* Same research-grade pattern as S1. Requires a d_pat derivation
     for e2 in the extended context (x : A1) — which transfers by
     weakening — plus a d_refine_syn weakening (provable). The
     d_typing__app premise about the refined function type matches.

     But: the outer [d_typing__app (λx. f x e2) e1] requires the
     inner abs_anno to type at A1 → B, which depends on f's type
     containing A1 → ... — recovered by inversion on the original
     typing. Research-grade. Admitted. *)
Admitted.

(** * Order irrelevance (colleague's [order_irrel_app] adapted to Frost).

    Inspired by a stability lemma used in a colleague's mechanisation:
    if two variables [x] and [y] in scope have function types that are
    related by an argument permutation, then a curried application of
    [x] to a list of args and of [y] to the permuted args produce the
    same result type.

    The full n-argument version requires defining [curry_ty],
    [curry_tm], [forall_prefix] helpers — deferred. Below is the
    simplest concrete instance: 2 arguments, 0 forall-prefix, both
    arguments monotype (so the function types are first-order arrows).

    [paper-ref: stability:order-irrelevance] (no paper match yet; new
    target inspired by external system) *)

(** Two-argument adjacent swap when both functions are simultaneously
    in scope with the swapped function types. *)
Lemma d_typing_order_irrel_adj : forall Γ x y A1 A2 R e1 e2 m,
    binds x (dbind_typ (typ_arrow A1 (typ_arrow A2 R))) Γ ->
    binds y (dbind_typ (typ_arrow A2 (typ_arrow A1 R))) Γ ->
    d_typing m Γ (exp_app (exp_app (exp_var_f x) e1) e2) R ->
    d_typing m Γ (exp_app (exp_app (exp_var_f y) e2) e1) R.
Proof.
  (* Proof strategy via the colour/mode lens:

     Invert d_typing on the outer application: d_typing__app fires
     (with d_typing__sub for the function side at mode_fn). The
     function-side d_typing of [exp_app x e1] at [mode_fn m] inverts
     similarly, ending at d_typing__var for x. From binds-x we recover
     the type [A1 → A2 → R]. The d_refine_syn / d_pat structures pin
     e1 to A1 and e2 to A2.

     Reconstruct symmetrically: d_typing__app at [exp_app y e2] with
     [d_typing__var] for y giving [A2 → A1 → R], then outer app with e1.

     The skeleton inference (d_pat / d_refine_syn) for e2 and e1 is
     mode_tc and is mechanically preserved by argument-order swap
     (the patterns don't reference position).

     ADMITTED: requires non-trivial d_typing inversion through d_pat
     and d_refine_syn — same machinery as d_typing_swap_mono. The
     auxiliary d_pat-from-d_typing lemma (cited in d_typing_swap_mono)
     is the key blocker. *)
Admitted.

(** N-argument version (target). Requires [forall_prefix] /
    [curry_ty] / [curry_tm] helpers. The forall-prefixed version
    would interact with the colour discipline at [d_typing__forall]
    (value restriction) — extending the proof to n quantifiers
    needs commuting argument-permutation with the cofinite
    quantifier introduction. Documented as future work. *)


(** * Phase 2.D.9 — Expressiveness E1 (Church-encoded existentials).

    Three concrete typing theorems for the Church encoding of
    existential types: introduction, elimination, and round-trip.

    Concrete types (using typ_unit as the paper's "Int" stand-in
    since Frost has no separate Int):
        mkPkg : Int → ∀β. (∀α. α → β) → β
        getInt : (∀β. (∀α. α → β) → β) → Int

    Witness terms (using locally-nameless de Bruijn):
        mkPkg := λv. λk. k v
        getInt := λp. p [Int] (λα. λx. x)   -- but Frost has no
                                                explicit type-app;
                                                the type abstraction
                                                is silently introduced
                                                by [d_typing__forall].

    Status: the design doc §3.D explicitly flags this as a benchmark:
    "if Church-encoded existentials don't typecheck without
    annotations, document as a finding (not strictification)".
    We state the three theorems and document.
*)

Definition E1_mkPkg : exp :=
  (* λv. λk. k v *)
  exp_abs (exp_abs (exp_app (exp_var_b 0) (exp_var_b 1))).

Definition E1_pkg_typ : typ :=
  (* ∀β. (∀α. α → β) → β *)
  typ_all_col colour_inh
    (typ_arrow
       (typ_all_col colour_inh
          (typ_arrow (typ_var_b 0) (typ_var_b 1)))
       (typ_var_b 0)).

Definition E1_mkPkg_typ : typ :=
  (* unit → ∀β. (∀α. α → β) → β *)
  typ_arrow typ_unit E1_pkg_typ.

Theorem E1_intro : d_typing mode_tc nil E1_mkPkg E1_mkPkg_typ.
Proof.
  (* Witnessing this would require a derivation tree
     d_typing__abs (intro for the outer λv : unit)
       d_typing__forall (intro for the ∀β, since the body λk. k v
                        is a value and the forall rule applies)
         d_typing__abs (intro for λk : ∀α. α → β)
           d_typing__app (apply k to v)
             ... refinement chain producing the right pattern ...
     The β / α variables (bound in the [typ_all_col] scopes) cross
     under [d_typing__forall] via cofinite quantification, requiring
     [d_typing_pat_subst_typ_mut] (Task 3) to commute open with the
     body. Since Task 3 is admitted, this derivation cannot be
     constructed cleanly here.
     Documented as a Phase 2.D research-grade finding. *)
Admitted.

Definition E1_getInt : exp :=
  (* λp. p [unit] (λα. λx. x) — without explicit type-app, the value
     restriction's forall_inh / forall_syn rules silently introduce
     the [β = unit] instantiation. The applied function below is
     just a "default ε:unit" Church-style identity. *)
  exp_abs (exp_app (exp_var_b 0)
                   (exp_abs (exp_anno exp_unit typ_unit))).

Definition E1_getInt_typ : typ :=
  typ_arrow E1_pkg_typ typ_unit.

Theorem E1_elim : d_typing mode_tc nil E1_getInt E1_getInt_typ.
Proof.
  (* Witnessing requires applying p to a polymorphic continuation
     k : ∀α. α → unit. Producing the d_pat-side derivation for the
     k argument, including its refinement to the unfreshened [∀α. ...]
     shape, is again gated on Task 3 (type subst). Documented. *)
Admitted.

Theorem E1_roundtrip :
    d_typing mode_tc nil
      (exp_app E1_getInt (exp_app E1_mkPkg exp_unit))
      typ_unit.
Proof.
  (* Composition of E1_intro and E1_elim with a single d_typing__app
     in the middle. Since both intros are admitted, this is too.
     Documented as a research-grade benchmark per design §3.D. *)
Admitted.
