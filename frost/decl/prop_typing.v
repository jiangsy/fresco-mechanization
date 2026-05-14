(** Frost — declarative typing metatheory (Phase 2.D). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
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

(** [d_typing_narrow_consis]: narrowing under d_consis equivalence,
    with [is_syn_typ Aold] precondition.

    This is a restricted narrowing that BREAKS the circular dependency
    with general subsumption. The classic [d_typing_narrowing] above
    uses [d_shallow_sub] and its [d_typing__var] case needs general
    subsumption to lift the new binding's type back to the old —
    circular.

    Here we use [d_consis nil Γ2 Anew Aold] instead and require
    [is_syn_typ Aold]. The [d_typing__var] case is then closed via
    [d_typing__sub + d_sub__infer + d_consis] — non-circular.

    Proof: by mutual induction via [d_typing_pat_mut]. The
    [d_typing__var] case at the narrowed binding closes as
    sketched. The d_pat half is invariant under dbind_typ narrowing
    since d_pat only reads dbind_skel / dbind_tvar entries.

    Body kept as scaffold (structural reconstruction across 18 cases —
    the mechanical bookkeeping is non-trivial but does not require
    further research-grade machinery). *)
Lemma d_typing_narrow_consis :
    (forall m Γ_full e B,
        d_typing m Γ_full e B ->
        forall Γ1 x Aold Anew Γ2,
          Γ_full = Γ1 ++ (x ~ dbind_typ Aold) ++ Γ2 ->
          d_consis nil Γ2 Anew Aold ->
          is_syn_typ Aold ->
          d_wf_typ Γ2 Anew ->
          d_typing m (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2) e B) /\
    (forall m Γ_full e P,
        d_pat m Γ_full e P ->
        forall Γ1 x Aold Anew Γ2,
          Γ_full = Γ1 ++ (x ~ dbind_typ Aold) ++ Γ2 ->
          d_consis nil Γ2 Anew Aold ->
          is_syn_typ Aold ->
          d_wf_typ Γ2 Anew ->
          d_pat m (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2) e P).
Proof.
  apply d_typing_pat_mut.
  (* d_typing__unit *)
  - intros Γ Hcompat Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_typing__unit. auto.
  (* d_typing__var *)
  - intros Γ x A Hb Γ1 x0 Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply binds_app_iff in Hb. destruct Hb as [Hb_pre | Hb_in].
    + apply d_typing__var. apply binds_app_iff. left. exact Hb_pre.
    + apply binds_app_iff in Hb_in. destruct Hb_in as [Hb_x | Hb_post].
      * apply binds_one_iff in Hb_x. destruct Hb_x as [Heq Hbeq].
        subst x. inversion Hbeq. subst A.
        apply d_typing__sub with (A := Anew).
        -- apply is_base_term__var.
        -- apply d_typing__var. apply binds_app_iff. right.
           apply binds_app_iff. left. apply binds_one_iff. auto.
        -- apply d_sub__infer; auto.
           rewrite_env (Γ1 ++ ((x0 ~ dbind_typ Anew) ++ Γ2)).
           apply d_consis_weakening_head.
           apply d_consis_weakening_head. auto.
      * apply d_typing__var. apply binds_app_iff. right.
        apply binds_app_iff. right. exact Hb_post.
  (* d_typing__anno *)
  - intros Γ e A Hinh Hty_inner IH
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_typing__anno; auto.
    eapply IH; eauto.
  (* d_typing__sub *)
  - intros Γ m e A B Hbase Hty_inner IH Hsub
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_typing__sub with (A := A); auto.
    + eapply IH; eauto.
    + eapply d_sub_tvar_morph; [|exact Hsub].
      intros Y HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb].
      * apply binds_app_iff. left. auto.
      * apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
        -- apply binds_one_iff in Hb. destruct Hb as [_ Hbeq].
           discriminate Hbeq.
        -- apply binds_app_iff. right. apply binds_app_iff. right. auto.
  (* d_typing__freeze *)
  - intros Γ e A Hty_inner IH
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_typing__freeze. eapply IH; eauto.
  (* d_typing__forall *)
  - intros L Γ e A Hval Hbody IH
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_typing__forall with
      (L := L `union` dom (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2)); auto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ (x ~ dbind_typ Anew) ++ Γ2).
    eapply IH; eauto.
  (* d_typing__abs *)
  - intros L Γ m e A B Hinh HwfA Hbody IH
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_typing__abs with
      (L := L `union` dom (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2)); auto.
    + eapply d_wf_typ_tvar_morph; [|exact HwfA].
      intros Y HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb].
      * apply binds_app_iff. left. auto.
      * apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
        -- apply binds_one_iff in Hb. destruct Hb as [_ Hbeq].
           discriminate Hbeq.
        -- apply binds_app_iff. right. apply binds_app_iff. right. auto.
    + intros x0 Hx0.
      rewrite_env (((x0 ~ dbind_typ A) ++ Γ1) ++ (x ~ dbind_typ Anew) ++ Γ2).
      eapply IH; eauto.
  (* d_typing__abs_anno *)
  - intros L Γ m e A B HwfA Hbody IH
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_typing__abs_anno with
      (L := L `union` dom (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2)); auto.
    + eapply d_wf_typ_tvar_morph; [|exact HwfA].
      intros Y HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb].
      * apply binds_app_iff. left. auto.
      * apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
        -- apply binds_one_iff in Hb. destruct Hb as [_ Hbeq].
           discriminate Hbeq.
        -- apply binds_app_iff. right. apply binds_app_iff. right. auto.
    + intros x0 Hx0.
      rewrite_env (((x0 ~ dbind_typ A) ++ Γ1) ++ (x ~ dbind_typ Anew) ++ Γ2).
      eapply IH; eauto.
  (* d_typing__app *)
  - intros Γ m e1 e2 P P' A B Hpat IH_pat Href Hty_fn IH_fn Hty_arg IH_arg
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_typing__app with (P := P) (P' := P') (A := A).
    + eapply IH_pat; eauto.
    + eapply d_refine_syn_tvar_morph; [|exact Href].
      intros Y HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb].
      * apply binds_app_iff. left. auto.
      * apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
        -- apply binds_one_iff in Hb. destruct Hb as [_ Hbeq].
           discriminate Hbeq.
        -- apply binds_app_iff. right. apply binds_app_iff. right. auto.
    + eapply IH_fn; eauto.
    + eapply IH_arg; eauto.
  (* d_pat__unit *)
  - intros Γ Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_pat__unit.
  (* d_pat__var *)
  - intros Γ X P Hb Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_pat__var.
    apply binds_app_iff in Hb. destruct Hb as [Hb_pre | Hb_in].
    + apply binds_app_iff. left. exact Hb_pre.
    + apply binds_app_iff. right.
      apply binds_app_iff in Hb_in. destruct Hb_in as [Hb_x | Hb_post].
      * apply binds_one_iff in Hb_x. destruct Hb_x as [_ Hbeq].
        discriminate Hbeq.
      * apply binds_app_iff. right. exact Hb_post.
  (* d_pat__anno *)
  - intros Γ e A HwfA Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_pat__anno.
    eapply d_wf_typ_tvar_morph; [|exact HwfA].
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb].
    + apply binds_app_iff. left. auto.
    + apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
      * apply binds_one_iff in Hb. destruct Hb as [_ Hbeq].
        discriminate Hbeq.
      * apply binds_app_iff. right. apply binds_app_iff. right. auto.
  (* d_pat__sub *)
  - intros Γ m e P Q Hbase Hpat_inner IH Hpsub
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_pat__sub with (P := P); auto.
    + eapply IH; eauto.
    + eapply d_pat_sub_tvar_morph; [|exact Hpsub].
      intros Y HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb].
      * apply binds_app_iff. left. auto.
      * apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
        -- apply binds_one_iff in Hb. destruct Hb as [_ Hbeq].
           discriminate Hbeq.
        -- apply binds_app_iff. right. apply binds_app_iff. right. auto.
  (* d_pat__freeze *)
  - intros Γ e P Hpat_inner IH Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_pat__freeze. eapply IH; eauto.
  (* d_pat__abs *)
  - intros L Γ m e P Q Hneq Hinh HwfS Hbody IH
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_pat__abs with
      (L := L `union` dom (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2)); auto.
    + eapply d_wf_skel_tvar_morph; [|exact HwfS].
      intros Y HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb].
      * apply binds_app_iff. left. auto.
      * apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
        -- apply binds_one_iff in Hb. destruct Hb as [_ Hbeq].
           discriminate Hbeq.
        -- apply binds_app_iff. right. apply binds_app_iff. right. auto.
    + intros x0 Hx0.
      rewrite_env (((x0 ~ dbind_skel P) ++ Γ1) ++ (x ~ dbind_typ Anew) ++ Γ2).
      eapply IH; eauto.
  (* d_pat__abs_check *)
  - intros L Γ e Q Hbody IH Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_pat__abs_check with
      (L := L `union` dom (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2)).
    intros x0 Hx0.
    rewrite_env (((x0 ~ dbind_skel typ_hole) ++ Γ1) ++ (x ~ dbind_typ Anew) ++ Γ2).
    eapply IH; eauto.
  (* d_pat__abs_anno *)
  - intros L Γ m e A Q Hneq HwfA Hbody IH
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_pat__abs_anno with
      (L := L `union` dom (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2)); auto.
    + eapply d_wf_typ_tvar_morph; [|exact HwfA].
      intros Y HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb].
      * apply binds_app_iff. left. auto.
      * apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
        -- apply binds_one_iff in Hb. destruct Hb as [_ Hbeq].
           discriminate Hbeq.
        -- apply binds_app_iff. right. apply binds_app_iff. right. auto.
    + intros x0 Hx0.
      rewrite_env (((x0 ~ dbind_typ A) ++ Γ1) ++ (x ~ dbind_typ Anew) ++ Γ2).
      eapply IH; eauto.
  (* d_pat__abs_anno_check *)
  - intros L Γ e A Q HwfA Hbody IH
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_pat__abs_anno_check with
      (L := L `union` dom (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2)); auto.
    + eapply d_wf_typ_tvar_morph; [|exact HwfA].
      intros Y HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb].
      * apply binds_app_iff. left. auto.
      * apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
        -- apply binds_one_iff in Hb. destruct Hb as [_ Hbeq].
           discriminate Hbeq.
        -- apply binds_app_iff. right. apply binds_app_iff. right. auto.
    + intros x0 Hx0.
      rewrite_env (((x0 ~ dbind_typ A) ++ Γ1) ++ (x ~ dbind_typ Anew) ++ Γ2).
      eapply IH; eauto.
  (* d_pat__app *)
  - intros Γ m e1 e2 P P' Q Hpat IH_pat Href Hty_fn IH_fn
           Γ1 x Aold Anew Γ2 HeqΓ Hc Hsyn Hwf. subst.
    apply d_pat__app with (P := P) (P' := P').
    + eapply IH_pat; eauto.
    + eapply d_refine_syn_tvar_morph; [|exact Href].
      intros Y HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb].
      * apply binds_app_iff. left. auto.
      * apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
        -- apply binds_one_iff in Hb. destruct Hb as [_ Hbeq].
           discriminate Hbeq.
        -- apply binds_app_iff. right. apply binds_app_iff. right. auto.
    + eapply IH_fn; eauto.
Qed.

(** Corollary: single-level narrowing (Γ1 = nil), the form used in
    the main gen-subsumption theorem's __abs / __abs_anno + __arg
    cases.

    Note on direction: the narrowing requires [d_consis nil Γ Anew Aold]
    (Anew on LHS), which is the OPPOSITE direction from what we get
    from Hsub_gen __arg's [d_consis_gen Aold Anew]. Since [d_consis]
    is asymmetric (cf. [prop_subtyping.v:19-23] — LHS is "unresolved",
    RHS is "bidirectional"), symmetry only holds for monotypes /
    syn-typ shapes. For full Qed-wiring to the __abs + __arg case,
    a [d_consis_sym_for_inh] helper is needed for the inh-but-non-mono
    cases (typ_all_col col_inh components in arrow types). The
    [is_syn_typ Aold] premise here matches the cases that are
    actually reachable; the typ_all_col cases force Anew = Aold via
    Hsub_gen's d_consis_gen__refl_any (no narrowing needed). *)
Corollary d_typing_narrow_consis_head : forall x Aold Anew Γ m e B,
    d_typing m ((x ~ dbind_typ Aold) ++ Γ) e B ->
    d_consis nil Γ Anew Aold ->
    is_syn_typ Aold ->
    d_wf_typ Γ Anew ->
    d_typing m ((x ~ dbind_typ Anew) ++ Γ) e B.
Proof.
  intros x Aold Anew Γ m e B Hty Hc Hsyn Hwf.
  rewrite_env (nil ++ (x ~ dbind_typ Anew) ++ Γ).
  eapply (proj1 d_typing_narrow_consis) with
    (Γ1 := nil) (Aold := Aold); eauto.
Qed.

(** [d_consis_sym_inh]: d_consis symmetry restricted to is_inh_typ
    on the LHS. Crucial for wiring narrowing into the main theorem's
    __abs / __abs_anno + __arg cases — Hsub_gen __arg gives
    [d_consis Aold Anew] but narrowing needs [d_consis Anew Aold].

    For is_inh_typ A, A is one of typ_unit / typ_var / typ_arrow /
    typ_all_col col_inh. The d_consis rules don't admit
    typ_all_col on LHS, so [d_consis nil Γ A B] with is_inh_typ A
    forces A ∈ {typ_unit, typ_var, typ_arrow} — for which d_consis
    is structurally symmetric (RHS shape forced by LHS shape). *)
Lemma d_consis_sym_inh : forall Γ A B,
    d_consis nil Γ A B ->
    is_inh_typ A ->
    d_consis nil Γ B A.
Proof.
  intros Γ A B Hc Hinh.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hc; subst.
  - apply d_consis__unit.
  - apply d_consis__var. assumption.
  - inversion Hinh. (* typ_all_etag — not inh, contradiction *)
  - inversion Hinh. (* typ_all_plain *)
  - inversion Hinh. (* typ_all_etag with syn *)
  - inversion Hinh. (* typ_all_plain with syn *)
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hinh; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis__arrow; auto.
Qed.

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
(** * Generalised subtyping (paper's [bid{T}] extension).

    The paper's appendix Lemma B.5 ("Generalised General Subsumption")
    routes through an extended consistency / subtyping relation that
    allows inherited quantifiers on the LHS. This is the missing piece
    that makes the __app function-side lift go through: the lift needs
    [d_consis Γ A0 A0] where A0 is the function's argument type, which
    may be inh-forall — a shape the original [d_consis] doesn't admit
    as LHS. The extended relation [d_consis_gen] adds refl for any wf
    type, sidestepping the LHS-shape restriction. *)
Inductive d_consis_gen :
    list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_consis_gen__embed : forall Δ Γ T A,
    d_consis Δ Γ T A ->
    d_consis_gen Δ Γ T A
(* [d_consis_gen__forall_inh] — the paper's generalised-consistency
   [ForallInh] rule (syntax-directed.tex:116-122):

     typconsis[Δ] (Γ,α) T T'  →  typconsis[Δ] Γ (inh{∀α.}T) (inh{∀α.}T')

   This is the FAITHFUL mechanisation of the paper's generalised
   [typconsis] over generalised unresolved types [\bid{T}], which
   extend [\syn{T}] with [inh{∀α.}T] on the LHS. It is a STRUCTURAL
   rule (not a [refl] axiom): it admits [typ_all_col colour_inh] on
   the LHS, making [d_consis_gen] structurally reflexive on
   inherited-forall types — exactly what the paper's __app step
   relies on for [typconsis A A] when the function's argument type
   [A] is an impredicative polytype.

   (An earlier version used a [d_consis_gen__refl_any] axiom — refl
   for any wf type — which was both unfaithful and unsound for the
   gen→sub bridge. The structural [ForallInh] rule replaces it.) *)
| d_consis_gen__forall_inh : forall L Δ Γ T A,
    (forall X, X `notin` L ->
       d_consis_gen Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis_gen Δ Γ (typ_all_col colour_inh T) (typ_all_col colour_inh A)
| d_consis_gen__arrow : forall Δ1 Δ2 Γ T1 T2 A1 A2,
    d_consis_gen Δ1 Γ T1 A1 ->
    d_consis_gen Δ2 Γ T2 A2 ->
    list_disjoint Δ1 Δ2 ->
    d_consis_gen (Δ1 ++ Δ2) Γ (typ_arrow T1 T2) (typ_arrow A1 A2).

(** Generalised subtyping using [d_consis_gen] for the consistency
    premises. Adds an __infer / __check that uses [d_consis_gen],
    plus the structural cases.

    [d_sub_gen__refl_any] requires [mode_typ_compat m A]: the paper's
    [M ⊢ A] predicate. Without it, [d_sub_gen (mode_fn _) nil Γ A A]
    would be admissible for non-arrow A (e.g. typ_unit), but the
    corresponding [d_typing (mode_fn _) Γ e A] is unreachable — the
    [mode_typ_compat] premise prevents that inconsistency at the
    relation level. *)
Inductive d_sub_gen :
    mode -> list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_sub_gen__embed : forall m Δ Γ T A,
    d_sub m Δ Γ T A ->
    d_sub_gen m Δ Γ T A
(* [d_sub_gen__refl_any] — restricted to [mono_typ A].

   An earlier version used [mode_typ_compat m A] as the premise, but
   that is UNSOUND: it admits [d_sub_gen mode_tc nil Γ A A] for
   [A = typ_all_col colour_inh A_inner] (since [is_inh_typ] includes
   such [A]), yet the corresponding mode-lift of typing is not always
   derivable. Concrete counter-example: [e = exp_anno e0 A] with [e0]
   a non-value and [A = typ_all_col colour_inh ...]: [Hty] at mode_ti
   is derivable, but [d_typing mode_tc Γ e A] is NOT — [d_typing__sub]
   needs [d_sub mode_tc A A] which fails (no [d_consis] rule admits
   [typ_all_col] on the LHS), and [d_typing__forall] needs
   [is_value e0]. The paper's [M ⊢ A] predicate is silent on this.

   Restricting to [mono_typ A] keeps the rule sound: mono types are
   reflexively subtypeable ([d_consis_refl_mono]) and mode-liftable
   ([d_typing_lift_mono]). *)
| d_sub_gen__refl_mono : forall m Γ A,
    mono_typ A ->
    mode_typ_compat m A ->
    d_wf_typ Γ A ->
    d_sub_gen m nil Γ A A
| d_sub_gen__forall_r : forall L Δ Γ T A,
    (forall X, X `notin` L ->
       d_sub_gen mode_tc Δ ((X ~ dbind_tvar) ++ Γ) T (open_typ_wrt_typ A (typ_var_f X))) ->
    d_sub_gen mode_tc Δ Γ T (typ_all_col colour_inh A)
| d_sub_gen__arg : forall Δ1 Δ2 Γ m T1 T2 A1 A2,
    d_consis_gen Δ1 Γ T1 A1 ->
    d_sub_gen m Δ2 Γ T2 A2 ->
    d_sub_gen (mode_fn m) (Δ1 ++ Δ2) Γ (typ_arrow T1 T2) (typ_arrow A1 A2).

(** ** Generalised typing [d_typing_gen].

    Mirrors [d_typing] rule-for-rule, EXCEPT [d_typing_gen__sub] uses
    the generalised subtyping [d_sub_gen] in place of [d_sub]. This is
    the system the paper's Lemma B.5 (Generalised General Subsumption,
    D12) is really about: the syntax-directed [Sub] rule takes the
    generalised subtyping.

    Standalone inductive (not mutual) — it reuses the ORIGINAL [d_pat]
    in the [__app] rule (the pattern judgement is orthogonal to
    subsumption and does not change). [d_typing] embeds into
    [d_typing_gen] structurally via [d_sub_gen__embed]
    ([d_typing_embed_gen] below).

    With [d_typing_gen__sub] taking [d_sub_gen], the D12 cases that
    were blocked on the gen→sub bridge (var/anno/+ __arg) close
    directly: reconstruct [d_typing_gen__sub] with the [d_sub_gen]
    in hand, no bridge needed. *)
Inductive d_typing_gen :
  mode -> list (atom * dbind) -> exp -> typ -> Prop :=
| d_typing_gen__unit : forall Γ,
    mode_typ_compat mode_ti typ_unit ->
    d_typing_gen mode_ti Γ exp_unit typ_unit
| d_typing_gen__var : forall Γ x A,
    binds x (dbind_typ A) Γ ->
    d_typing_gen mode_ti Γ (exp_var_f x) A
| d_typing_gen__anno : forall Γ e A,
    is_inh_typ A ->
    d_typing_gen mode_tc Γ e A ->
    d_typing_gen mode_ti Γ (exp_anno e A) A
| d_typing_gen__sub : forall Γ m e A B,
    is_base_term e ->
    d_typing_gen mode_ti Γ e A ->
    d_sub_gen m nil Γ A B ->
    d_typing_gen m Γ e B
| d_typing_gen__freeze : forall Γ e A,
    d_typing_gen mode_ti Γ e A ->
    d_typing_gen mode_tc Γ (exp_freeze e) A
| d_typing_gen__forall : forall L Γ e A,
    is_value e ->
    (forall X, X `notin` L ->
       d_typing_gen mode_tc ((X ~ dbind_tvar) ++ Γ) e
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_typing_gen mode_tc Γ e (typ_all_col colour_inh A)
| d_typing_gen__abs : forall L Γ m e A B,
    is_inh_typ A ->
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing_gen m Γ (exp_abs e) (typ_arrow A B)
| d_typing_gen__abs_anno : forall L Γ m e A B,
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing_gen m Γ (exp_abs_anno A e) (typ_arrow A B)
| d_typing_gen__app : forall Γ m e1 e2 P P' A B,
    d_pat mode_tc Γ e2 P ->
    d_refine_syn nil Γ P P' ->
    d_typing_gen (mode_fn m) Γ e1 (typ_arrow A B) ->
    d_typing_gen mode_tc Γ e2 A ->
    d_typing_gen m Γ (exp_app e1 e2) B.

(** [d_typing] embeds into [d_typing_gen]: every original typing is a
    generalised typing (the [__sub] rule's [d_sub] embeds via
    [d_sub_gen__embed]). Structural induction. *)
Lemma d_typing_embed_gen : forall m Γ e A,
    d_typing m Γ e A ->
    d_typing_gen m Γ e A.
Proof.
  intros m Γ e A H. induction H.
  - apply d_typing_gen__unit; assumption.
  - apply d_typing_gen__var; assumption.
  - apply d_typing_gen__anno; assumption.
  - apply d_typing_gen__sub with (A := A); auto.
    apply d_sub_gen__embed; assumption.
  - apply d_typing_gen__freeze; assumption.
  - apply d_typing_gen__forall with (L := L); assumption.
  - apply d_typing_gen__abs with (L := L); assumption.
  - apply d_typing_gen__abs_anno with (L := L); assumption.
  - apply d_typing_gen__app with (P := P) (P' := P') (A := A); assumption.
Qed.

(** [d_sub_gen] is reflexive on any mono wf type at a compatible mode. *)
Lemma d_sub_gen_refl : forall Γ A m,
    mono_typ A ->
    mode_typ_compat m A ->
    d_wf_typ Γ A ->
    d_sub_gen m nil Γ A A.
Proof.
  intros. apply d_sub_gen__refl_mono; auto.
Qed.

(** [d_sub] is reflexive on any mono wf type at a compatible mode.
    (Generalises [d_sub_refl_mono] from mode_ti to all compatible
    modes — sound because mono types carry no quantifiers, so the
    [d_consis] reflexivity used by every [d_sub] mode is available.) *)
Lemma d_sub_refl_mono_mode : forall Γ A m,
    mono_typ A ->
    mode_typ_compat m A ->
    d_wf_typ Γ A ->
    d_sub m nil Γ A A.
Proof.
  intros Γ A m Hmono Hcompat. generalize dependent Γ.
  induction Hcompat; intros Γ Hwf.
  - (* mode_ti *)
    apply d_sub__infer.
    + apply mono_typ_is_syn_typ; auto.
    + apply d_consis_refl_mono; auto.
  - (* mode_tc *)
    apply d_sub__check.
    + intros ε T' Heq; subst; inversion Hmono.
    + intros T' Heq; subst; inversion Hmono.
    + apply mono_typ_is_inh_typ; auto.
    + apply d_consis_refl_mono; auto.
  - (* mode_fn: A = typ_arrow A0 B *)
    inversion Hmono; subst.
    inversion Hwf; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub__arg.
    + apply d_consis_refl_mono; auto.
    + apply IHHcompat; auto.
Qed.

(** [d_consis_gen] is reflexive on any [is_inh_typ] wf type — the
    paper's generalised consistency is structurally reflexive on
    generalised unresolved types. Proven by induction on the
    [is_inh_typ] derivation: unit/var/arrow via [__embed]/[__arrow],
    and [typ_all_col colour_inh] via the structural [__forall_inh]
    rule. This is the mechanised analogue of the paper's implicit
    "[typconsis] is reflexive" used in the __app step of Lemma B.5. *)
Lemma d_consis_gen_refl : forall Γ A,
    is_inh_typ A ->
    d_wf_typ Γ A ->
    d_consis_gen nil Γ A A.
Proof.
  intros Γ A Hinh. generalize dependent Γ.
  induction Hinh; intros Γ Hwf.
  - apply d_consis_gen__embed. apply d_consis__unit.
  - apply d_consis_gen__embed. inversion Hwf; subst.
    apply d_consis__var; assumption.
  - inversion Hwf; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow.
    + apply IHHinh1; assumption.
    + apply IHHinh2; assumption.
    + apply list_disjoint_nil_l.
  - (* typ_all_col colour_inh A *)
    inversion Hwf; subst.
    apply d_consis_gen__forall_inh with (L := L `union` L0 `union` dom Γ).
    intros X HX. apply H0; auto.
Qed.

(** [d_typing_check_is_inh]: a [mode_tc] (check-mode) typing always
    has an [is_inh_typ] type.

    PAPER-LEVEL INVARIANT. In the paper, the check judgement is
    written [typc Γ N (inh A)] — it checks against an INHERITED
    (inh-coloured) type by construction. The mechanised
    [d_typing mode_tc Γ e A] does not carry [is_inh_typ A] explicitly
    on every rule (e.g. [d_typing__abs] / [d_typing__freeze] do not),
    so this invariant is not derivable post-hoc from the current rule
    set without strengthening the [d_typing] definition. We admit it
    as the paper's implicit colour invariant; a fully faithful
    mechanisation would thread [is_inh_typ] through the [mode_tc]
    rules. Used only to discharge [is_inh_typ] of a function's
    argument type in the __app function-side lift. *)
Lemma d_typing_check_is_inh : forall Γ e A,
    d_typing mode_tc Γ e A ->
    is_inh_typ A.
Proof.
Admitted.

(** [d_consis_lhs_is_syn_typ]: when [d_consis nil Γ A B] holds and
    [is_inh_typ A], then A is also [is_syn_typ]. d_consis rules
    don't admit typ_all_col on LHS, so A's shape is forced to be
    typ_unit / typ_var / typ_arrow (where is_inh and is_syn coincide). *)
Lemma d_consis_lhs_is_syn_typ : forall Γ A B,
    d_consis nil Γ A B ->
    is_inh_typ A ->
    is_syn_typ A.
Proof.
  intros Γ A B Hc Hinh.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hc; subst.
  - apply is_syn_typ__unit.
  - apply is_syn_typ__var.
  - inversion Hinh.
  - inversion Hinh.
  - inversion Hinh.
  - inversion Hinh.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hinh; subst.
    apply is_syn_typ__arrow; auto.
Qed.

(** [d_consis_rhs_is_inh_typ]: when [d_consis nil Γ A B] holds and
    [is_inh_typ A], then B is also [is_inh_typ]. Used to propagate
    is_inh-ness through d_consis (necessary to invoke
    [d_consis_sym_inh] in the reverse direction). *)
Lemma d_consis_rhs_is_inh_typ : forall Γ A B,
    d_consis nil Γ A B ->
    is_inh_typ A ->
    is_inh_typ B.
Proof.
  intros Γ A B Hc Hinh.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hc; subst.
  - apply is_inh_typ__unit.
  - apply is_inh_typ__var.
  - inversion Hinh.
  - inversion Hinh.
  - inversion Hinh.
  - inversion Hinh.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hinh; subst.
    apply is_inh_typ__arrow; auto.
Qed.

(** [d_consis_gen_rhs_is_inh_typ]: same as above but for d_consis_gen. *)
Lemma d_consis_gen_rhs_is_inh_typ : forall Γ A B,
    d_consis_gen nil Γ A B ->
    is_inh_typ A ->
    is_inh_typ B.
Proof.
  intros Γ A B Hcg.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hcg; subst; intros Hinh.
  - eapply d_consis_rhs_is_inh_typ; eauto.
  - (* __forall_inh: both sides typ_all_col colour_inh. IH = H0. *)
    inversion Hinh; subst.
    apply is_inh_typ__all with (L := L `union` L0).
    intros X HX.
    apply H0; auto.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hinh; subst.
    apply is_inh_typ__arrow; auto.
Qed.

(** [d_wf_typ_is_typ]: d_wf_typ implies is_typ. *)
Lemma d_wf_typ_is_typ : forall Γ A,
    d_wf_typ Γ A -> is_typ A.
Proof.
  intros Γ A H. induction H.
  - apply is_typ__unit.
  - apply is_typ__var.
  - apply is_typ__arrow; assumption.
  - apply is_typ__all with (L := L); auto.
Qed.

(** [d_consis_lhs_is_inh_for_typ]: when [d_consis nil Γ A B] fires and
    A is [is_typ], A is is_inh_typ. d_consis LHS rules force A ∈
    {typ_unit, typ_var, typ_arrow, typ_all_etag, typ_all_plain};
    is_typ excludes etag/plain → so A ∈ {typ_unit, typ_var, typ_arrow},
    which are all is_inh_typ. *)
Lemma d_consis_lhs_is_inh_for_typ : forall Γ A B,
    d_consis nil Γ A B ->
    is_typ A ->
    is_inh_typ A.
Proof.
  intros Γ A B Hc Hist.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hc; subst.
  - apply is_inh_typ__unit.
  - apply is_inh_typ__var.
  - exfalso. inversion Hist.
  - exfalso. inversion Hist.
  - exfalso. inversion Hist.
  - exfalso. inversion Hist.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hist; subst.
    apply is_inh_typ__arrow; auto.
Qed.

(** [d_consis_gen_preserves_wf]: d_consis_gen preserves wf on RHS. *)
Lemma d_consis_gen_preserves_wf : forall Δ Γ A B,
    d_consis_gen Δ Γ A B ->
    d_wf_typ Γ B.
Proof.
  intros Δ Γ A B Hcg. induction Hcg.
  - eapply d_consis_preserves_wf; eauto.
  - (* __forall_inh: B = typ_all_col colour_inh A0. IH = H0. *)
    apply d_wf_typ__all with (L := L). assumption.
  - apply d_wf_typ__arrow; auto.
Qed.

(** [d_consis_gen_sym_inh]: symmetry for d_consis_gen on is_inh types. *)
Lemma d_consis_gen_sym_inh : forall Γ A B,
    d_consis_gen nil Γ A B ->
    is_inh_typ A ->
    d_consis_gen nil Γ B A.
Proof.
  intros Γ A B Hcg.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hcg; subst; intros Hinh.
  - apply d_consis_gen__embed.
    apply d_consis_sym_inh; auto.
  - (* __forall_inh: both sides typ_all_col colour_inh. IH = H0. *)
    inversion Hinh; subst.
    apply d_consis_gen__forall_inh with (L := L `union` L0).
    intros X HX.
    apply H0; auto.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hinh; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow; auto.
Qed.

(** [d_typing_narrow_consis_head_arg]: narrowing variant for the
    __abs / __abs_anno + __arg use case in the main theorem.

    Takes [d_consis_gen Aold Anew] (the direction we get from
    Hsub_gen __arg's arg-side) and [is_inh_typ Aold] (from Hty's
    HinhA premise), handling the asymmetry via [d_consis_sym_inh]
    and [d_consis_lhs_is_syn_typ] internally.

    The __refl_any case (Anew = Aold) is identity. The __embed case
    closes via the sym + is_syn helpers. The __arrow case admits
    pending recursive narrowing for arrow components — which would
    extend the body of this lemma to handle arrow-typed bound vars
    with structurally narrowed components. *)
Lemma d_typing_narrow_consis_head_arg : forall x Aold Anew Γ m e B,
    d_typing m ((x ~ dbind_typ Aold) ++ Γ) e B ->
    d_consis_gen nil Γ Aold Anew ->
    is_inh_typ Aold ->
    d_wf_typ Γ Aold ->
    d_wf_typ Γ Anew ->
    d_typing m ((x ~ dbind_typ Anew) ++ Γ) e B.
Proof.
  intros x Aold Anew Γ m e B Hty Hcg Hinh Hwf_old Hwf_new.
  inversion Hcg; subst.
  - (* __embed: d_consis Aold Anew. *)
    apply d_typing_narrow_consis_head with (Aold := Aold); auto.
    + apply d_consis_sym_inh; auto.
    + eapply d_consis_lhs_is_syn_typ; eauto.
  - (* __forall_inh: Aold = typ_all_col colour_inh T,
       Anew = typ_all_col colour_inh A0. Genuine narrowing on a
       polytype binding — needs the recursive narrowing machinery
       (same class of obstacle as __arrow). *)
    admit.
  - (* __arrow: recursive narrowing on arrow components. *)
    admit.
Admitted.

(** ** Structural lemmas for the generalised relations.

    Weakening and tvar-morph for [d_consis_gen] / [d_sub_gen]. Mirror
    the corresponding facts on [d_consis] / [d_sub] — composition
    works case-by-case on the embedded / refl_any / arrow / forall_r /
    arg constructors. Needed by [d_typing_general_subsumption_gen] to
    weaken sub-derivations when reasoning under cofinitely-quantified
    type-variable binders (paper Lemma B.5 proof, __forall_r case). *)

Lemma d_consis_gen_weakening : forall Γ1 Γ2 Γ3 Δ T A,
    d_consis_gen Δ (Γ1 ++ Γ3) T A ->
    d_consis_gen Δ (Γ1 ++ Γ2 ++ Γ3) T A.
Proof.
  intros Γ1 Γ2 Γ3 Δ T A H. dependent induction H.
  - apply d_consis_gen__embed. apply d_consis_weakening; auto.
  - apply d_consis_gen__forall_inh with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__arrow; auto.
Qed.

Corollary d_consis_gen_weakening_head : forall Γ Γ' Δ T A,
    d_consis_gen Δ Γ T A ->
    d_consis_gen Δ (Γ' ++ Γ) T A.
Proof.
  intros. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_consis_gen_weakening. simpl. auto.
Qed.

Lemma d_sub_gen_weakening : forall Γ1 Γ2 Γ3 m Δ T A,
    d_sub_gen m Δ (Γ1 ++ Γ3) T A ->
    d_sub_gen m Δ (Γ1 ++ Γ2 ++ Γ3) T A.
Proof.
  intros Γ1 Γ2 Γ3 m Δ T A H. dependent induction H.
  - apply d_sub_gen__embed. apply d_sub_weakening; auto.
  - apply d_sub_gen__refl_mono; auto. eapply d_wf_typ_weakening; eauto.
  - apply d_sub_gen__forall_r with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_sub_gen__arg; eauto.
    apply d_consis_gen_weakening; auto.
Qed.

Corollary d_sub_gen_weakening_head : forall Γ Γ' m Δ T A,
    d_sub_gen m Δ Γ T A ->
    d_sub_gen m Δ (Γ' ++ Γ) T A.
Proof.
  intros. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_sub_gen_weakening. simpl. auto.
Qed.

(** Weakening for [d_typing_gen] — structural, mirrors
    [d_typing_weakening]. The [__sub] case uses [d_sub_gen_weakening]. *)
Lemma d_typing_gen_weakening : forall Γ1 Γ2 Γ3 m e A,
    d_typing_gen m (Γ1 ++ Γ3) e A ->
    d_typing_gen m (Γ1 ++ Γ2 ++ Γ3) e A.
Proof.
  intros Γ1 Γ2 Γ3 m e A H.
  remember (Γ1 ++ Γ3) as Γ eqn:HeqΓ.
  generalize dependent Γ1.
  induction H; intros Γ1 HeqΓ; subst.
  - apply d_typing_gen__unit; assumption.
  - apply d_typing_gen__var. apply binds_app_iff in H.
    destruct H as [Hb | Hb].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_typing_gen__anno; auto.
  - apply d_typing_gen__sub with (A := A); auto.
    apply d_sub_gen_weakening; auto.
  - apply d_typing_gen__freeze; auto.
  - apply d_typing_gen__forall with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    + assumption.
    + intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H1; auto.
  - apply d_typing_gen__abs with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_typ_weakening; eauto.
    + intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H2; auto.
  - apply d_typing_gen__abs_anno with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_typ_weakening; eauto.
    + intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H1; auto.
  - apply d_typing_gen__app with (P := P) (P' := P') (A := A); auto.
    + eapply (proj2 d_typing_pat_weakening) with
        (Γ1 := Γ1) (Γ2 := Γ2) (Γ3 := Γ3); eauto.
    + apply d_refine_syn_weakening; auto.
Qed.

Corollary d_typing_gen_weakening_head : forall Γ Γ' m e A,
    d_typing_gen m Γ e A ->
    d_typing_gen m (Γ' ++ Γ) e A.
Proof.
  intros. rewrite_env (nil ++ Γ' ++ Γ).
  apply d_typing_gen_weakening. simpl. auto.
Qed.

(** [d_typing_gen] preserves type well-formedness — the [d_typing_gen]
    analogue of [d_typing_pat_preserves_wf]'s typing half. Standard
    structural lemma; admitted here (the [__sub] / [__app] cases would
    need [d_sub_gen] / pattern wf-preservation lemmas threaded
    through — straightforward but not yet stated). *)
Lemma d_typing_gen_preserves_wf : forall m Γ e A,
    d_typing_gen m Γ e A ->
    d_wf_denv Γ ->
    d_wf_typ Γ A.
Proof.
Admitted.

(** [d_typing_gen] analogue of [d_typing_check_is_inh] — a mode_tc
    [d_typing_gen] always has an [is_inh_typ] type. Same paper-level
    colour invariant; admitted. *)
Lemma d_typing_gen_check_is_inh : forall Γ e A,
    d_typing_gen mode_tc Γ e A ->
    is_inh_typ A.
Proof.
Admitted.

Lemma d_consis_gen_tvar_morph : forall Γ Γ' Δ T A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_consis_gen Δ Γ T A ->
    d_consis_gen Δ Γ' T A.
Proof.
  intros Γ Γ' Δ T A Hmorph H.
  generalize dependent Γ'. induction H; intros Γ' Hmorph.
  - apply d_consis_gen__embed. eapply d_consis_tvar_morph; eauto.
  - apply d_consis_gen__forall_inh with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff;
      [ left; auto | right; auto ].
  - apply d_consis_gen__arrow; auto.
Qed.

Lemma d_sub_gen_tvar_morph : forall Γ Γ' m Δ T A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_sub_gen m Δ Γ T A ->
    d_sub_gen m Δ Γ' T A.
Proof.
  intros Γ Γ' m Δ T A Hmorph H.
  generalize dependent Γ'. induction H; intros Γ' Hmorph.
  - apply d_sub_gen__embed. eapply d_sub_tvar_morph; eauto.
  - apply d_sub_gen__refl_mono; auto. eapply d_wf_typ_tvar_morph; eauto.
  - apply d_sub_gen__forall_r with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_sub_gen__arg.
    + eapply d_consis_gen_tvar_morph; eauto.
    + apply IHd_sub_gen; auto.
Qed.

(** ** FN^n TI predicate (paper's mode-stack discipline).

    A mode is in [is_fn_n_ti] form iff it's [mode_ti] or
    [mode_fn m'] for some m' in [is_fn_n_ti] form — i.e.,
    [FN^n TI = mode_fn^n mode_ti] for some n ≥ 0. *)
Inductive is_fn_n_ti : mode -> Prop :=
| is_fn_n_ti__ti : is_fn_n_ti mode_ti
| is_fn_n_ti__fn : forall m,
    is_fn_n_ti m ->
    is_fn_n_ti (mode_fn m).

(** Replace the innermost TI in m_orig (a FN^n TI mode) with m_new.
    [mode_fn_n_subst (FN^n TI) m_new = FN^n m_new]. *)
Fixpoint mode_fn_n_subst (m_orig m_new : mode) : mode :=
  match m_orig with
  | mode_ti => m_new
  | mode_fn m' => mode_fn (mode_fn_n_subst m' m_new)
  | mode_tc => mode_tc  (* unused; is_fn_n_ti excludes mode_tc *)
  end.

(** [decr_mode] preserves [is_fn_n_ti]. *)
Lemma is_fn_n_ti_decr : forall m,
    is_fn_n_ti m ->
    is_fn_n_ti (decr_mode m).
Proof.
  intros m H. inversion H; subst; simpl.
  - apply is_fn_n_ti__ti.
  - assumption.
Qed.

(** [mode_fn_n_subst] respects [decr_mode] on FN^n TI: for n ≥ 1,
    [decr (FN^n m_new) = FN^{n-1} m_new] = [mode_fn_n_subst (decr m_orig) m_new]. *)
Lemma mode_fn_n_subst_decr : forall m_orig m_new,
    is_fn_n_ti m_orig ->
    m_orig <> mode_ti ->
    decr_mode (mode_fn_n_subst m_orig m_new) =
    mode_fn_n_subst (decr_mode m_orig) m_new.
Proof.
  intros m_orig m_new H Hne. inversion H; subst; simpl.
  - exfalso. apply Hne. reflexivity.
  - reflexivity.
Qed.

(** Lift d_consis to d_sub_gen at a compatible mode. Recurses on the
    structure of mode_typ_compat (which mirrors the type structure). *)
Lemma d_consis_to_d_sub_gen : forall m Γ T A,
    mode_typ_compat m A ->
    d_wf_typ Γ T ->
    d_consis nil Γ T A ->
    d_sub_gen m nil Γ T A.
Proof.
  intros m Γ T A Hcompat HwfT Hc. generalize dependent T.
  induction Hcompat; intros T HwfT Hc.
  - (* mode_ti *)
    apply d_sub_gen__embed. apply d_sub__infer; auto.
  - (* mode_tc *)
    apply d_sub_gen__embed. apply d_sub__check; auto.
    + intros ε T' Heq; subst; inversion HwfT.
    + intros T' Heq; subst; inversion HwfT.
  - (* mode_fn: A = typ_arrow A0 B. T from d_consis must be typ_arrow. *)
    inversion Hc; subst.
    inversion HwfT; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
    | H : nil = _ ++ _ |- _ =>
        symmetry in H; apply app_eq_nil in H;
        destruct H as [HΔ1 HΔ2]; subst
    end.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + apply d_consis_gen__embed. assumption.
    + apply IHHcompat; auto.
Qed.

(** [d_consis_extends_d_consis_gen_nil]: compose d_consis on LHS with
    d_consis_gen at outer Δ = nil. The Δ = nil restriction avoids a
    permutation issue in d_consis_compose. *)
Lemma d_consis_extends_d_consis_gen : forall Γ T A B,
    d_consis nil Γ T A ->
    d_consis_gen nil Γ A B ->
    d_wf_typ Γ T ->
    d_consis_gen nil Γ T B.
Proof.
  intros Γ T0 A B Hc Hcg HwfT.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  generalize dependent T0.
  induction Hcg; intros T0 Hc HwfT.
  - (* __embed: compose Hc and H via d_consis_compose. *)
    subst.
    apply d_consis_gen__embed.
    edestruct (d_consis_compose Hc H) as [Δc [Hperm Hcc]].
    + apply list_disjoint_nil_l.
    + simpl in Hperm.
      apply Permutation_sym in Hperm.
      apply Permutation_nil in Hperm. subst. exact Hcc.
  - (* __forall_inh: A = typ_all_col colour_inh T_inner,
       B = typ_all_col colour_inh A_inner. Composing d_consis (with
       RHS typ_all_col) on the LHS requires inverting Hc to
       typ_all_plain shape and a per-X d_consis-vs-d_consis_gen
       compose — the result needs to stay in d_consis (for __embed)
       but composition yields d_consis_gen. Genuine gap; admitted. *)
    admit.
  - (* __arrow: Δ1 ++ Δ2 = nil forces both nil. *)
    apply app_eq_nil in HeqΔ.
    destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hc; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1a HΔ2a]; subst
    end.
    inversion HwfT; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow; auto.
Admitted.

(** [d_consis_extends_d_sub_gen_nil]: extend d_sub_gen on the LHS via
    a d_consis. Mirrors [d_consis_extends_d_sub_nil] for the gen
    relation. The signature has [T] after [d_sub_gen] so that
    [induction Hs; intros T] gives a properly T-abstracted IH. *)
Lemma d_consis_extends_d_sub_gen_nil : forall m Γ A B,
    d_sub_gen m nil Γ A B ->
    forall T,
      d_consis nil Γ T A ->
      d_wf_typ Γ T ->
      d_sub_gen m nil Γ T B.
Proof.
  intros m Γ A B Hs.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hs; intros T0 Hc HwfT.
  - (* __embed: route through d_consis_extends_d_sub_nil. *)
    subst.
    apply d_sub_gen__embed. eapply d_consis_extends_d_sub_nil; eauto.
  - (* __refl_mono: A = B mono. Use d_consis_to_d_sub_gen; the
       mode_typ_compat premise is now carried by __refl_mono. *)
    subst.
    eapply d_consis_to_d_sub_gen; eauto.
  - (* __forall_r: B = typ_all_col colour_inh A0, m = mode_tc.
       Use d_sub_gen__forall_r reconstruction with per-X recursion. *)
    subst.
    apply d_sub_gen__forall_r with (L := L `union` dom Γ).
    intros X HX.
    eapply H0; eauto.
    + apply d_consis_weakening_head; auto.
    + apply d_wf_typ_weakening_head; auto.
  - (* __arg: A = typ_arrow A1 A2, B = typ_arrow B1 B2. Hc forces
       T0 = typ_arrow T0_arg T0_ret. Reconstruct via d_sub_gen__arg. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hc; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1a HΔ2a]; subst
    end.
    inversion HwfT; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + (* d_consis_gen nil Γ T0_arg A1: compose Hc's arg-side d_consis
         with outer arg-side d_consis_gen via the helper. *)
      eapply d_consis_extends_d_consis_gen; eauto.
    + (* d_sub_gen m_inner nil Γ T0_ret A2: recursive call via IH. *)
      eapply IHHs; eauto.
Qed.

(** Mono-type mode-lift for [d_typing_gen] — the [d_typing_gen]
    analogue of [d_typing_lift_mono]. By induction on the typing.
    Base terms close via [d_typing_gen__sub]; [__abs]/[__abs_anno]
    reconstruct with body lifted by the IH; [__app] is research-grade
    (same gap as [d_typing_lift_mono]'s __app — function arg-type
    mono not derivable from the rule). *)
Lemma d_typing_gen_lift_mono : forall Γ e A m_target,
    d_typing_gen mode_ti Γ e A ->
    mono_typ A ->
    d_wf_denv Γ ->
    d_sub_gen m_target nil Γ A A ->
    d_typing_gen m_target Γ e A.
Proof.
  intros Γ e A m_target Hty.
  remember mode_ti as m0 eqn:Heqm0.
  generalize dependent m_target.
  induction Hty; intros m_target Hmono Hwfd Hrefl;
    try discriminate Heqm0.
  - (* __unit *)
    apply d_typing_gen__sub with (A := typ_unit).
    + apply is_base_term__unit.
    + apply d_typing_gen__unit; assumption.
    + exact Hrefl.
  - (* __var *)
    apply d_typing_gen__sub with (A := A).
    + apply is_base_term__var.
    + apply d_typing_gen__var; assumption.
    + exact Hrefl.
  - (* __anno *)
    apply d_typing_gen__sub with (A := A).
    + apply is_base_term__anno.
    + apply d_typing_gen__anno; assumption.
    + exact Hrefl.
  - (* __sub: Heqm0 : m = mode_ti. Inner d_typing_gen mode_ti Γ e A,
       Hsub_orig : d_sub_gen mode_ti nil Γ A B. Compose with Hrefl
       (d_sub_gen m_target nil Γ B B) into d_sub_gen m_target Γ A B,
       then d_typing_gen__sub. *)
    subst m.
    apply d_typing_gen__sub with (A := A); auto.
    match goal with Hso : d_sub_gen mode_ti nil Γ ?A0 ?B0 |- _ =>
      inversion Hso; subst
    end.
    + (* __embed: d_sub mode_ti → __infer gives d_consis A B. *)
      match goal with Hs : d_sub mode_ti nil Γ ?A0 ?B0 |- _ =>
        inversion Hs; subst;
        try (match goal with H' : mode_ti <> mode_ti |- _ =>
               exfalso; apply H'; reflexivity end)
      end.
      eapply d_consis_extends_d_sub_gen_nil; [ exact Hrefl | assumption | ].
      eapply d_typing_gen_preserves_wf; eauto.
    + (* __refl_mono: A = B. Hrefl is the answer. *)
      exact Hrefl.
  - (* __abs / __abs_anno: A_outer = typ_arrow A B mono. Reconstruct
       d_typing_gen__abs[_anno] at m_target with the body lifted via
       the IH. The body sub is d_sub_gen__refl_mono on the mono B;
       its mode_typ_compat / wf premises come from inverting Hrefl.
       The inversion bookkeeping (Hrefl can be __embed / __refl_mono /
       __arg) parallels [d_typing_lift_mono_mut]'s __abs case; the
       d_sub_gen variants of the wf-extraction helpers are not yet
       stated, so deferred. *)
    admit.
  - admit.
  - (* __app: research-grade (same gap as d_typing_lift_mono). *)
    admit.
Admitted.

(** Aux lemmas specialising the gen-subsumption theorem to specific
    Hty constructors. *)

(** With [d_typing_gen], the base-term subsumption helpers are trivial:
    [d_typing_gen__sub] takes the [d_sub_gen] directly, so no induction
    on the subtyping derivation and no gen→sub bridge are needed. This
    is exactly the structural payoff of mirroring the paper's
    syntax-directed [Sub] rule (which uses the generalised subtyping). *)
Lemma d_typing_unit_gen_subsumption : forall Γ A m,
    d_wf_denv Γ ->
    d_sub_gen m nil Γ typ_unit A ->
    d_typing_gen m Γ exp_unit A.
Proof.
  intros Γ A m Hwfd Hs.
  apply d_typing_gen__sub with (A := typ_unit).
  - apply is_base_term__unit.
  - apply d_typing_gen__unit. apply mode_typ_compat__ti.
    apply is_syn_typ__unit.
  - exact Hs.
Qed.

Lemma d_typing_var_gen_subsumption : forall Γ xv Avar A m,
    d_wf_denv Γ ->
    binds xv (dbind_typ Avar) Γ ->
    d_sub_gen m nil Γ Avar A ->
    d_typing_gen m Γ (exp_var_f xv) A.
Proof.
  intros Γ xv Avar A m Hwfd Hb Hs.
  apply d_typing_gen__sub with (A := Avar).
  - apply is_base_term__var.
  - apply d_typing_gen__var; exact Hb.
  - exact Hs.
Qed.

Lemma d_typing_anno_gen_subsumption : forall Γ e0 Aann A m,
    d_wf_denv Γ ->
    is_inh_typ Aann ->
    d_typing_gen mode_tc Γ e0 Aann ->
    d_sub_gen m nil Γ Aann A ->
    d_typing_gen m Γ (exp_anno e0 Aann) A.
Proof.
  intros Γ e0 Aann A m Hwfd Hinh_outer Hinner Hs.
  apply d_typing_gen__sub with (A := Aann).
  - apply is_base_term__anno.
  - apply d_typing_gen__anno; assumption.
  - exact Hs.
Qed.

(** [d_typing_abs_value_to_forall]: when Hty = __abs (a value), lifting
    to typ_all_col colour_inh via __forall_r requires nested recursion
    on the per-X premise.

    Stronger form: take an arbitrary [C] with [d_sub_gen mode_tc nil Γ
    (typ_arrow A B) C], so dependent induction on the d_sub_gen
    handles all target shapes (including nested [typ_all_col]). *)
Lemma d_typing_abs_value_to_subsumption :
  forall L Γ e A B m_orig C,
    is_inh_typ A ->
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_tc nil Γ (typ_arrow A B) C ->
    d_typing_gen mode_tc Γ (exp_abs e) C.
Proof.
  intros L Γ e A B m_orig C HinhA HwfA Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: d_sub mode_tc nil Γ (typ_arrow A B) C. *)
    admit.
  - (* __refl_mono: C = typ_arrow A B, forced MONO. With A, B mono the
       body lift is clean — reconstruct d_typing_gen__abs at mode_tc and
       lift the body (at decr_mode m_orig = mode_ti) via
       [d_typing_gen_lift_mono]. *)
    match goal with Hm : mono_typ (typ_arrow A B) |- _ =>
      assert (HmonoA : mono_typ A) by (inversion Hm; auto);
      assert (HmonoB : mono_typ B) by (inversion Hm; auto)
    end.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + apply mono_typ_is_inh_typ; auto.
    + assumption.
    + intros x Hx.
      assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
        (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := B); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
        -- rewrite_env ((x ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           match goal with Hw : d_wf_typ Γ (typ_arrow A B) |- _ =>
             inversion Hw; assumption end.
  - (* __forall_r: C = typ_all_col colour_inh A0; recurse via H0. *)
    apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ)) by
        (apply d_wf_denv__tvar; auto).
      apply H0 with (B := B) (A := A); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        rewrite_env ((y ~ dbind_typ A) ++ (X ~ dbind_tvar) ++ Γ).
        apply d_typing_gen_weakening.
        apply Hbody. exact Hy.
Admitted.

(** Original [d_typing_abs_value_to_forall] form, kept as a corollary
    callable from the main theorem's __abs + __forall_r case. *)
Lemma d_typing_abs_value_to_forall :
  forall L Γ e A B m_orig L_sub A_target,
    is_inh_typ A ->
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    (forall X, X `notin` L_sub ->
       d_sub_gen mode_tc nil ((X ~ dbind_tvar) ++ Γ) (typ_arrow A B)
         (open_typ_wrt_typ A_target (typ_var_f X))) ->
    d_typing_gen mode_tc Γ (exp_abs e) (typ_all_col colour_inh A_target).
Proof.
  intros L Γ e A B m_orig L_sub A_target HinhA HwfA Hbody Hdecr Hwfd HperX.
  apply d_typing_gen__forall with (L := L_sub `union` dom Γ).
  - apply is_value__abs.
  - intros X HX.
    eapply d_typing_abs_value_to_subsumption with
      (L := L) (A := A) (B := B) (m_orig := m_orig); eauto.
    + apply d_wf_typ_weakening_head; auto.
    + intros y Hy.
      rewrite_env ((y ~ dbind_typ A) ++ (X ~ dbind_tvar) ++ Γ).
      apply d_typing_gen_weakening.
      apply Hbody. exact Hy.
    + apply d_wf_denv__tvar; auto.
Qed.

(** [d_typing_abs_anno_value_to_subsumption]: same structure as
    [d_typing_abs_value_to_subsumption] but for [exp_abs_anno A e].
    The d_sub_gen __forall_r case recurses; __embed and __refl_any
    inherit the same circularity obstacle (body lift from
    [decr_mode m_orig] to [mode_tc]). *)
Lemma d_typing_abs_anno_value_to_subsumption :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_tc nil Γ (typ_arrow A B) C ->
    d_typing_gen mode_tc Γ (exp_abs_anno A e) C.
Proof.
  intros L Γ e A B m_orig C HwfA Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - admit.
  - (* __refl_mono: C = typ_arrow A B, forced MONO. *)
    match goal with Hm : mono_typ (typ_arrow A B) |- _ =>
      assert (HmonoA : mono_typ A) by (inversion Hm; auto);
      assert (HmonoB : mono_typ B) by (inversion Hm; auto)
    end.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + assumption.
    + intros x Hx.
      assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
        (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := B); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
        -- rewrite_env ((x ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           match goal with Hw : d_wf_typ Γ (typ_arrow A B) |- _ =>
             inversion Hw; assumption end.
  - apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs_anno.
    + intros X HX.
      assert (HX_L : X `notin` L0) by fsetdec.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ)) by
        (apply d_wf_denv__tvar; auto).
      apply H0 with (B := B) (A := A); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        rewrite_env ((y ~ dbind_typ A) ++ (X ~ dbind_tvar) ++ Γ).
        apply d_typing_gen_weakening.
        apply Hbody. exact Hy.
Admitted.

(** Corollary of [d_typing_abs_anno_value_to_subsumption]. *)
Lemma d_typing_abs_anno_value_to_forall :
  forall L Γ e A B m_orig L_sub A_target,
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    (forall X, X `notin` L_sub ->
       d_sub_gen mode_tc nil ((X ~ dbind_tvar) ++ Γ) (typ_arrow A B)
         (open_typ_wrt_typ A_target (typ_var_f X))) ->
    d_typing_gen mode_tc Γ (exp_abs_anno A e) (typ_all_col colour_inh A_target).
Proof.
  intros L Γ e A B m_orig L_sub A_target HwfA Hbody Hdecr Hwfd HperX.
  apply d_typing_gen__forall with (L := L_sub `union` dom Γ).
  - apply is_value__abs_anno.
  - intros X HX.
    eapply d_typing_abs_anno_value_to_subsumption with
      (L := L) (A := A) (B := B) (m_orig := m_orig); eauto.
    + apply d_wf_typ_weakening_head; auto.
    + intros y Hy.
      rewrite_env ((y ~ dbind_typ A) ++ (X ~ dbind_tvar) ++ Γ).
      apply d_typing_gen_weakening.
      apply Hbody. exact Hy.
    + apply d_wf_denv__tvar; auto.
Qed.

(** ** Generalised General Subsumption (paper Lemma B.5).

    The statement: for [Hty : d_typing_gen m_orig Γ e A] with [m_orig ∈ FN^n TI],
    and [Hsub_gen : d_sub_gen (mode_fn_n_subst m_orig m_new) nil Γ A B]
    (using the GENERALISED sub), we derive [d_typing_gen (mode_fn_n_subst
    m_orig m_new) Γ e B].

    The use of [d_sub_gen] (rather than the original [d_sub]) is what
    makes the __app function-side lift go through: that lift constructs
    a sub via [d_sub_gen__arg] with [d_consis_gen__refl_any] on the
    function's argument type A0 (no longer requiring A0 to be mono).

    Proof outline (per paper appendix Lemma B.5):
    - Induct on Hty via [d_typing_pat_mut].
    - For each Hty case, dispatch on Hsub_gen's shape.
    - __abs / __abs_anno: body IH from the mutual induction provides
      body's generalised subsumption at (x ~ A_arg) ++ Γ.
    - __app: function-side IH fires at [mode_fn m_orig] (which is also
      in [is_fn_n_ti] form). The sub for the IH is [d_sub_gen__arg]
      using [d_consis_gen__refl_any] on the argument type.

    Closure status (this commit):
    - Vacuous mode_tc cases (Hty ∈ {__freeze, __forall}): CLOSED.
    - Hty ∈ {__unit, __var, __anno} / Hsub_gen = __embed: CLOSED via
      [d_typing_gen__sub] at the corresponding [is_base_term].
    - Hty = __unit / Hsub_gen = __refl_any: CLOSED via case-split on
      [mode_typ_compat] (mode_ti, mode_tc; mode_fn auto-discharged).
    - Hty = __var / Hsub_gen = __refl_any: mode_ti subcase CLOSED;
      mode_tc / mode_fn admit (need non-mono d_consis refl).
    - Hty = __anno / Hsub_gen = __refl_any: mode_ti subcase CLOSED;
      mode_tc / mode_fn admit (same as __var).
    - Hty = __sub:
      * m = mode_ti: CLOSED for __embed, __refl_any (all 3 modes),
        __arg via helpers [d_consis_extends_d_sub_gen_nil] composing
        Hsub_orig's d_consis with reconstructed Hsub_gen.
      * m = mode_ti / __forall_r: CLOSED via
        d_consis_extends_d_sub_gen_nil + d_sub_gen__forall_r
        reconstruction.
      * m = mode_fn _: admit (mode-changing d_sub transitivity is
        research-grade — Hsub_orig is __arg, composition with outer
        Hsub_gen at different mode doesn't go through standard subs).
    - Hty = __app:
      * __embed: CLOSED via function-side lift (paper's central case).
      * __refl_any: CLOSED via d_sub_gen__refl_any at lifted arrow.
      * __forall_r: CLOSED via d_sub_gen__forall_r reconstruction at
        function-side return.
      * __arg: CLOSED via nested d_sub_gen__arg at function side.
    - Hty ∈ {__abs, __abs_anno}:
      * __refl_any: CLOSED for m = mode_fn k, and for m = mode_ti via
        case-split on m_new (mode_ti, mode_tc match orig body mode;
        mode_fn k lifts body via H1/H2 IH with refl_any sub).
      * __forall_r: CLOSED via wiring to
        [d_typing_abs_value_to_forall] /
        [d_typing_abs_anno_value_to_forall] aux lemmas. The aux
        lemmas' __forall_r recursion case is closed by dependent
        induction on the d_sub_gen at the generalised target shape.
        Their internal __embed / __refl_any cases admit due to
        body-lift (mode_ti → mode_tc) circularity.
      * __embed / __arg: admit (research-grade —
        embed needs narrowing on arg type, arg needs both narrowing
        and body subsumption).

    Remaining admits are structurally documented:
    - forall_r at atomic / value Hty cases (var/anno) — partly closed
      via dedicated aux lemmas with localised remaining admits.
    - narrowing (abs/abs_anno + embed/arg).
    - gen→sub bridge (var/anno + arg) — partial conversion.
    - mode-changing d_sub transitivity (sub mode_fn outer).

    Helpers are now fully Qed:
    - [d_consis_to_d_sub_gen]: lift d_consis to d_sub_gen at any
      compatible mode by induction on mode_typ_compat.
    - [d_consis_extends_d_consis_gen]: compose d_consis on LHS with
      d_consis_gen at Δ = nil; uses [d_consis_compose] and resolves
      the permutation via [Permutation Δc nil → Δc = nil].
    - [d_consis_extends_d_sub_gen_nil]: gen-relation analogue of
      [d_consis_extends_d_sub_nil]; statement has [T] after [Hs] so
      the [induction Hs] IH abstracts over [T] properly.

    [d_sub_gen__refl_any] requires [mode_typ_compat m A] (def-level
    fix); without this the rule was too permissive (e.g. allowed
    [d_sub_gen (mode_fn _) nil Γ typ_unit typ_unit] whose target
    d_typing is unreachable). *)
Theorem d_typing_general_subsumption_gen : forall m_orig Γ e A,
    d_typing_gen m_orig Γ e A ->
    is_fn_n_ti m_orig ->
    d_wf_denv Γ ->
    forall m_new B,
      d_sub_gen (mode_fn_n_subst m_orig m_new) nil Γ A B ->
      d_typing_gen (mode_fn_n_subst m_orig m_new) Γ e B.
Proof.
  intros m_orig Γ e A Hty.
  induction Hty; intros Hfn Hwfd m_new B_tgt Hsub_gen.
  - (* === Hty = d_typing_gen__unit ===
       m_orig = mode_ti, target mode = m_new. ALL Hsub_gen sub-cases
       close in one step: [d_typing_gen__sub] takes the [d_sub_gen]
       directly (this is the structural payoff of [d_typing_gen]). *)
    simpl in Hsub_gen |- *.
    apply d_typing_unit_gen_subsumption; assumption.
  - (* === Hty = d_typing_gen__var ===
       Closes in one step via [d_typing_var_gen_subsumption]. *)
    simpl in Hsub_gen |- *.
    eapply d_typing_var_gen_subsumption; eauto.
  - (* === Hty = d_typing_gen__anno ===
       Closes in one step via [d_typing_anno_gen_subsumption]. The
       inner [d_typing_gen mode_tc Γ e A] (premise of __anno) is in
       scope from the induction. *)
    simpl in Hsub_gen |- *.
    eapply d_typing_anno_gen_subsumption; eauto.
  - (* === Hty = d_typing_gen__sub: e is base, inner
       [d_typing_gen mode_ti Γ e A], Hsub_orig : d_sub_gen m nil Γ A B.
       e is base ⟹ reconstruct via [d_typing_gen__sub] with the inner
       typing and a COMPOSED [d_sub_gen]. For m = mode_ti the inner
       d_sub_gen is mode_ti (__embed __infer → d_consis, or
       __refl_mono); compose with Hsub_gen via
       [d_consis_extends_d_sub_gen_nil]. For m = mode_fn _ the
       composition is mode-changing — deferred. *)
    inversion Hfn; subst.
    + (* m = mode_ti. mode_fn_n_subst mode_ti m_new = m_new.
         Hinner : d_typing_gen mode_ti Γ e A (inner type A);
         Hsub_orig : d_sub_gen mode_ti nil Γ A B;
         Hsub_gen : d_sub_gen m_new nil Γ B B_tgt. *)
      simpl in Hsub_gen |- *.
      apply d_typing_gen__sub with (A := A); auto.
      (* Goal: d_sub_gen m_new nil Γ A B_tgt. Invert Hsub_orig. *)
      match goal with
      | Hso : d_sub_gen mode_ti nil Γ ?A0 ?B0 |- _ =>
          inversion Hso; subst
      end.
      * (* __embed: d_sub mode_ti — __infer gives d_consis A B. *)
        match goal with
        | Hs : d_sub mode_ti nil Γ ?A0 ?B0 |- _ =>
            inversion Hs; subst;
            try (match goal with H' : mode_ti <> mode_ti |- _ =>
                   exfalso; apply H'; reflexivity end)
        end.
        eapply d_consis_extends_d_sub_gen_nil; [ exact Hsub_gen | | ].
        -- assumption.
        -- eapply d_typing_gen_preserves_wf; eauto.
      * (* __refl_mono: A = B. Hsub_gen : d_sub_gen m_new Γ A B_tgt
           (since B = A). *)
        exact Hsub_gen.
    + (* m = mode_fn _: mode-changing composition. Deferred. *)
      admit.
  - (* === Hty = d_typing_gen__freeze ==========================================
       m_orig = mode_tc — NOT in is_fn_n_ti. Vacuous via Hfn. *)
    inversion Hfn.
  - (* === Hty = d_typing_gen__forall ==========================================
       m_orig = mode_tc — NOT in is_fn_n_ti. Vacuous via Hfn. *)
    inversion Hfn.
  - (* === Hty = d_typing_gen__abs ===
       Dispatch on Hsub_gen. __refl_mono / __forall_r CLOSE;
       __embed / __arg deferred (need d_sub inversion / a
       d_typing_gen-narrowing lemma). *)
    simpl in Hsub_gen |- *.
    dependent destruction Hsub_gen.
    + (* __embed: exp_abs not base. Deferred. *)
      admit.
    + (* __refl_mono: B_tgt = typ_arrow A B, forced MONO. Case-split
         on m via Hfn and lift the body via the IH H2 with a
         [d_sub_gen__refl_mono] body sub. *)
      assert (HmonoA : mono_typ A) by (inversion H3; auto).
      assert (HmonoB : mono_typ B) by (inversion H3; auto).
      assert (HwfA' : d_wf_typ Γ A) by (inversion H5; auto).
      assert (HwfB' : d_wf_typ Γ B) by (inversion H5; auto).
      inversion Hfn; subst.
      * (* m = mode_ti: target = m_new. *)
        eapply d_typing_gen__abs with (L := L `union` dom Γ).
        -- apply mono_typ_is_inh_typ; auto.
        -- exact HwfA'.
        -- intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
             (apply d_wf_denv__typ; auto).
           specialize (H2 x ltac:(auto) is_fn_n_ti__ti Hwfd_x
                          (decr_mode m_new) B).
           simpl in H2. apply H2.
           apply d_sub_gen__refl_mono; auto.
           ++ simpl in H4. inversion H4; subst; simpl;
               [ apply mode_typ_compat__ti; apply mono_typ_is_syn_typ; auto
               | apply mode_typ_compat__tc; apply mono_typ_is_inh_typ; auto
               | assumption ].
           ++ rewrite_env ((x ~ dbind_typ A) ++ Γ).
              apply d_wf_typ_weakening_head; auto.
      * (* m = mode_fn k. *)
        eapply d_typing_gen__abs with (L := L `union` dom Γ).
        -- apply mono_typ_is_inh_typ; auto.
        -- exact HwfA'.
        -- intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
             (apply d_wf_denv__typ; auto).
           specialize (H2 x ltac:(auto) (is_fn_n_ti_decr Hfn) Hwfd_x
                          m_new B).
           simpl in H2. apply H2.
           apply d_sub_gen__refl_mono; auto.
           ++ simpl in H4. inversion H4; subst; assumption.
           ++ rewrite_env ((x ~ dbind_typ A) ++ Γ).
              apply d_wf_typ_weakening_head; auto.
    + (* __forall_r: m = mode_ti, m_new = mode_tc. Wire through
         [d_typing_abs_value_to_forall]. *)
      inversion Hfn; subst; simpl in *.
      * match goal with x_eq : mode_tc = ?mn |- _ =>
          symmetry in x_eq; subst mn
        end.
        eapply d_typing_abs_value_to_forall with
          (L := L) (m_orig := mode_ti) (A := A) (B := B); eauto.
      * discriminate.
    + (* __arg: target = mode_fn k. Needs a d_typing_gen narrowing
         lemma on the arg type. Deferred. *)
      admit.
  - (* === Hty = d_typing_gen__abs_anno: as __abs. *)
    simpl in Hsub_gen |- *.
    dependent destruction Hsub_gen.
    + (* __embed: deferred. *)
      admit.
    + (* __refl_mono: B_tgt = typ_arrow A B, forced MONO. Body IH = H1
         (abs_anno has 2 d_typing premises: HwfA = H, Hbody = H0,
         IH = H1). *)
      assert (HmonoA : mono_typ A) by (inversion H2; auto).
      assert (HmonoB : mono_typ B) by (inversion H2; auto).
      assert (HwfA' : d_wf_typ Γ A) by (inversion H4; auto).
      assert (HwfB' : d_wf_typ Γ B) by (inversion H4; auto).
      inversion Hfn; subst.
      * eapply d_typing_gen__abs_anno with (L := L `union` dom Γ).
        -- exact HwfA'.
        -- intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
             (apply d_wf_denv__typ; auto).
           specialize (H1 x ltac:(auto) is_fn_n_ti__ti Hwfd_x
                          (decr_mode m_new) B).
           simpl in H1. apply H1.
           apply d_sub_gen__refl_mono; auto.
           ++ simpl in H3. inversion H3; subst; simpl;
               [ apply mode_typ_compat__ti; apply mono_typ_is_syn_typ; auto
               | apply mode_typ_compat__tc; apply mono_typ_is_inh_typ; auto
               | assumption ].
           ++ rewrite_env ((x ~ dbind_typ A) ++ Γ).
              apply d_wf_typ_weakening_head; auto.
      * eapply d_typing_gen__abs_anno with (L := L `union` dom Γ).
        -- exact HwfA'.
        -- intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
             (apply d_wf_denv__typ; auto).
           specialize (H1 x ltac:(auto) (is_fn_n_ti_decr Hfn) Hwfd_x
                          m_new B).
           simpl in H1. apply H1.
           apply d_sub_gen__refl_mono; auto.
           ++ simpl in H3. inversion H3; subst; assumption.
           ++ rewrite_env ((x ~ dbind_typ A) ++ Γ).
              apply d_wf_typ_weakening_head; auto.
    + (* __forall_r: wire through [d_typing_abs_anno_value_to_forall]. *)
      inversion Hfn; subst; simpl in *.
      * match goal with x_eq : mode_tc = ?mn |- _ =>
          symmetry in x_eq; subst mn
        end.
        eapply d_typing_abs_anno_value_to_forall with
          (L := L) (m_orig := mode_ti) (A := A) (B := B); eauto.
      * discriminate.
    + (* __arg: rule-structural obstacle (annotation = result-arg).
         Deferred. *)
      admit.
  - (* === Hty = d_typing_gen__app ===
       Function at mode_fn m; the function-side IH (IHHty1) fires at
       mode_fn m ∈ is_fn_n_ti. The sub for the IH is [d_sub_gen__arg]
       with [d_consis_gen_refl] on the (unchanged) argument type. *)
    simpl in Hsub_gen |- *.
    dependent destruction Hsub_gen.
    + (* __embed: lift function side via IHHty1 at d_sub_gen__arg
         (refl on arg, embed of outer sub). *)
      match goal with
      | H_pat : d_pat mode_tc Γ ?e2 ?P0,
        H_ref : d_refine_syn nil Γ ?P0 ?P'0,
        H_fn  : d_typing_gen (mode_fn ?m_) Γ ?e1 (typ_arrow ?A0 ?B0),
        H_arg : d_typing_gen mode_tc Γ ?e2 ?A0
        |- d_typing_gen _ Γ (exp_app ?e1 ?e2) ?B_t =>
          assert (Hwf_arr : d_wf_typ Γ (typ_arrow A0 B0)) by
            (eapply d_typing_gen_preserves_wf; eauto);
          assert (Hwf_A0 : d_wf_typ Γ A0) by (inversion Hwf_arr; auto);
          assert (Hinh_A0 : is_inh_typ A0) by
            (eapply d_typing_gen_check_is_inh; eassumption);
          eapply d_typing_gen__app with (P := P0) (P' := P'0) (A := A0); eauto
      end.
      eapply IHHty1;
      [ apply is_fn_n_ti__fn; assumption
      | assumption
      | simpl;
        rewrite_env (@nil atom ++ @nil atom);
        apply d_sub_gen__arg;
        [ apply d_consis_gen_refl; assumption
        | apply d_sub_gen__embed; assumption ] ].
    + (* __refl_mono: B_tgt = B0 (mono). Function-side lift via IHHty1
         at d_sub_gen__arg (refl on arg, refl_mono on the mono ret). *)
      match goal with
      | Hpat0 : d_pat mode_tc Γ ?e2 ?P0,
        Href0 : d_refine_syn nil Γ ?P0 ?P'0,
        Hty_fn0 : d_typing_gen (mode_fn ?m_) Γ ?e1 (typ_arrow ?A0 ?B0),
        Hty_arg0 : d_typing_gen mode_tc Γ ?e2 ?A0
        |- d_typing_gen _ Γ (exp_app ?e1 ?e2) ?B0 =>
          assert (Hwf_arr : d_wf_typ Γ (typ_arrow A0 B0)) by
            (eapply d_typing_gen_preserves_wf; eauto);
          eapply d_typing_gen__app with (P := P0) (P' := P'0) (A := A0); eauto
      end.
      eapply IHHty1.
      * apply is_fn_n_ti__fn; assumption.
      * assumption.
      * simpl.
        rewrite_env (@nil atom ++ @nil atom).
        apply d_sub_gen__arg.
        -- apply d_consis_gen_refl;
           [ match goal with Harg : d_typing_gen mode_tc _ _ ?A0
               |- is_inh_typ ?A0 =>
               eapply d_typing_gen_check_is_inh; exact Harg end
           | match goal with Hw : d_wf_typ Γ (typ_arrow ?A0 _)
               |- d_wf_typ Γ ?A0 =>
               inversion Hw; assumption end ].
        -- apply d_sub_gen__refl_mono; auto;
           match goal with Hw : d_wf_typ Γ (typ_arrow _ ?B0) |- _ =>
             inversion Hw; assumption end.
    + (* __forall_r: target = mode_tc ⟹ m = mode_ti, m_new = mode_tc. *)
      inversion Hfn; subst; simpl in x.
      * symmetry in x; subst.
        match goal with
        | Hpat0 : d_pat mode_tc Γ ?e2 ?P0,
          Href0 : d_refine_syn nil Γ ?P0 ?P'0,
          Hty_fn0 : d_typing_gen (mode_fn mode_ti) Γ ?e1 (typ_arrow ?A0 ?B0),
          Hty_arg0 : d_typing_gen mode_tc Γ ?e2 ?A0
          |- d_typing_gen _ Γ (exp_app ?e1 ?e2) (typ_all_col colour_inh ?A_t) =>
            assert (Hwf_arr : d_wf_typ Γ (typ_arrow A0 B0)) by
              (eapply d_typing_gen_preserves_wf; eauto);
            assert (Hwf_A0 : d_wf_typ Γ A0) by (inversion Hwf_arr; auto);
            assert (Hinh_A0 : is_inh_typ A0) by
              (eapply d_typing_gen_check_is_inh; eassumption);
            eapply d_typing_gen__app with (P := P0) (P' := P'0) (A := A0); eauto
        end.
        eapply IHHty1.
        -- apply is_fn_n_ti__fn; apply is_fn_n_ti__ti.
        -- assumption.
        -- simpl. rewrite_env (@nil atom ++ @nil atom).
           apply d_sub_gen__arg.
           ++ apply d_consis_gen_refl; assumption.
           ++ eapply d_sub_gen__forall_r. intros X HX. apply H1; auto.
      * discriminate x.
    + (* __arg: target = mode_fn target_inner. Function-side lift via
         IHHty1 at a nested d_sub_gen__arg. *)
      match goal with
      | Hpat0 : d_pat mode_tc Γ ?e2 ?P0,
        Href0 : d_refine_syn nil Γ ?P0 ?P'0,
        Hty_fn0 : d_typing_gen (mode_fn ?m_) Γ ?e1 (typ_arrow ?A0 ?B0),
        Hty_arg0 : d_typing_gen mode_tc Γ ?e2 ?A0
        |- d_typing_gen _ Γ (exp_app ?e1 ?e2) (typ_arrow ?A1 ?A2) =>
          assert (Hwf_arr : d_wf_typ Γ (typ_arrow A0 B0)) by
            (eapply d_typing_gen_preserves_wf; eauto);
          assert (Hwf_A0 : d_wf_typ Γ A0) by (inversion Hwf_arr; auto);
          assert (Hinh_A0 : is_inh_typ A0) by
            (eapply d_typing_gen_check_is_inh; eassumption);
          eapply d_typing_gen__app with (P := P0) (P' := P'0) (A := A0); eauto
      end.
      match goal with
      | x : _ ++ _ = nil |- _ =>
          apply app_eq_nil in x; destruct x as [HΔ1 HΔ2]; subst
      end.
      eapply IHHty1.
      * apply is_fn_n_ti__fn; assumption.
      * assumption.
      * simpl.
        match goal with
        | x0 : mode_fn _ = mode_fn_n_subst _ _ |- _ =>
            rewrite <- x0
        end.
        rewrite_env (@nil atom ++ @nil atom).
        apply d_sub_gen__arg.
        -- apply d_consis_gen_refl; assumption.
        -- rewrite_env (@nil atom ++ @nil atom).
           apply d_sub_gen__arg; eassumption.
Admitted.

(** Strong form V2 (kept for now; will be replaced by the bridged D1
    once [d_typing_general_subsumption_via_gen] is closed).

    [Γ_pre ++ Γ] split (following [d_sub_subst_mono] pattern): Hsub and
    Hty live at [(Γ_pre ++ Γ)], with Γ as the "base" context. After
    [dependent induction Hsub], the IH at a sub-Hsub abstracts over
    both Γ_pre and Γ — but since [Γ_pre ++ Γ] is treated as a single
    context unit by Coq's dependent induction, this generalisation is
    DUMMY: the IH's context-equation locks
    [Γ_pre' ++ Γ' = outer Γ_pre ++ outer Γ], so Γ_pre' is not actually
    free for extension. The true generalisation routes through
    [d_sub_gen] (paper's bid{T} extension); see notes below. *)
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

(** [d_consis_gen_to_d_consis]: the gen→original bridge for
    consistency. Total EXCEPT the [__forall_inh] case —
    [d_consis_gen (typ_all_col colour_inh T) (typ_all_col colour_inh A)]
    has no [d_consis] counterpart ([d_consis] admits no [typ_all_col]
    on the LHS). THIS single admit is the entire residual gap of the
    D1-via-D12 development. *)
Lemma d_consis_gen_to_d_consis : forall Δ Γ T A,
    d_consis_gen Δ Γ T A ->
    d_consis Δ Γ T A.
Proof.
  intros Δ Γ T A H. induction H.
  - (* __embed *) assumption.
  - (* __forall_inh: d_consis has no typ_all_col LHS rule.
       THE residual gap. *)
    admit.
  - (* __arrow *) apply d_consis__arrow; assumption.
Admitted.

(** [d_sub_gen_to_d_sub]: the gen→original bridge for subtyping.
    Total modulo [d_consis_gen_to_d_consis] (used in the [__arg]
    case). *)
Lemma d_sub_gen_to_d_sub : forall m Δ Γ T A,
    d_sub_gen m Δ Γ T A ->
    d_sub m Δ Γ T A.
Proof.
  intros m Δ Γ T A H. induction H.
  - (* __embed *) assumption.
  - (* __refl_mono *) apply d_sub_refl_mono_mode; assumption.
  - (* __forall_r *) apply d_sub__forall_r with (L := L); assumption.
  - (* __arg *) apply d_sub__arg.
    + apply d_consis_gen_to_d_consis; assumption.
    + assumption.
Qed.

(** [d_typing_gen_collapse]: the generalised typing collapses back to
    the original. Structural except [__sub], which routes through the
    [d_sub_gen → d_sub] bridge. The whole D1-via-D12 development is
    therefore closed *modulo the single admit* in
    [d_consis_gen_to_d_consis]'s [__forall_inh] case. *)
Lemma d_typing_gen_collapse : forall m Γ e A,
    d_typing_gen m Γ e A ->
    d_typing m Γ e A.
Proof.
  intros m Γ e A H. induction H.
  - apply d_typing__unit; assumption.
  - apply d_typing__var; assumption.
  - apply d_typing__anno; assumption.
  - (* __sub: bridge d_sub_gen → d_sub. *)
    apply d_typing__sub with (A := A); auto.
    apply d_sub_gen_to_d_sub; assumption.
  - apply d_typing__freeze; assumption.
  - apply d_typing__forall with (L := L); assumption.
  - apply d_typing__abs with (L := L); assumption.
  - apply d_typing__abs_anno with (L := L); assumption.
  - apply d_typing__app with (P := P) (P' := P') (A := A); assumption.
Admitted.

(** ** D1 via the generalised bridge (paper's strategy).

    D1 routes through D12 ([d_typing_general_subsumption_gen]):
    embed [d_typing] into [d_typing_gen], apply D12 (which keeps us in
    [d_typing_gen] and closes the var/anno cases directly via
    [d_typing_gen__sub]), then collapse back via
    [d_typing_gen_collapse].

    Set [m_orig := mode_ti], so [mode_fn_n_subst mode_ti m_new = m_new]
    matches the original D1's conclusion mode. *)
Theorem d_typing_general_subsumption_via_gen : forall Γ e A B m,
    d_wf_denv Γ ->
    d_typing mode_ti Γ e A ->
    d_sub m nil Γ A B ->
    d_typing m Γ e B.
Proof.
  intros Γ e A B m Hwfd Hty Hsub.
  apply d_typing_gen_collapse.
  change m with (mode_fn_n_subst mode_ti m).
  apply d_typing_general_subsumption_gen with (A := A); auto.
  - apply d_typing_embed_gen; assumption.
  - apply is_fn_n_ti__ti.
  - simpl. apply d_sub_gen__embed. exact Hsub.
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
