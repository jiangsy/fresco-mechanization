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
| d_consis_gen__refl_any : forall Γ A,
    d_wf_typ Γ A ->
    d_consis_gen nil Γ A A
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
| d_sub_gen__refl_any : forall m Γ A,
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

(** [d_sub_gen] is reflexive on any wf type at compatible mode. *)
Lemma d_sub_gen_refl : forall Γ A m,
    mode_typ_compat m A ->
    d_wf_typ Γ A ->
    d_sub_gen m nil Γ A A.
Proof.
  intros. apply d_sub_gen__refl_any; auto.
Qed.

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
  intros Γ A B Hcg Hinh.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hcg; subst.
  - eapply d_consis_rhs_is_inh_typ; eauto.
  - assumption.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hinh; subst.
    apply is_inh_typ__arrow; auto.
Qed.

(** [d_consis_gen_preserves_wf]: d_consis_gen preserves wf on RHS. *)
Lemma d_consis_gen_preserves_wf : forall Δ Γ A B,
    d_consis_gen Δ Γ A B ->
    d_wf_typ Γ B.
Proof.
  intros Δ Γ A B Hcg. induction Hcg.
  - eapply d_consis_preserves_wf; eauto.
  - assumption.
  - apply d_wf_typ__arrow; auto.
Qed.

(** [d_consis_gen_sym_inh]: symmetry for d_consis_gen on is_inh types. *)
Lemma d_consis_gen_sym_inh : forall Γ A B,
    d_consis_gen nil Γ A B ->
    is_inh_typ A ->
    d_consis_gen nil Γ B A.
Proof.
  intros Γ A B Hcg Hinh.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hcg; subst.
  - apply d_consis_gen__embed.
    apply d_consis_sym_inh; auto.
  - apply d_consis_gen__refl_any. assumption.
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
  - (* __refl_any: Aold = Anew. Identity. *)
    assumption.
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
  - apply d_consis_gen__refl_any. eapply d_wf_typ_weakening; eauto.
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
  - apply d_sub_gen__refl_any; auto. eapply d_wf_typ_weakening; eauto.
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

Lemma d_consis_gen_tvar_morph : forall Γ Γ' Δ T A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_consis_gen Δ Γ T A ->
    d_consis_gen Δ Γ' T A.
Proof.
  intros Γ Γ' Δ T A Hmorph H.
  generalize dependent Γ'. induction H; intros Γ' Hmorph.
  - apply d_consis_gen__embed. eapply d_consis_tvar_morph; eauto.
  - apply d_consis_gen__refl_any. eapply d_wf_typ_tvar_morph; eauto.
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
  - apply d_sub_gen__refl_any; auto. eapply d_wf_typ_tvar_morph; eauto.
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
  - (* __refl_any: B = A, Hc gives the result via embed. *)
    apply d_consis_gen__embed. assumption.
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
Qed.

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
  - (* __refl_any: A = B. Use d_consis_to_d_sub_gen. *)
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

(** Aux lemmas specialising the gen-subsumption theorem to specific
    Hty constructors. Each is proven by induction on Hsub_gen so the
    [__forall_r] case can recurse on the per-X premise — handling
    the nested-induction obstacle that the outer Hty-induction
    cannot. *)

(** [d_typing_unit_gen_subsumption]: gen-subsumption at Hty = __unit. *)
Lemma d_typing_unit_gen_subsumption : forall Γ A m,
    d_wf_denv Γ ->
    d_sub_gen m nil Γ typ_unit A ->
    d_typing m Γ exp_unit A.
Proof.
  intros Γ A m Hwfd Hs. dependent induction Hs.
  - (* __embed: d_sub m nil Γ typ_unit A. *)
    apply d_typing__sub with (A := typ_unit);
      [ apply is_base_term__unit
      | apply d_typing__unit;
          apply mode_typ_compat__ti; apply is_syn_typ__unit
      | assumption ].
  - (* __refl_any: A = typ_unit, mode_typ_compat m typ_unit. *)
    inversion H; subst.
    + apply d_typing__unit. apply mode_typ_compat__ti.
      apply is_syn_typ__unit.
    + apply d_typing__sub with (A := typ_unit);
        [ apply is_base_term__unit
        | apply d_typing__unit;
            apply mode_typ_compat__ti; apply is_syn_typ__unit
        | apply d_sub__check;
            [ intros ε T' Heq; discriminate Heq
            | intros T' Heq; discriminate Heq
            | apply mono_typ_is_inh_typ; apply mono_typ__unit
            | apply d_consis__unit ] ].
  - (* __forall_r: m = mode_tc, A = typ_all_col col_inh A0.
       Use d_typing__forall; the per-X IH (H0) fires on per-X
       Hsub_gen at extended Γ. (sub_gen__arg auto-discharged:
       typ_unit ≠ typ_arrow.) *)
    apply d_typing__forall with (L := L `union` dom Γ).
    + apply is_value__unit.
    + intros X HX.
      apply H0 with (X := X); auto.
      apply d_wf_denv__tvar; auto.
Qed.

(** ** Generalised General Subsumption (paper Lemma B.5).

    The statement: for [Hty : d_typing m_orig Γ e A] with [m_orig ∈ FN^n TI],
    and [Hsub_gen : d_sub_gen (mode_fn_n_subst m_orig m_new) nil Γ A B]
    (using the GENERALISED sub), we derive [d_typing (mode_fn_n_subst
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
      [d_typing__sub] at the corresponding [is_base_term].
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
      * __embed / __forall_r / __arg: admit (research-grade —
        embed needs narrowing on arg type, forall_r needs nested
        induction on Hsub_gen at extended Γ, arg needs both).

    Remaining 12 admits are structurally documented:
    - 5 forall_r at atomic / value Hty cases (need nested induction on
      Hsub_gen at extended Γ).
    - 4 narrowing (abs/abs_anno + embed/arg).
    - 2 gen→sub bridge (var/anno + arg) — partial conversion.
    - 1 mode-changing d_sub transitivity (sub mode_fn outer).

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
    d_typing m_orig Γ e A ->
    is_fn_n_ti m_orig ->
    d_wf_denv Γ ->
    forall m_new B,
      d_sub_gen (mode_fn_n_subst m_orig m_new) nil Γ A B ->
      d_typing (mode_fn_n_subst m_orig m_new) Γ e B.
Proof.
  intros m_orig Γ e A Hty.
  induction Hty; intros Hfn Hwfd m_new B_tgt Hsub_gen.
  - (* === Hty = d_typing__unit ============================================
       m_orig = mode_ti, e = exp_unit, A = typ_unit.
       Target mode = [mode_fn_n_subst mode_ti m_new] = m_new.
       Hsub_gen : d_sub_gen m_new nil Γ typ_unit B.

       Dispatch on Hsub_gen. The [__embed] and [__arg] sub-cases close
       cleanly. The [__refl_any] sub-case is sound only if m_new admits
       typ_unit (i.e. [mode_typ_compat m_new typ_unit]) — for
       m_new = mode_fn _, the conclusion is unreachable.
       This is a gap in the current [d_sub_gen__refl_any] rule, which
       lacks a [mode_typ_compat] premise. Documented as future
       def-level fix. The [__forall_r] sub-case needs nested
       recursion on Hsub_gen (Hty is atomic at __unit). *)
    simpl in Hsub_gen |- *.
    (* All __unit sub-cases close via the dedicated auxiliary
       [d_typing_unit_gen_subsumption], which uses dependent induction
       on Hsub_gen to handle __forall_r's nested recursion. *)
    apply d_typing_unit_gen_subsumption; assumption.
  - (* === Hty = d_typing__var =============================================
       m_orig = mode_ti, e = exp_var_f x, A = bound type for x.
       binds x (dbind_typ A) Γ in scope.
       Sub-case __embed: direct via d_typing__sub at is_base_term__var.
       __refl_any: mode_typ_compat gap (same as __unit).
       __forall_r: nested recursion needed.
       __arg: A unifies to typ_arrow; conclusion needs converting
       d_consis_gen / d_sub_gen pieces back to d_consis / d_sub —
       only partial (gen __refl_any has no general inverse). *)
    simpl in Hsub_gen |- *.
    dependent destruction Hsub_gen.
    + (* sub_gen__embed *)
      match goal with
      | Hb : binds _ (dbind_typ ?A0) Γ |- _ =>
          apply d_typing__sub with (A := A0);
            [ apply is_base_term__var
            | apply d_typing__var; exact Hb
            | assumption ]
      end.
    + (* sub_gen__refl_any: case-split on mode_typ_compat.
         mode_ti: trivial (Hty itself). mode_tc/mode_fn: research-grade
         (need d_consis_refl on possibly non-mono A). *)
      match goal with
      | Hcompat : mode_typ_compat ?m_ ?A0,
        Hb : binds _ (dbind_typ ?A0) Γ
        |- d_typing _ Γ (exp_var_f _) ?A0 =>
          inversion Hcompat; subst;
          [ apply d_typing__var; exact Hb
          | admit (* mode_tc *)
          | admit (* mode_fn *) ]
      end.
    + (* sub_gen__forall_r: nested recursion. *)
      admit.
    + (* sub_gen__arg: needs gen→sub bridge (partial). *)
      admit.
  - (* === Hty = d_typing__anno ============================================
       m_orig = mode_ti, e = exp_anno e' A, target mode = m_new.
       The inner d_typing is at mode_tc — IH on it has Hfn premise
       which fails (mode_tc ∉ is_fn_n_ti), so IH doesn't help.
       Dispatch on Hsub_gen as in __var. *)
    simpl in Hsub_gen |- *.
    dependent destruction Hsub_gen.
    + (* sub_gen__embed *)
      match goal with
      | HinhA : is_inh_typ ?A0,
        Hinner : d_typing mode_tc Γ _ ?A0 |- _ =>
          apply d_typing__sub with (A := A0);
            [ apply is_base_term__anno
            | apply d_typing__anno; [ exact HinhA | exact Hinner ]
            | assumption ]
      end.
    + (* sub_gen__refl_any: case-split on mode_typ_compat.
         mode_ti: Hty itself. mode_tc/mode_fn: research-grade. *)
      match goal with
      | Hcompat : mode_typ_compat ?m_ ?A0,
        HinhA : is_inh_typ ?A0,
        Hinner : d_typing mode_tc Γ ?e0 ?A0
        |- d_typing _ Γ (exp_anno ?e0 ?A0) ?A0 =>
          inversion Hcompat; subst;
          [ apply d_typing__anno; assumption
          | admit (* mode_tc *)
          | admit (* mode_fn *) ]
      end.
    + (* sub_gen__forall_r: nested recursion. *)
      admit.
    + (* sub_gen__arg: needs gen→sub bridge (partial). *)
      admit.
  - (* === Hty = d_typing__sub =============================================
       Case-split on Hfn to get m's shape. For m = mode_ti,
       Hsub_orig = d_sub__infer (only mode_ti shape), giving a
       d_consis we can compose via [d_consis_extends_d_sub_nil].
       For m = mode_fn _, Hsub_orig = d_sub__arg (wf excludes
       __forall_l_tagged / __forall_l_untagged); composition needs
       mode-changing transitivity. *)
    inversion Hfn; subst.
    + (* m = mode_ti. mode_fn_n_subst mode_ti m_new = m_new. Apply IHHty
         (the IH on Hty_inner at mode_ti) with the SAME outer sub —
         the IH gives the result directly via d_sub_gen at the new
         target, constructed by composing Hsub_orig and Hsub_gen. *)
      simpl in Hsub_gen |- *.
      (* Hsub_orig at mode_ti has d_consis embedded; extract it. *)
      match goal with
      | Hs_o : d_sub mode_ti nil Γ _ _ |- _ =>
          inversion Hs_o; subst;
          try (match goal with
               | H_ne : mode_ti <> mode_ti |- _ =>
                   exfalso; apply H_ne; reflexivity
               end)
      end.
      (* Now we have d_consis nil Γ A0 B0_inner (renamed). Use IHHty
         on the inner d_typing with the composed sub_gen, dispatching
         on Hsub_gen for each constructor. *)
      dependent destruction Hsub_gen.
      * (* __embed: d_sub m_new nil Γ B0_inner B_tgt. Compose with
           d_consis A0 B0_inner via [d_consis_extends_d_sub_nil] to get
           d_sub m_new A0 B_tgt; embed into d_sub_gen; apply IHHty. *)
        match goal with
        | Hconsis : d_consis nil Γ ?A0 ?B0,
          IHHty : is_fn_n_ti mode_ti -> d_wf_denv Γ -> _
          |- d_typing _ Γ _ ?B_t =>
            apply IHHty with (B := B_t);
            [ apply is_fn_n_ti__ti
            | assumption
            | apply d_sub_gen__embed;
              eapply d_consis_extends_d_sub_nil; eauto;
              eapply (proj1 d_typing_pat_preserves_wf); eauto ]
        end.
      * (* __refl_any: B_tgt = B0_inner. Build d_sub_gen m_new nil Γ A0
           B0_inner by composing d_consis A0 B0 (from Hsub_orig __infer)
           with d_sub_gen m_new B0 B0 (refl_any from mode_typ_compat)
           via the helper [d_consis_extends_d_sub_gen_nil]. *)
        match goal with
        | Hconsis : d_consis nil Γ ?A0 ?B0,
          IHHty : is_fn_n_ti mode_ti -> d_wf_denv Γ -> _,
          Hcompat : mode_typ_compat ?m_ ?B0,
          Hwfb : d_wf_typ Γ ?B0
          |- d_typing _ Γ _ ?B0 =>
            apply IHHty with (B := B0);
            [ apply is_fn_n_ti__ti
            | assumption
            | eapply d_consis_extends_d_sub_gen_nil;
              [ apply d_sub_gen__refl_any; assumption
              | exact Hconsis
              | eapply (proj1 d_typing_pat_preserves_wf); eauto ] ]
        end.
      * (* __forall_r: B_tgt = typ_all_col colour_inh A_target.
           Apply IHHty with sub built via d_consis_extends_d_sub_gen_nil
           and d_sub_gen__forall_r reconstruction. *)
        match goal with
        | Hconsis : d_consis nil Γ ?A0 ?B0,
          IHHty : is_fn_n_ti mode_ti -> d_wf_denv Γ -> _
          |- d_typing _ Γ _ (typ_all_col colour_inh ?A_t) =>
            apply IHHty with (B := typ_all_col colour_inh A_t);
            [ apply is_fn_n_ti__ti
            | assumption
            | eapply d_consis_extends_d_sub_gen_nil;
              [ eapply d_sub_gen__forall_r; intros X HX; eauto
              | exact Hconsis
              | eapply (proj1 d_typing_pat_preserves_wf); eauto ] ]
        end.
      * (* __arg: H3 = d_consis, H1 = d_consis_gen arg, Hsub_gen = d_sub_gen ret.
           Δ1 ++ Δ2 = nil ⟹ Δ1 = Δ2 = nil. *)
        match goal with
        | x : _ ++ _ = nil |- _ =>
            apply app_eq_nil in x; destruct x as [HΔ1 HΔ2]; subst
        end.
        match goal with
        | |- d_typing _ Γ _ (typ_arrow ?A1 ?A2) =>
            apply IHHty with (B := typ_arrow A1 A2);
            [ apply is_fn_n_ti__ti
            | assumption
            | eapply d_consis_extends_d_sub_gen_nil;
              [ rewrite_env (@nil atom ++ @nil atom);
                apply d_sub_gen__arg; [exact H1 | exact Hsub_gen]
              | exact H3
              | eapply (proj1 d_typing_pat_preserves_wf); eauto ] ]
        end.
    + (* m = mode_fn _ *)
      admit.
  - (* === Hty = d_typing__freeze ==========================================
       m_orig = mode_tc — NOT in is_fn_n_ti. Vacuous via Hfn. *)
    inversion Hfn.
  - (* === Hty = d_typing__forall ==========================================
       m_orig = mode_tc — NOT in is_fn_n_ti. Vacuous via Hfn. *)
    inversion Hfn.
  - (* === Hty = d_typing__abs =============================================
       Body's typing is at decr_mode m, which is in is_fn_n_ti
       (by [is_fn_n_ti_decr]). *)
    simpl in Hsub_gen |- *.
    dependent destruction Hsub_gen.
    + (* __embed: exp_abs not base, so __sub doesn't apply directly.
         Research-grade absorption into __abs. *)
      admit.
    + (* __refl_any: B_tgt = typ_arrow A B. Reconstruct via
         d_typing__abs at the lifted target. Case-split on m's shape
         (Hfn). For m = mode_fn k, body's IH fires at m_new directly
         and mode_typ_compat at body level follows from outer __fn. *)
      inversion Hfn; subst.
      * (* m = mode_ti: target = m_new (any mode). Case-split on m_new
           via mode_typ_compat. For m_new ∈ {mode_ti, mode_tc}, body's
           lifted mode = mode_ti = orig — use Hbody directly. For
           m_new = mode_fn k, body's lifted mode = k — use IH with
           a refl_any sub built from inverting compat. *)
        inversion H3; subst.
        -- (* mode_ti: target=mode_ti. Body lifted mode = decr_mode
              mode_ti = mode_ti = orig. Use Hbody directly. *)
          eapply d_typing__abs; try assumption.
          instantiate (1 := L `union` dom Γ).
          intros x Hx. simpl. apply H1; auto.
        -- (* mode_tc: target=mode_tc. Body lifted mode = decr_mode
              mode_tc = mode_tc (≠ orig mode_ti). Use IH (H2) at
              m_new' := mode_tc with refl_any body sub. *)
          eapply d_typing__abs; try assumption.
          instantiate (1 := L `union` dom Γ).
          intros x Hx.
          assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
            (apply d_wf_denv__typ; auto).
          specialize (H2 x ltac:(auto) is_fn_n_ti__ti Hwfd_x mode_tc B);
          simpl in H2; apply H2.
          apply d_sub_gen__refl_any.
          ++ (* mode_typ_compat mode_tc B from __tc inversion *)
            apply mode_typ_compat__tc.
            inversion H4; subst. inversion H5; subst. assumption.
          ++ inversion H4; subst.
             rewrite_env ((x ~ dbind_typ A) ++ Γ).
             apply d_wf_typ_weakening_head; auto.
        -- (* mode_fn k: m_new = mode_fn k where k is renamed `m`.
              Body lift via H2 at m_new' := m (decr of the lifted target). *)
          eapply d_typing__abs; try assumption.
          instantiate (1 := L `union` dom Γ).
          intros x Hx.
          assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
            (apply d_wf_denv__typ; auto).
          specialize (H2 x ltac:(auto) is_fn_n_ti__ti Hwfd_x m B);
          simpl in H2; apply H2.
          apply d_sub_gen__refl_any.
          ++ assumption. (* mode_typ_compat m B from inversion *)
          ++ inversion H4; subst.
             rewrite_env ((x ~ dbind_typ A) ++ Γ).
             apply d_wf_typ_weakening_head; auto.
      * (* m = mode_fn k: target = mode_fn (mode_fn_n_subst k m_new). *)
        eapply d_typing__abs; try assumption.
        instantiate (1 := L `union` dom Γ).
        intros x Hx.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
          (apply d_wf_denv__typ; auto).
        specialize (H2 x ltac:(auto) (is_fn_n_ti_decr Hfn) Hwfd_x m_new B);
        simpl in H2; apply H2.
        apply d_sub_gen__refl_any.
        -- (* mode_typ_compat (mode_fn_n_subst k m_new) B *)
          inversion H3; subst; assumption.
        -- (* d_wf_typ ((x~A)::Γ) B *)
          inversion H4; subst.
          rewrite_env ((x ~ dbind_typ A) ++ Γ).
          apply d_wf_typ_weakening_head; auto.
    + (* __forall_r: target = mode_tc. Use d_typing__forall (exp_abs
         is a value). Per-X premise needs nested recursion. *)
      admit.
    + (* __arg: target = mode_fn k. After destruction:
         H3 : d_consis_gen Δ1 Γ A A1 (arg-side)
         Hsub_gen : d_sub_gen k Δ2 Γ B A2 (ret-side)
         B_tgt = typ_arrow A1 A2, with Δ1 ++ Δ2 = nil.
         Reconstruct via d_typing__abs at mode_fn k. *)
      match goal with
      | x_eq : _ ++ _ = nil |- _ =>
          apply app_eq_nil in x_eq; destruct x_eq as [HΔ1 HΔ2]; subst
      end.
      apply d_typing__abs with
        (L := L `union` dom Γ).
      * (* is_inh_typ A1 from d_consis_gen + is_inh_typ A. *)
        eapply d_consis_gen_rhs_is_inh_typ; eauto.
      * (* d_wf_typ Γ A1 from d_consis_gen preserves wf. *)
        eapply d_consis_gen_preserves_wf; eauto.
      * (* Body: lift via IH (H2) at m_new' such that the IH's mode
           matches k, then narrow context (y:A) → (y:A1).
           Case-split on m to find right m_new' for IH. *)
        intros y Hy.
        inversion Hfn; subst.
        -- (* m = mode_ti: subst m_new := mode_fn k via the
              constructor equation, then apply IH H2 at m_new' := k. *)
          simpl in *.
          match goal with
          | x_eq : mode_fn _ = m_new |- _ =>
              symmetry in x_eq; subst m_new
          end.
          assert (Hwfd_y : d_wf_denv ((y ~ dbind_typ A) ++ Γ)) by
            (apply d_wf_denv__typ; auto).
          assert (Hwf_A1 : d_wf_typ Γ A1) by
            (eapply d_consis_gen_preserves_wf; eauto).
          apply d_typing_narrow_consis_head_arg with (Aold := A); auto.
          ++ (* d_typing k ((y:A)::Γ) (open e y) A2 via IH H2. *)
            assert (Hsub_weak : d_sub_gen m0 nil ((y ~ dbind_typ A) ++ Γ) B A2)
              by (apply d_sub_gen_weakening_head; assumption).
            apply H2 with (B := A2); auto.
        -- (* m = mode_fn m1: x0 : mode_fn k = mode_fn_n_subst (mode_fn m1) m_new.
              After simpl: mode_fn k = mode_fn (mode_fn_n_subst m1 m_new).
              Injection gives k = mode_fn_n_subst m1 m_new. *)
          simpl in *.
          injection x0 as Hkeq.
          assert (Hwfd_y : d_wf_denv ((y ~ dbind_typ A) ++ Γ)) by
            (apply d_wf_denv__typ; auto).
          assert (Hwf_A1 : d_wf_typ Γ A1) by
            (eapply d_consis_gen_preserves_wf; eauto).
          apply d_typing_narrow_consis_head_arg with (Aold := A); auto.
          ++ assert (Hsub_weak : d_sub_gen (mode_fn_n_subst m1 m_new)
                                          nil ((y ~ dbind_typ A) ++ Γ) B A2)
              by (rewrite <- Hkeq; apply d_sub_gen_weakening_head; assumption).
            apply H2 with (B := A2); auto.
  - (* === Hty = d_typing__abs_anno ========================================
       Symmetric to __abs but with explicit annotation (no is_inh_typ
       premise). Same dispatch shape on Hsub_gen. *)
    simpl in Hsub_gen |- *.
    dependent destruction Hsub_gen.
    + (* __embed: exp_abs_anno not base. *) admit.
    + (* __refl_any: B_tgt = typ_arrow A B. Same as __abs + __refl_any
         but with H1 = body cofinite. For m = mode_fn k, reconstruct
         via d_typing__abs_anno + IH (named H1 for __abs_anno since
         only 2 premises: HwfA, Hbody). *)
      inversion Hfn; subst.
      * (* m = mode_ti: case-split on m_new via outer mode_typ_compat. *)
        inversion H2; subst.
        -- (* m_new = mode_ti: body matches orig *)
          eapply d_typing__abs_anno; try assumption.
          instantiate (1 := L `union` dom Γ).
          intros x Hx. simpl. apply H0; auto.
        -- (* m_new = mode_tc: lift via H1 (IH for body) *)
          eapply d_typing__abs_anno; try assumption.
          instantiate (1 := L `union` dom Γ).
          intros x Hx.
          assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
            (apply d_wf_denv__typ; auto).
          specialize (H1 x ltac:(auto) is_fn_n_ti__ti Hwfd_x mode_tc B);
          simpl in H1; apply H1.
          apply d_sub_gen__refl_any.
          ++ apply mode_typ_compat__tc.
             inversion H3; subst. inversion H4; subst. assumption.
          ++ inversion H3; subst.
             rewrite_env ((x ~ dbind_typ A) ++ Γ).
             apply d_wf_typ_weakening_head; auto.
        -- (* m_new = mode_fn k: lift via H1 *)
          eapply d_typing__abs_anno; try assumption.
          instantiate (1 := L `union` dom Γ).
          intros x Hx.
          assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
            (apply d_wf_denv__typ; auto).
          specialize (H1 x ltac:(auto) is_fn_n_ti__ti Hwfd_x m B);
          simpl in H1; apply H1.
          apply d_sub_gen__refl_any.
          ++ assumption.
          ++ inversion H3; subst.
             rewrite_env ((x ~ dbind_typ A) ++ Γ).
             apply d_wf_typ_weakening_head; auto.
      * eapply d_typing__abs_anno; try assumption.
        instantiate (1 := L `union` dom Γ).
        intros x Hx.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ)) by
          (apply d_wf_denv__typ; auto).
        specialize (H1 x ltac:(auto) (is_fn_n_ti_decr Hfn) Hwfd_x m_new B);
        simpl in H1; apply H1.
        apply d_sub_gen__refl_any.
        -- inversion H2; subst; assumption.
        -- inversion H3; subst.
           rewrite_env ((x ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head; auto.
    + (* __forall_r: nested recursion. *) admit.
    + (* __arg: argument-type change + body lift. Research-grade. *)
      admit.
  - (* === Hty = d_typing__app =============================================
       m_orig = m, function at mode_fn m. IH on function fires at
       mode_fn m ∈ is_fn_n_ti. The sub for the IH is
       [d_sub_gen__arg] with [d_consis_gen__refl_any] on the
       argument type — the paper's bridge that removes the mono-A0
       requirement. *)
    simpl in Hsub_gen |- *.
    dependent destruction Hsub_gen.
    + (* __embed: lift function side via IHHty_fn at the constructed
         d_sub_gen__arg(refl_any on arg, embed of outer sub). *)
      match goal with
      | H_pat : d_pat mode_tc Γ ?e2 ?P0,
        H_ref : d_refine_syn nil Γ ?P0 ?P'0,
        H_fn  : d_typing (mode_fn ?m_) Γ ?e1 (typ_arrow ?A0 ?B0),
        H_arg : d_typing mode_tc Γ ?e2 ?A0
        |- d_typing _ Γ (exp_app ?e1 ?e2) ?B_t =>
          assert (Hwf_arr : d_wf_typ Γ (typ_arrow A0 B0)) by
            (eapply (proj1 d_typing_pat_preserves_wf); eauto);
          assert (Hwf_A0 : d_wf_typ Γ A0) by (inversion Hwf_arr; auto);
          eapply d_typing__app with (P := P0) (P' := P'0) (A := A0); eauto
      end.
      (* Solve the function-side d_typing via IH. The IH's name is
         auto-generated by [induction Hty]; we hunt for it by structure. *)
      eapply IHHty1;
      [ apply is_fn_n_ti__fn; assumption
      | assumption
      | simpl;
        rewrite_env (@nil atom ++ @nil atom);
        apply d_sub_gen__arg;
        [ apply d_consis_gen__refl_any;
          match goal with
          | Hw : d_wf_typ Γ (typ_arrow ?A0 _) |- _ =>
              inversion Hw; assumption
          end
        | apply d_sub_gen__embed; assumption ] ].
    + (* __refl_any: B_tgt = B0. Use IHHty1 (function-side IH) at a
         refl_any sub_gen for the lifted arrow. The arrow's compat
         follows from outer mode_typ_compat via mode_typ_compat__fn
         on the argument type. *)
      match goal with
      | Hpat0 : d_pat mode_tc Γ ?e2 ?P0,
        Href0 : d_refine_syn nil Γ ?P0 ?P'0,
        Hty_fn0 : d_typing (mode_fn ?m_) Γ ?e1 (typ_arrow ?A0 ?B0),
        Hty_arg0 : d_typing mode_tc Γ ?e2 ?A0
        |- d_typing _ Γ (exp_app ?e1 ?e2) ?B0 =>
          assert (Hwf_arr : d_wf_typ Γ (typ_arrow A0 B0)) by
            (eapply (proj1 d_typing_pat_preserves_wf); eauto);
          eapply d_typing__app with (P := P0) (P' := P'0) (A := A0); eauto
      end.
      eapply IHHty1.
      * apply is_fn_n_ti__fn; assumption.
      * assumption.
      * simpl.
        apply d_sub_gen__refl_any.
        -- (* mode_typ_compat (mode_fn _) (typ_arrow A B) *)
          apply mode_typ_compat__fn; assumption.
        -- (* d_wf_typ Γ (typ_arrow A B) *)
          assumption.
    + (* __forall_r: target = mode_tc. Constraint mode_tc =
         mode_fn_n_subst m m_new + Hfn ⟹ m = mode_ti, m_new = mode_tc. *)
      inversion Hfn; subst; simpl in x.
      * (* m = mode_ti, so m_new = mode_tc (from x : mode_tc = m_new). *)
        symmetry in x; subst.
        match goal with
        | Hpat0 : d_pat mode_tc Γ ?e2 ?P0,
          Href0 : d_refine_syn nil Γ ?P0 ?P'0,
          Hty_fn0 : d_typing (mode_fn mode_ti) Γ ?e1 (typ_arrow ?A0 ?B0),
          Hty_arg0 : d_typing mode_tc Γ ?e2 ?A0
          |- d_typing _ Γ (exp_app ?e1 ?e2) (typ_all_col colour_inh ?A_t) =>
            assert (Hwf_arr : d_wf_typ Γ (typ_arrow A0 B0)) by
              (eapply (proj1 d_typing_pat_preserves_wf); eauto);
            assert (Hwf_A0 : d_wf_typ Γ A0) by (inversion Hwf_arr; auto);
            eapply d_typing__app with (P := P0) (P' := P'0) (A := A0); eauto
        end.
        eapply IHHty1.
        -- apply is_fn_n_ti__fn; apply is_fn_n_ti__ti.
        -- assumption.
        -- simpl. rewrite_env (@nil atom ++ @nil atom).
           apply d_sub_gen__arg.
           ++ apply d_consis_gen__refl_any. assumption.
           ++ eapply d_sub_gen__forall_r. intros X HX. apply H1; auto.
      * (* m = mode_fn _: equation mode_tc = mode_fn (...) is False. *)
        discriminate x.
    + (* __arg: target = mode_fn target_inner. Reconstruct via
         d_typing__app at mode_fn target_inner, function-side lift via
         IHHty1 at a sub built via nested d_sub_gen__arg (refl_any on
         outer arg + d_sub_gen__arg-from-destructed-pieces on ret). *)
      match goal with
      | Hpat0 : d_pat mode_tc Γ ?e2 ?P0,
        Href0 : d_refine_syn nil Γ ?P0 ?P'0,
        Hty_fn0 : d_typing (mode_fn ?m_) Γ ?e1 (typ_arrow ?A0 ?B0),
        Hty_arg0 : d_typing mode_tc Γ ?e2 ?A0
        |- d_typing _ Γ (exp_app ?e1 ?e2) (typ_arrow ?A1 ?A2) =>
          assert (Hwf_arr : d_wf_typ Γ (typ_arrow A0 B0)) by
            (eapply (proj1 d_typing_pat_preserves_wf); eauto);
          assert (Hwf_A0 : d_wf_typ Γ A0) by (inversion Hwf_arr; auto);
          eapply d_typing__app with (P := P0) (P' := P'0) (A := A0); eauto
      end.
      (* Function-side lift: IHHty1 expects sub from typ_arrow A B
         to typ_arrow A (typ_arrow A1 A2) at mode mode_fn (mode_fn _). *)
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
        -- apply d_consis_gen__refl_any. assumption.
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

(** ** D1 via the generalised bridge (paper's strategy).

    An alternative derivation of D1 routing through the generalised
    [d_typing_general_subsumption_gen] (Lemma B.5). Once the latter is
    closed, this becomes the canonical D1.

    Set [m_orig := mode_ti], so [mode_fn_n_subst mode_ti m_new = m_new]
    and the conclusion matches the original D1. Embed the original
    [d_sub] into [d_sub_gen] via [d_sub_gen__embed]. *)
Theorem d_typing_general_subsumption_via_gen : forall Γ e A B m,
    d_wf_denv Γ ->
    d_typing mode_ti Γ e A ->
    d_sub m nil Γ A B ->
    d_typing m Γ e B.
Proof.
  intros Γ e A B m Hwfd Hty Hsub.
  change m with (mode_fn_n_subst mode_ti m).
  apply d_typing_general_subsumption_gen with (A := A); auto.
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
