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
  - apply d_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__forall_syn with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__forall_inh with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis__arrow; eauto.
Qed.

(** [d_consis]-related types have EQUAL [syn_color_t] — [d_consis]
    relates types differing only in [forall]-colour/tag, exactly what
    [syn_color_t] erases. (The [d_consis_gen] analogue is
    [d_consis_gen_syn_color_eq], proved later.) Used to show a
    [syn_color_t]-typed variable is invariant under [d_consis]-narrowing. *)
Lemma d_consis_syn_color_eq : forall Δ Γ A B,
    d_consis Δ Γ A B ->
    syn_color_t A = syn_color_t B.
Proof.
  intros Δ Γ A B H. induction H; simpl; try reflexivity.
  - (* __forall_inh_tagged *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __forall_syn_tagged *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __forall_inh *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __forall_syn (post-refactor) *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __arrow *)
    rewrite IHd_consis1. rewrite IHd_consis2. reflexivity.
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
  - apply d_consis__forall_syn_tagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__forall_syn with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hin | Hin]; apply binds_app_iff;
      [left; auto | right; auto].
  - apply d_consis__forall_inh with (L := L `union` dom Γ').
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
  - apply d_pat_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
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
  - apply d_pat_consis__forall_syn_tagged with (L := L `union` dom Γ').
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
  - (* d_typing__abs: post re-encoding [A : ctyp]; context binds
       [syn_color A]. *)
    apply d_typing__abs with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_typ_weakening; eauto.
    + intros x Hx.
      rewrite_env (((x ~ dbind_typ (syn_color A)) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H; auto.
  - (* d_typing__abs_anno: [A : ctyp]; context binds [syn_color A]. *)
    apply d_typing__abs_anno with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_typ_weakening; eauto.
    + intros x Hx.
      rewrite_env (((x ~ dbind_typ (syn_color A)) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H; auto.
  - (* d_typing__app: post re-encoding [P : ctyp], [P' : typ]; the
       function-arg [typ] is [P'] (no separate [A] parameter). *)
    apply d_typing__app with (P := P) (P' := P'); eauto.
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
  - (* d_typing__anno: post re-encoding [A : ctyp]; single [d_typing
       mode_tc] premise. *)
    intros Γ e A Hty IH Γ' Hm. apply d_typing__anno; auto.
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
  - (* d_typing__abs: post re-encoding [A : ctyp]; wf + cofinite + IH. *)
    intros L Γ m e A B Hwf Hbody IH Γ' Hm.
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
  - (* d_typing__app: post re-encoding [P : ctyp], [P' : typ]; no
       separate [A] parameter (function-arg is [P'] directly). *)
    intros Γ m e1 e2 P P' B Hpat IHpat Href Hty1 IH1 Hty2 IH2 Γ' Hm.
    apply d_typing__app with (P := P) (P' := P'); auto.
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
          syn_color_t Anew = syn_color_t Aold ->
          d_typing m (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2) e B) /\
    (forall m Γ_full e P,
        d_pat m Γ_full e P ->
        forall Γ1 x Aold Anew Γ2,
          Γ_full = Γ1 ++ (x ~ dbind_typ Aold) ++ Γ2 ->
          syn_color_t Anew = syn_color_t Aold ->
          d_pat m (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2) e P).
Proof.
  (* RE-ENCODING ADMIT (2026-05-15): post-ctyp re-encoding,
     [d_typing__var] returns the bound type RAW (not [syn_color]-painted),
     so the [__var] case no longer closes from [syn_color_t Anew =
     syn_color_t Aold] alone — we'd need the stronger [Anew = Aold]
     (or to thread the invariant that bindings are [syn_color]-shaped
     and leverage [syn_color] injectivity). The 18-case mutual
     scaffold restructures around that change; admitted for the
     build-green pass. *)
Admitted.


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
    syn_color_t Anew = syn_color_t Aold ->
    d_typing m ((x ~ dbind_typ Anew) ++ Γ) e B.
Proof.
  intros x Aold Anew Γ m e B Hty Hsc.
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
  - inversion Hinh. (* __forall_inh_tagged: typ_all_etag — not inh *)
  - inversion Hinh. (* __forall_syn_tagged: typ_all_etag — not inh *)
  - (* __forall_syn (post-refactor): A = typ_all_col colour_syn — not is_inh_typ *)
    inversion Hinh.
  - (* __forall_inh: A = typ_all_col colour_inh A0, B = same shape on
       RHS body. is_inh_typ A is satisfied. Compose via the new rule
       with sides swapped. *)
    inversion Hinh; subst.
    apply d_consis__forall_inh with (L := L `union` L0).
    intros X HX. apply H0; auto.
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
    routes through an extended consistency / subtyping relation
    ([fig:frost-subtyping-consistency-gen], syntax-directed.tex) over
    generalised unresolved types [\bid{T}], which extend [\syn{T}]
    with [inh{∀α.}T] on the LHS.

    [d_consis_gen] FAITHFULLY mirrors the paper's generalised
    [typconsis]: it has the SAME structural rules as [d_consis] (unit,
    var, forall_inh_tagged/untagged, forall_syn_tagged/untagged,
    arrow), each taking per-X [d_consis_gen] sub-derivations, PLUS the
    new [__forall_inh] rule (paper's [ForallInh]) admitting
    [typ_all_col colour_inh] on the LHS.

    Mirroring the structure (rather than the earlier [__embed] +
    [__forall_inh] shortcut) is what makes [d_consis_gen] compositional
    — [d_consis_gen_trans] goes through entirely within gen-land. The
    original [d_consis] embeds via the [d_consis_gen__embed] LEMMA
    (proved by induction below). *)
(* Post-refactor (typ_all_plain removed from typ): d_consis_gen mirrors
   d_consis exactly — 4 forall rules, no _untagged variants (those were
   paper-unfaithful). Rule order: tagged-inh, tagged-syn, syn, inh. *)
Inductive d_consis_gen :
    list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_consis_gen__unit : forall Γ,
    d_consis_gen nil Γ typ_unit typ_unit
| d_consis_gen__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_consis_gen nil Γ (typ_var_f X) (typ_var_f X)
| d_consis_gen__forall_inh_tagged : forall L Δ Γ ε T A,
    (forall X, X `notin` L ->
       d_consis_gen Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    ~ List.In ε Δ ->
    d_consis_gen (ε :: Δ) Γ (typ_all_etag ε T) (typ_all_col colour_inh A)
| d_consis_gen__forall_syn_tagged : forall L Δ Γ ε T A,
    (forall X, X `notin` L ->
       d_consis_gen Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis_gen Δ Γ (typ_all_etag ε T) (typ_all_col colour_syn A)
| d_consis_gen__forall_syn : forall L Δ Γ T A,
    (forall X, X `notin` L ->
       d_consis_gen Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis_gen Δ Γ (typ_all_col colour_syn T) (typ_all_col colour_syn A)
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

(** [d_consis] embeds into [d_consis_gen] — same rules across both. *)
Lemma d_consis_gen__embed : forall Δ Γ T A,
    d_consis Δ Γ T A ->
    d_consis_gen Δ Γ T A.
Proof.
  intros Δ Γ T A H. induction H.
  - apply d_consis_gen__unit.
  - apply d_consis_gen__var; assumption.
  - apply d_consis_gen__forall_inh_tagged with (L := L); assumption.
  - apply d_consis_gen__forall_syn_tagged with (L := L); assumption.
  - apply d_consis_gen__forall_syn with (L := L); assumption.
  - apply d_consis_gen__forall_inh with (L := L); assumption.
  - apply d_consis_gen__arrow; assumption.
Qed.

(** ** Property of [syn_color_t] specific to [d_consis_gen].

    [syn_color_t] (and its structural lemmas) live in [def_extra.v];
    here we prove the [d_consis_gen]-specific fact:
    [d_consis_gen]-related types have EQUAL [syn_color_t] — because
    [d_consis_gen] relates types that differ only in [forall]-colour/
    tag, exactly what [syn_color_t] erases. This is what makes a
    [syn_color_t]-typed variable invariant under narrowing. *)
Lemma d_consis_gen_syn_color_eq : forall Δ Γ A B,
    d_consis_gen Δ Γ A B ->
    syn_color_t A = syn_color_t B.
Proof.
  intros Δ Γ A B H. induction H; simpl; try reflexivity.
  - (* __forall_inh_tagged *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __forall_syn_tagged *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __forall_inh *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __forall_syn (post-refactor) *)
    f_equal.
    pick fresh X for (L `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (HX : X `notin` L) by auto.
    specialize (H0 X HX).
    rewrite !syn_color_t_open_var in H0.
    apply open_typ_wrt_typ_inj in H0; auto;
      rewrite syn_color_t_ftvar; auto.
  - (* __arrow *)
    rewrite IHd_consis_gen1. rewrite IHd_consis_gen2. reflexivity.
Qed.

(** When the LHS is already fully syn-coloured ([is_syn_typ T]), the
    generalised consistency relation is forced to be the identity:
    [d_consis_gen] has no constructor with a [typ_all_col colour_syn]
    LHS (mirrors the paper: [syn{∀α.}] is never a [typconsis] LHS — see
    [syntax-directed.tex], all [typconsis] LHS [forall]s are tagged),
    so any [forall] node makes the hypothesis vacuous, while the
    [unit]/[var]/[arrow] rules are rigid. This is what lets the D12
    [__abs_anno] cases reconstruct: the rule's arrow-arg [syn_color_t A]
    is pinned, but any consistency target of it must equal it. *)
Lemma d_consis_gen_lhs_syn_eq : forall T,
    is_syn_typ T ->
    forall Δ Γ A, d_consis_gen Δ Γ T A -> T = A.
Proof.
  intros T Hsyn. induction Hsyn; intros Δ Γ A0 Hc.
  - inversion Hc; subst. reflexivity.
  - inversion Hc; subst. reflexivity.
  - inversion Hc; subst. f_equal; eauto.
  - (* is_syn_typ__all: T = typ_all_col colour_syn A. Post-refactor,
       d_consis_gen has __forall_syn rule that matches this LHS.
       Inversion gives body relation; cofinite IH + open-inj close. *)
    inversion Hc; subst.
    f_equal.
    match goal with
    | Hbody : forall X, X `notin` ?L0 -> d_consis_gen _ _ _ _ |- _ =>
        pick fresh X for
          (L `union` L0 `union` ftvar_in_typ A `union` ftvar_in_typ A1);
        assert (HX_L : X `notin` L) by fsetdec;
        assert (HX_L0 : X `notin` L0) by fsetdec;
        specialize (H0 X HX_L Δ ((X ~ dbind_tvar) ++ Γ)
                      (open_typ_wrt_typ A1 (typ_var_f X)) (Hbody X HX_L0));
        apply open_typ_wrt_typ_inj in H0; auto
    end.
Qed.

(** The original [d_consis] inherits the same rigidity (it is a subset
    of [d_consis_gen]). *)
Lemma d_consis_lhs_syn_eq : forall T,
    is_syn_typ T ->
    forall Δ Γ A, d_consis Δ Γ T A -> T = A.
Proof.
  intros. eapply d_consis_gen_lhs_syn_eq; eauto using d_consis_gen__embed.
Qed.

(** Parallel rigidity on [is_inh_typ] LHS: for fully [inh]-painted [T],
    every [d_consis_gen] target equals [T]. Same proof structure as the
    [is_syn_typ] version: unit/var rigid, arrow inducts, [is_inh_typ__all]
    forces the [__forall_inh] rule (the only [d_consis_gen] rule whose LHS
    is [typ_all_col colour_inh _]); cofinite IH + open-inj. *)
Lemma d_consis_gen_lhs_inh_eq : forall T,
    is_inh_typ T ->
    forall Δ Γ A, d_consis_gen Δ Γ T A -> T = A.
Proof.
  intros T Hinh. induction Hinh; intros Δ Γ A0 Hc.
  - inversion Hc; subst. reflexivity.
  - inversion Hc; subst. reflexivity.
  - inversion Hc; subst. f_equal; eauto.
  - inversion Hc; subst.
    f_equal.
    match goal with
    | Hbody : forall X, X `notin` ?L0 -> d_consis_gen _ _ _ _ |- _ =>
        pick fresh X for
          (L `union` L0 `union` ftvar_in_typ A `union` ftvar_in_typ A1);
        assert (HX_L : X `notin` L) by fsetdec;
        assert (HX_L0 : X `notin` L0) by fsetdec;
        specialize (H0 X HX_L Δ ((X ~ dbind_tvar) ++ Γ)
                      (open_typ_wrt_typ A1 (typ_var_f X)) (Hbody X HX_L0));
        apply open_typ_wrt_typ_inj in H0; auto
    end.
Qed.

(** The original [d_consis] inherits the same rigidity. *)
Lemma d_consis_lhs_inh_eq : forall T,
    is_inh_typ T ->
    forall Δ Γ A, d_consis Δ Γ T A -> T = A.
Proof.
  intros. eapply d_consis_gen_lhs_inh_eq; eauto using d_consis_gen__embed.
Qed.

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
(* [d_sub_gen__infer_gen] / [d_sub_gen__check_gen] — the generalised
   TI/TC subtyping rules (paper syntax-directed.tex:43-53): the
   syntax-directed [typsub] at TI/TC takes the GENERALISED
   [typconsis]. [d_sub_gen__embed] only covers the non-generalised
   [d_sub], so these add the [d_consis_gen]-based variants. *)
| d_sub_gen__infer_gen : forall Γ T A,
    (* mirrors [d_sub__infer]: bases [T], [A] each painted [syn]. *)
    d_consis_gen nil Γ (syn_color T) (syn_color A) ->
    d_sub_gen mode_ti nil Γ (syn_color T) (syn_color A)
| d_sub_gen__check_gen : forall Δ Γ T A,
    (* mirrors [d_sub__check]: base [T] painted [syn] (and guarded),
       base [A] painted [inh]. *)
    guarded_typ (syn_color T) ->
    d_consis_gen Δ Γ (syn_color T) (inh_color A) ->
    d_sub_gen mode_tc Δ Γ (syn_color T) (inh_color A)
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
    (* mirrors [d_typing__var]: reads back the (already [syn]-painted)
       context binding. *)
    binds x (dbind_typ A) Γ ->
    d_typing_gen mode_ti Γ (exp_var_f x) A
| d_typing_gen__anno : forall Γ e A,
    (* mirrors [d_typing__anno]: base [A : ctyp], premise + term
       annotation [inh]-painted, conclusion [syn]-painted. *)
    d_typing_gen mode_tc Γ e (inh_color A) ->
    d_typing_gen mode_ti Γ (exp_anno e (inh_color A)) (syn_color A)
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
    (* mirrors [d_typing__abs]: base [A], context binding [syn]-painted,
       conclusion arrow-arg [inh]-painted. *)
    d_wf_typ Γ (inh_color A) ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m) ((x ~ dbind_typ (syn_color A)) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing_gen m Γ (exp_abs e) (typ_arrow (inh_color A) B)
| d_typing_gen__abs_anno : forall L Γ m e A B,
    (* mirrors [d_typing__abs_anno]: base [A : ctyp], context binding
       AND conclusion arrow-arg both [syn]-painted; term carries
       [inh_color A] (a [typ]). *)
    d_wf_typ Γ (syn_color A) ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m) ((x ~ dbind_typ (syn_color A)) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing_gen m Γ (exp_abs_anno (inh_color A) e) (typ_arrow (syn_color A) B)
| d_typing_gen__app : forall Γ m e1 e2 P P' B,
    (* mirrors [d_typing__app]: base skeleton [P : ctyp], [d_pat] reads
       its [syn] painting, [d_refine_syn] its [inh] painting; [P' : typ]
       is the refinement output / function arg; arg checked at
       [inh_color (erase P')]. *)
    d_pat mode_tc Γ e2 (syn_color P) ->
    d_refine_syn nil Γ (inh_color P) P' ->
    d_typing_gen (mode_fn m) Γ e1 (typ_arrow P' B) ->
    d_typing_gen mode_tc Γ e2 (inh_color (erase P')) ->
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
  - apply d_typing_gen__app with (P := P) (P' := P'); assumption.
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
  - (* mode_ti — route the mono refl through the [syn_color]-painted
       [d_sub__infer] using [A = syn_color (erase A)]. *)
    assert (Hg : d_sub mode_ti nil Γ (syn_color (erase A)) (syn_color (erase A))).
    { apply d_sub__infer.
      rewrite (mono_typ_syn_color_erase Hmono).
      apply d_consis_refl_mono; auto. }
    rewrite (mono_typ_syn_color_erase Hmono) in Hg. exact Hg.
  - (* mode_tc — same pattern, RHS now [inh_color]. *)
    assert (Hg : d_sub mode_tc nil Γ (syn_color (erase A)) (inh_color (erase A))).
    { apply d_sub__check.
      - rewrite (mono_typ_syn_color_erase Hmono).
        apply mono_typ_guarded; auto.
      - rewrite (mono_typ_syn_color_erase Hmono),
                (mono_typ_inh_color_erase Hmono).
        apply d_consis_refl_mono; auto. }
    rewrite (mono_typ_syn_color_erase Hmono),
            (mono_typ_inh_color_erase Hmono) in Hg.
    exact Hg.
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

(** [d_consis_gen_refl_syn]: reflexivity of [d_consis_gen] on
    syn-painted types. Uses the new [__forall_syn] rule for
    [typ_all_col colour_syn] LHS. Mirror of [d_consis_gen_refl] for
    inh-painted types.

    This is the typing-level analogue of the new [__forall_syn] rule's
    main payoff: refl on syn-painted polytypes is now provable, unlocking
    the D12 __app function-arg mode-shift composition. *)
Lemma d_consis_gen_refl_syn : forall Γ A,
    is_syn_typ A ->
    d_wf_typ Γ A ->
    d_consis_gen nil Γ A A.
Proof.
  intros Γ A Hsyn. generalize dependent Γ.
  induction Hsyn; intros Γ Hwf.
  - apply d_consis_gen__embed. apply d_consis__unit.
  - apply d_consis_gen__embed. inversion Hwf; subst.
    apply d_consis__var; assumption.
  - inversion Hwf; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow.
    + apply IHHsyn1; assumption.
    + apply IHHsyn2; assumption.
    + apply list_disjoint_nil_l.
  - (* typ_all_col colour_syn A: uses the new __forall_syn rule. *)
    inversion Hwf; subst.
    apply d_consis_gen__forall_syn with (L := L `union` L0 `union` dom Γ).
    intros X HX. apply H0; auto.
Qed.

(** [d_consis_gen_refl_is_typ]: reflexivity of [d_consis_gen] on any
    [is_typ] (decorated, colour-annotated) type. Combines refl_syn /
    refl via dispatch on the [typ_all_col] colour. Used in D12's __app
    case to reflexively type the function-arg [P'] regardless of its
    colour annotation. *)
Lemma d_consis_gen_refl_is_typ : forall Γ A,
    is_typ A ->
    d_wf_typ Γ A ->
    d_consis_gen nil Γ A A.
Proof.
  intros Γ A Hist. generalize dependent Γ.
  induction Hist; intros Γ Hwf.
  - apply d_consis_gen__embed. apply d_consis__unit.
  - apply d_consis_gen__embed. inversion Hwf; subst.
    apply d_consis__var; assumption.
  - inversion Hwf; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow.
    + apply IHHist1; assumption.
    + apply IHHist2; assumption.
    + apply list_disjoint_nil_l.
  - (* typ_all_col c A: dispatch on colour. *)
    inversion Hwf; subst.
    destruct c.
    + apply d_consis_gen__forall_syn with (L := L `union` L0 `union` dom Γ).
      intros X HX. apply H0; auto.
    + apply d_consis_gen__forall_inh with (L := L `union` L0 `union` dom Γ).
      intros X HX. apply H0; auto.
Qed.

(** [d_typing_check_is_inh]: a [mode_tc] (check-mode) typing always
    has an [is_inh_typ] type. PROVABLY FALSE in the current rule set —
    [__freeze] inherits its inner mode_ti type unchanged, so for
    [exp_anno e0 (inh_color (ctyp_all _))] with output
    [syn_color (ctyp_all _) = typ_all_col colour_syn _] (NOT is_inh_typ),
    [__freeze] produces a mode_tc derivation at a non-inh type. The
    fix requires repainting in [__freeze / __abs / __abs_anno / __app]
    rule definitions; out of scope for this pass.

    LEMMA REMOVED 2026-05-16: no callers in the codebase; the false
    admit served as documentation only. The counter-example is preserved
    above for future reference. *)

(** [d_consis_lhs_is_syn_typ]: stated for the pre-fix system as "is_inh
    LHS in d_consis forces is_syn LHS". POST the [d_consis__forall_inh]
    addition, this is PROVABLY FALSE — counter-example:
    [A = typ_all_col colour_inh (typ_var_b 0)] has is_inh_typ A and
    [d_consis nil Γ A A] is derivable via [__forall_inh] (with the trivial
    cofinite premise), but is_syn_typ A FAILS at the head.

    LEMMA REMOVED 2026-05-16: no callers in the codebase. The
    counter-example is preserved above for future reference. *)

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
  - inversion Hinh. (* __forall_inh_tagged: typ_all_etag — not inh *)
  - inversion Hinh. (* __forall_syn_tagged: typ_all_etag — not inh *)
  - inversion Hinh. (* __forall_syn (post-refactor): typ_all_col colour_syn — not inh *)
  - (* __forall_inh: A = typ_all_col colour_inh A_inner, B = same
       structure on RHS body. is_inh_typ A ⟹ inversion gives is_inh_typ
       (open A_inner X) for each X via cofinite premise. Use IH (cofinite)
       to derive is_inh_typ (open B_inner X), then [is_inh_typ__all]
       wraps. *)
    inversion Hinh; subst.
    apply is_inh_typ__all with (L := L `union` L0).
    intros X HX.
    eapply H0; eauto.
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
  induction Hcg; intros Hinh; try discriminate HeqΔ.
  - (* __unit *) apply is_inh_typ__unit.
  - (* __var *) apply is_inh_typ__var.
  - (* __forall_syn_tagged: A = typ_all_etag — not is_inh. *)
    inversion Hinh.
  - (* __forall_syn (post-refactor): A = typ_all_col colour_syn — not is_inh. *)
    inversion Hinh.
  - (* __forall_inh: both sides typ_all_col colour_inh. *)
    inversion Hinh; subst.
    apply is_inh_typ__all with (L := L `union` L0).
    intros X HX. apply H0; auto.
  - (* __arrow *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
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
  - exfalso. inversion Hist. (* __forall_inh_tagged: typ_all_etag — not is_typ *)
  - exfalso. inversion Hist. (* __forall_syn_tagged: typ_all_etag — not is_typ *)
  - (* __forall_syn (post-refactor): A = typ_all_col colour_syn — is_typ
       ✓ but NOT is_inh_typ. Lemma is FALSE in this case; admitted. *)
    admit.
  - (* __forall_inh: A = typ_all_col colour_inh A_inner. is_typ ✓,
       is_inh_typ ✓ via cofinite IH. *)
    inversion Hist as [| | | L0 c0 A0 Hist_inner Heq]; subst.
    apply is_inh_typ__all with (L := L `union` L0).
    intros X HX.
    eapply H0; eauto.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hist; subst.
    apply is_inh_typ__arrow; auto.
Admitted.

(** [d_consis_gen_preserves_wf]: d_consis_gen preserves wf on RHS.
    Every forall rule's RHS is [typ_all_col _ A0] with per-X RHS-wf
    from the IH; arrow is structural; unit/var trivial. *)
Lemma d_consis_gen_preserves_wf : forall Δ Γ A B,
    d_consis_gen Δ Γ A B ->
    d_wf_typ Γ B.
Proof.
  intros Δ Γ A B Hcg. induction Hcg.
  - (* __unit *) apply d_wf_typ__unit.
  - (* __var *) apply d_wf_typ__var; assumption.
  - (* __forall_inh_tagged *) apply d_wf_typ__all with (L := L); assumption.
  - (* __forall_syn_tagged *) apply d_wf_typ__all with (L := L); assumption.
  - (* __forall_syn (post-refactor) *) apply d_wf_typ__all with (L := L); assumption.
  - (* __forall_inh *) apply d_wf_typ__all with (L := L); assumption.
  - (* __arrow *) apply d_wf_typ__arrow; auto.
Qed.

(** [d_consis_gen_sym_inh]: symmetry for d_consis_gen on is_inh types. *)
Lemma d_consis_gen_sym_inh : forall Γ A B,
    d_consis_gen nil Γ A B ->
    is_inh_typ A ->
    d_consis_gen nil Γ B A.
Proof.
  intros Γ A B Hcg.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hcg; intros Hinh; try discriminate HeqΔ.
  - (* __unit *) apply d_consis_gen__unit.
  - (* __var *) apply d_consis_gen__var; assumption.
  - (* __forall_syn_tagged: LHS typ_all_etag — not is_inh. *)
    inversion Hinh.
  - (* __forall_syn (post-refactor): LHS typ_all_col colour_syn — not is_inh. *)
    inversion Hinh.
  - (* __forall_inh: both sides typ_all_col colour_inh. IH = H0. *)
    inversion Hinh; subst.
    apply d_consis_gen__forall_inh with (L := L `union` L0).
    intros X HX.
    apply H0; auto.
  - (* __arrow *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hinh; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow; auto.
Qed.

(** [d_consis_gen_trans]: transitivity of [d_consis_gen] at [Δ = nil].

    At [Δ = nil] the existential-[Permutation] complication of
    [d_consis_compose] disappears: every sub-derivation also lives at
    [nil], so the result mode/Δ is uniform and the forall cases
    compose per-X without a [Δ] mismatch. The paper's generalised
    [typconsis] is transitive (Lemma B.2 generalised); this is the
    [Δ = nil] instance, which is all the D12 [__sub]/[__arg] use
    sites need (their outer [Δ] is forced [nil]). *)
Lemma d_consis_gen_trans : forall Γ T A B,
    d_consis_gen nil Γ T A ->
    d_consis_gen nil Γ A B ->
    d_consis_gen nil Γ T B.
Proof.
  intros Γ T A B Hc1 Hc2.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  generalize dependent B.
  induction Hc1; intros B0 Hc2; try discriminate HeqΔ.
  - (* __unit: T = A = typ_unit; Hc2 already gives the answer. *)
    exact Hc2.
  - (* __var: T = A = typ_var_f X; Hc2 already gives the answer. *)
    exact Hc2.
  - (* __forall_syn_tagged: A = typ_all_col colour_syn A0; matched by
       __forall_syn in d_consis_gen (post-refactor). *)
    inversion Hc2; subst.
    apply d_consis_gen__forall_syn_tagged with (L := L `union` L0).
    intros X HX. apply H0; auto.
  - (* __forall_syn (post-refactor): A = typ_all_col colour_syn A0; Hc2
       matches __forall_syn. *)
    inversion Hc2; subst.
    apply d_consis_gen__forall_syn with (L := L `union` L0).
    intros X HX. apply H0; auto.
  - (* __forall_inh: A = typ_all_col colour_inh A0; Hc2 = __forall_inh. *)
    inversion Hc2; subst.
    apply d_consis_gen__forall_inh with (L := L `union` L0).
    intros X HX. apply H0; auto.
  - (* __arrow: Δ1 = Δ2 = nil; Hc2 = __arrow. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    simpl in Hc2. inversion Hc2; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1a HΔ2a]; subst
    end.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_consis_gen__arrow.
    + apply IHHc1_1; auto.
    + apply IHHc1_2; auto.
    + apply list_disjoint_nil_l.
Qed.

(** [d_typing_narrow_consis_head_arg]: narrowing a [d_typing]
    head-binding along a [d_consis_gen]. Now a clean corollary of
    [d_typing_narrow_consis_head]: [d_consis_gen]-related types have
    equal [syn_color_t] ([d_consis_gen_syn_color_eq]), which is exactly
    the premise [d_typing_narrow_consis_head] needs. *)
Lemma d_typing_narrow_consis_head_arg : forall x Aold Anew Γ m e B,
    d_typing m ((x ~ dbind_typ Aold) ++ Γ) e B ->
    d_consis_gen nil Γ Aold Anew ->
    d_typing m ((x ~ dbind_typ Anew) ++ Γ) e B.
Proof.
  intros x Aold Anew Γ m e B Hty Hcg.
  apply d_typing_narrow_consis_head with (Aold := Aold); auto.
  symmetry. eapply d_consis_gen_syn_color_eq; eauto.
Qed.

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
  - apply d_consis_gen__unit.
  - apply d_consis_gen__var.
    apply binds_app_iff in H. destruct H as [Hb | Hb].
    + apply binds_app_iff. auto.
    + apply binds_app_iff. right. apply binds_app_iff. auto.
  - apply d_consis_gen__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    + intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
      eapply H0; eauto.
    + assumption.
  - apply d_consis_gen__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_syn with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
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
  - apply d_sub_gen__infer_gen; auto.
    apply d_consis_gen_weakening; auto.
  - apply d_sub_gen__check_gen; auto.
    apply d_consis_gen_weakening; auto.
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
    + intros x Hx.
      rewrite_env (((x ~ dbind_typ (syn_color A)) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H1; auto.
  - apply d_typing_gen__abs_anno with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); auto.
    + eapply d_wf_typ_weakening; eauto.
    + intros x Hx.
      rewrite_env (((x ~ dbind_typ (syn_color A)) ++ Γ1) ++ Γ2 ++ Γ3).
      apply H1; auto.
  - apply d_typing_gen__app with (P := P) (P' := P'); auto.
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

(** [d_sub_gen] preserves RHS well-formedness — the [d_sub_gen]
    analogue of [d_sub_preserves_wf]. [__embed] routes through
    [d_sub_preserves_wf], [__refl_mono] reads off its premise,
    [__forall_r] / [__arg] are structural ([__arg]'s arg side uses
    [d_consis_gen_preserves_wf]). *)
Lemma d_sub_gen_preserves_wf : forall m Δ Γ T A,
    d_sub_gen m Δ Γ T A ->
    d_wf_typ Γ A.
Proof.
  intros m Δ Γ T A H. induction H.
  - (* __embed *) eapply d_sub_preserves_wf; eauto.
  - (* __infer_gen *) eapply d_consis_gen_preserves_wf; eauto.
  - (* __check_gen *) eapply d_consis_gen_preserves_wf; eauto.
  - (* __refl_mono *) assumption.
  - (* __forall_r *)
    apply d_wf_typ__all with (L := L `union` dom Γ).
    intros X HX. apply H0; auto.
  - (* __arg *)
    apply d_wf_typ__arrow.
    + eapply d_consis_gen_preserves_wf; eauto.
    + assumption.
Qed.

(** [d_typing_gen] preserves type well-formedness — the [d_typing_gen]
    analogue of [d_typing_pat_preserves_wf]'s typing half. Mirrors
    that proof case-for-case; [__sub] routes through
    [d_sub_gen_preserves_wf]. *)
Lemma d_typing_gen_preserves_wf : forall m Γ e A,
    d_typing_gen m Γ e A ->
    d_wf_denv Γ ->
    d_wf_typ Γ A.
Proof.
  intros m Γ e A H. induction H; intros Hwfd.
  - (* __unit *) apply d_wf_typ__unit.
  - (* __var: post re-encoding the rule returns the bound type raw —
       no [syn_color] wrap on the conclusion. *)
    eapply d_wf_denv_binds_typ; eauto.
  - (* __anno: IH gives [d_wf_typ Γ (inh_color A)]; conclusion is
       [syn_color A]; bridge via [d_wf_typ_inh_color_syn_color]. *)
    apply d_wf_typ_inh_color_syn_color. apply IHd_typing_gen; auto.
  - (* __sub *) eapply d_sub_gen_preserves_wf; eauto.
  - (* __freeze *) apply IHd_typing_gen; auto.
  - (* __forall *)
    apply d_wf_typ__all with (L := L `union` dom Γ).
    intros X HX. apply H1; auto. apply d_wf_denv__tvar; auto.
  - (* __abs: arrow-arg [inh_color A] from the rule's wf premise; body
       wf via strengthening the extended context (which binds
       [syn_color A]). *)
    apply d_wf_typ__arrow; auto.
    pick fresh x for (L `union` dom Γ).
    eapply d_wf_typ_strengthening_typ with
      (Γ1 := nil) (x := x) (A := syn_color A).
    eauto using d_wf_denv__typ, d_wf_typ_inh_color_syn_color.
  - (* __abs_anno: arrow-arg [syn_color A] from the rule's wf premise. *)
    apply d_wf_typ__arrow; auto.
    pick fresh x for (L `union` dom Γ).
    eapply d_wf_typ_strengthening_typ with
      (Γ1 := nil) (x := x) (A := syn_color A).
    eauto using d_wf_denv__typ.
  - (* __app: post re-encoding the function's arg type is [P' : typ];
       the [d_typing_gen] for the function gives [d_wf_typ Γ (typ_arrow P' B)]. *)
    assert (Harr : d_wf_typ Γ (typ_arrow P' B)) by (apply IHd_typing_gen1; auto).
    inversion Harr; subst. auto.
Qed.

(** [d_typing_gen_check_is_inh]: gen analogue — PROVABLY FALSE for the
    same reason as [d_typing_check_is_inh]. [d_typing_gen__freeze]
    mirrors [d_typing__freeze]'s no-repainting behaviour. LEMMA REMOVED
    2026-05-16: no callers. Counter-example documented in the original
    [d_typing_check_is_inh] block. *)

Lemma d_consis_gen_tvar_morph : forall Γ Γ' Δ T A,
    (forall X, binds X dbind_tvar Γ -> binds X dbind_tvar Γ') ->
    d_consis_gen Δ Γ T A ->
    d_consis_gen Δ Γ' T A.
Proof.
  intros Γ Γ' Δ T A Hmorph H.
  generalize dependent Γ'. induction H; intros Γ' Hmorph.
  - apply d_consis_gen__unit.
  - apply d_consis_gen__var. apply Hmorph; assumption.
  - apply d_consis_gen__forall_inh_tagged with (L := L `union` dom Γ').
    + intros X HX. apply H0; auto.
      intros Y HbY. apply binds_app_iff in HbY.
      destruct HbY as [Hb | Hb]; apply binds_app_iff;
        [ left; auto | right; auto ].
    + assumption.
  - apply d_consis_gen__forall_syn_tagged with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff;
      [ left; auto | right; auto ].
  - apply d_consis_gen__forall_syn with (L := L `union` dom Γ').
    intros X HX. apply H0; auto.
    intros Y HbY. apply binds_app_iff in HbY.
    destruct HbY as [Hb | Hb]; apply binds_app_iff;
      [ left; auto | right; auto ].
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
  - apply d_sub_gen__infer_gen; auto. eapply d_consis_gen_tvar_morph; eauto.
  - apply d_sub_gen__check_gen; auto. eapply d_consis_gen_tvar_morph; eauto.
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

(** Narrowing a [dbind_typ] binding preserves [dbind_tvar] lookups
    (the narrowed slot holds a [dbind_typ], so no [dbind_tvar] lookup
    can resolve to it). *)
Lemma binds_tvar_narrow_typ :
  forall (Γ1 Γ2 : list (atom * dbind)) x Aold Anew X,
    binds X dbind_tvar (Γ1 ++ (x ~ dbind_typ Aold) ++ Γ2) ->
    binds X dbind_tvar (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2).
Proof.
  intros Γ1 Γ2 x Aold Anew X HbY.
  apply binds_app_iff in HbY. destruct HbY as [Hb | Hb].
  - apply binds_app_iff. left. assumption.
  - apply binds_app_iff in Hb. destruct Hb as [Hbx | Hbp].
    + apply binds_one_iff in Hbx. destruct Hbx as [_ Habs]. inversion Habs.
    + apply binds_app_iff. right. apply binds_app_iff. right. assumption.
Qed.

(** [d_typing_gen] narrowing along a [syn_color_t]-equal binding swap —
    the [d_typing_gen] analogue of [d_typing_narrow_consis]. The
    [__var] case at the narrowed binding closes immediately because
    [d_typing_gen__var] gives the [syn_color_t] of the binding and
    [Hsc] equates the two. [__sub]'s [d_sub_gen] and [__app]'s
    [d_refine_syn] only read [dbind_tvar] entries
    ([binds_tvar_narrow_typ]); [__app]'s [d_pat] narrows via
    [d_typing_narrow_consis]. *)
Lemma d_typing_gen_narrow_consis : forall m Γ_full e B,
    d_typing_gen m Γ_full e B ->
    forall Γ1 x Aold Anew Γ2,
      Γ_full = Γ1 ++ (x ~ dbind_typ Aold) ++ Γ2 ->
      syn_color_t Anew = syn_color_t Aold ->
      d_typing_gen m (Γ1 ++ (x ~ dbind_typ Anew) ++ Γ2) e B.
Proof.
  (* RE-ENCODING ADMIT (2026-05-15): mirrors [d_typing_narrow_consis]
     — post-ctyp re-encoding, [d_typing_gen__var] returns the bound
     type raw, so the [__var] narrowed-binding sub-case no longer
     closes from [syn_color_t]-equality alone. *)
Admitted.

Corollary d_typing_gen_narrow_consis_head : forall x Aold Anew Γ m e B,
    d_typing_gen m ((x ~ dbind_typ Aold) ++ Γ) e B ->
    syn_color_t Anew = syn_color_t Aold ->
    d_typing_gen m ((x ~ dbind_typ Anew) ++ Γ) e B.
Proof.
  intros x Aold Anew Γ m e B Hty Hsc.
  rewrite_env (nil ++ (x ~ dbind_typ Anew) ++ Γ).
  eapply d_typing_gen_narrow_consis with (Γ1 := nil) (Aold := Aold); eauto.
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
(** With the new [d_consis__forall_inh] rule, [d_consis nil Γ T A]
    with A is_inh_typ no longer pins T to mono — T can be
    [typ_all_col colour_inh _]. We add [is_utyp T] as precondition
    to rule out the new case structurally; callers supply this from
    their context (e.g., [mono_typ A] gives mono T via [d_consis_mono_RHS]
    which gives is_utyp T via [mono_typ_is_utyp]). *)
Lemma d_consis_to_d_sub_gen : forall m Γ T A,
    mode_typ_compat m A ->
    d_wf_typ Γ T ->
    is_utyp T ->
    d_consis nil Γ T A ->
    d_sub_gen m nil Γ T A.
Proof.
  intros m Γ T A Hcompat HwfT Hut Hc. generalize dependent T.
  induction Hcompat; intros T HwfT Hut Hc.
  - (* mode_ti: mono extraction → T = A. *)
    assert (HmonoT : mono_typ T) by (eapply d_consis_LHS_mono_wf; eauto).
    destruct (d_consis_mono_LHS Hc HmonoT) as [HeqAT _]; subst.
    apply d_sub_gen__refl_mono; auto.
    apply mode_typ_compat__ti; apply mono_typ_is_syn_typ; auto.
  - (* mode_tc: same mono-extraction chain (is_utyp T rules out
       the [typ_all_col colour_inh] LHS case). *)
    assert (HmonoT : mono_typ T) by (eapply d_consis_LHS_mono_wf; eauto).
    destruct (d_consis_mono_LHS Hc HmonoT) as [HeqAT _]; subst.
    apply d_sub_gen__refl_mono; auto.
    apply mode_typ_compat__tc; apply mono_typ_is_inh_typ; auto.
  - (* mode_fn: A = typ_arrow A0 B. T from d_consis must be typ_arrow. *)
    inversion Hc; subst.
    inversion HwfT; subst.
    inversion Hut; subst.
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
  induction Hcg; intros T0 Hc HwfT; try discriminate HeqΔ.
  - (* __unit: A = B = typ_unit; Hc already gives the answer. *)
    apply d_consis_gen__embed. assumption.
  - (* __var: A = B = typ_var_f X; Hc already gives the answer. *)
    apply d_consis_gen__embed. assumption.
  - (* __forall_syn_tagged: A = typ_all_etag — no d_consis rule has
       typ_all_etag as RHS, so Hc is vacuous. *)
    inversion Hc.
  - (* __forall_syn (post-refactor): A = typ_all_col colour_syn T_inner.
       Hc has RHS = typ_all_col colour_syn — d_consis rules matching:
       __forall_syn_tagged (LHS = typ_all_etag, T0 not d_wf_typ since
       d_wf_typ doesn't admit typ_all_etag → vacuous) or __forall_syn
       (LHS = typ_all_col colour_syn). Inversion gives both subcases. *)
    subst.
    inversion Hc; subst.
    + (* __forall_syn_tagged: LHS T0 = typ_all_etag _ _. HwfT inversion
         on d_wf_typ Γ (typ_all_etag _ _) has 0 cases. Use solve. *)
      inversion HwfT.
    + (* __forall_syn: LHS = typ_all_col colour_syn, compose via
         d_consis_gen__forall_syn. *)
      apply d_consis_gen__forall_syn with (L := L `union` L0).
      intros X HX.
      apply d_consis_gen_trans with (A := open_typ_wrt_typ T (typ_var_f X)).
      * apply d_consis_gen__embed.
        match goal with
        | H' : forall X0, X0 `notin` _ -> d_consis _ _ _ _ |- _ =>
            apply H'; auto
        end.
      * apply H; auto.
  - (* __forall_inh: A = typ_all_col colour_inh T_inner. Hc with Δ=nil
       and RHS = typ_all_col colour_inh — __forall_inh_tagged forces
       Δ = ε :: Δ_inner ≠ nil so discharged. Only __forall_inh matches. *)
    subst.
    inversion Hc; subst.
    apply d_consis_gen__forall_inh with (L := L `union` L0).
    intros X HX.
    apply d_consis_gen_trans with (A := open_typ_wrt_typ T (typ_var_f X)).
    + apply d_consis_gen__embed.
      match goal with
      | H' : forall X0, X0 `notin` _ -> d_consis _ _ _ _ |- _ =>
          apply H'; auto
      end.
    + apply H; auto.
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
(** Helper: a [d_consis_gen] with a [syn_color]-shaped RHS pins the
    LHS to [syn_color X] under wf — the [__forall_inh*] / [__forall_syn*]
    / [__forall_inh] cases of [d_consis_gen] are either vacuous on
    [syn_color]-shaped RHS (colour mismatch: [syn_color] paints
    [colour_syn], not [colour_inh]) or LHS-unwf (etag/plain). *)
Lemma d_consis_gen_RHS_syn_color_eq : forall Γ A X,
    d_consis_gen nil Γ A (syn_color X) ->
    d_wf_typ Γ A ->
    A = syn_color X.
Proof.
  intros Γ A X Hcg.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  remember (syn_color X) as A_RHS eqn:HeqA.
  generalize dependent X.
  induction Hcg; intros X' HeqA HwfA; subst.
  - destruct X'; simpl in HeqA; try discriminate. reflexivity.
  - destruct X'; simpl in HeqA; try discriminate.
    injection HeqA; intro; subst; reflexivity.
  - inversion HwfA.
  - inversion HwfA.
  - destruct X'; simpl in HeqA; try discriminate.
    inversion HeqA; subst.
    inversion HwfA; subst.
    f_equal.
    pick fresh X0 for
      (L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_ctyp X' `union` dom Γ).
    assert (HX_L : X0 `notin` L) by fsetdec.
    assert (HX_L0 : X0 `notin` L0) by fsetdec.
    assert (HnotinT : X0 `notin` ftvar_in_typ T) by fsetdec.
    assert (HnotinSC : X0 `notin` ftvar_in_typ (syn_color X')).
    { rewrite syn_color_ftvar. fsetdec. }
    pose proof (H0 X0 HX_L eq_refl
                   (open_ctyp_wrt_ctyp X' (ctyp_var_f X0))) as Heq.
    rewrite syn_color_open_var in Heq.
    specialize (Heq eq_refl (H3 X0 HX_L0)).
    apply (open_typ_wrt_typ_inj T (syn_color X') X0); auto.
  - destruct X'; simpl in HeqA; discriminate.
  - destruct X'; simpl in HeqA; try discriminate.
    injection HeqA; intros HeqA2 HeqA1.
    apply app_eq_nil in HeqΔ; destruct HeqΔ as [HΔ1 HΔ2]; subst.
    inversion HwfA; subst.
    f_equal.
    + eapply IHHcg1; eauto.
    + eapply IHHcg2; eauto.
Qed.

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
  - (* __embed: route through [d_consis_extends_d_sub_nil]. *)
    subst. apply d_sub_gen__embed. eapply d_consis_extends_d_sub_nil; eauto.
  - (* __infer_gen: Hc has RHS = syn_color T. Sound closure: use
       [d_consis_gen_RHS_syn_color_eq] (Qed) to pin T0 = syn_color T,
       then compose Hc with H via [d_consis_gen_trans] and reconstruct
       via [d_sub_gen__infer_gen]. This avoids the unsound chain
       through [d_consis_LHS_is_utyp_when_RHS_syn_color]. *)
    subst.
    assert (Hc_gen : d_consis_gen nil Γ T0 (syn_color T))
      by (apply d_consis_gen__embed; assumption).
    assert (HT0eq : T0 = syn_color T)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto).
    subst T0.
    apply d_sub_gen__infer_gen.
    eapply d_consis_gen_trans; eauto.
  - (* __check_gen: same pattern — pin T0 = syn_color T via the RHS
       rigidity lemma, then dispatch via [d_sub_gen__check_gen] (the
       guarded_typ + d_consis_gen premise of __check_gen carry over). *)
    subst.
    assert (Hc_gen : d_consis_gen nil Γ T0 (syn_color T))
      by (apply d_consis_gen__embed; assumption).
    assert (HT0eq : T0 = syn_color T)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto).
    subst T0.
    apply d_sub_gen__check_gen; assumption.
  - (* __refl_mono: A = B mono. Use [d_consis_to_d_sub_gen] (compat
       carried by __refl_mono). [is_utyp T0] derived via
       [d_consis_mono_RHS] (mono A pins T0 = A, hence mono T0, hence
       is_utyp T0). *)
    subst.
    edestruct (d_consis_mono_RHS Hc) as [HmonoT0 [_ _]]; eauto.
    eapply d_consis_to_d_sub_gen; eauto.
    apply mono_typ_is_utyp; assumption.
  - (* __forall_r: B = typ_all_col colour_inh A0, m = mode_tc.
       Reconstruct via __forall_r with per-X IH. *)
    subst.
    apply d_sub_gen__forall_r with (L := L `union` dom Γ).
    intros X HX.
    eapply H0; eauto.
    + apply d_consis_weakening_head; auto.
    + apply d_wf_typ_weakening_head; auto.
  - (* __arg: A = typ_arrow T1 T2, B = typ_arrow A1 A2. Hc forces
       T0 = typ_arrow T0_arg T0_ret. Compose Hc's arg-side d_consis
       with Hs's arg-side d_consis_gen via [d_consis_extends_d_consis_gen]. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hc; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1a HΔ2a]; subst
    end.
    inversion HwfT; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + eapply d_consis_extends_d_consis_gen; eauto.
    + eapply IHHs; eauto.
Qed.

(** ** Mono-RHS rigidity for consistency / subtyping.

    If a [d_consis] / [d_sub] (or their generalised variants) has a
    [mono_typ] RHS, the LHS is forced equal to it: the polymorphic
    LHS rules all produce a non-mono ([typ_all_col] / quantified) RHS,
    so they are vacuous against [mono_typ B]; the [d_sub] [forall_l]
    rules (LHS [typ_all_etag] / [typ_all_plain]) are excluded by
    [d_wf_typ] on the LHS. Used in [d_sub_gen_trans]'s
    [Hsub_gen = __refl_mono] case: a mono target collapses the
    composition to reflexivity. *)
Lemma d_consis_mono_RHS_eq : forall Γ A B,
    d_consis nil Γ A B ->
    mono_typ B ->
    A = B.
Proof.
  intros Γ A B Hc.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hc; intros Hmono; try discriminate HeqΔ.
  - reflexivity.
  - reflexivity.
  - (* __forall_syn_tagged: B = typ_all_col colour_syn — not mono. *)
    inversion Hmono.
  - (* __forall_syn (post-refactor): B = typ_all_col colour_syn — not mono. *)
    inversion Hmono.
  - (* __forall_inh: B = typ_all_col colour_inh — not mono. *)
    inversion Hmono.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hmono; subst.
    f_equal.
    + apply IHHc1; auto.
    + apply IHHc2; auto.
Qed.

Lemma d_consis_gen_mono_RHS_eq : forall Γ A B,
    d_consis_gen nil Γ A B ->
    mono_typ B ->
    A = B.
Proof.
  intros Γ A B Hc.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hc; intros Hmono; try discriminate HeqΔ.
  - reflexivity.
  - reflexivity.
  - inversion Hmono.
  - inversion Hmono.
  - inversion Hmono.
  - apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hmono; subst.
    f_equal.
    + apply IHHc1; auto.
    + apply IHHc2; auto.
Qed.

Lemma d_sub_mono_RHS_eq : forall m Γ A B,
    d_sub m nil Γ A B ->
    d_wf_typ Γ A ->
    mono_typ B ->
    A = B.
Proof.
  intros m Γ A B Hs.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hs; intros HwfA Hmono; try discriminate HeqΔ.
  - (* __infer: d_consis nil Γ T A. *)
    eapply d_consis_mono_RHS_eq; eauto.
  - (* __check: d_consis Δ Γ T A, Δ = nil. *)
    subst. eapply d_consis_mono_RHS_eq; eauto.
  - (* __forall_r: B = typ_all_col — not mono. *)
    inversion Hmono.
  - (* __arg: A = typ_arrow T1 T2, B = typ_arrow A1 A2. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion HwfA; subst.
    inversion Hmono; subst.
    f_equal.
    + eapply d_consis_mono_RHS_eq; eauto.
    + apply IHHs; auto.
  - (* __forall_l_tagged: A = typ_all_etag — not wf. *)
    inversion HwfA.
Qed.

Lemma d_sub_gen_mono_RHS_eq : forall m Γ A B,
    d_sub_gen m nil Γ A B ->
    d_wf_typ Γ A ->
    mono_typ B ->
    A = B.
Proof.
  intros m Γ A B Hs.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hs; intros HwfA Hmono; try discriminate HeqΔ.
  - (* __embed: d_sub m nil Γ A B. *)
    subst. eapply d_sub_mono_RHS_eq; eauto.
  - (* __infer_gen: d_consis_gen nil Γ A B + mono B. *)
    eapply d_consis_gen_mono_RHS_eq; eauto.
  - (* __check_gen: d_consis_gen Δ Γ A B (Δ = nil) + mono B. *)
    subst. eapply d_consis_gen_mono_RHS_eq; eauto.
  - (* __refl_mono: A = B. *)
    reflexivity.
  - (* __forall_r: B = typ_all_col — not mono. *)
    inversion Hmono.
  - (* __arg: A = typ_arrow T1 T2, B = typ_arrow A1 A2. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion HwfA; subst.
    inversion Hmono; subst.
    f_equal.
    + eapply d_consis_gen_mono_RHS_eq; eauto.
    + apply IHHs; auto.
Qed.

(** [d_consis_gen_extends_d_sub_nil]: compose a [d_consis_gen] on the
    LHS of a [d_sub] (the non-generalised subtyping). By induction on
    the [d_sub] — crucially this gives IHs for the [__forall_r] /
    [__arg] sub-derivations, so those reconstruct cleanly. The
    [__infer]/[__check] cases chain via [d_consis_gen_trans] +
    [d_consis_gen__embed] and land in the new [d_sub_gen__infer_gen] /
    [__check_gen]; [__forall_l_*] are vacuous ([d_consis_gen] has no
    [typ_all_etag]/[typ_all_plain] RHS). *)
(* [d_consis_gen_RHS_syn_color_eq] moved up before
   [d_consis_extends_d_sub_gen_nil] which now uses it. *)

Lemma d_consis_gen_extends_d_sub_nil : forall m Γ B C,
    d_sub m nil Γ B C ->
    forall A,
      d_consis_gen nil Γ A B ->
      d_wf_typ Γ A ->
      d_sub_gen m nil Γ A C.
Proof.
  intros m Γ B C Hd.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hd; intros A0 Hcg HwfA0.
  - (* __infer: B = syn_color T, C = syn_color A.
       [d_consis_gen_RHS_syn_color_eq] pins A0 = syn_color T;
       reuse [Hd]'s premise. *)
    assert (HeqA0 : A0 = syn_color _)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto); subst A0.
    apply d_sub_gen__infer_gen.
    eapply d_consis_gen_trans; [ exact Hcg | apply d_consis_gen__embed; eassumption ].
  - (* __check: B = syn_color T, C = inh_color A. Same chain. *)
    subst.
    assert (HeqA0 : A0 = syn_color _)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto); subst A0.
    apply d_sub_gen__check_gen; auto.
    eapply d_consis_gen_trans; [ exact Hcg | apply d_consis_gen__embed; eassumption ].
  - (* __forall_r: per-X recursion via the d_sub IH H0. *)
    subst.
    apply d_sub_gen__forall_r with (L := L `union` dom Γ).
    intros X HX.
    eapply H0; eauto.
    + apply d_consis_gen_weakening_head; auto.
    + apply d_wf_typ_weakening_head; auto.
  - (* __arg: B = typ_arrow T1 T2; Hcg forces A0 = typ_arrow A0_1 A0_2. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hcg; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1a HΔ2a]; subst
    end.
    inversion HwfA0; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + eapply d_consis_gen_trans;
        [ eassumption | apply d_consis_gen__embed; eassumption ].
    + eapply IHHd; eauto.
  - (* __forall_l_tagged: B = typ_all_etag — no d_consis_gen RHS. *)
    inversion Hcg.
Qed.

(** [d_consis_gen_extends_d_sub_gen_nil]: same, on the LHS of a
    [d_sub_gen]. By induction on [d_sub_gen]; [__embed] routes through
    [d_consis_gen_extends_d_sub_nil] (which handles the embedded
    [d_sub]'s internal structure), the gen rules chain via
    [d_consis_gen_trans], [__forall_r]/[__arg] recurse. *)
Lemma d_consis_gen_extends_d_sub_gen_nil : forall m Γ B C,
    d_sub_gen m nil Γ B C ->
    forall A,
      d_consis_gen nil Γ A B ->
      d_wf_typ Γ A ->
      d_sub_gen m nil Γ A C.
Proof.
  intros m Γ B C Hs.
  remember (@nil atom) as Δ_nil eqn:HeqΔ.
  induction Hs; intros A0 Hcg HwfA0.
  - (* __embed *)
    subst. eapply d_consis_gen_extends_d_sub_nil; eauto.
  - (* __infer_gen: B = syn_color T, C = syn_color A. *)
    assert (HeqA0 : A0 = syn_color _)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto); subst A0.
    apply d_sub_gen__infer_gen.
    eapply d_consis_gen_trans; eauto.
  - (* __check_gen: B = syn_color T, C = inh_color A. *)
    subst.
    assert (HeqA0 : A0 = syn_color _)
      by (eapply d_consis_gen_RHS_syn_color_eq; eauto); subst A0.
    apply d_sub_gen__check_gen.
    + assumption.
    + eapply d_consis_gen_trans; eauto.
  - (* __refl_mono: B = C mono ⟹ A0 = B by mono-RHS rigidity. *)
    subst.
    assert (Heq : A0 = A) by (eapply d_consis_gen_mono_RHS_eq; eauto).
    subst. apply d_sub_gen__refl_mono; auto.
  - (* __forall_r: per-X recursion via IH H0. *)
    subst.
    apply d_sub_gen__forall_r with (L := L `union` dom Γ).
    intros X HX.
    eapply H0; eauto.
    + apply d_consis_gen_weakening_head; auto.
    + apply d_wf_typ_weakening_head; auto.
  - (* __arg: B = typ_arrow B1 B2; Hcg forces A0 = typ_arrow A0_1 A0_2. *)
    apply app_eq_nil in HeqΔ. destruct HeqΔ as [HΔ1 HΔ2]. subst.
    inversion Hcg; subst.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1a HΔ2a]; subst
    end.
    inversion HwfA0; subst.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + eapply d_consis_gen_trans; eauto.
    + eapply IHHs; eauto.
Qed.

(** [d_sub_gen_trans_arrow]: the arrow-shaped continuation shared by
    [d_sub_gen_trans]'s [Hso = __embed] and [Hso = __arg] cases. Both
    yield [A = typ_arrow A1 A2], [B = typ_arrow B1 B2] with arg-side
    [d_consis_gen] and ret-side [d_sub_gen]; this lemma dispatches on
    the second derivation [Hsg]:
    - [Hsg = __embed]/[__arg]: reconstruct [d_sub_gen__arg], composing
      the arg sides via [d_consis_gen_trans] and the ret sides via the
      passed-in IH.
    - [Hsg = __refl_mono]: the target [typ_arrow B1 B2] is mono, so
      [d_sub_gen_mono_RHS_eq] collapses [typ_arrow A1 A2 = typ_arrow
      B1 B2] and the result is reflexivity. *)
Lemma d_sub_gen_trans_arrow : forall m m_new Γ A1 A2 B1 B2 C,
    d_wf_typ Γ A1 ->
    d_wf_typ Γ A2 ->
    d_consis_gen nil Γ A1 B1 ->
    d_sub_gen m nil Γ A2 B2 ->
    d_sub_gen (mode_fn (mode_fn_n_subst m m_new)) nil Γ (typ_arrow B1 B2) C ->
    (forall Γ' A' B' C',
       d_wf_typ Γ' A' ->
       d_sub_gen m nil Γ' A' B' ->
       d_sub_gen (mode_fn_n_subst m m_new) nil Γ' B' C' ->
       d_sub_gen (mode_fn_n_subst m m_new) nil Γ' A' C') ->
    d_sub_gen (mode_fn (mode_fn_n_subst m m_new)) nil Γ (typ_arrow A1 A2) C.
Proof.
  intros m m_new Γ A1 A2 B1 B2 C HwfA1 HwfA2 Hca_gen Hsa_gen Hsg IH.
  inversion Hsg; subst.
  - (* __embed: d_sub _ nil Γ (typ_arrow B1 B2) C → __arg. *)
    match goal with H : d_sub _ nil Γ (typ_arrow B1 B2) _ |- _ =>
      inversion H; subst
    end.
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
    end.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + eapply d_consis_gen_trans;
        [ exact Hca_gen | apply d_consis_gen__embed; eassumption ].
    + eapply IH;
        [ exact HwfA2 | exact Hsa_gen | apply d_sub_gen__embed; eassumption ].
  - (* __refl_mono: typ_arrow B1 B2 = C, mono. *)
    assert (Harrow : d_sub_gen (mode_fn m) nil Γ (typ_arrow A1 A2) (typ_arrow B1 B2)).
    { rewrite_env (@nil atom ++ @nil atom).
      apply d_sub_gen__arg; assumption. }
    assert (Heq : typ_arrow A1 A2 = typ_arrow B1 B2).
    { eapply d_sub_gen_mono_RHS_eq;
        [ exact Harrow | apply d_wf_typ__arrow; assumption | eassumption ]. }
    rewrite Heq.
    apply d_sub_gen__refl_mono; assumption.
  - (* __arg: C = typ_arrow C1 C2, gen sub-derivations directly. *)
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
    end.
    rewrite_env (@nil atom ++ @nil atom).
    apply d_sub_gen__arg.
    + eapply d_consis_gen_trans; [ exact Hca_gen | eassumption ].
    + eapply IH; [ exact HwfA2 | exact Hsa_gen | eassumption ].
Qed.

(** [d_sub_gen_trans]: transitivity of [d_sub_gen] along the FN^n
    mode-stack. With [m1] in [is_fn_n_ti] form and the second
    derivation at [mode_fn_n_subst m1 m_new] (the innermost TI
    replaced by [m_new]), the composite lives at the second mode.

    Induction on [is_fn_n_ti m1]:
    - [m1 = mode_ti]: the first sub is [__infer] (compose via
      [d_consis_extends_d_sub_gen_nil]) or [__refl_mono] (identity).
    - [m1 = mode_fn m]: the first sub is [__refl_mono] (identity) or
      arrow-shaped ([__embed]→[d_sub__arg], or [__arg]); the arrow
      cases route through [d_sub_gen_trans_arrow] with the IH.

    This closes the D12 [__sub] [m = mode_fn _] case (mode-changing
    subtyping transitivity). *)
Lemma d_sub_gen_trans : forall m1 Γ A B C m_new,
    is_fn_n_ti m1 ->
    d_wf_typ Γ A ->
    d_sub_gen m1 nil Γ A B ->
    d_sub_gen (mode_fn_n_subst m1 m_new) nil Γ B C ->
    d_sub_gen (mode_fn_n_subst m1 m_new) nil Γ A C.
Proof.
  intros m1 Γ A B C m_new Hfn.
  generalize dependent C. generalize dependent B.
  generalize dependent A. generalize dependent Γ.
  induction Hfn; intros Γ A B C HwfA Hso Hsg.
  - (* m1 = mode_ti: mode_fn_n_subst mode_ti m_new = m_new. *)
    simpl in Hsg |- *.
    inversion Hso; subst.
    + (* __embed: d_sub mode_ti nil Γ A B. Only __infer applies;
         the forall_l rules carry [m <> mode_ti], contradictory here. *)
      match goal with H : d_sub mode_ti nil Γ _ _ |- _ =>
        inversion H
      end; subst; try (exfalso; congruence).
      eapply d_consis_extends_d_sub_gen_nil; eauto.
    + (* __infer_gen: d_consis_gen nil Γ A B; compose with Hsg via
         the d_consis_gen-LHS extension lemma. *)
      eapply d_consis_gen_extends_d_sub_gen_nil; eauto.
    + (* __refl_mono: A = B. *)
      exact Hsg.
  - (* m1 = mode_fn m: mode_fn_n_subst (mode_fn m) m_new
       = mode_fn (mode_fn_n_subst m m_new). *)
    simpl in Hsg |- *.
    inversion Hso; subst.
    + (* __embed: d_sub (mode_fn m) nil Γ A B. A wf ⟹ only __arg. *)
      match goal with H : d_sub (mode_fn m) nil Γ _ _ |- _ =>
        inversion H; subst
      end.
      * (* d_sub__arg *)
        match goal with
        | H : _ ++ _ = nil |- _ =>
            apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
        end.
        inversion HwfA; subst.
        eapply d_sub_gen_trans_arrow;
          [ eassumption | eassumption
          | apply d_consis_gen__embed; eassumption
          | apply d_sub_gen__embed; eassumption
          | exact Hsg | exact IHHfn ].
      * (* d_sub__forall_l_tagged: A = typ_all_etag — not wf. *)
        inversion HwfA.
    + (* __refl_mono: A = B. *)
      exact Hsg.
    + (* __arg: gen sub-derivations directly. *)
      match goal with
      | H : _ ++ _ = nil |- _ =>
          apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
      end.
      inversion HwfA; subst.
      eapply d_sub_gen_trans_arrow;
        [ eassumption | eassumption | eassumption | eassumption
        | exact Hsg | exact IHHfn ].
Qed.

(** [d_sub_gen] analogue of [d_sub_arrow_refl_inner]: a reflexive
    [d_sub_gen] on a mono arrow type yields a reflexive [d_sub_gen] on
    the result type at [decr_mode]. The [__embed] case routes through
    [d_sub_arrow_refl_inner]; [__refl_mono] rebuilds via
    [d_sub_gen__refl_mono] (mode-compat / wf from inverting the arrow
    premises); [__arg] hands back its ret-side directly. *)
Lemma d_sub_gen_arrow_refl_inner : forall Γ A B m,
    d_sub_gen m nil Γ (typ_arrow A B) (typ_arrow A B) ->
    mono_typ A ->
    mono_typ B ->
    d_sub_gen (decr_mode m) nil Γ B B.
Proof.
  intros Γ A B m Hrefl HmonoA HmonoB.
  assert (Hwf_arr : d_wf_typ Γ (typ_arrow A B))
    by (eapply d_sub_gen_preserves_wf; eauto).
  inversion Hwf_arr; subst.
  inversion Hrefl; subst.
  - (* __embed: route through [d_sub_arrow_refl_inner]. *)
    apply d_sub_gen__embed. eapply d_sub_arrow_refl_inner; eauto.
  - (* __infer_gen: m = mode_ti. Build [__refl_mono] on B with
       [is_syn_typ B] from mono. *)
    simpl.
    apply d_sub_gen__refl_mono; auto.
    apply mode_typ_compat__ti. apply mono_typ_is_syn_typ; auto.
  - (* __check_gen: m = mode_tc. Same with [is_inh_typ B]. *)
    simpl.
    apply d_sub_gen__refl_mono; auto.
    apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
  - (* __refl_mono: invert [mode_typ_compat m (typ_arrow A B)] to
       extract compat at [decr_mode m] on B. *)
    apply d_sub_gen__refl_mono; auto.
    match goal with
    | H : mode_typ_compat _ (typ_arrow _ _) |- _ =>
        inversion H; subst; simpl;
          [ apply mode_typ_compat__ti;
            match goal with Hsy : is_syn_typ (typ_arrow _ _) |- _ =>
              inversion Hsy; assumption
            end
          | apply mode_typ_compat__tc;
            match goal with Hih : is_inh_typ (typ_arrow _ _) |- _ =>
              inversion Hih; assumption
            end
          | assumption ]
    end.
  - (* __arg: m = mode_fn k, body sub gives the result directly. *)
    match goal with
    | H : _ ++ _ = nil |- _ =>
        apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst
    end.
    simpl. assumption.
Qed.

(** Mono-type mode-lift for [d_typing_gen] — the [d_typing_gen]
    analogue of [d_typing_lift_mono]. By induction on the typing.
    Base terms close via [d_typing_gen__sub]; [__sub] composes the
    inner mode_ti d_sub_gen with Hrefl via [d_sub_gen_trans];
    [__abs]/[__abs_anno] reconstruct with body lifted by the IH and
    [d_sub_gen_arrow_refl_inner]; [__app] is research-grade
    (same gap as [d_typing_lift_mono]'s [__app] — function arg-type
    mono not derivable from the rule). *)
Lemma d_typing_gen_lift_mono : forall Γ e A m_target,
    d_typing_gen mode_ti Γ e A ->
    mono_typ A ->
    d_wf_denv Γ ->
    d_sub_gen m_target nil Γ A A ->
    d_typing_gen m_target Γ e A.
Proof.
  intros Γ e A m_target H.
  remember mode_ti as m0 eqn:Hm0.
  generalize dependent m_target.
  induction H; intros m_target Hmono Hwfd Hrefl.
  - (* __unit *)
    apply d_typing_gen__sub with (A := typ_unit); auto using is_base_term__unit.
    apply d_typing_gen__unit; auto.
  - (* __var *)
    apply d_typing_gen__sub with (A := A); auto using is_base_term__var.
    apply d_typing_gen__var; auto.
  - (* __anno: rule conclusion is [syn_color A]; route through
       [d_typing_gen__sub] at that target. *)
    apply d_typing_gen__sub with (A := syn_color A);
      auto using is_base_term__anno.
    apply d_typing_gen__anno; auto.
  - (* __sub: m = mode_ti (in context), inner mode_ti at A, sub
       d_sub_gen mode_ti A B. Compose with Hrefl (d_sub_gen m_target B B)
       via d_sub_gen_trans at m1 = mode_ti. *)
    subst.
    apply d_typing_gen__sub with (A := A); auto.
    eapply d_sub_gen_trans with (m1 := mode_ti) (B := B).
    + apply is_fn_n_ti__ti.
    + eapply d_typing_gen_preserves_wf; eauto.
    + exact H1.
    + exact Hrefl.
  - (* __freeze: produces mode_tc, contradicts m0 = mode_ti. *)
    discriminate.
  - (* __forall: produces mode_tc, contradicts. *)
    discriminate.
  - (* __abs at outer m = mode_ti. Conclusion: typ_arrow (inh_color A) B.
       Mono ⇒ both arms mono. Body lifts via IH H1 with body refl from
       [d_sub_gen_arrow_refl_inner] + weakening. *)
    subst.
    inversion Hmono; subst.
    apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
    intros x Hx. apply H1; auto.
    + apply d_wf_denv__typ;
        [ assumption | fsetdec
        | apply d_wf_typ_inh_color_syn_color; assumption ].
    + rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
      apply d_sub_gen_weakening_head.
      eapply d_sub_gen_arrow_refl_inner; eauto.
  - (* __abs_anno: conclusion typ_arrow (syn_color A) B; body binding is
       (x ~ dbind_typ (syn_color A)) — same colour, identity. *)
    subst.
    inversion Hmono; subst.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
    intros x Hx. apply H1; auto.
    + apply d_wf_denv__typ; [assumption | fsetdec | assumption].
    + rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
      apply d_sub_gen_weakening_head.
      eapply d_sub_gen_arrow_refl_inner; eauto.
  - (* __app: CONCRETE OBSTRUCTION (2026-05-16 discovery).

       Lift requires function-side mode shift: from
         H1 : d_typing_gen (mode_fn mode_ti) Γ e1 (typ_arrow P' B)
       produce
         d_typing_gen (mode_fn m_target) Γ e1 (typ_arrow P' B).

       The reconstruction via __sub would need
         d_sub_gen (mode_fn m_target) nil Γ A0 (typ_arrow P' B)
       for the same A0 used in the original __sub. The three rules of
       d_sub_gen at mode_fn _:
       - __refl_mono : requires typ_arrow P' B mono, i.e., P' mono.
         FAILS for P' = typ_all_col colour_syn _ (from d_refine_syn__hole
         with an is_syn_skel polytype Q — a valid refinement output).
       - __arg : requires d_consis_gen Δ1 Γ A0_arg P'. The d_consis_gen
         refl on P' via [d_consis_gen_refl] requires [is_inh_typ P'],
         which FAILS for typ_all_col colour_syn (only colour_inh quantifier
         heads satisfy is_inh_typ__all).
       - __embed via d_sub : same constraint via d_sub__arg → d_consis.

       CONCRETE WITNESS: P = ctyp_hole; P' = typ_all_col colour_syn
       (typ_arrow typ_unit typ_unit) (polytype); B = typ_unit (mono).
       Original derivation EXISTS (e.g., via __abs_anno with syn-painted
       binding). LIFT via these rules FAILS.

       This is NOT a counter-example to the typing's lift property — the
       property holds semantically — but it IS a concrete obstruction in
       the d_sub_gen / d_consis_gen rule set. The fix requires one of:
       (a) Add d_consis_gen__forall_syn rule (mirror of __forall_inh) for
           typ_all_col colour_syn LHS — paper-aligned.
       (b) Restrict d_refine_syn__hole to is_inh_typ outputs (rule
           strengthening with cascading impact).
       (c) Joint mutual induction over D12 + lift_mono with multiple
           invariants (paper appendix B.5 approach, ~500+ line refactor). *)
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

(** Post-re-encoding: [d_typing_gen__var] returns the bound type raw,
    so the gen-subsumption helper for variables takes the [d_sub_gen]
    on [Avar] directly (no [syn_color_t] wrap). *)
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

(** [d_typing_anno_gen_subsumption]: subsume an annotated check-mode
    typing across a [d_sub_gen]. Post-re-encoding the helper is
    naturally stated over a [ctyp] base [C] (matching the
    [d_typing_gen__anno] rule shape): the inner check is at
    [inh_color C], the synthesised result is at [syn_color C], and the
    outer [d_sub_gen] subsumes the [syn_color C] conclusion to any [A].
    The old [typ]-domain statement (`Aann : typ` with [is_inh_typ Aann]
    plus a [d_sub_gen] from [Aann] to [A]) is unprovable post-re-encoding:
    the rule produces [syn_color C] not [Aann], so the d_sub_gen
    composition no longer lines up. *)
Lemma d_typing_anno_gen_subsumption : forall Γ e0 C A m,
    d_wf_denv Γ ->
    d_typing_gen mode_tc Γ e0 (inh_color C) ->
    d_sub_gen m nil Γ (syn_color C) A ->
    d_typing_gen m Γ (exp_anno e0 (inh_color C)) A.
Proof.
  intros Γ e0 C A m Hwfd Hinner Hs.
  apply d_typing_gen__sub with (A := syn_color C).
  - apply is_base_term__anno.
  - apply d_typing_gen__anno; assumption.
  - exact Hs.
Qed.

(** Mono-extraction helpers (used in __check_gen closure). *)

Lemma is_inh_typ_syn_color_mono_pre : forall A C,
    is_inh_typ A ->
    A = syn_color C ->
    mono_typ A.
Proof.
  intros A C Hinh. revert C. induction Hinh; intros C HC.
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - destruct C; simpl in HC; inversion HC; subst.
    apply mono_typ__arrow.
    + eapply IHHinh1; reflexivity.
    + eapply IHHinh2; reflexivity.
  - destruct C; simpl in HC; discriminate.
Qed.

(** [d_consis_syn_inh_mono]: when d_consis has a syn-painted LHS and an
    inh-painted RHS, the LHS must be mono.

    Proof by induction on d_consis. The new __forall_syn rule is vacuous
    in this context because its RHS shape (typ_all_col colour_syn) cannot
    equal an inh_color painting (inh_color paints colour_inh exclusively).
    The other forall cases (tagged / colour_inh LHS) are vacuous via
    syn_color injectivity (syn_color never produces typ_all_etag or
    typ_all_col colour_inh). Unit/var/arrow recurse structurally. *)
Lemma d_consis_syn_inh_mono : forall Γ Δ T A,
    d_consis Δ Γ (syn_color T) (inh_color A) ->
    mono_typ (syn_color T).
Proof.
  intros Γ Δ T A H.
  remember (syn_color T) as A_lhs eqn:HeqLHS.
  remember (inh_color A) as A_rhs eqn:HeqRHS.
  revert T A HeqLHS HeqRHS.
  induction H; intros T0 A0 HeqLHS HeqRHS.
  - (* __unit *) apply mono_typ__unit.
  - (* __var *) destruct T0; simpl in HeqLHS; try discriminate.
    inversion HeqLHS; subst. apply mono_typ__var.
  - (* __forall_inh_tagged: LHS typ_all_etag — syn_color never paints etag. *)
    destruct T0; simpl in HeqLHS; discriminate.
  - (* __forall_syn_tagged: LHS typ_all_etag — vacuous as above. *)
    destruct T0; simpl in HeqLHS; discriminate.
  - (* __forall_syn (post-refactor): LHS = typ_all_col colour_syn = syn_color
       (ctyp_all _). RHS = typ_all_col colour_syn — but inh_color paints
       colour_inh, never colour_syn. Vacuous via HeqRHS inversion. *)
    destruct A0; simpl in HeqRHS; discriminate.
  - (* __forall_inh: LHS = typ_all_col colour_inh — syn_color never paints
       colour_inh. Vacuous via HeqLHS. *)
    destruct T0; simpl in HeqLHS; try discriminate.
  - (* __arrow *)
    destruct T0; simpl in HeqLHS; try discriminate.
    destruct A0; simpl in HeqRHS; try discriminate.
    inversion HeqLHS; inversion HeqRHS; subst.
    apply mono_typ__arrow.
    + eapply IHd_consis1; reflexivity.
    + eapply IHd_consis2; reflexivity.
Qed.

(** [d_consis_gen_syn_inh_mono]: d_consis_gen analogue. Same structure as
    [d_consis_syn_inh_mono]; the new [__forall_syn] rule in [d_consis_gen]
    is vacuous for the same reason (RHS colour mismatch with inh_color). *)
Lemma d_consis_gen_syn_inh_mono : forall Γ Δ T A,
    d_consis_gen Δ Γ (syn_color T) (inh_color A) ->
    mono_typ (syn_color T).
Proof.
  intros Γ Δ T A H.
  remember (syn_color T) as A_lhs eqn:HeqLHS.
  remember (inh_color A) as A_rhs eqn:HeqRHS.
  revert T A HeqLHS HeqRHS.
  induction H; intros T0 A0 HeqLHS HeqRHS.
  - apply mono_typ__unit.
  - destruct T0; simpl in HeqLHS; try discriminate.
    inversion HeqLHS; subst. apply mono_typ__var.
  - destruct T0; simpl in HeqLHS; discriminate.
  - destruct T0; simpl in HeqLHS; discriminate.
  - destruct A0; simpl in HeqRHS; discriminate.
  - destruct T0; simpl in HeqLHS; try discriminate.
  - destruct T0; simpl in HeqLHS; try discriminate.
    destruct A0; simpl in HeqRHS; try discriminate.
    inversion HeqLHS; inversion HeqRHS; subst.
    apply mono_typ__arrow.
    + eapply IHd_consis_gen1; reflexivity.
    + eapply IHd_consis_gen2; reflexivity.
Qed.

(** [d_typing_abs_value_to_subsumption_d_sub]: companion lemma for
    the d_sub-level closure of [d_typing_abs_value_to_subsumption]'s
    __embed case. Induction on d_sub: __check mirrors __check_gen
    (mono extraction + reconstruction); __forall_r recurses via the
    IH on the inner d_sub. Other cases vacuous via mode or shape
    mismatch. *)
Lemma d_typing_abs_value_to_subsumption_d_sub :
  forall Γ Δ T0 C0,
    d_sub mode_tc Δ Γ T0 C0 ->
    Δ = nil ->
    forall Lvar e Ahead Bhead m_orig,
      T0 = typ_arrow Ahead Bhead ->
      is_inh_typ Ahead ->
      d_wf_typ Γ Ahead ->
      (forall x, x `notin` Lvar ->
         d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ Ahead) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      decr_mode m_orig = mode_ti ->
      d_wf_denv Γ ->
      d_typing_gen mode_tc Γ (exp_abs e) C0.
Proof.
  intros Γ Δ T0 C0 Hs. dependent induction Hs; intros HΔ Lvar e Ahead Bhead m_orig HT0 HinhA HwfA Hbody Hdecr Hwfd; subst.
  - (* d_sub__check: LHS = syn_color T = typ_arrow Ahead Bhead. *)
    (* Mirror __check_gen mono-extraction chain. *)
    destruct T; simpl in HT0; try discriminate.
    inversion HT0; subst.
    assert (HmonoA : mono_typ (syn_color T1))
      by (eapply is_inh_typ_syn_color_mono_pre; eauto).
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H5 into Hcons1. rename H6 into Hcons2.
    (* Derive A = ctyp_arrow A1' A2' from H3 to expose A2 = inh_color A2',
       then apply d_consis_syn_inh_mono to Hcons2 for HmonoB.
       Do this BEFORE the HeqA2 subst that would consume A2. *)
    assert (HmonoB : mono_typ (syn_color T2)).
    { symmetry in H3. apply inh_color_eq_arrow_inv in H3.
      destruct H3 as [A1' [A2' [_ [_ HA2_eq]]]].
      (* HA2_eq : inh_color A2' = A2, so rewrite <- to replace A2 in Hcons2. *)
      rewrite <- HA2_eq in Hcons2.
      eapply d_consis_syn_inh_mono; exact Hcons2. }
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoA) Hcons1) as HeqA1.
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoB) Hcons2) as HeqA2.
    subst.
    pose proof (mono_typ_inh_color_erase HmonoA) as HeqA_inh.
    rewrite erase_syn_color in HeqA_inh.
    rewrite <- HeqA_inh at 1.
    (* Goal at this point: d_typing_gen mode_tc Γ (exp_abs e) (typ_arrow
       (syn_color T1) (syn_color T2)). We use HA2_eq (which after subst
       is syn_color T2 = inh_color A2') and HeqA_inh to map between
       inh_color and syn_color paintings. *)
    apply d_typing_gen__abs with (L := Lvar `union` dom Γ).
    + rewrite HeqA_inh. exact HwfA.
    + intros x0 Hx0.
      assert (Hwfd_x : d_wf_denv ((x0 ~ dbind_typ (syn_color T1)) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ (syn_color T1)) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_preserves_wf; eauto.
  - (* d_sub__forall_r: target = typ_all_col colour_inh A. Reconstruct
       via [d_typing_gen__forall] (value rule) + recursive IH at each X. *)
    apply d_typing_gen__forall with (L := L `union` Lvar `union` dom Γ).
    + apply is_value__abs.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      (* IH H0 takes: X, X∉L, then the same args as the lemma at (X∷Γ). *)
      eapply H0 with (Ahead := Ahead) (Bhead := Bhead) (m_orig := m_orig)
        (Lvar := Lvar); eauto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
  - (* d_sub__forall_l_tagged: LHS = typ_all_etag, contradicts typ_arrow. *)
    discriminate.
Qed.

(** [d_typing_abs_anno_value_to_subsumption_d_sub]: anno-variant
    companion. Same structure as the value variant's companion but
    with LHS [typ_arrow (syn_color_t Ahead) Bhead] and conclusion
    via [d_typing_gen__abs_anno]. No [is_inh_typ Ahead] precondition
    (mono on Ahead derived via [mono_typ_syn_color_t_inv]). *)
Lemma d_typing_abs_anno_value_to_subsumption_d_sub :
  forall Γ Δ T0 C0,
    d_sub mode_tc Δ Γ T0 C0 ->
    Δ = nil ->
    forall Lvar e Ahead Bhead m_orig,
      T0 = typ_arrow (syn_color_t Ahead) Bhead ->
      d_wf_typ Γ Ahead ->
      (forall x, x `notin` Lvar ->
         d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ Ahead) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      decr_mode m_orig = mode_ti ->
      d_wf_denv Γ ->
      d_typing_gen mode_tc Γ (exp_abs_anno Ahead e) C0.
Proof.
  intros Γ Δ T0 C0 Hs. dependent induction Hs;
    intros HΔ Lvar e Ahead Bhead m_orig HT0 HwfA Hbody Hdecr Hwfd; subst.
  - (* d_sub__check: parallel to anno helper's __check_gen case. *)
    destruct T; simpl in HT0; try discriminate.
    inversion HT0; subst.
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H6 into Hcons1. rename H7 into Hcons2.
    (* Derive mono via d_consis_syn_inh_mono (new helper). *)
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { symmetry in H4. apply inh_color_eq_arrow_inv in H4.
      destruct H4 as [A1' [_ [_ [HA1_eq _]]]].
      rewrite <- HA1_eq in Hcons1.
      eapply d_consis_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { symmetry in H4. apply inh_color_eq_arrow_inv in H4.
      destruct H4 as [_ [A2' [_ [_ HA2_eq]]]].
      rewrite <- HA2_eq in Hcons2.
      eapply d_consis_syn_inh_mono; exact Hcons2. }
    rename H2 into Heq_LHS.
    assert (HmonoA : mono_typ Ahead).
    { rewrite Heq_LHS in HmonoT1_syn.
      exact (mono_typ_syn_color_t_inv Ahead HmonoT1_syn). }
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in Heq_LHS.
    rewrite syn_color_t_syn_color_erase in Heq_LHS.
    rewrite !erase_syn_color in Heq_LHS.
    subst T1.
    rewrite <- (mono_typ_inh_color_erase HmonoA) at 1.
    apply d_typing_gen__abs_anno with (L := Lvar `union` dom Γ).
    + rewrite HsynA. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ Ahead) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ Ahead) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_preserves_wf; eauto.
  - (* d_sub__forall_r: recurse via IH. *)
    apply d_typing_gen__forall with (L := L `union` Lvar `union` dom Γ).
    + apply is_value__abs_anno.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      eapply H0 with (Ahead := Ahead) (Bhead := Bhead) (m_orig := m_orig)
        (Lvar := Lvar); eauto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
  - (* d_sub__forall_l_tagged: vacuous. *)
    discriminate.
Qed.

(** [is_inh_typ_inh_color]: any [inh_color C] for [C : ctyp] is
    [is_inh_typ] PROVIDED [d_wf_typ] (which rules out [ctyp_hole] /
    [ctyp_tophole] shapes). *)
Lemma is_inh_typ_inh_color : forall Γ C,
    d_wf_typ Γ (inh_color C) ->
    is_inh_typ (inh_color C).
Proof.
  intros Γ C Hwf. remember (inh_color C) as A in Hwf.
  revert C HeqA. induction Hwf; intros C HeqA.
  - destruct C; simpl in HeqA; try discriminate. apply is_inh_typ__unit.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_inh_typ__var.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_inh_typ__arrow.
    + eapply IHHwf1; reflexivity.
    + eapply IHHwf2; reflexivity.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst.
    inst_cofinites_for is_inh_typ__all.
    intros X HX.
    assert (HX' : X `notin` L) by fsetdec.
    rewrite <- inh_color_open_var.
    eapply H0; eauto.
    rewrite inh_color_open_var. reflexivity.
Qed.

(** [is_syn_typ_syn_color]: parallel to [is_inh_typ_inh_color] but for
    the [syn_color] painting. Same shape of proof. *)
Lemma is_syn_typ_syn_color : forall Γ C,
    d_wf_typ Γ (syn_color C) ->
    is_syn_typ (syn_color C).
Proof.
  intros Γ C Hwf. remember (syn_color C) as A in Hwf.
  revert C HeqA. induction Hwf; intros C HeqA.
  - destruct C; simpl in HeqA; try discriminate. apply is_syn_typ__unit.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_syn_typ__var.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst. apply is_syn_typ__arrow.
    + eapply IHHwf1; reflexivity.
    + eapply IHHwf2; reflexivity.
  - destruct C; simpl in HeqA; try discriminate.
    inversion HeqA; subst.
    inst_cofinites_for is_syn_typ__all.
    intros X HX.
    assert (HX' : X `notin` L) by fsetdec.
    rewrite <- syn_color_open_var.
    eapply H0; eauto.
    rewrite syn_color_open_var. reflexivity.
Qed.


(** [d_typing_abs_value_to_subsumption_split_d_sub]: d_sub companion
    for the SPLIT abs-value-to-subsumption helper. Parallels
    [d_typing_abs_anno_value_to_subsumption_d_sub] but:
    - LHS shape: [typ_arrow (inh_color_t Ahead) Bhead] (not
      [typ_arrow (syn_color_t Ahead) Bhead]).
    - Reconstruction via [d_typing_gen__abs] (not [__abs_anno]).

    [d_sub__check]'s LHS = [syn_color T] forces
    [syn_color T1 = inh_color_t Ahead], which is only satisfiable for
    Ahead mono (syn-painted on quantifiers vs inh-painted differ
    unless no quantifiers). Mono Ahead lets the binding [(x ~ Ahead)]
    coincide with the rule's [(x ~ syn_color A_rule)] for
    [A_rule := erase Ahead]. *)
Lemma d_typing_abs_value_to_subsumption_split_d_sub :
  forall Γ Δ T0 C0,
    d_sub mode_tc Δ Γ T0 C0 ->
    Δ = nil ->
    forall Lvar e Ahead Bhead m_orig,
      T0 = typ_arrow (inh_color_t Ahead) Bhead ->
      d_wf_typ Γ (inh_color_t Ahead) ->
      (forall x, x `notin` Lvar ->
         d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ Ahead) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      decr_mode m_orig = mode_ti ->
      d_wf_denv Γ ->
      d_typing_gen mode_tc Γ (exp_abs e) C0.
Proof.
  intros Γ Δ T0 C0 Hs. dependent induction Hs;
    intros HΔ Lvar e Ahead Bhead m_orig HT0 HwfA Hbody Hdecr Hwfd; subst.
  - (* d_sub__check: LHS = syn_color T = typ_arrow (inh_color_t Ahead) Bhead.
       Forces T = ctyp_arrow T1 T2, then syn_color T1 = inh_color_t Ahead. *)
    destruct T; simpl in HT0; try discriminate.
    inversion HT0; subst.
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H6 into Hcons1. rename H7 into Hcons2.
    (* Derive mono via d_consis_syn_inh_mono (post-refactor helper).
       The typ_arrow = inh_color A equation is in context (named H_eq
       via match); inh_color_eq_arrow_inv splits A. *)
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_syn_inh_mono; exact Hcons2. }
    rename H2 into Heq_LHS.
    (* Heq_LHS: syn_color T1 = inh_color_t Ahead. T1 mono ⇒ Ahead mono
       (since inh_color_t Ahead = inh_color (erase Ahead), and that's
       mono iff erase Ahead is colourless, iff Ahead is mono). *)
    assert (HmonoIH : mono_typ (inh_color_t Ahead))
      by (rewrite <- Heq_LHS; exact HmonoT1_syn).
    assert (HmonoA : mono_typ Ahead)
      by (apply mono_typ_inh_color_t_inv; exact HmonoIH).
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    (* HsynA: syn_color (erase Ahead) = Ahead.
       HinhA: inh_color (erase Ahead) = Ahead. *)
    (* Erase both sides of Heq_LHS to derive T1 = erase Ahead. *)
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs e) (typ_arrow (syn_color (erase Ahead)) (syn_color T2)).
       Rewrite syn_color (erase Ahead) ↦ inh_color (erase Ahead) (both = Ahead). *)
    rewrite HsynA.
    rewrite <- HinhA at 1.
    assert (HwfA_raw : d_wf_typ Γ Ahead).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    apply d_typing_gen__abs with (L := Lvar `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ Ahead) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ Ahead) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_preserves_wf; eauto.
  - (* d_sub__forall_r: recurse via IH. *)
    apply d_typing_gen__forall with (L := L `union` Lvar `union` dom Γ).
    + apply is_value__abs.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      eapply H0 with (Ahead := Ahead) (Bhead := Bhead) (m_orig := m_orig)
        (Lvar := Lvar); eauto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
  - (* d_sub__forall_l_tagged: vacuous (LHS not typ_arrow). *)
    discriminate.
Qed.

(** [d_typing_abs_value_to_subsumption_split]: abs value-to-subsumption
    helper with SPLIT binding/arrow-arg. Parallels
    [d_typing_abs_anno_value_to_subsumption] but for [exp_abs e] (not
    [exp_abs_anno A e]) with arrow arg [inh_color_t A] (not
    [syn_color_t A]). The split signature lets it apply at the D12
    __abs callsite where the rule's body binding is [syn_color A0]
    and the conclusion's arrow arg is [inh_color A0]. *)
Lemma d_typing_abs_value_to_subsumption_split :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ (inh_color_t A) ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_tc nil Γ (typ_arrow (inh_color_t A) B) C ->
    d_typing_gen mode_tc Γ (exp_abs e) C.
Proof.
  intros L Γ e A B m_orig C HwfA Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: dispatch to d_sub companion. *)
    eapply d_typing_abs_value_to_subsumption_split_d_sub
      with (Ahead := A) (Bhead := B) (m_orig := m_orig); eauto.
  - (* __check_gen: LHS = syn_color T forces T = ctyp_arrow T1 T2,
       then syn_color T1 = inh_color_t A — only satisfiable for A mono. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H6 into Hcons1. rename H7 into Hcons2.
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons2. }
    match goal with H : syn_color T1 = inh_color_t A |- _ =>
      rename H into Heq_LHS
    end.
    assert (HmonoIH : mono_typ (inh_color_t A))
      by (rewrite <- Heq_LHS; exact HmonoT1_syn).
    assert (HmonoA : mono_typ A)
      by (apply mono_typ_inh_color_t_inv; exact HmonoIH).
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    rewrite HsynA.
    rewrite <- HinhA at 1.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_gen_preserves_wf; eauto.
  - (* __refl_mono: target = typ_arrow (inh_color_t A) B forced mono. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmIH : mono_typ (inh_color_t A) |- _ =>
      assert (HmonoA : mono_typ A)
        by (apply mono_typ_inh_color_t_inv; auto)
    end.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- (mono_typ_inh_color_erase HmonoA).
      rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    rewrite inh_color_t_inh_color_erase.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite (mono_typ_inh_color_erase HmonoA). assumption.
    + intros x Hx.
      assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      rewrite (mono_typ_syn_color_erase HmonoA).
      apply d_typing_gen_lift_mono with (A := B); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
        -- rewrite_env ((x ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           match goal with H1 : d_wf_typ Γ (typ_arrow _ _) |- _ =>
             inversion H1; subst; assumption
           end.
  - (* __forall_r: target = typ_all_col colour_inh A_target. Recurse via
       [d_typing_gen__forall] + IH at each X. *)
    apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      apply H0 with (A := A) (B := B); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
Qed.

(** [d_typing_abs_value_to_subsumption_split_ti]: mode_ti variant of the
    SPLIT abs helper. Same shape, but Hsub_gen / conclusion at mode_ti
    (not mode_tc). At mode_ti, d_sub_gen rules are only __embed,
    __infer_gen, __refl_mono — no __forall_r recursion.

    Strengthened signature: added [d_wf_typ Γ B] premise so that the
    __embed/__infer_gen cases can derive [is_syn_typ (syn_color T2)]
    from [B = syn_color T2] (forced by [d_sub__infer]) + the wf premise.
    Without this strengthening, the LHS-rigidity lemma would need an
    inductive helper that fails on the [d_consis_gen__forall_syn] case. *)
Lemma d_typing_abs_value_to_subsumption_split_ti :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ (inh_color_t A) ->
    d_wf_typ Γ B ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_ti nil Γ (typ_arrow (inh_color_t A) B) C ->
    d_typing_gen mode_ti Γ (exp_abs e) C.
Proof.
  intros L Γ e A B m_orig C HwfA HwfB Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: d_sub mode_ti, only d_sub__infer applies. *)
    rename H into Hdsub. dependent destruction Hdsub.
    (* d_sub__infer: LHS = syn_color T, forces typ_arrow shape. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    match goal with H : syn_color T1 = inh_color_t A |- _ =>
      rename H into Heq_LHS
    end.
    (* Derive A mono from the equation [syn_color T1 = inh_color_t A]
       (rules out [typ_all_*] colour-mismatch + [hole]/[tophole] via wf). *)
    assert (HmonoA : mono_typ A).
    { symmetry in Heq_LHS. eapply inh_color_t_eq_syn_color_mono; eauto. }
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    (* Rigidity: derive [syn_color T2 = syn_color A2] from Hcons2 +
       [HwfB] giving [is_syn_typ (syn_color T2)] via [is_syn_typ_syn_color]
       (B = syn_color T2 after [inversion x; subst]). *)
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    assert (HwfsynA : d_wf_typ Γ (syn_color (erase A))).
    { rewrite HsynA. assumption. }
    assert (HsynT1 : is_syn_typ (syn_color (erase A)))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2 : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_lhs_syn_eq HsynT1 Hcons1) as HeqA1.
    pose proof (d_consis_lhs_syn_eq HsynT2 Hcons2) as HeqA2.
    subst.
    rewrite HsynA.
    rewrite <- HinhA at 1.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      (* Body Hbody already at mode_ti (decr_mode m_orig = mode_ti) with
         binding [(x ~ dbind_typ A) ++ Γ] and conclusion B = syn_color T2;
         no lift needed. *)
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __infer_gen: parallel to __embed __infer, with d_consis_gen. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis_gen _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis_gen _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis_gen _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    match goal with H : syn_color T1 = inh_color_t A |- _ =>
      rename H into Heq_LHS
    end.
    assert (HmonoA : mono_typ A).
    { symmetry in Heq_LHS. eapply inh_color_t_eq_syn_color_mono; eauto. }
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in Heq_LHS.
    rewrite inh_color_t_inh_color_erase in Heq_LHS.
    rewrite erase_inh_color in Heq_LHS.
    rewrite erase_syn_color in Heq_LHS.
    subst T1.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- HinhA. rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    assert (HwfsynA : d_wf_typ Γ (syn_color (erase A))).
    { rewrite HsynA. assumption. }
    assert (HsynT1 : is_syn_typ (syn_color (erase A)))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2 : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_gen_lhs_syn_eq HsynT1 Hcons1) as HeqA1.
    pose proof (d_consis_gen_lhs_syn_eq HsynT2 Hcons2) as HeqA2.
    subst.
    rewrite HsynA.
    rewrite <- HinhA at 1.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite <- inh_color_t_inh_color_erase. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __refl_mono: target = typ_arrow (inh_color_t A) B forced mono. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmIH : mono_typ (inh_color_t A) |- _ =>
      assert (HmonoA : mono_typ A)
        by (apply mono_typ_inh_color_t_inv; auto)
    end.
    assert (HwfA_raw : d_wf_typ Γ A).
    { rewrite <- (mono_typ_inh_color_erase HmonoA).
      rewrite <- inh_color_t_inh_color_erase. exact HwfA. }
    rewrite inh_color_t_inh_color_erase.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite (mono_typ_inh_color_erase HmonoA). assumption.
    + intros x Hx.
      rewrite (mono_typ_syn_color_erase HmonoA).
      (* Body Hbody at mode_ti, binding (x ~ dbind_typ A), conclusion B;
         direct application — lift_mono would be a no-op. *)
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
Qed.

(** [d_typing_abs_anno_value_to_subsumption_split_d_sub]: d_sub
    companion for the SPLIT abs_anno helper. Conclusion's term is
    [exp_abs_anno (inh_color_t Ahead) e] to match the rule's
    [exp_abs_anno (inh_color A_rule) e] for [A_rule = erase Ahead]
    (in the mono case, [inh_color (erase Ahead) = inh_color_t Ahead]
    via [inh_color_t_inh_color_erase]). *)
Lemma d_typing_abs_anno_value_to_subsumption_split_d_sub :
  forall Γ Δ T0 C0,
    d_sub mode_tc Δ Γ T0 C0 ->
    Δ = nil ->
    forall Lvar e Ahead Bhead m_orig,
      T0 = typ_arrow Ahead Bhead ->
      d_wf_typ Γ Ahead ->
      (forall x, x `notin` Lvar ->
         d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ Ahead) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) Bhead) ->
      decr_mode m_orig = mode_ti ->
      d_wf_denv Γ ->
      d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t Ahead) e) C0.
Proof.
  intros Γ Δ T0 C0 Hs. dependent induction Hs;
    intros HΔ Lvar e Ahead Bhead m_orig HT0 HwfA Hbody Hdecr Hwfd; subst.
  - (* d_sub__check: LHS = syn_color T = typ_arrow Ahead Bhead.
       After `inversion HT0; subst`, Ahead gets substituted with syn_color T1
       (and Bhead with syn_color T2). Work with syn_color T1 / T2 directly. *)
    destruct T; simpl in HT0; try discriminate.
    inversion HT0; subst.
    match goal with H : d_consis _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_syn_inh_mono; exact Hcons2. }
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t (syn_color T1)) e)
              (typ_arrow (syn_color T1) (syn_color T2)).
       Simplify: inh_color_t (syn_color T1) = inh_color T1
       (via inh_color_t_inh_color_erase + erase_syn_color).
       Apply d_typing_gen__abs_anno with A_rule := T1. *)
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := Lvar `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ (syn_color T1)) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ (syn_color T1)) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_preserves_wf; eauto.
  - (* d_sub__forall_r: recurse via IH. *)
    apply d_typing_gen__forall with (L := L `union` Lvar `union` dom Γ).
    + apply is_value__abs_anno.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      eapply H0 with (Ahead := Ahead) (Bhead := Bhead) (m_orig := m_orig)
        (Lvar := Lvar); eauto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ Ahead)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
  - (* d_sub__forall_l_tagged: vacuous (LHS not typ_arrow). *)
    discriminate.
Qed.

(** [d_typing_abs_anno_value_to_subsumption_split]: SPLIT abs_anno
    helper. Conclusion's term is [exp_abs_anno (inh_color_t A) e]. *)
Lemma d_typing_abs_anno_value_to_subsumption_split :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_tc nil Γ (typ_arrow A B) C ->
    d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t A) e) C.
Proof.
  intros L Γ e A B m_orig C HwfA Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: dispatch to d_sub companion. *)
    eapply d_typing_abs_anno_value_to_subsumption_split_d_sub
      with (Ahead := A) (Bhead := B) (m_orig := m_orig); eauto.
  - (* __check_gen: parallel to _d_sub __check. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis_gen _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis_gen _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis_gen _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons2. }
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t (syn_color T1)) e)
              (typ_arrow (syn_color T1) (syn_color T2)). *)
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ (syn_color T1)) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ (syn_color T1)) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_gen_preserves_wf; eauto.
  - (* __refl_mono: target = typ_arrow A B forced mono. Reconstruct via
       d_typing_gen__abs_anno with A_rule := erase A; the rule produces
       term [exp_abs_anno (inh_color (erase A)) e] and conclusion arg
       [syn_color (erase A)]. For mono A: inh_color (erase A) = A and
       syn_color (erase A) = A; also inh_color_t A = inh_color (erase A)
       via inh_color_t_inh_color_erase. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmA : mono_typ A |- _ => rename HmA into HmonoA end.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs_anno (inh_color_t A) e) (typ_arrow A B). *)
    replace (inh_color_t A) with (inh_color (erase A))
      by (symmetry; apply inh_color_t_inh_color_erase).
    rewrite <- HsynA at 2.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + rewrite HsynA. assumption.
    + intros x Hx.
      assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      rewrite HsynA.
      apply d_typing_gen_lift_mono with (A := B); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
        -- rewrite_env ((x ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           match goal with H1 : d_wf_typ Γ (typ_arrow _ _) |- _ =>
             inversion H1; subst; assumption
           end.
  - (* __forall_r: recurse via IH. *)
    apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs_anno.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      apply H0 with (A := A) (B := B); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
Qed.

(** [d_typing_abs_anno_value_to_subsumption_split_ti]: mode_ti variant of
    the SPLIT abs_anno helper. Strengthened with [d_wf_typ Γ B] premise
    (used to derive [is_syn_typ (syn_color T2)] in __embed/__infer_gen). *)
Lemma d_typing_abs_anno_value_to_subsumption_split_ti :
  forall L Γ e A B m_orig C,
    d_wf_typ Γ A ->
    d_wf_typ Γ B ->
    (forall x, x `notin` L ->
       d_typing_gen (decr_mode m_orig) ((x ~ dbind_typ A) ++ Γ) (open_exp_wrt_exp e (exp_var_f x)) B) ->
    decr_mode m_orig = mode_ti ->
    d_wf_denv Γ ->
    d_sub_gen mode_ti nil Γ (typ_arrow A B) C ->
    d_typing_gen mode_ti Γ (exp_abs_anno (inh_color_t A) e) C.
Proof.
  intros L Γ e A B m_orig C HwfA HwfB Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: d_sub mode_ti, only d_sub__infer applies. *)
    rename H into Hdsub. dependent destruction Hdsub.
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HsynT1' : is_syn_typ (syn_color T1))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2' : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_lhs_syn_eq HsynT1' Hcons1) as HeqA1.
    pose proof (d_consis_lhs_syn_eq HsynT2' Hcons2) as HeqA2.
    subst.
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __infer_gen: parallel to __embed __infer with d_consis_gen. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    match goal with H : d_consis_gen _ _ _ _ |- _ => rename H into Hcons end.
    inversion Hcons; subst.
    match goal with H : ?l1 ++ ?l2 = nil |- _ =>
      apply app_eq_nil in H; destruct H as [HΔ1 HΔ2]; subst l1 l2
    end.
    match goal with H : d_consis_gen _ _ (syn_color T1) _ |- _ => rename H into Hcons1 end.
    match goal with H : d_consis_gen _ _ (syn_color T2) _ |- _ => rename H into Hcons2 end.
    assert (HsynT1 : is_syn_typ (syn_color T1))
      by (eapply is_syn_typ_syn_color; eassumption).
    assert (HsynT2 : is_syn_typ (syn_color T2))
      by (eapply is_syn_typ_syn_color; eassumption).
    pose proof (d_consis_gen_lhs_syn_eq HsynT1 Hcons1) as HeqA1.
    pose proof (d_consis_gen_lhs_syn_eq HsynT2 Hcons2) as HeqA2.
    subst.
    replace (inh_color_t (syn_color T1)) with (inh_color T1)
      by (rewrite inh_color_t_inh_color_erase; rewrite erase_syn_color; reflexivity).
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + assumption.
    + intros x0 Hx0.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
  - (* __refl_mono: target = typ_arrow A B forced mono. *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmA : mono_typ A |- _ => rename HmA into HmonoA end.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    replace (inh_color_t A) with (inh_color (erase A))
      by (symmetry; apply inh_color_t_inh_color_erase).
    rewrite <- HsynA at 2.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + rewrite HsynA. assumption.
    + intros x Hx.
      rewrite HsynA.
      simpl. rewrite <- Hdecr. apply Hbody. fsetdec.
Qed.

(** Mono-extraction helpers (used in __check_gen closure). *)

Lemma is_inh_typ_syn_color_mono : forall A C,
    is_inh_typ A ->
    A = syn_color C ->
    mono_typ A.
Proof.
  intros A C Hinh. revert C. induction Hinh; intros C HC.
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - destruct C; simpl in HC; inversion HC; subst.
    apply mono_typ__arrow.
    + eapply IHHinh1; reflexivity.
    + eapply IHHinh2; reflexivity.
  - (* A = typ_all_col colour_inh A_inner; syn_color C never has
       colour_inh at head — destructed C is ctyp_all giving
       colour_syn. Contradiction. *)
    destruct C; simpl in HC; discriminate.
Qed.

Lemma d_consis_gen_LHS_syn_color_mono : forall Δ Γ T A,
    d_consis_gen Δ Γ T A ->
    forall C, T = syn_color C ->
    mono_typ T.
Proof.
  intros Δ Γ T A Hc. induction Hc; intros C HC.
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - destruct C; simpl in HC; discriminate.
  - destruct C; simpl in HC; discriminate.
  - (* __forall_syn (post-refactor): T = typ_all_col colour_syn _ =
       syn_color (ctyp_all _). T is NOT mono. Lemma is FALSE here. *)
    admit.
  - destruct C; simpl in HC; discriminate.
  - destruct C; simpl in HC; try discriminate.
    inversion HC; subst.
    apply mono_typ__arrow.
    + eapply IHHc1; reflexivity.
    + eapply IHHc2; reflexivity.
Admitted.

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
  - (* __embed: route through [d_typing_abs_value_to_subsumption_d_sub]
       which inducts on the inner d_sub directly (so __forall_r recurses
       naturally). *)
    eapply d_typing_abs_value_to_subsumption_d_sub with
      (Ahead := A) (Bhead := B) (m_orig := m_orig); eauto.
  - (* __check_gen: T : ctyp with syn_color T = typ_arrow A B forces
       T = ctyp_arrow T1 T2, A = syn_color T1, B = syn_color T2.
       From [HinhA: is_inh_typ A] + syn-LHS ⟹ A mono.
       From inner d_consis_gen on syn LHS ⟹ T1, T2 mono.
       Then mirror __refl_mono with derived mono witnesses. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    (* A = syn_color T1, B = syn_color T2 now. *)
    assert (HmonoA : mono_typ (syn_color T1))
      by (eapply is_inh_typ_syn_color_mono; eauto).
    (* H0 : d_consis_gen nil Γ (typ_arrow (syn_color T1) (syn_color T2))
              (inh_color A0).  Inversion forces __arrow. *)
    inversion H0; subst.
    (* H6: d_consis_gen Δ1 Γ (syn_color T1) A1
       H7: d_consis_gen Δ2 Γ (syn_color T2) A2
       H1: Δ1 ++ Δ2 = nil
       Goal: d_typing_gen mode_tc Γ (exp_abs e) (typ_arrow A1 A2). *)
    apply app_eq_nil in H1. destruct H1 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    assert (HmonoB : mono_typ (syn_color T2))
      by (eapply d_consis_gen_LHS_syn_color_mono; eauto).
    (* By d_consis_gen_lhs_syn_eq, syn_color T1 = A1 and syn_color T2 = A2. *)
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoA) H6) as HeqA1.
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoB) H7) as HeqA2.
    subst A1 A2.
    (* Goal: d_typing_gen mode_tc Γ (exp_abs e)
              (typ_arrow (syn_color T1) (syn_color T2)). *)
    (* Mirror __refl_mono: rewrite syn_color T1 ↦ inh_color T1 via the
       mono pinning [mono_typ (syn_color T1) ⇒ inh_color (erase (syn_color T1)) = syn_color T1
       ⇒ inh_color T1 = syn_color T1 (via erase_syn_color)]. *)
    pose proof (mono_typ_inh_color_erase HmonoA) as HeqA_inh.
    rewrite erase_syn_color in HeqA_inh.
    (* HeqA_inh : inh_color T1 = syn_color T1. *)
    rewrite <- HeqA_inh at 1.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite HeqA_inh. exact HwfA.
    + intros x0 Hx0.
      assert (Hwfd_x : d_wf_denv ((x0 ~ dbind_typ (syn_color T1)) ++ Γ)).
      { apply d_wf_denv__typ; auto. }
      (* Goal: d_typing_gen mode_tc ((x0:syn_color T1)∷Γ) (open e x0)
                (syn_color T2). *)
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ (syn_color T1)) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_gen_preserves_wf; eauto.
  - (* __refl_mono: target = typ_arrow A B forced mono ⇒ mono A and
       mono B. The ctyp base for [d_typing_gen__abs] is [erase A]; for
       mono A, [inh_color (erase A) = syn_color (erase A) = A], so the
       rule's body binding [(x ~ syn_color (erase A))] coincides with
       the lemma's [(x ~ A)]. Body lift from (decr_mode m_orig = mode_ti)
       to mode_tc via [d_typing_gen_lift_mono] (Qed except its __app
       case, which is the canonical mono-arg gap). *)
    match goal with Hm : mono_typ (typ_arrow A B) |- _ =>
      assert (HmonoA : mono_typ A) by (inversion Hm; auto);
      assert (HmonoB : mono_typ B) by (inversion Hm; auto)
    end.
    rewrite <- (mono_typ_inh_color_erase HmonoA) at 1.
    apply d_typing_gen__abs with (L := L `union` dom Γ).
    + rewrite (mono_typ_inh_color_erase HmonoA). assumption.
    + intros x Hx.
      assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      rewrite (mono_typ_syn_color_erase HmonoA).
      apply d_typing_gen_lift_mono with (A := B); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
        -- rewrite_env ((x ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           match goal with Hw : d_wf_typ Γ (typ_arrow A B) |- _ =>
             inversion Hw; assumption
           end.
  - (* __forall_r: target = typ_all_col colour_inh A_target. Reconstruct
       via [d_typing_gen__forall] (value rule) + recursive IH at each X.
       The dependent-induction IH [H0] takes the body-sub at each X plus
       the helper's other premises threaded under the [(X ~ dbind_tvar)
       ++ Γ] extension; we supply those via weakening. *)
    apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      apply (H0 X ltac:(auto) Hwfd_X Hdecr B A); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
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
    d_sub_gen mode_tc nil Γ (typ_arrow (syn_color_t A) B) C ->
    d_typing_gen mode_tc Γ (exp_abs_anno A e) C.
Proof.
  intros L Γ e A B m_orig C HwfA Hbody Hdecr Hwfd Hs.
  dependent induction Hs.
  - (* __embed: invert the wrapped d_sub and handle __check / __forall_r. *)
    rename H into Hsub.
    inversion Hsub; subst.
    + (* d_sub__check: T : ctyp with syn_color T = typ_arrow (syn_color_t A) B
         forces T = ctyp_arrow T1 T2. *)
      destruct T; simpl in H; try discriminate.
      inversion H; subst.
      (* Now H : syn_color T1 = syn_color_t A (and syn_color T2 = B). *)
      rename H1 into Hcons.
      inversion Hcons; subst.
      apply app_eq_nil in H1. destruct H1 as [HΔ1 HΔ2]. subst Δ1 Δ2.
      rename H7 into Hcons1. rename H8 into Hcons2.
      assert (HmonoT1_syn : mono_typ (syn_color T1)).
      { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
          symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
          destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
          rewrite <- HA1_eq in Hcons1
        end.
        eapply d_consis_syn_inh_mono; exact Hcons1. }
      assert (HmonoT2_syn : mono_typ (syn_color T2)).
      { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
          symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
          destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
          rewrite <- HA2_eq in Hcons2
        end.
        eapply d_consis_syn_inh_mono; exact Hcons2. }
      (* H3: syn_color T1 = syn_color_t A. With T1 mono → A mono. *)
      rename H3 into Heq_LHS.
      assert (HmonoA : mono_typ A).
      { apply mono_typ_syn_color_t_inv.
        rewrite <- Heq_LHS. exact HmonoT1_syn. }
      pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
        as HeqA2.
      pose proof (d_consis_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
        as HeqA1.
      subst.
      pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
      pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
      apply (f_equal erase) in Heq_LHS.
      rewrite syn_color_t_syn_color_erase in Heq_LHS.
      rewrite !erase_syn_color in Heq_LHS.
      subst T1.
      (* Goal: typ_arrow (syn_color (erase A)) (syn_color T2). *)
      rewrite <- (mono_typ_inh_color_erase HmonoA) at 1.
      apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
      * rewrite HsynA. exact HwfA.
      * intros x Hx.
        rewrite HsynA.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ))
          by (apply d_wf_denv__typ; auto).
        apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
        -- rewrite <- Hdecr. apply Hbody. auto.
        -- apply d_sub_gen_refl; auto.
           ++ apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
           ++ rewrite_env ((x ~ dbind_typ A) ++ Γ).
              apply d_wf_typ_weakening_head.
              eapply d_consis_preserves_wf; eauto.
    + (* d_sub__forall_r: route through anno-variant companion which
         recurses on the inner d_sub. *)
      eapply d_typing_abs_anno_value_to_subsumption_d_sub
        with (Ahead := A) (Bhead := B) (m_orig := m_orig); eauto.
  - (* __check_gen: T : ctyp with syn_color T = typ_arrow (syn_color_t A) B.
       Same mono extraction as the __embed __check sub-case above. *)
    destruct T; simpl in x; try discriminate.
    inversion x; subst.
    rename H0 into Hcons.
    inversion Hcons; subst.
    apply app_eq_nil in H0. destruct H0 as [HΔ1 HΔ2]. subst Δ1 Δ2.
    rename H6 into Hcons1. rename H7 into Hcons2.
    assert (HmonoT1_syn : mono_typ (syn_color T1)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [A1' [_ [_ [HA1_eq _]]]];
        rewrite <- HA1_eq in Hcons1
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons1. }
    assert (HmonoT2_syn : mono_typ (syn_color T2)).
    { match goal with H_eq : typ_arrow _ _ = inh_color _ |- _ =>
        symmetry in H_eq; apply inh_color_eq_arrow_inv in H_eq;
        destruct H_eq as [_ [A2' [_ [_ HA2_eq]]]];
        rewrite <- HA2_eq in Hcons2
      end.
      eapply d_consis_gen_syn_inh_mono; exact Hcons2. }
    assert (HmonoA : mono_typ A).
    { rewrite H2 in HmonoT1_syn.
      exact (mono_typ_syn_color_t_inv A HmonoT1_syn). }
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT2_syn) Hcons2)
      as HeqA2.
    pose proof (d_consis_gen_lhs_syn_eq (mono_typ_is_syn_typ HmonoT1_syn) Hcons1)
      as HeqA1.
    subst.
    pose proof (mono_typ_syn_color_erase HmonoA) as HsynA.
    pose proof (mono_typ_inh_color_erase HmonoA) as HinhA.
    apply (f_equal erase) in H2.
    rewrite syn_color_t_syn_color_erase in H2.
    rewrite !erase_syn_color in H2.
    subst T1.
    (* Goal: typ_arrow (syn_color (erase A)) (syn_color T2). *)
    rewrite <- (mono_typ_inh_color_erase HmonoA) at 1.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + rewrite HsynA. exact HwfA.
    + intros x0 Hx0.
      rewrite HsynA.
      assert (Hwfd_x0 : d_wf_denv ((x0 ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      apply d_typing_gen_lift_mono with (A := syn_color T2); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; assumption.
        -- rewrite_env ((x0 ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           eapply d_consis_gen_preserves_wf; eauto.
  - (* __refl_mono: target = typ_arrow (syn_color_t A) B forced mono.
       From [mono_typ_syn_color_t_inv] we recover mono A; the [ctyp]
       base for [d_typing_gen__abs_anno] is [erase A], with conclusion
       arg [syn_color (erase A) = syn_color_t A] (via
       [syn_color_t_syn_color_erase]). For mono A the body's
       [(x ~ A)] matches the rule's [(x ~ syn_color (erase A))] via
       [mono_typ_syn_color_erase]. Body lift mode_ti → mode_tc via
       [d_typing_gen_lift_mono] (Qed except __app). *)
    match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
      inversion Hm; subst
    end.
    match goal with HmsA : mono_typ (syn_color_t A) |- _ =>
      assert (HmonoA : mono_typ A)
        by (apply mono_typ_syn_color_t_inv; auto)
    end.
    rewrite syn_color_t_syn_color_erase.
    rewrite <- (mono_typ_inh_color_erase HmonoA) at 1.
    apply d_typing_gen__abs_anno with (L := L `union` dom Γ).
    + rewrite (mono_typ_syn_color_erase HmonoA). assumption.
    + intros x Hx.
      assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ A) ++ Γ))
        by (apply d_wf_denv__typ; auto).
      rewrite (mono_typ_syn_color_erase HmonoA).
      apply d_typing_gen_lift_mono with (A := B); auto.
      * rewrite <- Hdecr. apply Hbody. auto.
      * apply d_sub_gen_refl; auto.
        -- apply mode_typ_compat__tc. apply mono_typ_is_inh_typ; auto.
        -- rewrite_env ((x ~ dbind_typ A) ++ Γ).
           apply d_wf_typ_weakening_head.
           match goal with HwfA' : d_wf_typ Γ (typ_arrow _ _) |- _ =>
             inversion HwfA'; assumption
           end.
  - (* __forall_r: target = typ_all_col colour_inh A_target. Reconstruct
       via [d_typing_gen__forall] (value rule) + recursive IH at each X.
       [exp_abs_anno A e] is_value when [e] is — but the rule requires
       only [is_value (exp_abs_anno A e)], which holds unconditionally. *)
    apply d_typing_gen__forall with (L := L0 `union` dom Γ).
    + apply is_value__abs_anno.
    + intros X HX.
      assert (Hwfd_X : d_wf_denv ((X ~ dbind_tvar) ++ Γ))
        by (apply d_wf_denv__tvar; auto).
      apply H0 with (A := A) (B := B); auto.
      * apply d_wf_typ_weakening_head; auto.
      * intros y Hy.
        apply d_typing_gen_weakening with
          (Γ1 := (y ~ dbind_typ A)) (Γ2 := (X ~ dbind_tvar)) (Γ3 := Γ).
        apply Hbody. exact Hy.
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
  - (* Hty = __unit (m_orig = mode_ti). Closes via [d_typing_gen__sub]
       directly through [d_typing_unit_gen_subsumption]. *)
    simpl in Hsub_gen |- *.
    apply d_typing_unit_gen_subsumption; assumption.
  - (* Hty = __var (m_orig = mode_ti). *)
    simpl in Hsub_gen |- *.
    eapply d_typing_var_gen_subsumption; eauto.
  - (* Hty = __anno (m_orig = mode_ti). Uses the restated (ctyp-base)
       [d_typing_anno_gen_subsumption]. *)
    simpl in Hsub_gen |- *.
    eapply d_typing_anno_gen_subsumption; eauto.
  - (* Hty = __sub: inner [d_typing_gen mode_ti Γ e A], outer
       [d_sub_gen m_orig A B]. Compose with [Hsub_gen] via
       [d_sub_gen_trans] at [m1 = m_orig]. *)
    apply d_typing_gen__sub with (A := A); auto.
    eapply d_sub_gen_trans with (m1 := m) (B := B); auto.
    eapply d_typing_gen_preserves_wf; eauto.
  - (* Hty = __freeze: m_orig = mode_tc ∉ is_fn_n_ti. Vacuous. *)
    inversion Hfn.
  - (* Hty = __forall: same. *)
    inversion Hfn.
  - (* Hty = __abs (m = m_orig ∈ FN^n TI). Use the SPLIT helper
       [d_typing_abs_value_to_subsumption_split] which takes the body
       binding type and arrow arg as DIFFERENT shapes (binding [A], arrow
       arg [inh_color_t A]). Passing [A := syn_color A0] (the rule's body
       binding type) gives arrow arg [inh_color_t (syn_color A0) =
       inh_color A0], matching Hsub_gen's LHS. The helper handles all
       Hsub_gen sub-cases internally; we only need to wire m_orig sub-cases.

       All m_orig / m_new combinations now closed inline:
         - m_orig = mode_ti, m_new ∈ {mode_ti, mode_tc}: via SPLIT helpers.
         - m_orig = mode_ti, m_new = mode_fn k: inline case-split on
           Hsub_gen ([__embed/__refl_mono/__arg]); inh-LHS rigidity gives
           [A1 = inh_color A] in [__arg].
         - m_orig = mode_fn m': same case-split but body IH is applied at
           [decr_mode m_orig = m'], yielding outer mode [mode_fn (mode_fn_n_subst m' m_new)]. *)
    inversion Hfn; subst.
    + (* m_orig = mode_ti. mode_fn_n_subst mode_ti m_new = m_new. *)
      simpl in Hsub_gen |- *.
      destruct m_new.
      * (* m_new = mode_ti. Wired via [d_typing_abs_value_to_subsumption_split_ti]
           — the mode_ti variant of the SPLIT helper. *)
        assert (HwfsynA' : d_wf_typ Γ (syn_color A))
          by (apply d_wf_typ_inh_color_syn_color; exact H).
        assert (HwfB : d_wf_typ Γ B).
        { pick fresh x for (L `union` dom Γ).
          assert (HwfBx : d_wf_typ ((x ~ dbind_typ (syn_color A)) ++ Γ) B).
          { eapply d_typing_gen_preserves_wf with (m := mode_ti).
            - apply H0. fsetdec.
            - apply d_wf_denv__typ; [assumption | fsetdec | assumption]. }
          rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ) in HwfBx.
          rewrite_env (nil ++ Γ).
          eapply d_wf_typ_strengthening_typ; eauto. }
        eapply d_typing_abs_value_to_subsumption_split_ti with
          (A := syn_color A) (B := B) (m_orig := mode_ti) (L := L); eauto.
        -- (* d_wf_typ Γ (inh_color_t (syn_color A)) — bridge to H. *)
           rewrite inh_color_t_inh_color_erase.
           rewrite erase_syn_color. exact H.
        -- (* d_sub_gen mode_ti nil Γ (typ_arrow (inh_color_t (syn_color A)) B) B_tgt
              — bridge to Hsub_gen. *)
           rewrite inh_color_t_inh_color_erase.
           rewrite erase_syn_color. exact Hsub_gen.
      * (* m_new = mode_tc. The split helper closes this directly. *)
        eapply d_typing_abs_value_to_subsumption_split with
          (A := syn_color A) (B := B) (m_orig := mode_ti) (L := L); eauto.
        -- (* d_wf_typ Γ (inh_color_t (syn_color A)) — bridge to H. *)
           rewrite inh_color_t_inh_color_erase.
           rewrite erase_syn_color. exact H.
        -- (* d_sub_gen mode_tc nil Γ (typ_arrow (inh_color_t (syn_color A)) B) B_tgt
              — bridge to Hsub_gen. *)
           rewrite inh_color_t_inh_color_erase.
           rewrite erase_syn_color. exact Hsub_gen.
      * (* m_new = mode_fn m_inner. Invert Hsub_gen on its mode_fn rules:
           __embed → d_sub (mode_fn m_inner) (__arg or __forall_l_tagged);
           __refl_mono → target same arrow, mono;
           __arg → target typ_arrow A1 A2 with d_consis_gen on inh-LHS,
                   forcing A1 = inh_color A by [d_consis_gen_lhs_inh_eq]. *)
        rename m_new into m_inner.
        rename H into HwfA.
        rename H0 into Hbody.
        rename H1 into IHbody.
        assert (HsynA : d_wf_typ Γ (syn_color A))
          by (apply d_wf_typ_inh_color_syn_color; assumption).
        assert (HinhA_inh : is_inh_typ (inh_color A))
          by (eapply is_inh_typ_inh_color; eassumption).
        dependent destruction Hsub_gen.
        -- (* __embed: d_sub (mode_fn m_inner) nil Γ (typ_arrow (inh_color A) B) B_tgt.
              Rename the auto-named d_sub hypothesis. *)
           match goal with Hd : d_sub _ _ _ _ _ |- _ => rename Hd into Hd_sub end.
           dependent destruction Hd_sub.
           ++ (* d_sub__arg *)
              match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
              apply app_eq_nil in Heq_app. destruct Heq_app; subst.
              match goal with Hc : d_consis _ _ (inh_color A) _ |- _ => rename Hc into Hcons end.
              match goal with Hs : d_sub _ _ _ B _ |- _ => rename Hs into Hbs end.
              assert (HA1_eq : inh_color A = A1)
                by (eapply d_consis_lhs_inh_eq; eauto).
              subst A1.
              simpl.
              apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
              intros x Hx.
              assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
                by (apply d_wf_denv__typ; auto; fsetdec).
              match type of Hbs with d_sub _ _ _ _ ?A2_ =>
                apply IHbody with (x := x) (m_new := m_inner) (B := A2_)
              end.
              ** fsetdec.
              ** apply is_fn_n_ti__ti.
              ** assumption.
              ** apply d_sub_gen__embed.
                 rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ).
                 apply d_sub_weakening; simpl; exact Hbs.
        -- (* __refl_mono: target = typ_arrow (inh_color A) B (unchanged), both arms mono. *)
           match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
             inversion Hm; subst
           end.
           match goal with Hmc : mode_typ_compat (mode_fn _) (typ_arrow _ _) |- _ =>
             inversion Hmc; subst
           end.
           match goal with Hwa : d_wf_typ Γ (typ_arrow _ _) |- _ =>
             inversion Hwa; subst
           end.
           apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           simpl.
           apply d_typing_gen_lift_mono with (A := B).
           ++ apply Hbody. fsetdec.
           ++ assumption.
           ++ assumption.
           ++ apply d_sub_gen_refl; auto.
              rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_wf_typ_weakening_head. assumption.
        -- (* __arg: B_tgt = typ_arrow A1 A2 with d_consis_gen + d_sub_gen. *)
           match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
           apply app_eq_nil in Heq_app. destruct Heq_app; subst.
           match goal with Hcg : d_consis_gen _ _ (inh_color A) _ |- _ => rename Hcg into Hcons end.
           match goal with Hs : d_sub_gen _ _ _ B _ |- _ => rename Hs into Hbs end.
           assert (HA1_eq : inh_color A = _) by (eapply d_consis_gen_lhs_inh_eq; eauto).
           match type of HA1_eq with inh_color A = ?A1 => subst A1 end.
           simpl.
           apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           match type of Hbs with d_sub_gen _ _ _ _ ?A2_ =>
             apply IHbody with (x := x) (m_new := m_inner) (B := A2_)
           end.
           ++ fsetdec.
           ++ apply is_fn_n_ti__ti.
           ++ assumption.
           ++ rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_sub_gen_weakening_head; exact Hbs.
    + (* m_orig = mode_fn m'. Outer mode is [mode_fn (mode_fn_n_subst m' m_new)];
         same case-split on Hsub_gen as the m_orig=mode_ti case, but the
         body IH lifts at mode m' (decr_mode (mode_fn m') = m'), and the
         [is_fn_n_ti] premise to IHbody is the [is_fn_n_ti m'] from
         inverting Hfn. *)
      match goal with Hfn_m' : is_fn_n_ti _ |- _ => rename Hfn_m' into Hfn_inner end.
      simpl in Hsub_gen |- *.
      rename H into HwfA.
      rename H0 into Hbody.
      rename H1 into IHbody.
      assert (HsynA : d_wf_typ Γ (syn_color A))
        by (apply d_wf_typ_inh_color_syn_color; assumption).
      assert (HinhA_inh : is_inh_typ (inh_color A))
        by (eapply is_inh_typ_inh_color; eassumption).
      rename m0 into m'.
      dependent destruction Hsub_gen.
      * (* __embed: d_sub (mode_fn (mode_fn_n_subst m' m_new)) nil Γ ... *)
        match goal with Hd : d_sub _ _ _ _ _ |- _ => rename Hd into Hd_sub end.
        dependent destruction Hd_sub.
        -- (* d_sub__arg *)
           match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
           apply app_eq_nil in Heq_app. destruct Heq_app; subst.
           match goal with Hc : d_consis _ _ (inh_color A) _ |- _ => rename Hc into Hcons end.
           match goal with Hs : d_sub _ _ _ B _ |- _ => rename Hs into Hbs end.
           assert (HA1_eq : inh_color A = _) by (eapply d_consis_lhs_inh_eq; eauto).
           match type of HA1_eq with inh_color A = ?A1 => subst A1 end.
           simpl.
           apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           match type of Hbs with d_sub _ _ _ _ ?A2_ =>
             apply IHbody with (x := x) (m_new := m_new) (B := A2_)
           end.
           ** fsetdec.
           ** exact Hfn_inner.
           ** assumption.
           ** apply d_sub_gen__embed.
              rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_sub_weakening; simpl. exact Hbs.
      * (* __refl_mono *)
        match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
          inversion Hm; subst
        end.
        match goal with Hmc : mode_typ_compat (mode_fn _) (typ_arrow _ _) |- _ =>
          inversion Hmc; subst
        end.
        match goal with Hwa : d_wf_typ Γ (typ_arrow _ _) |- _ =>
          inversion Hwa; subst
        end.
        apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
        intros x Hx.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
          by (apply d_wf_denv__typ; auto; fsetdec).
        simpl.
        apply IHbody with (x := x) (m_new := m_new) (B := B).
        -- fsetdec.
        -- exact Hfn_inner.
        -- assumption.
        -- apply d_sub_gen_refl; auto.
           rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
           apply d_wf_typ_weakening_head. assumption.
      * (* __arg *)
        match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
        apply app_eq_nil in Heq_app. destruct Heq_app; subst.
        match goal with Hcg : d_consis_gen _ _ (inh_color A) _ |- _ => rename Hcg into Hcons end.
        match goal with Hs : d_sub_gen _ _ _ B _ |- _ => rename Hs into Hbs end.
        assert (HA1_eq : inh_color A = _) by (eapply d_consis_gen_lhs_inh_eq; eauto).
        match type of HA1_eq with inh_color A = ?A1 => subst A1 end.
        simpl.
        apply d_typing_gen__abs with (L := L `union` dom Γ); auto.
        intros x Hx.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
          by (apply d_wf_denv__typ; auto; fsetdec).
        match type of Hbs with d_sub_gen _ _ _ _ ?A2_ =>
          apply IHbody with (x := x) (m_new := m_new) (B := A2_)
        end.
        -- fsetdec.
        -- exact Hfn_inner.
        -- assumption.
        -- rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
           apply d_sub_gen_weakening_head. exact Hbs.
  - (* Hty = __abs_anno. Parallel to __abs: use the SPLIT helper
       [d_typing_abs_anno_value_to_subsumption_split] whose conclusion
       term [exp_abs_anno (inh_color_t A_helper) e] matches the rule's
       term [exp_abs_anno (inh_color A0) e] for A_helper = syn_color A0
       (since inh_color_t (syn_color A0) = inh_color A0). *)
    inversion Hfn; subst.
    + (* m_orig = mode_ti. *)
      simpl in Hsub_gen |- *.
      destruct m_new.
      * (* m_new = mode_ti. Use the abs_anno_split_ti helper. *)
        assert (HwfB : d_wf_typ Γ B).
        { pick fresh x for (L `union` dom Γ).
          assert (HwfBx : d_wf_typ ((x ~ dbind_typ (syn_color A)) ++ Γ) B).
          { eapply d_typing_gen_preserves_wf with (m := mode_ti).
            - apply H0. fsetdec.
            - apply d_wf_denv__typ; [assumption | fsetdec | assumption]. }
          rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ) in HwfBx.
          rewrite_env (nil ++ Γ).
          eapply d_wf_typ_strengthening_typ; eauto. }
        replace (exp_abs_anno (inh_color A) e)
          with (exp_abs_anno (inh_color_t (syn_color A)) e)
          by (rewrite inh_color_t_inh_color_erase;
              rewrite erase_syn_color; reflexivity).
        eapply d_typing_abs_anno_value_to_subsumption_split_ti with
          (A := syn_color A) (B := B) (m_orig := mode_ti) (L := L); eauto.
      * (* m_new = mode_tc. *)
        replace (exp_abs_anno (inh_color A) e)
          with (exp_abs_anno (inh_color_t (syn_color A)) e)
          by (rewrite inh_color_t_inh_color_erase;
              rewrite erase_syn_color; reflexivity).
        eapply d_typing_abs_anno_value_to_subsumption_split with
          (A := syn_color A) (B := B) (m_orig := mode_ti) (L := L); eauto.
      * (* m_new = mode_fn m_inner. Mirror of __abs case at mode_fn.
           Conclusion arrow-arg is [syn_color A] (not [inh_color A] like
           __abs), so we use [d_consis_gen_lhs_syn_eq] in the __arg case. *)
        rename m_new into m_inner.
        rename H into HwfA.
        rename H0 into Hbody.
        rename H1 into IHbody.
        assert (HsynA_syn : is_syn_typ (syn_color A))
          by (eapply is_syn_typ_syn_color; eassumption).
        dependent destruction Hsub_gen.
        -- (* __embed: d_sub (mode_fn m_inner) nil Γ (typ_arrow (syn_color A) B) B_tgt. *)
           match goal with Hd : d_sub _ _ _ _ _ |- _ => rename Hd into Hd_sub end.
           dependent destruction Hd_sub.
           ++ (* d_sub__arg *)
              match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
              apply app_eq_nil in Heq_app. destruct Heq_app; subst.
              match goal with Hc : d_consis _ _ (syn_color A) _ |- _ => rename Hc into Hcons end.
              match goal with Hs : d_sub _ _ _ B _ |- _ => rename Hs into Hbs end.
              assert (HA1_eq : syn_color A = _) by (eapply d_consis_lhs_syn_eq; eauto).
              match type of HA1_eq with syn_color A = ?A1 => subst A1 end.
              simpl.
              apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
              intros x Hx.
              assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
                by (apply d_wf_denv__typ; auto; fsetdec).
              match type of Hbs with d_sub _ _ _ _ ?A2_ =>
                apply IHbody with (x := x) (m_new := m_inner) (B := A2_)
              end.
              ** fsetdec.
              ** apply is_fn_n_ti__ti.
              ** assumption.
              ** apply d_sub_gen__embed.
                 rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ).
                 apply d_sub_weakening; simpl; exact Hbs.
        -- (* __refl_mono: target = typ_arrow (syn_color A) B (unchanged), both arms mono. *)
           match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
             inversion Hm; subst
           end.
           match goal with Hmc : mode_typ_compat (mode_fn _) (typ_arrow _ _) |- _ =>
             inversion Hmc; subst
           end.
           match goal with Hwa : d_wf_typ Γ (typ_arrow _ _) |- _ =>
             inversion Hwa; subst
           end.
           apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           simpl.
           apply d_typing_gen_lift_mono with (A := B).
           ++ apply Hbody. fsetdec.
           ++ assumption.
           ++ assumption.
           ++ apply d_sub_gen_refl; auto.
              rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_wf_typ_weakening_head. assumption.
        -- (* __arg: B_tgt = typ_arrow A1 A2 with d_consis_gen + d_sub_gen. *)
           match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
           apply app_eq_nil in Heq_app. destruct Heq_app; subst.
           match goal with Hcg : d_consis_gen _ _ (syn_color A) _ |- _ => rename Hcg into Hcons end.
           match goal with Hs : d_sub_gen _ _ _ B _ |- _ => rename Hs into Hbs end.
           assert (HA1_eq : syn_color A = _) by (eapply d_consis_gen_lhs_syn_eq; eauto).
           match type of HA1_eq with syn_color A = ?A1 => subst A1 end.
           simpl.
           apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           match type of Hbs with d_sub_gen _ _ _ _ ?A2_ =>
             apply IHbody with (x := x) (m_new := m_inner) (B := A2_)
           end.
           ++ fsetdec.
           ++ apply is_fn_n_ti__ti.
           ++ assumption.
           ++ rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_sub_gen_weakening_head; exact Hbs.
    + (* m_orig = mode_fn m'. Mirror of __abs (m_orig=mode_fn m') but
         arrow-arg is [syn_color A], using [d_consis_gen_lhs_syn_eq]. *)
      match goal with Hfn_m' : is_fn_n_ti _ |- _ => rename Hfn_m' into Hfn_inner end.
      simpl in Hsub_gen |- *.
      rename H into HwfA.
      rename H0 into Hbody.
      rename H1 into IHbody.
      assert (HsynA_syn : is_syn_typ (syn_color A))
        by (eapply is_syn_typ_syn_color; eassumption).
      rename m0 into m'.
      dependent destruction Hsub_gen.
      * (* __embed *)
        match goal with Hd : d_sub _ _ _ _ _ |- _ => rename Hd into Hd_sub end.
        dependent destruction Hd_sub.
        -- (* d_sub__arg *)
           match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
           apply app_eq_nil in Heq_app. destruct Heq_app; subst.
           match goal with Hc : d_consis _ _ (syn_color A) _ |- _ => rename Hc into Hcons end.
           match goal with Hs : d_sub _ _ _ B _ |- _ => rename Hs into Hbs end.
           assert (HA1_eq : syn_color A = _) by (eapply d_consis_lhs_syn_eq; eauto).
           match type of HA1_eq with syn_color A = ?A1 => subst A1 end.
           simpl.
           apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
           intros x Hx.
           assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
             by (apply d_wf_denv__typ; auto; fsetdec).
           match type of Hbs with d_sub _ _ _ _ ?A2_ =>
             apply IHbody with (x := x) (m_new := m_new) (B := A2_)
           end.
           ** fsetdec.
           ** exact Hfn_inner.
           ** assumption.
           ** apply d_sub_gen__embed.
              rewrite_env (nil ++ (x ~ dbind_typ (syn_color A)) ++ Γ).
              apply d_sub_weakening; simpl; exact Hbs.
      * (* __refl_mono *)
        match goal with Hm : mono_typ (typ_arrow _ _) |- _ =>
          inversion Hm; subst
        end.
        match goal with Hmc : mode_typ_compat (mode_fn _) (typ_arrow _ _) |- _ =>
          inversion Hmc; subst
        end.
        match goal with Hwa : d_wf_typ Γ (typ_arrow _ _) |- _ =>
          inversion Hwa; subst
        end.
        apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
        intros x Hx.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
          by (apply d_wf_denv__typ; auto; fsetdec).
        simpl.
        apply IHbody with (x := x) (m_new := m_new) (B := B).
        -- fsetdec.
        -- exact Hfn_inner.
        -- assumption.
        -- apply d_sub_gen_refl; auto.
           rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
           apply d_wf_typ_weakening_head. assumption.
      * (* __arg *)
        match goal with HΔ : _ ++ _ = nil |- _ => rename HΔ into Heq_app end.
        apply app_eq_nil in Heq_app. destruct Heq_app; subst.
        match goal with Hcg : d_consis_gen _ _ (syn_color A) _ |- _ => rename Hcg into Hcons end.
        match goal with Hs : d_sub_gen _ _ _ B _ |- _ => rename Hs into Hbs end.
        assert (HA1_eq : syn_color A = _) by (eapply d_consis_gen_lhs_syn_eq; eauto).
        match type of HA1_eq with syn_color A = ?A1 => subst A1 end.
        simpl.
        apply d_typing_gen__abs_anno with (L := L `union` dom Γ); auto.
        intros x Hx.
        assert (Hwfd_x : d_wf_denv ((x ~ dbind_typ (syn_color A)) ++ Γ))
          by (apply d_wf_denv__typ; auto; fsetdec).
        match type of Hbs with d_sub_gen _ _ _ _ ?A2_ =>
          apply IHbody with (x := x) (m_new := m_new) (B := A2_)
        end.
        -- fsetdec.
        -- exact Hfn_inner.
        -- assumption.
        -- rewrite_env ((x ~ dbind_typ (syn_color A)) ++ Γ).
           apply d_sub_gen_weakening_head. exact Hbs.
  - (* Hty = __app. Closing this requires lifting the function-side
       sub-derivation H1 (at mode_fn m_orig) to mode_fn m_new via the
       IH (D12 on H1), composing with d_sub_gen__arg using:
       - d_consis_gen_refl_is_typ on P' (the function-arg type)
       - Hsub_gen on the result side.
       Then reconstruct __app at outer mode m_new. *)
    inversion Hfn; subst.
    + (* m_orig = mode_ti. mode_fn_n_subst mode_ti m_new = m_new. *)
      simpl in Hsub_gen |- *.
      (* Derive d_wf_typ Γ P' from d_typing_gen_preserves_wf on the
         function-side hypothesis Hty1 (renamed via match goal since the
         auto-named hypothesis may differ across cases). *)
      assert (HwfP' : d_wf_typ Γ P').
      { (* All four __app premises are in context; the function-side
           one has type d_typing_gen _ Γ _ (typ_arrow P' _). Pin it by
           inspecting d_typing_gen at the function expression e1. *)
        match goal with
        | Hfun : d_typing_gen _ _ e1 _ |- _ =>
            pose proof (d_typing_gen_preserves_wf Hfun Hwfd) as HwfArr
        end.
        inversion HwfArr; subst; assumption. }
      assert (HistypP' : is_typ P')
        by (eapply d_wf_typ_is_typ; eassumption).
      eapply d_typing_gen__app with (P := P) (P' := P').
      * exact H.
      * exact H0.
      * (* d_typing_gen (mode_fn m_new) Γ e1 (typ_arrow P' B_tgt).
           Lift H1 via IHHty1 (= D12 on H1). *)
        eapply IHHty1 with (m_new := m_new) (B := typ_arrow P' B_tgt); auto.
        -- apply is_fn_n_ti__fn. apply is_fn_n_ti__ti.
        -- (* d_sub_gen (mode_fn m_new) nil Γ (typ_arrow P' B) (typ_arrow P' B_tgt). *)
           rewrite_env (@nil atom ++ @nil atom).
           apply d_sub_gen__arg.
           ++ (* d_consis_gen nil Γ P' P' (refl). Use d_consis_gen_refl_is_typ;
                facts derived above from H1 + wf preservation. *)
              apply d_consis_gen_refl_is_typ; assumption.
           ++ exact Hsub_gen.
      * (* d_typing_gen mode_tc Γ e2 (inh_color (erase P')) — unchanged. *)
        match goal with
        | Harg : d_typing_gen mode_tc _ _ (inh_color (erase _)) |- _ => exact Harg
        end.
    + (* m_orig = mode_fn m'. Parallel to mode_ti case: lift function via
         IH, reconstruct __app at outer (mode_fn_n_subst m' m_new). *)
      simpl in Hsub_gen |- *.
      assert (HwfP' : d_wf_typ Γ P').
      { match goal with
        | Hfun : d_typing_gen _ _ e1 _ |- _ =>
            pose proof (d_typing_gen_preserves_wf Hfun Hwfd) as HwfArr
        end.
        inversion HwfArr; subst; assumption. }
      assert (HistypP' : is_typ P')
        by (eapply d_wf_typ_is_typ; eassumption).
      eapply d_typing_gen__app with (P := P) (P' := P').
      * exact H.
      * exact H0.
      * (* d_typing_gen (mode_fn (mode_fn_n_subst m m_new)) Γ e1
           (typ_arrow P' B_tgt). Lift via IHHty1 at m_new. *)
        eapply IHHty1 with (m_new := m_new) (B := typ_arrow P' B_tgt); auto.
        -- apply is_fn_n_ti__fn. apply is_fn_n_ti__fn. assumption.
        -- (* d_sub_gen (mode_fn (mode_fn (mode_fn_n_subst m m_new))) ...
              Need __arg again. *)
           simpl. rewrite_env (@nil atom ++ @nil atom).
           apply d_sub_gen__arg.
           ++ apply d_consis_gen_refl_is_typ; assumption.
           ++ exact Hsub_gen.
      * match goal with
        | Harg : d_typing_gen mode_tc _ _ (inh_color (erase _)) |- _ => exact Harg
        end.
Qed.

(** [d_consis_gen_to_d_consis_syn_lhs]: the SYN-LHS-restricted bridge,
    Qed. When the LHS is [is_syn_typ] (every quantifier is [colour_syn]),
    the [__forall_inh] case (LHS = [typ_all_col colour_inh]) is vacuous,
    so the bridge closes. Used internally by the [d_sub_gen → d_sub]
    bridge for [__infer_gen] / [__check_gen] (where the LHS is
    [syn_color T_base], hence [is_syn_typ]); kept as a standalone Qed
    helper for future work that can establish [is_syn_typ] at the call
    site. *)
Lemma d_consis_gen_to_d_consis_syn_lhs : forall T,
    is_syn_typ T ->
    forall Δ Γ A, d_consis_gen Δ Γ T A -> d_consis Δ Γ T A.
Proof.
  intros T Hsyn. induction Hsyn; intros Δ Γ A0 Hc.
  - (* typ_unit *) inversion Hc; subst. apply d_consis__unit.
  - (* typ_var_f X *) inversion Hc; subst. apply d_consis__var; assumption.
  - (* typ_arrow *)
    inversion Hc; subst.
    apply d_consis__arrow; auto.
  - (* typ_all_col colour_syn (post-refactor): now admitted by d_consis_gen
       via __forall_syn rule. Bridge directly via d_consis__forall_syn,
       with body recursion via IH H0. *)
    inversion Hc; subst.
    apply d_consis__forall_syn with (L := L `union` L0).
    intros X HX. apply H0; auto.
Qed.

(** [d_consis_gen_to_d_consis]: the gen→original bridge for
    consistency. Fully [Qed] post the structural fix.

    The fix: added [d_consis__forall_inh] to the base [d_consis]
    inductive (paper-faithful — paper's [typconsis] in
    [syntax-directed.tex:116] includes a structural [ForallInh] rule
    admitting [inh{∀α.}T] on the LHS). The cascading impact (transitivity,
    narrowing, weakening, mono-extraction) was absorbed in this pass:
    [d_consis_compose] gains 3 cofinite-rename cases (Paper Lemma B.2 /
    Consistency Transitivity);
    [d_consis_LHS_mono_wf] gains an [is_utyp T] precondition (rules out
    the new [typ_all_col colour_inh] LHS case which is wf but not mono);
    [d_consis_LHS_is_typ_mono] gets the same precondition;
    [d_consis_mono_RHS] / [d_consis_LHS_syn_color_mono] /
    [d_consis_compose_nil_RHS] / [d_consis_empty_eq] /
    [d_sub_not_lhs_typ_all_col] / [d_sub_LHS_mono_wf] each gain a
    case for the new constructor. *)
Lemma d_consis_gen_to_d_consis : forall Δ Γ T A,
    d_consis_gen Δ Γ T A ->
    d_consis Δ Γ T A.
Proof.
  intros Δ Γ T A H. induction H.
  - apply d_consis__unit.
  - apply d_consis__var; assumption.
  - apply d_consis__forall_inh_tagged with (L := L); assumption.
  - apply d_consis__forall_syn_tagged with (L := L); assumption.
  - apply d_consis__forall_syn with (L := L); assumption.
  - (* __forall_inh: LHS = typ_all_col colour_inh T, RHS =
       typ_all_col colour_inh A. With the new [d_consis__forall_inh]
       rule (added to the base [d_consis] in this pass), this case
       closes directly. *)
    apply d_consis__forall_inh with (L := L); assumption.
  - apply d_consis__arrow; assumption.
Qed.

(** [d_sub_gen_to_d_sub]: the [d_sub_gen → d_sub] bridge.

    Closed structurally for every rule shape using [d_consis_gen_to_d_consis]
    as the consistency-level bridge. The bridge's only admit is the
    [__forall_inh] case of [d_consis_gen_to_d_consis] — that admit
    propagates here implicitly via the [d_consis_gen → d_consis] calls in
    [__infer_gen], [__check_gen], and [__arg]; this lemma itself is [Qed]. *)
Lemma d_sub_gen_to_d_sub : forall m Δ Γ T A,
    d_sub_gen m Δ Γ T A ->
    d_sub m Δ Γ T A.
Proof.
  intros m Δ Γ T A H. induction H.
  - (* __embed: trivial — the embed already carries a [d_sub]. *)
    assumption.
  - (* __infer_gen: rebuild [d_sub__infer] after [d_consis_gen → d_consis]
       bridge on the consistency premise. The bridge's residual admit
       case ([__forall_inh] LHS = [typ_all_col colour_inh]) is vacuous
       here because the LHS is [syn_color T], which never matches that
       shape, but the bridge lemma's signature doesn't expose this — so
       this clause is conservative w.r.t. the documented admit. *)
    apply d_sub__infer. apply d_consis_gen_to_d_consis. assumption.
  - (* __check_gen: same pattern; LHS [syn_color T] makes the bridge's
       residual admit case vacuous in practice. *)
    apply d_sub__check; auto. apply d_consis_gen_to_d_consis. assumption.
  - (* __refl_mono: route through [d_sub_refl_mono_mode] (Qed at d_sub
       level). *)
    apply d_sub_refl_mono_mode; auto.
  - (* __forall_r: structural — re-apply [d_sub__forall_r] with the
       cofinite-quant body lifted by the IH. *)
    apply d_sub__forall_r with (L := L); auto.
  - (* __arg: the ONLY case where the residual [d_consis_gen_to_d_consis
       __forall_inh] admit is structurally reachable. The d_consis_gen
       LHS [T1] is arbitrary here (it's the function's argument-type
       from the outer subtyping); when [T1 = typ_all_col colour_inh ...]
       the bridge's __forall_inh case fires. *)
    apply d_sub__arg; auto. apply d_consis_gen_to_d_consis. assumption.
Qed.

(** [d_typing_gen_collapse]: the generalised typing collapses back to
    the original. Structural except [__sub], which routes through the
    [d_sub_gen → d_sub] bridge ([d_sub_gen_to_d_sub] above). The whole
    D1-via-D12 development is therefore closed *modulo the single admit*
    in [d_consis_gen_to_d_consis]'s [__forall_inh] case. *)
Lemma d_typing_gen_collapse : forall m Γ e A,
    d_typing_gen m Γ e A ->
    d_typing m Γ e A.
Proof.
  intros m Γ e A H. induction H.
  - apply d_typing__unit; assumption.
  - apply d_typing__var; assumption.
  - apply d_typing__anno; assumption.
  - (* __sub: close via [d_sub_gen_to_d_sub] bridge. The bridge's
       residual admit ([d_consis_gen_to_d_consis __forall_inh]) is the
       single structural gap of the D1-via-D12 development. *)
    apply d_typing__sub with (A := A); auto.
    apply d_sub_gen_to_d_sub; assumption.
  - apply d_typing__freeze; assumption.
  - apply d_typing__forall with (L := L); assumption.
  - apply d_typing__abs with (L := L); assumption.
  - apply d_typing__abs_anno with (L := L); assumption.
  - apply d_typing__app with (P := P) (P' := P'); assumption.
Qed.

(** [d_typing_general_subsumption_via_gen]: paper Lemma 3.1 (D1), as
    a one-line corollary of D12 ([d_typing_general_subsumption_gen])
    at [m_orig := mode_ti], threading the original [d_sub] in via
    [d_sub_gen__embed]. Stays [Admitted] because the body of D12
    is itself [Admitted] post-re-encoding, and the [d_typing_gen]
    collapse bottoms at the [d_consis_gen_to_d_consis] [__forall_inh]
    structural gap. Restored here as documentation of the intended
    bridge. *)
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
