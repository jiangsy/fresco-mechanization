Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.prop_tag.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.consistency.prop_precision_recovery.
Require Import src.fresco.algo_decl.prop_subtyping.

Set Implicit Arguments.

Fixpoint pskl_no_forall (P : pskl) : Prop :=
  match P with
  | pskl_all_syn _ => False
  | pskl_arrow P1 P2 => pskl_no_forall P1 /\ pskl_no_forall P2
  | pskl_univ_ghost P0 => pskl_no_forall P0
  | _ => True
  end.

Lemma pskl_no_forall_inh_eq_syn : forall P,
  pskl_no_forall P -> pskl_to_bskl_inh P = pskl_to_bskl_syn P.
Proof.
  induction P; simpl; intros H; try reflexivity.
  - destruct H as [H1 H2]. rewrite IHP1, IHP2; auto.
  - contradiction.
  - rewrite IHP; auto.
Qed.

Lemma d_tags_empty_no_forall : forall Ψ ψ,
  d_tags_skl Ψ ψ -> Ψ [=] empty -> pskl_no_forall (uskl_to_pskl ψ).
Proof.
  intros Ψ ψ H. induction H; intros HΨ; simpl.
  - exact I.
  - exact I.
  - split; [ apply IHd_tags_skl1 | apply IHd_tags_skl2 ]; fsetdec.
  - fsetdec.
  - exact I.
  - apply IHd_tags_skl; assumption.
Qed.

Lemma d_tags_skl_unit_inv : forall Ψ,
  d_tags_skl Ψ uskl_unit -> Ψ [=] empty.
Proof. intros Ψ H. inversion H; subst; auto. Qed.

Lemma d_tags_skl_var_inv : forall Ψ α,
  d_tags_skl Ψ (uskl_var_f α) -> Ψ [=] empty.
Proof. intros Ψ α H. inversion H; subst; auto. Qed.

Lemma d_tags_skl_arrow_inv : forall Ψ ψ1 ψ2,
  d_tags_skl Ψ (uskl_arrow ψ1 ψ2) ->
  exists Ψ1 Ψ2, d_tags_skl Ψ1 ψ1 /\ d_tags_skl Ψ2 ψ2
             /\ Ψ1 ∩ Ψ2 [=] empty /\ Ψ [=] Ψ1 `union` Ψ2.
Proof. intros Ψ ψ1 ψ2 H. inversion H; subst. eauto 10. Qed.

Lemma d_tags_skl_all_tag_inv : forall Ψ ε ψ,
  d_tags_skl Ψ (uskl_all_tag ε ψ) ->
  exists L Ψ0,
    (forall α, α `notin` L ->
       d_tags_skl Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f α)))
    /\ ε `notin` Ψ0 /\ Ψ [=] add ε Ψ0.
Proof. intros Ψ ε ψ H. inversion H; subst. eauto 8. Qed.

Lemma d_tags_skl_dot_univ_ghost_inv : forall Ψ ψ,
  d_tags_skl Ψ (uskl_dot_univ_ghost ψ) -> d_tags_skl Ψ ψ.
Proof. intros Ψ ψ H. inversion H; subst; auto. Qed.

Lemma d_tags_skl_dot_ghost_inv : forall Ψ,
  d_tags_skl Ψ uskl_dot_ghost -> Ψ [=] empty.
Proof. intros Ψ H; inversion H; subst; auto. Qed.

Lemma a_tags_sort_d_tags : forall NM Ψ ψ,
  a_tags_sort NM Ψ ψ -> d_tags_skl Ψ ψ.
Proof. intros NM Ψ ψ H. inversion H; auto. Qed.

Lemma a_tags_sort_psi_cong : forall NM Ψ Ψ' ψ,
  a_tags_sort NM Ψ ψ -> Ψ [=] Ψ' -> a_tags_sort NM Ψ' ψ.
Proof.
  intros NM Ψ Ψ' ψ H Heq. inversion H; subst;
    [ apply a_tags_sort__sk | apply a_tags_sort__ty ]; auto;
    eapply d_tags_skl_psi_cong; eauto.
Qed.

Lemma a_tags_sort_arrow_inv : forall NM Ψ ψ1 ψ2,
  a_tags_sort NM Ψ (uskl_arrow ψ1 ψ2) ->
  exists Ψ1 Ψ2, a_tags_sort NM Ψ1 ψ1 /\ a_tags_sort NM Ψ2 ψ2
             /\ Ψ1 ∩ Ψ2 [=] empty /\ Ψ [=] Ψ1 `union` Ψ2.
Proof.
  intros NM Ψ ψ1 ψ2 H. inversion H; subst;
    match goal with Ht : is_dskl _ |- _ => inversion Ht; subst end;
    match goal with Hd : d_tags_skl _ (uskl_arrow _ _) |- _ =>
      apply d_tags_skl_arrow_inv in Hd as [Ψa [Ψb [Hd1 [Hd2 [Hdisj Hun]]]]] end.
  - exists Ψa, Ψb. repeat apply conj; try assumption; apply a_tags_sort__sk; auto.
  - match goal with Hg : uskl_ghost_free (uskl_arrow _ _) |- _ =>
      inversion Hg; subst end.
    exists Ψa, Ψb. repeat apply conj; try assumption; apply a_tags_sort__ty; auto.
Qed.

Lemma a_tags_sort_all_tag_inv : forall NM Ψ ε ψ,
  a_tags_sort NM Ψ (uskl_all_tag ε ψ) ->
  exists L Ψ0,
    (forall α, α `notin` L ->
       a_tags_sort NM Ψ0 (open_uskl_wrt_uskl ψ (uskl_var_f α)))
    /\ ε `notin` Ψ0 /\ Ψ [=] add ε Ψ0.
Proof.
  intros NM Ψ ε ψ H. inversion H; subst.
  -
    match goal with Hit : is_dskl (uskl_all_tag _ _) |- _ =>
      inversion Hit; subst end.
    match goal with Hd : d_tags_skl _ (uskl_all_tag _ _) |- _ =>
      apply d_tags_skl_all_tag_inv in Hd as [Ld [Ψ0 [Hd0 [Hεt Hun]]]] end.
    match goal with Hit0 : forall α, α `notin` ?Li -> is_dskl _ |- _ =>
      exists (Li `union` Ld), Ψ0; repeat apply conj; try assumption;
      intros α Hα; apply a_tags_sort__sk; [ apply Hit0 | apply Hd0 ]; fsetdec end.
  -
    match goal with Hit : is_dskl (uskl_all_tag _ _) |- _ =>
      inversion Hit; subst end.
    match goal with Hd : d_tags_skl _ (uskl_all_tag _ _) |- _ =>
      apply d_tags_skl_all_tag_inv in Hd as [Ld [Ψ0 [Hd0 [Hεt Hun]]]] end.
    match goal with Hgf : uskl_ghost_free (uskl_all_tag _ _) |- _ =>
      inversion Hgf; subst end.
    match goal with
    | Hit0 : forall α, α `notin` ?Li -> is_dskl _,
      Hgf0 : forall α, α `notin` ?Lg -> uskl_ghost_free _ |- _ =>
      exists (Li `union` Lg `union` Ld), Ψ0; repeat apply conj; try assumption;
      intros α Hα;
      apply a_tags_sort__ty; [ apply Hit0 | apply Hd0 | apply Hgf0 ]; fsetdec
    end.
Qed.

Lemma ad_pat_consis_strip_tags : forall Ψt Θ ψa Q,
  {{ Ψt ⨟ Θ ⊢ˢ ψa ∼ Q }}ad ->
  {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (uskl_to_pskl ψa)) ∼ Q }}ad.
Proof.
  intros Ψt Θ ψa Q H. induction H; simpl.
  - apply ad_pat_consis__unit. reflexivity.
  - apply ad_pat_consis__var; [ reflexivity | assumption ].
  - eapply ad_pat_consis__arrow;
      [ exact IHad_pat_consis1 | exact IHad_pat_consis2 | fsetdec ].
  - eapply ad_pat_consis__forall_inh_untagged with (L := L).
    intros α Hα. rewrite <- strip_uskl_open. exact (H0 α Hα).
  - eapply ad_pat_consis__forall_inh_untagged with (L := L).
    intros α Hα. rewrite <- strip_uskl_open. exact (H0 α Hα).
  - eapply ad_pat_consis__forall_syn with (L := L).
    intros α Hα. rewrite <- strip_uskl_open. exact (H0 α Hα).
  - eapply ad_pat_consis__forall_syn with (L := L).
    intros α Hα. rewrite <- strip_uskl_open. exact (H0 α Hα).
  - change bskl_ghost with (pskl_to_bskl_inh pskl_ghost).
    apply ad_pat_consis__ghost; [ reflexivity ].
  -
    apply ad_pat_consis__univ_ghost. exact IHad_pat_consis.
  - apply ad_pat_consis__ghost; [ reflexivity ].
  - apply ad_pat_consis__univ_ghost. exact IHad_pat_consis.
  - eapply ad_pat_consis__univ_ghost_inh with (L := L).
    intros α Hα. specialize (H0 α Hα). simpl in H0. exact H0.
  - apply ad_pat_consis__univ_ghost_drop. exact IHad_pat_consis.
  - eapply ad_pat_consis__flex_l; [ exact H | ].
    rewrite uskl_to_pskl_ptyp_to_uskl_syn, pskl_to_uskl_ptyp in IHad_pat_consis.
    exact IHad_pat_consis.
  - eapply ad_pat_consis__flex_r; [ exact H | exact IHad_pat_consis ].
Qed.

Lemma wf_open_of_all : forall Θ Δ Q0 α,
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ)
    ⊢ₚₛ open_pskl_wrt_pskl (bskl_to_pskl Q0) (pskl_var_f α) }}a ->
  {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ
    ⊢ₚₛ bskl_to_pskl (open_bskl_wrt_bskl Q0 (bskl_var_f α)) }}a.
Proof.
  intros Θ Δ Q0 α Hb.
  rewrite bskl_to_pskl_open.
  eapply a_wf_pskl_delta_mono; [ exact Hb | ].
  intros β2 _ HW. clear - HW. fsetdec.
Qed.

Lemma mono_ptyp_pskl_no_forall : forall τ,
  mono_ptyp τ -> pskl_no_forall (ptyp_to_pskl τ).
Proof. intros τ Hm; induction Hm; simpl; auto. Qed.

Lemma inh_eq_syn_no_forall : forall A B,
  pskl_to_bskl_inh A = pskl_to_bskl_syn B -> pskl_no_forall A.
Proof.
  induction A; intros B H; destruct B; simpl in H; try discriminate;
    simpl; auto.
  - inversion H. split; [ eapply IHA1 | eapply IHA2 ]; eauto.
  - inversion H. eapply IHA; eauto.
Qed.

Lemma consis_concrete_target_inh : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall P, R = pskl_to_uskl P ->
  pskl_no_forall P ->
  Ψ [=] empty /\ pskl_to_bskl_inh (bskl_to_pskl Q) = Q.
Proof.
  intros Ψ Θ R Q Hc; induction Hc; intros Hwfa P0 HR Hnf.
  -   split; [ exact H | reflexivity ].
  -    split; [ exact H | reflexivity ].
  -
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. inversion HR; subst.
    simpl in Hnf; destruct Hnf as [Hnf1 Hnf2].
    destruct (IHHc1 Hwfa _ eq_refl Hnf1) as [HΨ1 Heq1].
    destruct (IHHc2 Hwfa _ eq_refl Hnf2) as [HΨ2 Heq2].
    split; [ fsetdec | simpl; rewrite Heq1, Heq2; reflexivity ].
  -
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ]; simpl in HR; discriminate HR.
  -
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. simpl in Hnf; contradiction.
  -
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ]; simpl in HR; discriminate HR.
  -
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. simpl in Hnf; contradiction.
  -
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ]; simpl in HR; discriminate HR.
  -
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ]; simpl in HR; discriminate HR.
  -
    split; [ exact H
           | simpl; rewrite bskl_to_pskl_pskl_to_bskl_inh; reflexivity ].
  -
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. inversion HR; subst.
    simpl in Hnf.
    destruct (IHHc Hwfa _ eq_refl Hnf) as [HΨ0 Heq0].
    split; [ exact HΨ0 | simpl; rewrite Heq0; reflexivity ].
  -
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. inversion HR; subst.
    simpl in Hnf.
    pick fresh α for (L `union` dom Θ `union` ftvar_in_bskl Q).
    assert (HwfX : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ fsetdec | exact Hwfa ]).
    destruct (H0 α ltac:(solve_notin_auto) HwfX (pskl_univ_ghost Pt) eq_refl Hnf)
      as [HΨα HeqX].
    split; [ exact HΨα | ].
    simpl. f_equal.
    eapply open_bskl_wrt_bskl_inj with (α1 := α).
    + rewrite ftvar_in_bskl_inh, ftvar_bskl_to_pskl. fsetdec.
    + fsetdec.
    + rewrite <- pskl_to_bskl_inh_open, <- bskl_to_pskl_open. exact HeqX.
  -
    destruct P0 as [ | n | αv | Pl Pr | Pq | | Pt ];
      simpl in HR; try discriminate HR. inversion HR; subst.
    simpl in Hnf.
    destruct (IHHc Hwfa _ eq_refl Hnf) as [HΨ0 Heq0].
    split; [ exact HΨ0 | exact Heq0 ].
  -
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Heq : ptyp_to_uskl_syn τ = pskl_to_uskl (ptyp_to_pskl τ))
      by (symmetry; apply pskl_to_uskl_ptyp).
    assert (Hnf' : pskl_no_forall (ptyp_to_pskl τ))
      by (apply mono_ptyp_pskl_no_forall; auto).
    destruct (IHHc Hwfa (ptyp_to_pskl τ) Heq Hnf') as [HΨ Heqq].
    split; [ exact HΨ | exact Heqq ].
  -
    destruct (IHHc Hwfa P0 HR Hnf) as [HΨ _].
    split; [ exact HΨ | reflexivity ].
Qed.

Lemma ad_pat_consis_ftag_sub : forall Ψ Θ R' Q,
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ Q }}ad ->
  Ψ [<=] ftag_in_uskl R'.
Proof.
  intros Ψ Θ R' Q H; induction H; simpl; try fsetdec.
  -
    match goal with |- _ [<=] add _ (ftag_in_uskl ?R) =>
      pick fresh α for L;
      pose proof (H0 α ltac:(solve_notin_auto)) as Hα;
      pose proof (ftag_in_uskl_open_var R α) as Hov
    end; fsetdec.
  -
    match goal with |- _ [<=] ftag_in_uskl ?R =>
      pick fresh α for L;
      pose proof (H0 α ltac:(solve_notin_auto)) as Hα;
      pose proof (ftag_in_uskl_open_var R α) as Hov
    end; fsetdec.
  -
    match goal with |- _ [<=] add _ (ftag_in_uskl ?R) =>
      pick fresh α for L;
      pose proof (H0 α ltac:(solve_notin_auto)) as Hα;
      pose proof (ftag_in_uskl_open_var R α) as Hov
    end; fsetdec.
  -
    match goal with |- _ [<=] ftag_in_uskl ?R =>
      pick fresh α for L;
      pose proof (H0 α ltac:(solve_notin_auto)) as Hα;
      pose proof (ftag_in_uskl_open_var R α) as Hov
    end; fsetdec.
  -
    pick fresh α for L;
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα; simpl in Hα; fsetdec.
  -
    match goal with H0 : _ [<=] ftag_in_uskl (ptyp_to_uskl_syn ?t) |- _ =>
      pose proof (ftag_ptyp_to_uskl_syn t) end; fsetdec.
Qed.

Inductive uskl_precise (Θ : aenv) : atoms -> uskl -> uskl -> Prop :=
| upre__refl : forall Ψrep R,
    lc_uskl R ->
    Ψrep [=] empty ->
    uskl_precise Θ Ψrep R R
| upre__arrow : forall Ψrep Ψ1 Ψ2 R1' R2' R1 R2,
    uskl_precise Θ Ψ1 R1' R1 ->
    uskl_precise Θ Ψ2 R2' R2 ->
    Ψrep [=] Ψ1 `union` Ψ2 ->
    uskl_precise Θ Ψrep (uskl_arrow R1' R2') (uskl_arrow R1 R2)
| upre__all_syn : forall L Ψrep R' R,
    (forall α, α `notin` L ->
       uskl_precise Θ Ψrep
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_precise Θ Ψrep (uskl_all_syn R') (uskl_all_syn R)
| upre__all_tag : forall L Ψrep ε R' R,
    (forall α, α `notin` L ->
       uskl_precise Θ Ψrep
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    uskl_precise Θ Ψrep (uskl_all_tag ε R') (uskl_all_tag ε R)
| upre__all_inst : forall L Ψrep Ψ0 ε R' R,
    (forall α, α `notin` L ->
       uskl_precise Θ Ψ0
         (open_uskl_wrt_uskl R' (uskl_var_f α))
         (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    Ψrep [=] add ε Ψ0 ->
    uskl_precise Θ Ψrep (uskl_all_syn R') (uskl_all_tag ε R)
| upre__univ_ghost : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_univ_ghost R') (uskl_univ_ghost R)
| upre__dot_univ_ghost : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_dot_univ_ghost R') (uskl_dot_univ_ghost R)
| upre__univ_ghost_keepg : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_univ_ghost R') (uskl_dot_univ_ghost R)
| upre__ghost : forall Ψrep R,
    Ψrep [=] empty ->
    pskl_no_forall (uskl_to_pskl R) ->
    {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl R) }}a ->
    uskl_precise Θ Ψrep uskl_ghost R
| upre__univ_ghost_remove : forall Ψrep R' R,
    uskl_precise Θ Ψrep R' R ->
    uskl_precise Θ Ψrep (uskl_univ_ghost R') R
| upre__flex_l : forall Ψrep α τ R,
    binds α (abind_flex_mono_def τ) Θ ->
    uskl_precise Θ Ψrep (ptyp_to_uskl_syn τ) R ->
    uskl_precise Θ Ψrep (uskl_var_f α) R
| upre__flex_r : forall Ψrep α τ R',
    binds α (abind_flex_mono_def τ) Θ ->
    uskl_precise Θ Ψrep R' (ptyp_to_uskl_syn τ) ->
    uskl_precise Θ Ψrep R' (uskl_var_f α).

Lemma uskl_precise_psi_cong : forall Θ Ψrep R' R,
  uskl_precise Θ Ψrep R' R ->
  forall Ψrep', Ψrep [=] Ψrep' ->
  uskl_precise Θ Ψrep' R' R.
Proof.
  intros Θ Ψrep R' R H; induction H; intros Ψrep' Heq.
  - apply upre__refl; [ assumption | fsetdec ].
  - eapply upre__arrow; [ exact H | exact H0 | fsetdec ].
  - eapply upre__all_syn with (L := L); intros α Hα; eauto.
  - eapply upre__all_tag with (L := L); intros α Hα; eauto.
  - eapply upre__all_inst with (L := L) (Ψ0 := Ψ0);
      [ intros α Hα; eauto | fsetdec ].
  - apply upre__univ_ghost; eauto.
  - apply upre__dot_univ_ghost; eauto.
  - apply upre__univ_ghost_keepg; eauto.
  - apply upre__ghost; [ fsetdec | assumption | assumption ].
  - apply upre__univ_ghost_remove; eauto.
  - eapply upre__flex_l; eauto.
  - eapply upre__flex_r; eauto.
Qed.

Lemma uskl_precise_ftag_sub : forall Θ Ψrep R' R,
  uskl_precise Θ Ψrep R' R ->
  ftag_in_uskl R' [<=] ftag_in_uskl R.
Proof.
  intros Θ Ψrep R' R H; induction H; simpl; try fsetdec.
  -
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
  -
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
  -
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R' α).
    pose proof (ftag_in_uskl_open_var R α).
    fsetdec.
  -
    pose proof (ftag_ptyp_to_uskl_syn τ). fsetdec.
Qed.

Lemma no_forall_uskl_ftag : forall ψ,
  pskl_no_forall (uskl_to_pskl ψ) ->
  ftag_in_uskl ψ [=] empty.
Proof.
  induction ψ; simpl; intros H; try fsetdec.
  - destruct H as [H1 H2].
    pose proof (IHψ1 H1); pose proof (IHψ2 H2); fsetdec.
  - pose proof (IHψ H); fsetdec.
  - pose proof (IHψ H); fsetdec.
Qed.

Lemma pskl_to_bskl_syn_inj : forall P Q,
  pskl_to_bskl_syn P = pskl_to_bskl_syn Q -> P = Q.
Proof.
  induction P; intros Q Heq; destruct Q; simpl in Heq;
    try discriminate Heq; inversion Heq; subst; f_equal; auto.
Qed.

Lemma uskl_precise_subst : forall Θ Ψrep R' R,
  uskl_precise Θ Ψrep R' R ->
  forall α' ψs,
  lc_uskl ψs ->
  {{ ⊢ Θ }}a ->
  α' `notin` dom Θ ->
  uskl_precise Θ Ψrep
    (subst_uskl_in_uskl ψs α' R') (subst_uskl_in_uskl ψs α' R).
Proof.
  intros Θ Ψrep R' R Hup; induction Hup; intros α0 ψs Hlc Hwf Hα; simpl.
  -
    apply upre__refl;
      [ apply subst_uskl_in_uskl_lc_uskl; assumption | assumption ].
  -
    eapply upre__arrow;
      [ apply IHHup1; assumption | apply IHHup2; assumption | assumption ].
  -
    apply upre__all_syn with (L := L `union` singleton α0).
    intros β Hβ.
    assert (HYX : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R' ψs α0 β HYX Hlc).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψs α0 β HYX Hlc).
    apply H0; [ clear - Hβ; fsetdec | exact Hlc | exact Hwf | exact Hα ].
  -
    apply upre__all_tag with (L := L `union` singleton α0).
    intros β Hβ.
    assert (HYX : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R' ψs α0 β HYX Hlc).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψs α0 β HYX Hlc).
    apply H0; [ clear - Hβ; fsetdec | exact Hlc | exact Hwf | exact Hα ].
  -
    apply upre__all_inst with (L := L `union` singleton α0) (Ψ0 := Ψ0);
      [ | assumption ].
    intros β Hβ.
    assert (HYX : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R' ψs α0 β HYX Hlc).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψs α0 β HYX Hlc).
    apply H0; [ clear - Hβ; fsetdec | exact Hlc | exact Hwf | exact Hα ].
  -
    apply upre__univ_ghost; apply IHHup; assumption.
  -
    apply upre__dot_univ_ghost; apply IHHup; assumption.
  -
    apply upre__univ_ghost_keepg; apply IHHup; assumption.
  -
    assert (Hfr : α0 `notin` ftvar_in_uskl R).
    { pose proof (a_wf_pskl_ftv_dom H1) as Hsc.
      rewrite ftvar_in_pskl_uskl_to_pskl in Hsc.
      clear - Hsc Hα. fsetdec. }
    rewrite (subst_uskl_in_uskl_fresh_eq R ψs α0 Hfr).
    apply upre__ghost; assumption.
  -
    apply upre__univ_ghost_remove; apply IHHup; assumption.
  -
    assert (Hdom : α `in` dom Θ) by (eapply binds_In; exact H).
    destruct_if as [-> | Hne]; [ exfalso; clear - Hdom Hα; fsetdec | ].
    eapply upre__flex_l; [ exact H | ].
    assert (Hfrτ : α0 `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ)).
    { rewrite ftvar_ptyp_to_uskl_syn.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; [ exact Hwf | exact H ]).
      clear - Hsc Hα; fsetdec. }
    pose proof (IHHup α0 ψs Hlc Hwf Hα) as Hrec.
    rewrite (subst_uskl_in_uskl_fresh_eq (ptyp_to_uskl_syn τ) ψs α0 Hfrτ)
      in Hrec.
    exact Hrec.
  -
    assert (Hdom : α `in` dom Θ) by (eapply binds_In; exact H).
    destruct_if as [-> | Hne]; [ exfalso; clear - Hdom Hα; fsetdec | ].
    eapply upre__flex_r; [ exact H | ].
    assert (Hfrτ : α0 `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ)).
    { rewrite ftvar_ptyp_to_uskl_syn.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; [ exact Hwf | exact H ]).
      clear - Hsc Hα; fsetdec. }
    pose proof (IHHup α0 ψs Hlc Hwf Hα) as Hrec.
    rewrite (subst_uskl_in_uskl_fresh_eq (ptyp_to_uskl_syn τ) ψs α0 Hfrτ)
      in Hrec.
    exact Hrec.
Qed.

Lemma uskl_precise_of_precise_gen : forall Θ Δ Qsrc Qtgt,
  ad_refine_syn Θ Δ Qsrc Qtgt ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ₚₛ bskl_to_pskl Qtgt }}a ->
  forall Θb,
  (forall α, a_binds_tvar α Θ -> α `notin` Δ -> a_binds_tvar α Θb) ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     binds α (abind_flex_mono_def τ) Θb) ->
  forall Pa ψt Ψt,
  Qsrc = pskl_to_bskl_inh Pa ->
  Qtgt = pskl_to_bskl_inh (uskl_to_pskl ψt) ->
  is_dskl ψt ->
  d_tags_skl Ψt ψt ->
  uskl_precise Θb Ψt (pskl_to_uskl Pa) ψt.
Proof.
  intros Θ Δ Qsrc Qtgt Hr; induction Hr;
    intros Hwf Hwft Θb Hmtv Hmfl Pa ψt Ψt HSrc HTgt Htsk Hdt.
  -
    destruct Pa; simpl in HSrc; try discriminate HSrc.
    destruct ψt; simpl in HTgt; try discriminate HTgt.
    simpl. apply upre__refl;
      [ auto | exact (d_tags_skl_unit_inv Hdt) ].
  -
    destruct Pa; simpl in HSrc; try discriminate HSrc.
    destruct ψt; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    simpl. apply upre__refl;
      [ auto | exact (d_tags_skl_var_inv Hdt) ].
  -
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    destruct ψt; simpl in HTgt; try discriminate HTgt.
    inversion HSrc; inversion HTgt; subst.
    inversion Htsk; subst.
    apply d_tags_skl_arrow_inv in Hdt
      as [Ψa1 [Ψa2 [Hd1 [Hd2 [Hdisj Hun]]]]].
    simpl in Hwft.
    inversion Hwft as [ | | Θz Δz Pw1 Pw2 Hwft1 Hwft2 | | | ]; subst.
    simpl.
    eapply upre__arrow;
      [ eapply IHHr1; try reflexivity; try eassumption
      | eapply IHHr2; try reflexivity; try eassumption
      | exact Hun ].
  -
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    destruct ψt as [ | n | α0 | ψ1 ψ2 | ψ0 | ε ψ0 | | ψ0 | | ψ0 ];
      simpl in HTgt; try discriminate HTgt;
      [ inversion Htsk | ].
    inversion HSrc; inversion HTgt; subst.
    inversion Htsk as [ | | | Lt ε' ψ0' Ht0 | | ]; subst.
    apply d_tags_skl_all_tag_inv in Hdt
      as [Ld [Ψ0d [Hd0 [Hε Hun]]]].
    simpl in Hwft. destruct (a_wf_pskl_all_inv Hwft) as [Lw Hwbody].
    simpl.
    apply upre__all_inst
      with (L := L `union` Lt `union` Ld `union` Lw `union` dom Θ)
           (Ψ0 := Ψ0d);
      [ | exact Hun ].
    intros α Hα.
    rewrite <- pskl_to_uskl_open_var.
    eapply H1 with (α := α) (ψt := open_uskl_wrt_uskl ψ0 (uskl_var_f α));
      [ clear - Hα; solve_notin_auto
      | apply a_wf_aenv__tvar; [ clear - Hα; solve_notin_auto | exact Hwf ]
      | rewrite bskl_to_pskl_open; apply Hwbody; clear - Hα; solve_notin_auto
      | intros β Hβ HβΔ;
        apply a_binds_tvar_cons_tvar_inv in Hβ as [-> | Hβ];
        [ exfalso; clear - HβΔ; fsetdec
        | apply Hmtv; [ exact Hβ | clear - HβΔ; fsetdec ] ]
      | intros β τ Hb; apply Hmfl; eapply binds_flex_def_cons_tvar_inv; exact Hb
      | symmetry; apply pskl_to_bskl_inh_open
      | rewrite uskl_to_pskl_open; symmetry; apply pskl_to_bskl_inh_open
      | apply Ht0; clear - Hα; solve_notin_auto
      | apply Hd0; clear - Hα; solve_notin_auto ].
  -
    destruct Pa; simpl in HSrc; try discriminate HSrc.
    assert (Hnf : pskl_no_forall (uskl_to_pskl ψt))
      by (eapply inh_eq_syn_no_forall; symmetry; exact HTgt).
    assert (HeqP : P = uskl_to_pskl ψt).
    { apply pskl_to_bskl_syn_inj.
      rewrite HTgt.
      apply pskl_no_forall_inh_eq_syn. exact Hnf. }
    simpl. apply upre__ghost.
    + pose proof (d_tags_skl_ftag Hdt) as Htg.
      pose proof (no_forall_uskl_ftag _ Hnf) as Hfe.
      clear - Htg Hfe; fsetdec.
    + exact Hnf.
    +
      rewrite <- HeqP.
      rewrite bskl_to_pskl_pskl_to_bskl_syn in Hwft.
      assert (Hwf0 : {{ Θ ⨟ empty ⊢ₚₛ P }}a)
        by (eapply a_wf_pskl_delta_mono;
            [ exact Hwft | intros β _ Hβ; clear - Hβ; fsetdec ]).
      eapply a_wf_pskl_tvar_mono_ftv; [ exact Hwf0 | ].
      intros β HβP Hβ. apply Hmtv; [ exact Hβ | ].
      intro HβΔ.
      assert (Hin : β `in` Δ ∩ ftvar_in_pskl P) by (apply inter_3; auto).
      rewrite H in Hin. clear - Hin. fsetdec.
  -
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    simpl. apply upre__univ_ghost_remove.
    eapply IHHr; try reflexivity; try eassumption.
  -
    destruct ψt; simpl in HTgt; discriminate HTgt.
  -
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    destruct ψt as [ | n | α0 | ψ1 ψ2 | ψ0 | ε ψ0 | | ψ0 | | ψ0 ];
      simpl in HTgt; try discriminate HTgt;
      [ inversion Htsk | ].
    inversion HSrc; inversion HTgt; subst.
    inversion Htsk; subst.
    apply d_tags_skl_dot_univ_ghost_inv in Hdt.
    simpl in Hwft. apply a_wf_pskl_univ_ghost_body in Hwft.
    simpl. apply upre__univ_ghost_keepg.
    eapply IHHr; try reflexivity; try eassumption.
  -
    destruct Pa as [ | n | α0 | Pa1 Pa2 | Pa0 | | Pa0 ];
      simpl in HSrc; try discriminate HSrc.
    inversion HSrc; subst.
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    simpl. eapply upre__flex_l; [ apply Hmfl; exact H | ].
    rewrite <- pskl_to_uskl_ptyp.
    eapply IHHr;
      [ exact Hwf | exact Hwft | exact Hmtv | exact Hmfl
      | symmetry; apply (ptyp_to_bskl_inh_syn_eq Hm)
      | reflexivity | exact Htsk | exact Hdt ].
  -
    destruct ψt as [ | n | α0 | ψ1 ψ2 | ψ0 | ε ψ0 | | ψ0 | | ψ0 ];
      simpl in HTgt; try discriminate HTgt.
    inversion HTgt; subst.
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    eapply uskl_precise_psi_cong with (Ψrep := empty);
      [ | pose proof (d_tags_skl_var_inv Hdt); fsetdec ].
    eapply upre__flex_r; [ apply Hmfl; exact H | ].
    eapply IHHr;
      [ exact Hwf
      | rewrite bskl_to_pskl_ptyp_to_bskl_syn;
        apply a_wf_ptyp_to_wf_pskl;
        eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact H ]
      | exact Hmtv | exact Hmfl
      | reflexivity
      | rewrite uskl_to_pskl_ptyp_to_uskl_syn;
        symmetry; apply (ptyp_to_bskl_inh_syn_eq Hm)
      | apply mono_ptyp_to_uskl_syn_is_dskl; exact Hm
      | apply (mono_ptyp_to_uskl_syn_tags Hm); reflexivity ].
Qed.

Lemma uskl_precise_of_precise : forall Θ Δ Qsrc Qtgt,
  ad_refine_syn Θ Δ Qsrc Qtgt ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ₚₛ bskl_to_pskl Qtgt }}a ->
  forall Pa ψt Ψt,
  Qsrc = pskl_to_bskl_inh Pa ->
  Qtgt = pskl_to_bskl_inh (uskl_to_pskl ψt) ->
  is_dskl ψt ->
  d_tags_skl Ψt ψt ->
  uskl_precise Θ Ψt (pskl_to_uskl Pa) ψt.
Proof.
  intros Θ Δ Qsrc Qtgt Hr Hwf Hwft.
  eapply uskl_precise_of_precise_gen;
    [ exact Hr | exact Hwf | exact Hwft
    | intros α Hα _; exact Hα | intros α τ Hb; exact Hb ].
Qed.

Definition consis_split_transport (Θb : aenv) (Ψsup : atoms) (A B : uskl) :=
  forall Θ' Ψfull Ψn Ψna Q,
    {{ Ψfull ⨟ Θ' ⊢ˢ A ∼ Q }}ad ->
    (forall x b, binds x b Θb -> binds x b Θ') ->
    {{ ⊢ Θ' }}a ->
    Ψfull [=] Ψn `union` Ψna ->
    Ψna [<=] Ψsup ->
    Ψsup ∩ Ψn [=] empty ->
    {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
    {{ Ψn ⨟ Θ' ⊢ˢ B ∼ Q }}ad.

Lemma consis_split_transport_arrow : forall Θb Ψsup R1 R2 R1' R2',
  consis_split_transport Θb Ψsup R1 R1' ->
  consis_split_transport Θb Ψsup R2 R2' ->
  consis_split_transport Θb Ψsup (uskl_arrow R1 R2) (uskl_arrow R1' R2').
Proof.
  intros Θb Ψsup R1 R2 R1' R2' Ht1 Ht2.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_arrow R1 R2) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  -
    inversion HeqS; subst.
    simpl in Hwfq.
    inversion Hwfq as [ | | Θz Δz Pw1 Pw2 Hwfq1 Hwfq2 | | | ]; subst.
    eapply ad_pat_consis__arrow with
      (Ψ1 := Ψ1 ∖ Ψsup) (Ψ2 := Ψ2 ∖ Ψsup).
    + eapply Ht1 with (Ψna := Ψ1 ∩ Ψsup);
        [ exact Hc1 | exact Hmon | exact Hwf
        | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
        | clear - Hdisj; fsetdec | exact Hwfq1 ].
    + eapply Ht2 with (Ψna := Ψ2 ∩ Ψsup);
        [ exact Hc2 | exact Hmon | exact Hwf
        | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
        | clear - Hdisj; fsetdec | exact Hwfq2 ].
    + clear - H HΨf HΨa Hdisj; fsetdec.
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    eapply a_wf_pskl_flex_def_payload; eauto.
Qed.

Lemma consis_split_transport_all_syn : forall Θb Ψsup R0 R0' L0,
  (forall α, α `notin` L0 ->
     consis_split_transport Θb Ψsup
       (open_uskl_wrt_uskl R0 (uskl_var_f α))
       (open_uskl_wrt_uskl R0' (uskl_var_f α))) ->
  consis_split_transport Θb Ψsup (uskl_all_syn R0) (uskl_all_syn R0').
Proof.
  intros Θb Ψsup R0 R0' L0 Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_all_syn R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  -
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__forall_inh_untagged with
      (L := L `union` L0 `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (Ht α ltac:(clear - Hα; solve_notin_auto)) with (Ψna := Ψna);
      [ apply H; clear - Hα; fsetdec
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | exact HΨf | exact HΨa | exact Hdisj
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  -
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__forall_syn with
      (L := L `union` L0 `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (Ht α ltac:(clear - Hα; solve_notin_auto)) with (Ψna := Ψna);
      [ apply H; clear - Hα; fsetdec
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | exact HΨf | exact HΨa | exact Hdisj
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    eapply a_wf_pskl_flex_def_payload; eauto.
Qed.

Lemma consis_split_transport_all_tag_cong : forall Θb Ψsup ε R0 R0' L0,
  ε `notin` Ψsup ->
  (forall α, α `notin` L0 ->
     consis_split_transport Θb Ψsup
       (open_uskl_wrt_uskl R0 (uskl_var_f α))
       (open_uskl_wrt_uskl R0' (uskl_var_f α))) ->
  consis_split_transport Θb Ψsup (uskl_all_tag ε R0) (uskl_all_tag ε R0').
Proof.
  intros Θb Ψsup ε R0 R0' L0 Hεout Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_all_tag ε R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  -
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    assert (HεΨn : ε `in` Ψn)
      by (clear - H1 HΨf HΨa Hεout; fsetdec).
    eapply ad_pat_consis__forall_inh_tagged with
      (L := L `union` L0 `union` Lw `union` dom Θ)
      (Ψ0 := Ψ0 ∖ Ψsup).
    + intros α Hα.
      eapply (Ht α ltac:(clear - Hα; solve_notin_auto))
        with (Ψna := Ψ0 ∩ Ψsup);
        [ apply H; clear - Hα; fsetdec
        | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
        | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
        | clear - Hdisj; fsetdec | clear - Hdisj; fsetdec
        | clear - Hdisj; fsetdec
        | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
    + clear - H1 HΨf HΨa Hdisj HεΨn Hεout; fsetdec.
  -
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__forall_syn_tagged with
      (L := L `union` L0 `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (Ht α ltac:(clear - Hα; solve_notin_auto)) with (Ψna := Ψna);
      [ apply H; clear - Hα; fsetdec
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | exact HΨf | exact HΨa | exact Hdisj
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    eapply a_wf_pskl_flex_def_payload; eauto.
Qed.

Lemma consis_split_transport_all_inst : forall Θb Ψsup ε R0 R0' L0,
  ε `in` Ψsup ->
  (forall α, α `notin` L0 ->
     consis_split_transport Θb Ψsup
       (open_uskl_wrt_uskl R0 (uskl_var_f α))
       (open_uskl_wrt_uskl R0' (uskl_var_f α))) ->
  consis_split_transport Θb Ψsup (uskl_all_tag ε R0) (uskl_all_syn R0').
Proof.
  intros Θb Ψsup ε R0 R0' L0 Hεin Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_all_tag ε R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  -
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__forall_inh_untagged with
      (L := L `union` L0 `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (Ht α ltac:(clear - Hα; solve_notin_auto))
      with (Ψna := Ψ0 ∩ Ψsup);
      [ apply H; clear - Hα; fsetdec
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | clear - H1 HΨf HΨa Hdisj Hεin; fsetdec
      | clear - Hdisj; fsetdec
      | clear - Hdisj; fsetdec
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  -
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__forall_syn with
      (L := L `union` L0 `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (Ht α ltac:(clear - Hα; solve_notin_auto)) with (Ψna := Ψna);
      [ apply H; clear - Hα; fsetdec
      | intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | exact HΨf | exact HΨa | exact Hdisj
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    eapply a_wf_pskl_flex_def_payload; eauto.
Qed.

Lemma consis_split_transport_univ_ghost : forall Θb Ψsup R0 R0',
  consis_split_transport Θb Ψsup R0 R0' ->
  consis_split_transport Θb Ψsup (uskl_univ_ghost R0) (uskl_univ_ghost R0').
Proof.
  intros Θb Ψsup R0 R0' Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_univ_ghost R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  -
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_univ_ghost_inv Hwfq) as [Hg Hwb].
    apply ad_pat_consis__univ_ghost.
    eapply Ht with (Ψna := Ψna);
      [ exact Hc | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwb ].
  -
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_all_inv Hwfq) as [Lw Hwbody].
    eapply ad_pat_consis__univ_ghost_inh with
      (L := L `union` Lw `union` dom Θ).
    intros α Hα.
    eapply (H0 α ltac:(clear - Hα; solve_notin_auto) eq_refl Ψn Ψna HΨf HΨa Hdisj);
      [ intros x b Hb; unfold binds; simpl; right; apply Hmon; exact Hb
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | apply wf_open_of_all; apply Hwbody; clear - Hα; fsetdec ].
  -
    inversion HeqS; subst.
    apply ad_pat_consis__univ_ghost_drop.
    eapply Ht with (Ψna := Ψna);
      [ exact Hc | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwfq ].
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    eapply a_wf_pskl_flex_def_payload; eauto.
Qed.

Lemma consis_split_transport_dot_univ_ghost : forall Θb Ψsup R0 R0',
  consis_split_transport Θb Ψsup R0 R0' ->
  consis_split_transport Θb Ψsup (uskl_dot_univ_ghost R0) (uskl_dot_univ_ghost R0').
Proof.
  intros Θb Ψsup R0 R0' Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_dot_univ_ghost R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  -
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_univ_ghost_inv Hwfq) as [Hg Hwb].
    apply ad_pat_consis__dot_univ_ghost.
    eapply Ht with (Ψna := Ψna);
      [ exact Hc | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwb ].
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    eapply a_wf_pskl_flex_def_payload; eauto.
Qed.

Lemma consis_split_transport_keepg : forall Θb Ψsup R0 R0',
  consis_split_transport Θb Ψsup R0 R0' ->
  consis_split_transport Θb Ψsup (uskl_dot_univ_ghost R0) (uskl_univ_ghost R0').
Proof.
  intros Θb Ψsup R0 R0' Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_dot_univ_ghost R0) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  -
    inversion HeqS; subst.
    simpl in Hwfq. destruct (a_wf_pskl_univ_ghost_inv Hwfq) as [Hg Hwb].
    apply ad_pat_consis__univ_ghost.
    eapply Ht with (Ψna := Ψna);
      [ exact Hc | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwb ].
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    eapply a_wf_pskl_flex_def_payload; eauto.
Qed.

Lemma consis_split_transport_flexvar : forall Θb Ψsup α τ R,
  binds α (abind_flex_mono_def τ) Θb ->
  consis_split_transport Θb Ψsup (ptyp_to_uskl_syn τ) R ->
  consis_split_transport Θb Ψsup (uskl_var_f α) R.
Proof.
  intros Θb Ψsup α τ R Hb Ht.
  intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
  remember (uskl_var_f α) as Ssub eqn:HeqS.
  revert Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  induction Hc; try discriminate HeqS;
    intros Ψn Ψna HΨf HΨa Hdisj Hmon Hwf Hwfq.
  -
    inversion HeqS; subst.
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ) by (apply Hmon; exact Hb).
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact Hb' ]).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb' ]).
    eapply ad_pat_consis__flex_r; [ exact Hb' | ].
    eapply Ht with (Ψfull := empty) (Ψna := Ψna);
      [ apply consis_mono_refl;
        [ exact Hm
        | intros β Hβ; eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfτ | exact Hβ ] ]
      | exact Hmon | exact Hwf
      | clear - H HΨf; fsetdec | exact HΨa | exact Hdisj
      | rewrite bskl_to_pskl_ptyp_to_bskl_syn;
        apply a_wf_pskl_mono_ptyp; [ exact Hm | exact Hwfτ ] ].
  -
    inversion HeqS; subst.
    assert (Hb' : binds α (abind_flex_mono_def τ) Θ) by (apply Hmon; exact Hb).
    assert (Hu : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwf).
    pose proof (binds_unique _ _ _ _ _ H Hb' Hu) as He; inversion He; subst.
    eapply Ht with (Ψna := Ψna);
      [ exact Hc | exact Hmon | exact Hwf
      | exact HΨf | exact HΨa | exact Hdisj | exact Hwfq ].
  -
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    apply (IHHc HeqS Ψn Ψna HΨf HΨa Hdisj Hmon Hwf).
    eapply a_wf_pskl_flex_def_payload; eauto.
Qed.

Lemma ad_pat_consis_precise_upre : forall Θb Ψrep R' R,
  uskl_precise Θb Ψrep R' R ->
  forall Ψsup,
  Ψrep [<=] Ψsup ->
  Ψsup ∩ ftag_in_uskl R' [=] empty ->
  consis_split_transport Θb Ψsup R R'.
Proof.
  intros Θb Ψrep R' R Hup; induction Hup;
    intros Ψsup HΨsup Hftag; simpl in Hftag.
  -
    intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
    assert (Ha0 : Ψna [<=] empty).
    { pose proof (ad_pat_consis_ftag_sub Hc) as Hfs.
      clear - Hfs HΨf HΨa Hftag; fsetdec. }
    eapply ad_pat_consis_psi_cong;
      [ exact Hc | clear - HΨf Ha0; fsetdec ].
  -
    apply consis_split_transport_arrow.
    + apply IHHup1; [ clear - HΨsup H; fsetdec | clear - Hftag; fsetdec ].
    + apply IHHup2; [ clear - HΨsup H; fsetdec | clear - Hftag; fsetdec ].
  -
    apply consis_split_transport_all_syn with (L0 := L).
    intros α Hα.
    apply (H0 α Hα);
      [ exact HΨsup
      | match goal with
        | |- _ ∩
               (ftag_in_uskl (open_uskl_wrt_uskl ?B _)) [=] _ =>
            pose proof (ftag_in_uskl_open_var B α) as Hov
        end; clear - Hftag Hov; fsetdec ].
  -
    assert (Hεout : ε `notin` Ψsup) by (clear - Hftag; fsetdec).
    apply consis_split_transport_all_tag_cong with (L0 := L);
      [ exact Hεout | ].
    intros α Hα.
    apply (H0 α Hα);
      [ exact HΨsup
      | match goal with
        | |- _ ∩
               (ftag_in_uskl (open_uskl_wrt_uskl ?B _)) [=] _ =>
            pose proof (ftag_in_uskl_open_var B α) as Hov
        end; clear - Hftag Hov; fsetdec ].
  -
    assert (Hεin : ε `in` Ψsup) by (clear - HΨsup H1; fsetdec).
    apply consis_split_transport_all_inst with (L0 := L);
      [ exact Hεin | ].
    intros α Hα.
    apply (H0 α Hα);
      [ clear - HΨsup H1; fsetdec
      | match goal with
        | |- _ ∩
               (ftag_in_uskl (open_uskl_wrt_uskl ?B _)) [=] _ =>
            pose proof (ftag_in_uskl_open_var B α) as Hov
        end; clear - Hftag Hov; fsetdec ].
  -
    apply consis_split_transport_univ_ghost.
    apply IHHup; [ exact HΨsup | clear - Hftag; fsetdec ].
  -
    apply consis_split_transport_dot_univ_ghost.
    apply IHHup; [ exact HΨsup | clear - Hftag; fsetdec ].
  -
    apply consis_split_transport_keepg.
    apply IHHup; [ exact HΨsup | clear - Hftag; fsetdec ].
  -
    intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
    assert (HΨe : Ψn [=] empty).
    { pose proof (ad_pat_consis_ftag_sub Hc) as Hfs.
      pose proof (no_forall_uskl_ftag _ H0) as Hfe.
      clear - Hfs Hfe HΨf; fsetdec. }
    pose proof (ad_pat_consis_strip_tags Hc) as Hstr.
    destruct (consis_concrete_target_inh Hstr Hwf (uskl_to_pskl R) eq_refl H0)
      as [_ Heqinh].
    rewrite <- Heqinh.
    apply ad_pat_consis__ghost; [ exact HΨe ].
  -
    intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
    apply ad_pat_consis__univ_ghost_drop.
    assert (Hftag' : Ψsup ∩ ftag_in_uskl R' [=] empty)
      by (clear - Hftag; fsetdec).
    exact (IHHup Ψsup HΨsup Hftag' Θ' Ψfull Ψn Ψna Q
             Hc Hmon Hwf HΨf HΨa Hdisj Hwfq).
  -
    intros Θ' Ψfull Ψn Ψna Q Hc Hmon Hwf HΨf HΨa Hdisj Hwfq.
    eapply ad_pat_consis__flex_l; [ apply Hmon; exact H | ].
    assert (Hftag' : Ψsup ∩
                       (ftag_in_uskl (ptyp_to_uskl_syn τ)) [=] empty)
      by (pose proof (ftag_ptyp_to_uskl_syn τ) as Hpt; clear - Hpt; fsetdec).
    exact (IHHup Ψsup HΨsup Hftag' Θ' Ψfull Ψn Ψna Q
             Hc Hmon Hwf HΨf HΨa Hdisj Hwfq).
  -
    apply consis_split_transport_flexvar with (τ := τ); [ exact H | ].
    apply IHHup; [ exact HΨsup | exact Hftag ].
Qed.

Lemma uskl_precise_ftag_rep : forall Θ Ψrep R' R,
  uskl_precise Θ Ψrep R' R ->
  Ψrep [<=] ftag_in_uskl R.
Proof.
  intros Θ Ψrep R' R H; induction H; simpl; try fsetdec.
  -
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R α); fsetdec.
  -
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R α); fsetdec.
  -
    pick fresh α for L.
    pose proof (H0 α ltac:(solve_notin_auto)) as Hα.
    pose proof (ftag_in_uskl_open_var R α); fsetdec.
  -
    pose proof (ftag_ptyp_to_uskl_syn τ); fsetdec.
Qed.

Lemma uskl_precise_lc_l : forall Θ Ψrep R' R,
  uskl_precise Θ Ψrep R' R -> lc_uskl R'.
Proof.
  intros Θ Ψrep R' R Hup; induction Hup.
  - assumption.
  - apply lc_uskl_arrow; assumption.
  - pick fresh α for L.
    apply lc_uskl_all_syn_exists with (α1 := α). apply H0; fsetdec.
  - pick fresh α for L.
    apply lc_uskl_all_tag_exists with (α1 := α). apply H0; fsetdec.
  - pick fresh α for L.
    apply lc_uskl_all_syn_exists with (α1 := α). apply H0; fsetdec.
  - apply lc_uskl_univ_ghost; assumption.
  - apply lc_uskl_dot_univ_ghost; assumption.
  - apply lc_uskl_univ_ghost; assumption.
  - apply lc_uskl_ghost.
  - apply lc_uskl_univ_ghost; assumption.
  - apply lc_uskl_var_f.
  - assumption.
Qed.

Lemma uskl_precise_subst_into_in : forall R,
  lc_uskl R ->
  forall Θ Ψrep ψ' ψ α0,
  uskl_precise Θ Ψrep ψ' ψ ->
  lc_uskl ψ ->
  α0 `in` ftvar_in_uskl R ->
  uskl_precise Θ Ψrep
    (subst_uskl_in_uskl ψ' α0 R) (subst_uskl_in_uskl ψ α0 R).
Proof.
  intros R Hlc; induction Hlc; intros Θ Ψrep ψ' ψ α0 Hp Hlcψ Hin;
    simpl in Hin |- *.
  -  exfalso; clear - Hin; fsetdec.
  -
    destruct_if as [-> | Hne]; [ exact Hp | ].
    exfalso; clear - Hin Hne; fsetdec.
  -
    destruct (AtomSetProperties.In_dec α0 (ftvar_in_uskl R1))
      as [Hin1 | Hni1];
      destruct (AtomSetProperties.In_dec α0 (ftvar_in_uskl R2))
        as [Hin2 | Hni2].
    + apply upre__arrow with (Ψ1 := Ψrep) (Ψ2 := Ψrep);
        [ apply IHHlc1; assumption | apply IHHlc2; assumption
        | clear; fsetdec ].
    + apply upre__arrow with (Ψ1 := Ψrep) (Ψ2 := empty);
        [ apply IHHlc1; assumption
        | rewrite (subst_uskl_in_uskl_fresh_eq R2 ψ' α0 Hni2);
          rewrite (subst_uskl_in_uskl_fresh_eq R2 ψ α0 Hni2);
          apply upre__refl; [ assumption | reflexivity ]
        | clear; fsetdec ].
    + apply upre__arrow with (Ψ1 := empty) (Ψ2 := Ψrep);
        [ rewrite (subst_uskl_in_uskl_fresh_eq R1 ψ' α0 Hni1);
          rewrite (subst_uskl_in_uskl_fresh_eq R1 ψ α0 Hni1);
          apply upre__refl; [ assumption | reflexivity ]
        | apply IHHlc2; assumption
        | clear; fsetdec ].
    + exfalso; clear - Hin Hni1 Hni2; fsetdec.
  -
    assert (Hlcψ' : lc_uskl ψ') by (eapply uskl_precise_lc_l; exact Hp).
    apply upre__all_syn with (L := singleton α0).
    intros β Hβ.
    assert (Hne : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ' α0 β Hne Hlcψ').
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ α0 β Hne Hlcψ).
    apply H0; [ exact Hp | exact Hlcψ | ].
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - Hin Hlo; fsetdec.
  -
    assert (Hlcψ' : lc_uskl ψ') by (eapply uskl_precise_lc_l; exact Hp).
    apply upre__all_tag with (L := singleton α0).
    intros β Hβ.
    assert (Hne : α0 <> β) by (clear - Hβ; fsetdec).
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ' α0 β Hne Hlcψ').
    rewrite (subst_uskl_in_uskl_open_uskl_wrt_uskl_var R ψ α0 β Hne Hlcψ).
    apply H0; [ exact Hp | exact Hlcψ | ].
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f β))
      as Hlo.
    clear - Hin Hlo; fsetdec.
  -  exfalso; clear - Hin; fsetdec.
  -
    apply upre__univ_ghost. apply IHHlc; assumption.
  -  exfalso; clear - Hin; fsetdec.
  -
    apply upre__dot_univ_ghost. apply IHHlc; assumption.
Qed.

Lemma uskl_precise_subst_into : forall R Θ Ψrep ψ' ψ α0,
  lc_uskl R ->
  uskl_precise Θ Ψrep ψ' ψ ->
  lc_uskl ψ ->
  exists Ψrep',
    (Ψrep' [=] Ψrep \/ Ψrep' [=] empty) /\
    uskl_precise Θ Ψrep'
      (subst_uskl_in_uskl ψ' α0 R) (subst_uskl_in_uskl ψ α0 R).
Proof.
  intros R Θ Ψrep ψ' ψ α0 Hlc Hp Hlcψ.
  destruct (AtomSetProperties.In_dec α0 (ftvar_in_uskl R)) as [Hin | Hni].
  - exists Ψrep. split; [ left; reflexivity | ].
    eapply uskl_precise_subst_into_in; eauto.
  - exists empty. split; [ right; reflexivity | ].
    rewrite (subst_uskl_in_uskl_fresh_eq R ψ' α0 Hni).
    rewrite (subst_uskl_in_uskl_fresh_eq R ψ α0 Hni).
    apply upre__refl; [ exact Hlc | reflexivity ].
Qed.

Lemma uskl_precise_open_into : forall R Θ Ψrep ψ' ψ,
  (forall α, lc_uskl (open_uskl_wrt_uskl R (uskl_var_f α))) ->
  uskl_precise Θ Ψrep ψ' ψ ->
  lc_uskl ψ ->
  exists Ψrep',
    (Ψrep' [=] Ψrep \/ Ψrep' [=] empty) /\
    uskl_precise Θ Ψrep'
      (open_uskl_wrt_uskl R ψ') (open_uskl_wrt_uskl R ψ).
Proof.
  intros R Θ Ψrep ψ' ψ Hbody Hp Hlcψ.
  pick fresh α for (ftvar_in_uskl R).
  rewrite (subst_uskl_in_uskl_intro α R ψ' ltac:(clear - Fr; solve_notin_auto)).
  rewrite (subst_uskl_in_uskl_intro α R ψ ltac:(clear - Fr; solve_notin_auto)).
  eapply uskl_precise_subst_into;
    [ apply Hbody | exact Hp | exact Hlcψ ].
Qed.

Lemma ad_refine_pskl_ftv_policed : forall Θ Δ P Q,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad ->
  forall S,
  S [<=] Δ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     S ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` S -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  S ∩ ftvar_in_pskl P [=] empty ->
  S ∩ ftvar_in_pskl Q [=] empty.
Proof.
  intros Θ Δ P Q Href; induction Href; intros S HSΔ Hdefs Hflex Hsrc;
    simpl in Hsrc |- *.
  -  exact Hsrc.
  -  exact Hsrc.
  -
    assert (Hs1 : S ∩ ftvar_in_pskl P1 [=] empty) by (clear - Hsrc; fsetdec).
    assert (Hs2 : S ∩ ftvar_in_pskl P2 [=] empty) by (clear - Hsrc; fsetdec).
    pose proof (IHHref1 S HSΔ Hdefs Hflex Hs1) as Ht1.
    pose proof (IHHref2 S HSΔ Hdefs Hflex Hs2) as Ht2.
    clear - Ht1 Ht2; fsetdec.
  -
    pick fresh α for (L `union` S `union` ftvar_in_pskl P `union` ftvar_in_pskl P').
    destruct (@delta_flex_defs_cons_tvar α Θ S Hdefs Hflex) as [Hdefs' Hflex'].
    assert (Hs0 : S ∩ ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α))
                    [=] empty).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    P (pskl_var_f α)) as Hup.
      simpl in Hup. clear - Hsrc Hup Fr. fsetdec. }
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto) S
                  ltac:(clear - HSΔ; fsetdec) Hdefs' Hflex' Hs0) as Ht.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower
                  P' (pskl_var_f α)) as Hlo.
    clear - Ht Hlo. fsetdec.
  -
    clear - H HSΔ. fsetdec.
  -
    apply IHHref; auto.
  -
    pick fresh α for (L `union` S `union` ftvar_in_pskl P').
    destruct (@delta_flex_defs_cons_tvar α Θ S Hdefs Hflex) as [Hdefs' Hflex'].
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto) S HSΔ
                  Hdefs' Hflex' Hsrc) as Ht.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower
                  P' (pskl_var_f α)) as Hlo.
    clear - Ht Hlo. fsetdec.
  -
    apply IHHref; auto.
  -
    apply IHHref; auto.
    rewrite ftvar_ptyp_to_pskl. eapply Hdefs; exact H.
  -
    apply inter_empty_pointwise. intros β Hβ. intro Hc.
    assert (Heqβ : β = α) by (clear - Hc; fsetdec). subst β.
    exact (Hflex α τ Hβ H).
Qed.

Lemma ad_refine_pskl_ghost_l : forall Θ Δ Qm Qr,
  {{ Θ ⨟ Δ ⊢ᵣₚ Qm ⊳ Qr }}ad ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  Δ ∩ ftvar_in_pskl Qm [=] empty ->
  {{ Θ ⨟ Δ ⊢ᵣₚ pskl_ghost ⊳ Qr }}ad.
Proof.
  intros Θ Δ Qm Qr Href Hdefs Hflex Hsrc.
  apply ad_refine_pskl__ghost.
  eapply ad_refine_pskl_ftv_policed;
    [ exact Href | clear; fsetdec | exact Hdefs | exact Hflex | exact Hsrc ].
Qed.

Lemma uskl_precise_mono_refine : forall Θb Ψr R' R,
  uskl_precise Θb Ψr R' R ->
  forall Θ Δ τ',
  R = ptyp_to_uskl_syn τ' ->
  mono_ptyp τ' ->
  (forall x (b : abind), binds x b Θb -> binds x b Θ) ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ (ptyp_to_pskl τ') }}a ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  Δ ∩ ftvar_in_ptyp τ' [=] empty ->
  {{ Θ ⨟ Δ ⊢ᵣₚ ⌊ R' ⌋ˢ ⊳ (ptyp_to_pskl τ') }}ad.
Proof.
  intros Θb Ψr R' R Hp; induction Hp;
    intros Θ' Δ τ' Heq Hm Hmon Hwf Hwfτ Hdefs Hfree.
  -
    rewrite Heq. rewrite uskl_to_pskl_ptyp.
    eapply ad_refine_pskl_refl_gen. exact Hwfτ.
  -
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; try discriminate Heq.
    inversion Heq; subst.
    inversion Hm; subst.
    simpl in Hfree.
    assert (Hw1 : {{ Θ' ⨟ empty ⊢ₚₛ (ptyp_to_pskl τ1) }}a)
      by (inversion Hwfτ; subst; assumption).
    assert (Hw2 : {{ Θ' ⨟ empty ⊢ₚₛ (ptyp_to_pskl τ2) }}a)
      by (inversion Hwfτ; subst; assumption).
    simpl. apply ad_refine_pskl__arrow.
    + eapply IHHp1;
        [ unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; reflexivity
        | assumption | exact Hmon | exact Hwf | exact Hw1 | exact Hdefs
        | clear - Hfree; fsetdec ].
    + eapply IHHp2;
        [ unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; reflexivity
        | assumption | exact Hmon | exact Hwf | exact Hw2 | exact Hdefs
        | clear - Hfree; fsetdec ].
  -
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; try discriminate Heq.
    inversion Hm.
  -
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  -
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  -
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  -
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  -
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; discriminate Heq.
  -
    simpl. apply ad_refine_pskl__ghost.
    rewrite ftvar_ptyp_to_pskl. exact Hfree.
  -
    simpl. apply ad_refine_pskl__univ_ghost_remove.
    eapply IHHp;
      [ exact Heq | exact Hm | exact Hmon | exact Hwf | exact Hwfτ
      | exact Hdefs | exact Hfree ].
  -
    simpl. eapply ad_refine_pskl__flex_l; [ apply Hmon; eassumption | ].
    pose proof (IHHp Θ' Δ τ' Heq Hm Hmon Hwf Hwfτ Hdefs Hfree) as Ht.
    rewrite uskl_to_pskl_ptyp in Ht. exact Ht.
  -
    destruct τ' as [ | n | β | τ1 τ2 | τ0 ];
      unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in Heq;
      simpl in Heq; try discriminate Heq.
    inversion Heq; subst.
    simpl. eapply ad_refine_pskl__flex_r; [ apply Hmon; eassumption | ].
    match goal with
      Hb : binds _ (abind_flex_mono_def ?t) Θb |- _ =>
      eapply IHHp;
        [ reflexivity
        | eapply a_wf_aenv_binds_def_mono; [ exact Hwf | apply Hmon; exact Hb ]
        | exact Hmon | exact Hwf
        | apply a_wf_ptyp_to_wf_pskl;
          eapply a_wf_aenv_binds_def_wf; [ exact Hwf | apply Hmon; exact Hb ]
        | exact Hdefs
        | eapply Hdefs; apply Hmon; exact Hb ]
    end.
Qed.

Local Ltac erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq :=
  simpl;
  eapply ad_refine_pskl_ghost_l;
    [ exact Hrr | exact Hdefs | exact Hflex
    | rewrite <- Heq;
      eapply a_wf_pskl_empty_delta_free with (Θ := Θb);
        [ eassumption | exact HΔb ] ].

Local Ltac erase_refine_remove IHHp Heq :=
  simpl; apply ad_refine_pskl__univ_ghost_remove; apply IHHp; exact Heq.

Local Ltac erase_refine_flexl Hmon IHHp Heq :=
  simpl; eapply ad_refine_pskl__flex_l;
    [ apply Hmon; eassumption
    | let Ht := fresh "Ht" in
      pose proof (IHHp Heq) as Ht;
      rewrite uskl_to_pskl_ptyp in Ht; exact Ht ].

Local Ltac erase_refine_all H0 Hfam LL L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb :=
  apply ad_refine_pskl__all
    with (L := L `union` LL `union` dom Θ `union` dom Θb `union` Δ);
  let α2 := fresh "α2" in
  let Hα2 := fresh "Hα2" in
  let HαΘ := fresh "HαΘ" in
  let Hdefs' := fresh "Hdefs'" in
  let Hflex' := fresh "Hflex'" in
  intros α2 Hα2;
  rewrite <- uskl_to_pskl_open;
  assert (HαΘ : α2 `notin` dom Θ) by (clear - Hα2; fsetdec);
  destruct (delta_flex_defs_cons_tvar_add Hwf HαΘ Hdefs Hflex)
    as [Hdefs' Hflex'];
  eapply H0;
    [ clear - Hα2; fsetdec
    | apply a_wf_aenv__tvar; [ exact HαΘ | exact Hwf ]
    | exact Hdefs' | exact Hflex'
    | apply Hfam; clear - Hα2; fsetdec
    | intros x b0 Hb0; apply binds_cons_3; apply Hmon; exact Hb0
    | let β := fresh "β" in
      let Hβ := fresh "Hβ" in
      let Hne := fresh "Hne" in
      intros β Hβ;
      destruct (β == α2) as [-> | Hne];
        [ clear - Hα2; fsetdec
        | apply HΔb; clear - Hβ Hne; fsetdec ]
    | apply uskl_to_pskl_open ].

Local Ltac erase_refine_fill H0 L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb ctor :=
  apply ad_refine_pskl__univ_ghost_fill
    with (L := L `union` dom Θ `union` dom Θb `union` Δ);
  let α2 := fresh "α2" in
  let Hα2 := fresh "Hα2" in
  let Hdefs' := fresh "Hdefs'" in
  let Hflex' := fresh "Hflex'" in
  intros α2 Hα2;
  match goal with
  |- {{ _ ⨟ _ ⊢ᵣₚ (pskl_univ_ghost (uskl_to_pskl ?RR)) ⊳ _ }}ad =>
    change (pskl_univ_ghost (uskl_to_pskl RR))
      with (uskl_to_pskl (ctor RR))
  end;
  destruct (@delta_flex_defs_cons_tvar α2 Θ Δ Hdefs Hflex)
    as [Hdefs' Hflex'];
  eapply H0;
    [ clear - Hα2; fsetdec
    | apply a_wf_aenv__tvar; [ clear - Hα2; fsetdec | exact Hwf ]
    | exact Hdefs' | exact Hflex'
    | first [ apply upre__univ_ghost; eassumption
            | apply upre__dot_univ_ghost; eassumption
            | apply upre__univ_ghost_keepg; eassumption ]
    | intros x b0 Hb0; apply binds_cons_3; apply Hmon; exact Hb0
    | exact HΔb
    | reflexivity ].

Lemma uskl_precise_erase_refine_gen : forall Θ Δ Qm Qr,
  {{ Θ ⨟ Δ ⊢ᵣₚ Qm ⊳ Qr }}ad ->
  {{ ⊢ Θ }}a ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  forall Θb Ψr R' R,
  uskl_precise Θb Ψr R' R ->
  (forall x (b : abind), binds x b Θb -> binds x b Θ) ->
  (forall α, α `in` Δ -> α `notin` dom Θb) ->
  ⌊ R ⌋ˢ = Qm ->
  {{ Θ ⨟ Δ ⊢ᵣₚ ⌊ R' ⌋ˢ ⊳ Qr }}ad.
Proof.
  intros Θ Δ Qm Qr Hr; induction Hr;
    intros Hwf Hdefs Hflex Θb Ψr R' R Hp Hmon HΔb Heq.
  -
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ pskl_unit ⊳ pskl_unit }}ad)
      by (apply ad_refine_pskl__unit).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  -
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_var_f α) ⊳ (pskl_var_f α) }}ad)
      by (apply ad_refine_pskl__var).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
    +
      inversion Heq; subst.
      simpl. eapply ad_refine_pskl__flex_r; [ apply Hmon; eassumption | ].
      match goal with
        Hb : binds _ (abind_flex_mono_def ?t) Θb |- _ =>
        eapply uskl_precise_mono_refine;
          [ eassumption | reflexivity
          | eapply a_wf_aenv_binds_def_mono;
              [ exact Hwf | apply Hmon; exact Hb ]
          | exact Hmon | exact Hwf
          | apply a_wf_ptyp_to_wf_pskl;
            eapply a_wf_aenv_binds_def_wf; [ exact Hwf | apply Hmon; exact Hb ]
          | exact Hdefs
          | eapply Hdefs; apply Hmon; exact Hb ]
      end.
  -
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_arrow P1 P2) ⊳ (pskl_arrow P3 P4) }}ad)
      by (apply ad_refine_pskl__arrow; assumption).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    +
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__arrow.
      * eapply IHHr1;
          [ exact Hwf | exact Hdefs | exact Hflex
          | eassumption | exact Hmon | exact HΔb | reflexivity ].
      * eapply IHHr2;
          [ exact Hwf | exact Hdefs | exact Hflex
          | eassumption | exact Hmon | exact HΔb | reflexivity ].
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  -
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_all_syn P) ⊳ (pskl_all_syn P') }}ad)
      by (apply ad_refine_pskl__all with (L := L); exact H).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    +
      inversion Heq; subst.
      simpl.
      match goal with
        Hfam : forall β, β `notin` ?LL -> uskl_precise _ _ _ _ |- _ =>
        erase_refine_all H0 Hfam LL L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb
      end.
    +
      inversion Heq; subst.
      simpl.
      match goal with
        Hfam : forall β, β `notin` ?LL -> uskl_precise _ _ _ _ |- _ =>
        erase_refine_all H0 Hfam LL L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb
      end.
    +
      inversion Heq; subst.
      simpl.
      match goal with
        Hfam : forall β, β `notin` ?LL -> uskl_precise _ _ _ _ |- _ =>
        erase_refine_all H0 Hfam LL L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb
      end.
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  -
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ pskl_ghost ⊳ P' }}ad)
      by (apply ad_refine_pskl__ghost; exact H).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + simpl. exact Hrr.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  -
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ P' }}ad)
      by (apply ad_refine_pskl__univ_ghost_remove; exact Hr).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    +
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_remove.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    +
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_remove.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    +
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_remove.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  -
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ (pskl_all_syn P') }}ad)
      by (apply ad_refine_pskl__univ_ghost_fill with (L := L); exact H).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    +
      inversion Heq; subst.
      simpl.
      erase_refine_fill H0 L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb uskl_univ_ghost.
    +
      inversion Heq; subst.
      simpl.
      erase_refine_fill H0 L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb uskl_dot_univ_ghost.
    +
      inversion Heq; subst.
      simpl.
      erase_refine_fill H0 L Θ Θb Δ Hwf Hdefs Hflex Hmon HΔb uskl_univ_ghost.
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  -
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ (pskl_univ_ghost P') }}ad)
      by (apply ad_refine_pskl__univ_ghost_keep; assumption).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    +
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_keep.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    +
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_keep.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    +
      inversion Heq; subst.
      simpl. apply ad_refine_pskl__univ_ghost_keep.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | reflexivity ].
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
  -
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_var_f α) ⊳ P' }}ad)
      by (eapply ad_refine_pskl__flex_l; eassumption).
    revert Heq; induction Hp; intros Heq; simpl in Heq; try discriminate Heq.
    + rewrite Heq. exact Hrr.
    + erase_refine_ghost Hrr Hdefs Hflex HΔb Θb Heq.
    + erase_refine_remove IHHp Heq.
    + erase_refine_flexl Hmon IHHp Heq.
    +
      inversion Heq; subst.
      match goal with
        Hb : binds _ (abind_flex_mono_def ?t) Θb |- _ =>
        assert (Heqτ : t = τ) by
          (pose proof (a_wf_aenv_uniq Hwf) as Hu;
           pose proof (binds_unique _ _ _ _ _ (Hmon _ _ Hb) H Hu) as He;
           inversion He; reflexivity)
      end.
      subst.
      eapply IHHr;
        [ exact Hwf | exact Hdefs | exact Hflex
        | eassumption | exact Hmon | exact HΔb | apply uskl_to_pskl_ptyp ].
  -
    eapply ad_refine_pskl__flex_r; [ eassumption | ].
    eapply IHHr;
      [ exact Hwf | exact Hdefs | exact Hflex
      | exact Hp | exact Hmon | exact HΔb | exact Heq ].
Qed.

Lemma uskl_precise_erase_refine : forall Θ Δ Qm Qr,
  {{ Θ ⨟ Δ ⊢ᵣₚ Qm ⊳ Qr }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  forall Θb Ψr R' R,
  uskl_precise Θb Ψr R' R ->
  (forall x (b : abind), binds x b Θb -> binds x b Θ) ->
  ⌊ R ⌋ˢ = Qm ->
  {{ Θ ⨟ Δ ⊢ᵣₚ ⌊ R' ⌋ˢ ⊳ Qr }}ad.
Proof.
  intros Θ Δ Qm Qr Hr Hwf Hdisj Θb Ψr R' R Hp Hmon Heq.
  destruct (delta_fresh_flex_defs Hwf Hdisj) as [Hdefs Hflex].
  eapply uskl_precise_erase_refine_gen;
    [ exact Hr | exact Hwf | exact Hdefs | exact Hflex
    | exact Hp | exact Hmon | | exact Heq ].
  intros α Hα Hin. apply (Hdisj α Hα).
  apply binds_In_inv in Hin as [b Hb].
  eapply binds_In. apply Hmon. exact Hb.
Qed.

Lemma ad_refine_mono_paint_lhs_partial_precise : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  Δr [=] empty ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall τb τ, Q' = ptyp_to_bskl_syn τb -> Q = ptyp_to_bskl_syn τ ->
  mono_ptyp τb -> mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  forall Δ, {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τ) }}ad.
Proof.
  intros Θ Δr Q' Q HwfΘ HΔr H; induction H;
    intros τb τu HeqL HeqQ Hmb Hmu Hwτ Δo;
    try solve [ exfalso; symmetry in HeqL;
                solve [ eapply ptyp_to_bskl_syn_all_inh_absurd; exact HeqL
                      | eapply ptyp_to_bskl_syn_ghost_absurd; exact HeqL
                      | eapply ptyp_to_bskl_syn_univ_ghost_absurd; exact HeqL ] ].
  -
    symmetry in HeqL; apply ptyp_to_bskl_syn_unit_inv in HeqL; subst.
    symmetry in HeqQ; apply ptyp_to_bskl_syn_unit_inv in HeqQ; subst.
    simpl. apply ad_ppre__unit. clear; fsetdec.
  -
    symmetry in HeqL; apply ptyp_to_bskl_syn_var_inv in HeqL; subst.
    symmetry in HeqQ; apply ptyp_to_bskl_syn_var_inv in HeqQ.
    inversion HeqQ; subst.
    simpl. apply ad_ppre__var. clear; fsetdec.
  -
    symmetry in HeqL.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqL)
      as (τb1 & τb2 & -> & Heqb1 & Heqb2).
    symmetry in HeqQ.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqQ)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    assert (Hmb1 : mono_ptyp τb1) by (inversion Hmb; assumption).
    assert (Hmb2 : mono_ptyp τb2) by (inversion Hmb; assumption).
    assert (Hm1 : mono_ptyp τ1) by (inversion Hmu; assumption).
    assert (Hm2 : mono_ptyp τ2) by (inversion Hmu; assumption).
    assert (Hw1 : a_wf_ptyp Θ τ1) by (inversion Hwτ; assumption).
    assert (Hw2 : a_wf_ptyp Θ τ2) by (inversion Hwτ; assumption).
    simpl.
    apply ad_ppre__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHad_refine_syn1; auto
      | apply IHad_refine_syn2; auto
      | clear; fsetdec ].
  -
    symmetry in HeqL; apply ptyp_to_bskl_syn_var_inv in HeqL; subst.
    simpl.
    eapply ad_ppre__flex_l; [ eassumption | ].
    apply IHad_refine_syn; auto;
      [ eapply a_wf_aenv_binds_def_mono; eauto ].
  -
    symmetry in HeqQ; apply ptyp_to_bskl_syn_var_inv in HeqQ; subst.
    simpl.
    eapply ad_ppre__flex_r; [ eassumption | ].
    apply IHad_refine_syn; auto;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
Qed.

Lemma ad_pat_consis_monoish_counterpart : forall Ψs Θ ψa Q,
  {{ Ψs ⨟ Θ ⊢ˢ ψa ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  is_dskl ψa ->
  bskl_monoish Q ->
  Ψs [=] empty /\
  exists τa, mono_ptyp τa /\ ψa = ptyp_to_uskl_syn τa.
Proof.
  intros Ψs Θ ψa Q H; induction H; intros HwfΘ Htsk Hmi.
  -
    split; [ assumption | exists ptyp_unit; split;
      [ apply mono_ptyp__unit | reflexivity ] ].
  -
    split; [ assumption | exists (ptyp_var_f α); split;
      [ apply mono_ptyp__var | reflexivity ] ].
  -
    inversion Hmi; subst.
    assert (Ht1 : is_dskl R1) by (inversion Htsk; assumption).
    assert (Ht2 : is_dskl R2) by (inversion Htsk; assumption).
    destruct (IHad_pat_consis1 HwfΘ Ht1 ltac:(assumption))
      as (HΨ1 & τ1 & Hm1 & ->).
    destruct (IHad_pat_consis2 HwfΘ Ht2 ltac:(assumption))
      as (HΨ2 & τ2 & Hm2 & ->).
    split.
    + match goal with HΨ : Ψ [=] union _ _ |- _ =>
        clear - HΨ HΨ1 HΨ2; fsetdec end.
    + exists (ptyp_arrow τ1 τ2); split;
        [ apply mono_ptyp__arrow; assumption | reflexivity ].
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Hmi.
  -  inversion Htsk.
  -  inversion Htsk.
  -  inversion Htsk.
  -  inversion Htsk.
  -
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    destruct (IHad_pat_consis HwfΘ
                ltac:(apply mono_ptyp_to_uskl_syn_is_dskl; exact Hmd) Hmi)
      as (HΨ & _).
    split; [ exact HΨ | ].
    exists (ptyp_var_f α); split; [ apply mono_ptyp__var | reflexivity ].
  -
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    apply IHad_pat_consis;
      [ exact HwfΘ | exact Htsk | apply bskl_monoish_paint; exact Hmd ].
Qed.

Lemma ad_pat_consis_mono_subject_wf : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall τ, R = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  a_wf_ptyp Θ τ.
Proof.
  intros Ψ Θ R Q H; induction H; intros τ0 Heq Hm;
    try solve [ destruct τ0; simpl in Heq;
                solve [ discriminate Heq | inversion Hm ] ].
  -  destruct τ0; simpl in Heq; try discriminate Heq.
    apply a_wf_ptyp__unit.
  -
    destruct τ0; simpl in Heq; try discriminate Heq.
    inversion Heq; subst. apply a_wf_ptyp__var; assumption.
  -
    destruct τ0; simpl in Heq; try discriminate Heq.
    inversion Heq; subst. inversion Hm; subst.
    apply a_wf_ptyp__arrow;
      [ eapply IHad_pat_consis1 | eapply IHad_pat_consis2 ];
      solve [ reflexivity | assumption ].
  -
    destruct τ0; simpl in Heq; try discriminate Heq.
    inversion Heq; subst. apply a_wf_ptyp__var. right; right; eauto.
  -
    eapply IHad_pat_consis; [ exact Heq | exact Hm ].
Qed.

Lemma mono_paint_paint_refine_consis_partial_precise : forall Ψs Θ R Q,
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall τa, R = ptyp_to_uskl_syn τa -> mono_ptyp τa ->
  forall Δr τb, Δr [=] empty -> mono_ptyp τb ->
  {{ Θ ⨟ Δr ⊢ᵣ (ptyp_to_bskl_syn τb) ⊳ Q }}ad ->
  forall Δ, {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τa) }}ad.
Proof.
  intros Ψ Θ R Q Hc Hwf τa Heqa Hma Δr τb HΔr Hmb Hr Δ.
  destruct (consis_mono_join Hc Hwf Heqa Hma) as (Ca & HmCa & HQa & Ha).
  destruct (refine_mono_join Hr Hwf eq_refl Hmb) as (Cb & HmCb & HQb & Hb).
  assert (Hsame : Ca = Cb).
  { apply ptyp_to_bskl_syn_inj; auto. rewrite <- HQa, <- HQb; reflexivity. }
  subst Cb.
  assert (Heq : {{ Θ ⊢ τb ≡ᵗ τa }}a)
    by (eapply a_tyequiv__trans; [ exact Hb | apply a_tyequiv__sym; exact Ha ]).
  pose proof (ad_pat_consis_mono_subject_wf Hc Heqa Hma) as Hwa.
  assert (Hva : forall α, α `in` ftvar_in_ptyp τa -> a_binds_tvar α Θ)
    by (intros; eapply a_wf_ptyp_ftv_tvarish; eassumption).
  destruct ((proj2 (a_tyequiv_mono_vis Heq Hwf)) (conj Hma Hva)) as [_ Hvb].
  eapply ad_refine_mono_paint_lhs_partial_precise with (Δr := empty) (Q' := ptyp_to_bskl_syn τb)
      (Q := ptyp_to_bskl_syn τa);
    [ exact Hwf | clear; fsetdec
    | apply tyequiv_mono_refine_syn; assumption
    | reflexivity | reflexivity | exact Hmb | exact Hma | exact Hwa ].
Qed.

Lemma ad_partial_precise_mono_subject_target_tags_empty : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall τ, P = ptyp_to_pskl τ -> mono_ptyp τ ->
  forall Ψt, d_tags_skl Ψt ψ -> Ψt [=] empty.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros τ0 HeqP Hm Ψt Hdt.
  -  exact (d_tags_skl_unit_inv Hdt).
  -  exact (d_tags_skl_var_inv Hdt).
  -
    destruct τ0; simpl in HeqP; try discriminate HeqP.
    inversion HeqP; subst.
    destruct (d_tags_skl_arrow_inv Hdt)
      as (Ψt1 & Ψt2 & Hd1 & Hd2 & _ & HeqΨt).
    assert (Hm1 : mono_ptyp τ0_1) by (inversion Hm; assumption).
    assert (Hm2 : mono_ptyp τ0_2) by (inversion Hm; assumption).
    pose proof (IHad_partial_precise1 HwfΘ _ eq_refl Hm1 _ Hd1) as He1.
    pose proof (IHad_partial_precise2 HwfΘ _ eq_refl Hm2 _ Hd2) as He2.
    clear - HeqΨt He1 He2; fsetdec.
  -
    destruct τ0; simpl in HeqP; try discriminate HeqP.
    inversion Hm.
  -
    destruct τ0; simpl in HeqP; discriminate HeqP.
  -
    destruct τ0; simpl in HeqP; discriminate HeqP.
  -
    destruct τ0; simpl in HeqP; discriminate HeqP.
  -
    destruct τ0; simpl in HeqP; discriminate HeqP.
  -
    destruct τ0; simpl in HeqP; try discriminate HeqP.
    inversion HeqP; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto | exact Hdt ].
  -
    exact (d_tags_skl_var_inv Hdt).
Qed.

Lemma ad_pat_consis_ftv_bound_open : forall L Θ R (Rβ : atom -> uskl) Q α0,
  (forall β, β `notin` L ->
     forall α', α' `in` ftvar_in_uskl (Rβ β) ->
     α' `in` ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f β)) \/
     (exists α τ, binds α (abind_flex_mono_def τ) ((β ~ abind_tvar) ++ Θ) /\
        (α' = α \/ α' `in` ftvar_in_ptyp τ))) ->
  (forall β, ftvar_in_uskl R [<=] ftvar_in_uskl (Rβ β)) ->
  α0 `in` ftvar_in_uskl R ->
  α0 `in` ftvar_in_bskl Q \/
  (exists α τ, binds α (abind_flex_mono_def τ) Θ /\
     (α0 = α \/ α0 `in` ftvar_in_ptyp τ)).
Proof.
  intros L Θ R Rβ Q α0 IH Hlow HX0.
  pick fresh β for (L `union` singleton α0 `union` ftvar_in_bskl Q).
  assert (HX0' : α0 `in` ftvar_in_uskl (Rβ β))
    by (pose proof (Hlow β) as Hlow'; clear - HX0 Hlow'; fsetdec).
  assert (HβL : β `notin` L) by (clear - Fr; solve_notin_auto).
  destruct (IH β HβL α0 HX0') as [Hin | (α & τ & Hb & Hor)].
  - left.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f β))
      as Hup.
    simpl in *. clear - Hin Hup Fr. fsetdec.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
      [ discriminate Hc | right; exists α, τ; auto ].
Qed.

Lemma ad_pat_consis_ftv_bound : forall Ψ Θ R' Q,
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ Q }}ad ->
  forall α', α' `in` ftvar_in_uskl R' ->
  α' `in` ftvar_in_bskl Q \/
  (exists α τ, binds α (abind_flex_mono_def τ) Θ /\
     (α' = α \/ α' `in` ftvar_in_ptyp τ)).
Proof.
  intros Ψ Θ R' Q H; induction H; intros α0 HX0; simpl in HX0.
  -  exfalso; clear - HX0; fsetdec.
  -  left; simpl; clear - HX0; fsetdec.
  -
    apply union_iff in HX0; destruct HX0 as [HX0 | HX0];
      [ destruct (IHad_pat_consis1 α0 HX0) as [Hin | Hdef]
      | destruct (IHad_pat_consis2 α0 HX0) as [Hin | Hdef] ];
      solve [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  -
    eapply ad_pat_consis_ftv_bound_open
      with (Q := Q) (Rβ := fun β => open_uskl_wrt_uskl R (uskl_var_f β));
      eauto using ftvar_in_uskl_open_uskl_wrt_uskl_lower.
  -
    eapply ad_pat_consis_ftv_bound_open
      with (Q := Q) (Rβ := fun β => open_uskl_wrt_uskl R (uskl_var_f β));
      eauto using ftvar_in_uskl_open_uskl_wrt_uskl_lower.
  -
    eapply ad_pat_consis_ftv_bound_open
      with (Q := Q) (Rβ := fun β => open_uskl_wrt_uskl R (uskl_var_f β));
      eauto using ftvar_in_uskl_open_uskl_wrt_uskl_lower.
  -
    eapply ad_pat_consis_ftv_bound_open
      with (Q := Q) (Rβ := fun β => open_uskl_wrt_uskl R (uskl_var_f β));
      eauto using ftvar_in_uskl_open_uskl_wrt_uskl_lower.
  -  exfalso; clear - HX0; fsetdec.
  -
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  -  exfalso; clear - HX0; fsetdec.
  -
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  -
    eapply ad_pat_consis_ftv_bound_open
      with (Q := Q) (Rβ := fun _ => uskl_univ_ghost R); eauto.
    intros _. simpl. clear. fsetdec.
  -
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ left; exact Hin | right; exact Hdef ].
  -
    right; exists α, τ; split; [ assumption | left; clear - HX0; fsetdec ].
  -
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ | right; exact Hdef ].
    unfold ptyp_to_bskl_syn in Hin.
    rewrite ftvar_pskl_to_bskl_syn in Hin.
    right; exists α, τ; split;
      [ assumption
      | right;
        pose proof (ftvar_ptyp_to_pskl τ) as Hp;
        clear - Hin Hp; fsetdec ].
Qed.

Lemma consis_subject_ftv_defs_bound : forall Ψ Θ R Q S,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     α `in` S /\ ftvar_in_ptyp τ0 [<=] S) ->
  ftvar_in_uskl R [<=] ftvar_in_bskl Q `union` S.
Proof.
  intros Ψ Θ R Q S H Hdefs x Hx.
  destruct (ad_pat_consis_ftv_bound H Hx) as [Hin | (α & τ & Hb & Hor)].
  - clear - Hin; fsetdec.
  - destruct (Hdefs _ _ Hb) as [Hα Hτ].
    destruct Hor as [-> | Hxτ];
      [ clear - Hα; fsetdec | clear - Hxτ Hτ; fsetdec ].
Qed.
