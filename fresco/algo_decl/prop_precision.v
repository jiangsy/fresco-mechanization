Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.consistency.prop_soundness_consis.

Set Implicit Arguments.

Open Scope fresco_ad_scope.

Definition ad_precise (Θ : aenv) (Δ : atoms) (P Q : pskl) : Prop :=
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh Q) }}ad.

Notation "{{ Θ ⨟ Δ ⊢ₚᵣ P ⊑ Q }}ad" := (ad_precise Θ Δ P Q)
  (at level 0, Δ at level 74, P at level 74, Q at level 74,
   format "'{{'  Θ  ⨟  Δ  ⊢ₚᵣ  P  ⊑  Q  '}}ad'") : fresco_ad_scope.

Lemma ad_precise_refl : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ Θ ⨟ Δ ⊢ₚᵣ P ⊑ P }}ad.
Proof. intros. apply ad_refine_syn_refl_inh; auto. Qed.

Lemma pskl_to_bskl_syn_close_rec : forall P α' k,
  pskl_to_bskl_syn (close_pskl_wrt_pskl_rec k α' P)
  = close_bskl_wrt_bskl_rec k α' (pskl_to_bskl_syn P).
Proof.
  induction P; intros; simpl; f_equal; auto;
    repeat match goal with
    | |- context [ if ?t then _ else _ ] => destruct t
    | |- context [ lt_ge_dec ?a ?b ] => destruct (lt_ge_dec a b)
    end; reflexivity.
Qed.

Lemma pskl_to_bskl_syn_close : forall P α,
  pskl_to_bskl_syn (close_pskl_wrt_pskl α P)
  = close_bskl_wrt_bskl α (pskl_to_bskl_syn P).
Proof.
  intros. unfold close_pskl_wrt_pskl, close_bskl_wrt_bskl.
  apply pskl_to_bskl_syn_close_rec.
Qed.

Lemma a_wf_pskl_of_ptyp_vis : forall A Θ Δ,
  lc_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (ptyp_to_pskl A) }}a.
Proof.
  intros A Θ Δ Hlc; revert Θ Δ; induction Hlc; intros Θ Δ Hvis; simpl.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. apply Hvis. simpl. fsetdec.
  - apply a_wf_pskl__arrow;
      [ apply IHHlc1 | apply IHHlc2 ];
      intros α Hα; apply Hvis; simpl; fsetdec.
  - apply a_wf_pskl__all with (L := ftvar_in_ptyp A).
    intros α Hα.
    rewrite <- ptyp_to_pskl_open.
    apply H0.
    intros β Hβ.
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper
                  A (ptyp_var_f α)) as Hup.
    simpl in Hup.
    assert (HY' : β `in` (singleton α `union` ftvar_in_ptyp A))
      by (clear - Hβ Hup; fsetdec).
    apply a_binds_tvar_cons_tvar.
    destruct (union_1 HY') as [HYX | HYA].
    + apply singleton_1 in HYX; subst. left; reflexivity.
    + right. apply Hvis. exact HYA.
Qed.

Lemma a_wf_ptyp_to_wf_pskl : forall Θ Δ A,
  a_wf_ptyp Θ A ->
  {{ Θ ⨟ Δ ⊢ₚₛ (ptyp_to_pskl A) }}a.
Proof.
  intros Θ Δ A H. apply a_wf_pskl_of_ptyp_vis.
  - eapply a_wf_ptyp_lc; eauto.
  - intros α Hα. eapply a_wf_ptyp_ftv_tvarish; eauto.
Qed.

Lemma ad_refine_syn_syn_l : forall Θ Δ Qb Q,
  {{ Θ ⨟ Δ ⊢ᵣ Qb ⊳ Q }}ad ->
  forall P, Qb = pskl_to_bskl_syn P ->
  exists P', Q = pskl_to_bskl_syn P'.
Proof.
  intros Θ Δ Qb Q Href; induction Href; intros P0 Heq.
  -  exists pskl_unit. reflexivity.
  -  exists (pskl_var_f α). reflexivity.
  -
    destruct P0 as [ | | | Pa Pb | | | ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (IHHref1 _ eq_refl) as [Pa' ->].
    destruct (IHHref2 _ eq_refl) as [Pb' ->].
    exists (pskl_arrow Pa' Pb'). reflexivity.
  -
    destruct P0; simpl in Heq; discriminate.
  -
    exists P. reflexivity.
  -
    destruct P0 as [ | | | | | | Pt ]; simpl in Heq; try discriminate.
    inversion Heq; subst. exact (IHHref _ eq_refl).
  -
    destruct P0 as [ | | | | | | Pt ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    pick fresh α for (L `union` dom Θ `union` ftvar_in_bskl Q').
    destruct (H1 α ltac:(auto) (pskl_univ_ghost Pt) eq_refl) as [RX HeqRX].
    exists (pskl_all_syn (close_pskl_wrt_pskl α RX)).
    simpl. rewrite pskl_to_bskl_syn_close. rewrite <- HeqRX.
    rewrite close_bskl_wrt_bskl_open_bskl_wrt_bskl;
      [ reflexivity | clear - Fr; fsetdec ].
  -
    destruct P0 as [ | | | | | | Pt ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (IHHref _ eq_refl) as [R ->].
    exists (pskl_univ_ghost R). reflexivity.
  -
    exact (IHHref (ptyp_to_pskl τ) eq_refl).
  -
    exists (pskl_var_f α). reflexivity.
Qed.

Lemma a_wf_pskl_empty_delta_free : forall Θ Δ P,
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  Δ ∩ ftvar_in_pskl P [=] empty.
Proof.
  intros Θ Δ P Hwf Hdisj.
  apply inter_empty_pointwise. intros α HαΔ.
  intro HXP.
  pose proof (a_wf_pskl_ftv_binds Hwf HXP) as Htv.
  apply (Hdisj α HαΔ).
  destruct Htv as [Hb | [Hb | [τ Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

Lemma binds_flex_def_cons_tvar_inv : forall α β τ Θ,
  binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ) ->
  binds β (abind_flex_mono_def τ) Θ.
Proof.
  intros * Hb.
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
    [ discriminate | exact Hb' ].
Qed.

Lemma delta_fresh_flex_defs : forall Θ Δ,
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) /\
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ).
Proof.
  intros Θ Δ Hwf Hdisj. split.
  - intros β τ Hb. apply inter_empty_pointwise. intros γ Hγ Hγτ.
    apply (Hdisj γ Hγ). apply a_binds_tvar_in_dom.
    eapply a_wf_ptyp_ftv_tvarish;
      [ eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb ] | exact Hγτ ].
  - intros β τ Hβ Hb. apply (Hdisj β Hβ). apply binds_In in Hb. exact Hb.
Qed.

Lemma delta_flex_defs_cons_tvar : forall α Θ Δ,
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  (forall β τ, binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ) ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) /\
  (forall β τ, β `in` Δ ->
     ~ binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ)).
Proof.
  intros α Θ Δ Hdefs Hflex. split.
  - intros β τ Hb. apply binds_flex_def_cons_tvar_inv in Hb.
    exact (Hdefs β τ Hb).
  - intros β τ Hβ Hb. apply binds_flex_def_cons_tvar_inv in Hb.
    exact (Hflex β τ Hβ Hb).
Qed.

Lemma delta_flex_defs_cons_tvar_add : forall α Θ Δ,
  {{ ⊢ Θ }}a ->
  α `notin` dom Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  (forall β τ, binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ) ->
     (add α Δ) ∩ ftvar_in_ptyp τ [=] empty) /\
  (forall β τ, β `in` (add α Δ) ->
     ~ binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ)).
Proof.
  intros α Θ Δ Hwf Hα Hdefs Hflex. split.
  - intros β τ Hb. apply binds_flex_def_cons_tvar_inv in Hb.
    pose proof (Hdefs β τ Hb) as Hd.
    apply inter_empty_pointwise. intros γ Hγ Hγτ.
    destruct (γ == α) as [-> | Hne].
    + apply Hα. apply a_binds_tvar_in_dom.
      eapply a_wf_ptyp_ftv_tvarish;
        [ eapply a_wf_aenv_binds_def_wf; [ exact Hwf | exact Hb ]
        | exact Hγτ ].
    + assert (HγΔ : γ `in` Δ) by (clear - Hγ Hne; fsetdec).
      assert (Hin : γ `in` Δ ∩ ftvar_in_ptyp τ) by (apply inter_3; auto).
      rewrite Hd in Hin. clear - Hin. fsetdec.
  - intros β τ Hβ Hb. apply binds_flex_def_cons_tvar_inv in Hb.
    destruct (β == α) as [-> | Hne].
    + apply Hα. apply binds_In in Hb. exact Hb.
    + apply (Hflex β τ); [ clear - Hβ Hne; fsetdec | exact Hb ].
Qed.

Lemma ad_refine_syn_syn_delta_free : forall Θ Δ Qb Q,
  {{ Θ ⨟ Δ ⊢ᵣ Qb ⊳ Q }}ad ->
  forall F, Qb = pskl_to_bskl_syn F ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  Δ ∩ ftvar_in_bskl Qb [=] empty ->
  Δ ∩ ftvar_in_bskl Q [=] empty.
Proof.
  intros Θ Δ Qb Q Href; induction Href; intros F Heq Hdefs Hflex Hfree.
  -  simpl. clear; fsetdec.
  -  exact Hfree.
  -
    destruct F as [ | | | Fa Fb | | | ]; simpl in Heq; try discriminate.
    inversion Heq; subst. simpl in Hfree |- *.
    apply inter_empty_pointwise. intros α Hα.
    assert (Ha := IHHref1 Fa eq_refl Hdefs Hflex
             ltac:(apply inter_empty_pointwise; intros β Hβ;
                   clear - Hβ Hfree; solve_notin_auto)).
    assert (Hb := IHHref2 Fb eq_refl Hdefs Hflex
             ltac:(apply inter_empty_pointwise; intros β Hβ;
                   clear - Hβ Hfree; solve_notin_auto)).
    clear - Hα Ha Hb. fsetdec.
  -
    destruct F; simpl in Heq; discriminate.
  -
    rewrite ftvar_pskl_to_bskl_syn. exact H.
  -
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    eapply IHHref; [ reflexivity | exact Hdefs | exact Hflex
                   | simpl in Hfree; exact Hfree ].
  -
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    pick fresh α for (L `union` Δ `union` ftvar_in_bskl Q').
    destruct (@delta_flex_defs_cons_tvar α Θ Δ Hdefs Hflex) as [Hdefs' Hflex'].
    assert (Hsub : Δ ∩
                     (ftvar_in_bskl (open_bskl_wrt_bskl Q' (bskl_var_f α)))
                   [=] empty).
    { eapply (H1 α ltac:(auto) (pskl_univ_ghost Ft) eq_refl Hdefs' Hflex').
      simpl in Hfree |- *. exact Hfree. }
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q' (bskl_var_f α))
      as Hlow.
    simpl.
    apply inter_empty_pointwise. intros β Hβ HYP.
    assert (HYo : β `in` ftvar_in_bskl (open_bskl_wrt_bskl Q' (bskl_var_f α)))
      by (clear - HYP Hlow; fsetdec).
    clear - Hβ HYo Hsub. fsetdec.
  -
    destruct F as [ | | | | | | Ft ]; simpl in Heq; try discriminate.
    inversion Heq; subst. simpl.
    eapply IHHref; [ reflexivity | exact Hdefs | exact Hflex
                   | simpl in Hfree; exact Hfree ].
  -
    eapply IHHref; [ reflexivity | exact Hdefs | exact Hflex | ].
    unfold ptyp_to_bskl_syn. rewrite ftvar_pskl_to_bskl_syn.
    pose proof (Hdefs α τ H) as Hd.
    apply inter_empty_pointwise. intros β Hβ Hβτ.
    rewrite ftvar_ptyp_to_pskl in Hβτ.
    assert (Hin : β `in` Δ ∩ ftvar_in_ptyp τ) by (apply inter_3; auto).
    rewrite Hd in Hin. clear - Hin. fsetdec.
  -
    simpl. apply inter_empty_pointwise. intros β Hβ Hβα.
    assert (HeqY : β = α) by (clear - Hβα; fsetdec). subst.
    exact (Hflex α τ Hβ H).
Qed.

Lemma ad_refine_syn_ghost_l : forall Θ Δ P Qr,
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_syn P) ⊳ Qr }}ad ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  Δ ∩ ftvar_in_pskl P [=] empty ->
  {{ Θ ⨟ Δ ⊢ᵣ bskl_ghost ⊳ Qr }}ad.
Proof.
  intros Θ Δ P Qr Href Hdefs Hflex HfrP.
  pose proof (ad_refine_syn_syn_delta_free Href P eq_refl Hdefs Hflex
                ltac:(rewrite ftvar_pskl_to_bskl_syn; exact HfrP)) as Hfr.
  destruct (ad_refine_syn_syn_l Href P eq_refl) as [G ->].
  apply ad_refine_syn__ghost.
  rewrite ftvar_pskl_to_bskl_syn in Hfr. exact Hfr.
Qed.

Lemma ad_refine_syn_trans_gen : forall Θ Δ Qm Qr,
  {{ Θ ⨟ Δ ⊢ᵣ Qm ⊳ Qr }}ad ->
  {{ ⊢ Θ }}a ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     Δ ∩ ftvar_in_ptyp τ [=] empty) ->
  (forall β τ, β `in` Δ -> ~ binds β (abind_flex_mono_def τ) Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Qr) }}a ->
  forall Ql,
  {{ Θ ⨟ Δ ⊢ᵣ Ql ⊳ Qm }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Ql ⊳ Qr }}ad.
Proof.
  intros Θ Δ Qm Qr Hr.
  induction Hr; intros Hwf Hdefs Hflex HwfQr Ql Hp.
  -  exact Hp.
  -  exact Hp.
  -
    rename Q1 into Qa. rename Q2 into Qb. rename Q3 into Qc. rename Q4 into Qd.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_arrow Qa Qb) ⊳ (bskl_arrow Qc Qd) }}ad)
      by (apply ad_refine_syn__arrow; assumption).
    remember (bskl_arrow Qa Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + inversion HM; subst. simpl in HwfQr.
      inversion HwfQr as [ | | Θw Δw Pw1 Pw2 Hw1 Hw2 | | | ]; subst.
      apply ad_refine_syn__arrow; [ assumption | apply IHHr1 | apply IHHr2 ]; auto.
    + eapply ad_refine_syn_ghost_l with (P := P);
        [ exact Hrr | exact Hdefs | exact Hflex | eassumption ].
    + apply ad_refine_syn__univ_ghost_remove; [ assumption | apply IHHp; auto ].
    + eapply ad_refine_syn__flex_l;
        [ eassumption | ]. apply IHHp; auto.
  -
    rename Q into Qb. rename Q' into Qc.
    remember (bskl_all_inh Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate;
      [ | destruct P; simpl in HM; discriminate | | ].
    +
      inversion HM; subst. simpl in HwfQr.
      inversion HwfQr as [ | | | L2 Θw Δw Pw Hbody | | ]; subst.
      apply ad_refine_syn__all
        with (L := L `union` L0 `union` L2 `union` dom Θ `union` Δ);
        [ assumption | intros α Hα ].
      assert (HαΘ : α `notin` dom Θ) by (clear - Hα; fsetdec).
      destruct (delta_flex_defs_cons_tvar_add Hwf HαΘ Hdefs Hflex)
        as [Hdefs' Hflex'].
      apply H1 with (α := α);
        [ clear - Hα; fsetdec | apply a_wf_aenv__tvar; auto
        | exact Hdefs' | exact Hflex'
        | rewrite bskl_to_pskl_open; apply Hbody; clear - Hα; fsetdec
        | apply H3; clear - Hα; fsetdec ].
    + apply ad_refine_syn__univ_ghost_remove; [ assumption | apply IHHp; auto ].
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  -
    rename P into Pf.
    remember (@bskl_ghost) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    +
      destruct P; simpl in HM; try discriminate.
      apply ad_refine_syn__ghost. assumption.
    + apply ad_refine_syn__univ_ghost_remove; [ assumption | apply IHHp; auto ].
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  -
    rename Q into Qb. rename Q' into Qc.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Qb) ⊳ Qc }}ad)
      by (apply ad_refine_syn__univ_ghost_remove; assumption).
    remember (bskl_univ_ghost Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_ghost_l with (P := P);
        [ exact Hrr | exact Hdefs | exact Hflex | eassumption ].
    + apply ad_refine_syn__univ_ghost_remove; [ assumption | apply IHHp; auto ].
    +
      inversion HM; subst.
      apply ad_refine_syn__univ_ghost_remove; [ assumption | apply IHHr; auto ].
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  -
    rename Q into Qb. rename Q' into Qc.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Qb) ⊳ (bskl_all_syn Qc) }}ad)
      by (eapply ad_refine_syn__univ_ghost_fill with (L := L); assumption).
    remember (bskl_univ_ghost Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_ghost_l with (P := P);
        [ exact Hrr | exact Hdefs | exact Hflex | eassumption ].
    + apply ad_refine_syn__univ_ghost_remove; [ assumption | apply IHHp; auto ].
    +
      inversion HM; subst.
      simpl in HwfQr.
      inversion HwfQr as [ | | | L2 Θw Δw Pw Hbody | | ]; subst.
      apply ad_refine_syn__univ_ghost_fill
        with (L := L `union` L2 `union` dom Θ `union` Δ);
        [ assumption | intros α Hα ].
      destruct (@delta_flex_defs_cons_tvar α Θ Δ Hdefs Hflex) as [Hdefs' Hflex'].
      apply H1 with (α := α);
        [ clear - Hα; fsetdec
        | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
        | exact Hdefs' | exact Hflex'
        | | ].
      { rewrite bskl_to_pskl_open.
        eapply a_wf_pskl_delta_mono;
          [ apply (Hbody α ltac:(clear - Hα; solve_notin_auto))
          | intros β _ Hβ; clear - Hβ; fsetdec ]. }
      { eapply ad_refine_syn_weaken;
          [ apply ad_refine_syn__univ_ghost_keep; eassumption
          | intros y b Hb; unfold binds; right; exact Hb ]. }
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  -
    rename Q into Qb. rename Q' into Qc.
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Qb) ⊳ (bskl_univ_ghost Qc) }}ad)
      by (apply ad_refine_syn__univ_ghost_keep; assumption).
    remember (bskl_univ_ghost Qb) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    + eapply ad_refine_syn_ghost_l with (P := P);
        [ exact Hrr | exact Hdefs | exact Hflex | eassumption ].
    + apply ad_refine_syn__univ_ghost_remove; [ assumption | apply IHHp; auto ].
    + inversion HM; subst.
      simpl in HwfQr.
      inversion HwfQr as [ | | | | | Θw Δw Pw Hg Hwb ]; subst.
      apply ad_refine_syn__univ_ghost_keep; [ assumption | ].
      apply IHHr; auto.

      eapply a_wf_pskl_delta_mono.
      * eapply a_wf_pskl_tvar_mono; [ exact Hwb | ].
        intros β Hb. apply a_binds_tvar_aenv_minus in Hb. apply Hb.
      * intros β Hβ HβΔ. exfalso.
        pose proof (a_wf_pskl_ftv_binds Hwb Hβ) as Hb.
        apply a_binds_tvar_aenv_minus in Hb. destruct Hb as [_ Hn].
        exact (Hn HβΔ).
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
  -
    assert (Hrr : {{ Θ ⨟ Δ ⊢ᵣ (bskl_var_f α) ⊳ Q' }}ad)
      by (eapply ad_refine_syn__flex_l; eassumption).
    remember (bskl_var_f α) as M eqn:HM. revert HM.
    induction Hp; intros HM; try discriminate.
    +
      inversion HM; subst.
      eapply ad_refine_syn__flex_l; eassumption.
    + eapply ad_refine_syn_ghost_l with (P := P);
        [ exact Hrr | exact Hdefs | exact Hflex | eassumption ].
    + apply ad_refine_syn__univ_ghost_remove; [ assumption | apply IHHp; auto ].
    + eapply ad_refine_syn__flex_l; [ eassumption | ]. apply IHHp; auto.
    +
      inversion HM; subst.
      match goal with
      | Hb1 : binds ?a (abind_flex_mono_def ?t1) Θ,
        Hb2 : binds ?a (abind_flex_mono_def ?t2) Θ |- _ =>
          assert (Heqτ : t1 = t2) by
            (pose proof (a_wf_aenv_uniq Hwf) as Hu;
             pose proof (binds_unique _ _ _ _ _ Hb1 Hb2 Hu) as He;
             inversion He; reflexivity)
      end.
      subst.
      apply IHHr; auto.
  -
    eapply ad_refine_syn__flex_r; [ eassumption | ].
    apply IHHr; auto.
    rewrite bskl_to_pskl_ptyp_to_bskl_syn.
    apply a_wf_ptyp_to_wf_pskl.
    eapply a_wf_aenv_binds_def_wf; [ exact Hwf | eassumption ].
Qed.

Lemma ad_refine_syn_trans : forall Θ Δ Qm Qr,
  {{ Θ ⨟ Δ ⊢ᵣ Qm ⊳ Qr }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Qr) }}a ->
  forall Ql,
  {{ Θ ⨟ Δ ⊢ᵣ Ql ⊳ Qm }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ Ql ⊳ Qr }}ad.
Proof.
  intros Θ Δ Qm Qr Hr Hwf Hdisj HwfQr Ql Hp.
  destruct (delta_fresh_flex_defs Hwf Hdisj) as [Hdefs Hflex].
  eapply ad_refine_syn_trans_gen; eauto.
Qed.

Corollary ad_precise_preserves_refine : forall Θ Δ P P' Q,
  {{ Θ ⨟ Δ ⊢ₚᵣ P ⊑ P' }}ad ->
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P') ⊳ Q }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α, α `in` Δ -> α `notin` dom Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  {{ Θ ⨟ Δ ⊢ᵣ (pskl_to_bskl_inh P) ⊳ Q }}ad.
Proof.
  intros Θ Δ P P' Q Hprec Href Hwf Hdisj HwfA.
  eapply ad_refine_syn_trans;
    [ exact Href | exact Hwf | exact Hdisj | exact HwfA | exact Hprec ].
Qed.

Lemma a_wf_pskl_all_inv : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}a ->
  exists L, forall α, α `notin` L ->
    {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ₚₛ
         (open_pskl_wrt_pskl P (pskl_var_f α)) }}a.
Proof. intros * H; inversion H; subst; eauto. Qed.

Definition delta_def_fresh (Δ : atoms) (Θ : aenv) : Prop :=
  forall β α τ, β `in` Δ ->
    binds α (abind_flex_mono_def τ) Θ ->
    β `notin` ftvar_in_ptyp τ.

Lemma delta_def_fresh_empty : forall Θ, delta_def_fresh empty Θ.
Proof. intros Θ β α τ Hin; clear - Hin; fsetdec. Qed.

Lemma delta_def_fresh_weaken_tvar : forall Δ Θ β,
  delta_def_fresh Δ Θ ->
  delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ).
Proof.
  intros * Hfr γ α τ Hγ Hb.
  eapply Hfr; [ exact Hγ | eapply binds_flex_def_cons_tvar_inv; exact Hb ].
Qed.

Lemma delta_def_fresh_open_tvar : forall Δ Θ β,
  {{ ⊢ Θ }}a -> β `notin` dom Θ -> delta_def_fresh Δ Θ ->
  delta_def_fresh (add β Δ) ((β ~ abind_tvar) ++ Θ).
Proof.
  intros * Hwf Hβ Hfr γ α τ Hγ Hb.
  apply binds_flex_def_cons_tvar_inv in Hb.
  destruct (γ == β) as [-> | Hne].
  - pose proof (a_wf_ptyp_ftv_dom (@a_wf_aenv_binds_def_wf Θ α τ Hwf Hb)) as Hd.
    clear - Hd Hβ; fsetdec.
  - eapply Hfr; [ clear - Hγ Hne; fsetdec | exact Hb ].
Qed.
