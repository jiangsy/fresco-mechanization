Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo_decl.def_consis_refine.

Set Implicit Arguments.

Local Ltac fold_def_split S HeqS :=
  destruct S as [ | n0x | X0x | R01 R02 | R00 | ε0 R00 | | R00 | | R00 ];
    simpl in HeqS; try discriminate HeqS.
Local Ltac fold_def_no_var X β Hm HeqS :=
  destruct (eq_var X β) as [->|?];
    [ unfold ptyp_to_uskl_syn in HeqS; destruct Hm; simpl in HeqS | ];
    discriminate HeqS.

Lemma ad_pat_consis_fold_def : forall Θ β τ Ψ R' Q,
  ad_pat_consis Ψ Θ R' Q ->
  binds β (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ ->
  forall S0x,
  R' = subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β S0x ->
  ad_pat_consis Ψ Θ S0x Q.
Proof.
  intros Θ β τ Ψ R' Q H Hb Hm.
  assert (Hlcτ : lc_uskl (ptyp_to_uskl_syn τ)).
  { clear - Hm. induction Hm; unfold ptyp_to_uskl_syn in *; simpl; auto. }

  induction H; intros S0x HeqS.
  -
    fold_def_split S0x HeqS.
    + apply ad_pat_consis__unit; auto.
    + destruct (eq_var X0x β) as [->|Hne].
      * apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb | ].
        rewrite <- HeqS. apply ad_pat_consis__unit; auto.
      * discriminate HeqS.
  -
    fold_def_split S0x HeqS.
    destruct (eq_var X0x β) as [->|Hne].
    + apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb | ].
      rewrite <- HeqS. apply ad_pat_consis__var; auto.
    + inversion HeqS; subst. apply ad_pat_consis__var; auto.
  -
    fold_def_split S0x HeqS.
    + destruct (eq_var X0x β) as [->|Hne].
      * apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb | ].
        rewrite <- HeqS. eapply ad_pat_consis__arrow; eauto.
      * discriminate HeqS.
    + inversion HeqS; subst. eapply ad_pat_consis__arrow; eauto.
  -
    fold_def_split S0x HeqS; [ fold_def_no_var X0x β Hm HeqS | ].
    inversion HeqS; subst.
    eapply ad_pat_consis__forall_inh_tagged with (L := L `union` {{β}});
      eauto.
    intros α Hα. eapply H0; auto.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  -
    fold_def_split S0x HeqS; [ fold_def_no_var X0x β Hm HeqS | ].
    inversion HeqS; subst.
    eapply ad_pat_consis__forall_inh_untagged with (L := L `union` {{β}}).
    intros α Hα. eapply H0; auto.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  -
    fold_def_split S0x HeqS; [ fold_def_no_var X0x β Hm HeqS | ].
    inversion HeqS; subst.
    eapply ad_pat_consis__forall_syn_tagged with (L := L `union` {{β}}).
    intros α Hα. eapply H0; auto.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  -
    fold_def_split S0x HeqS; [ fold_def_no_var X0x β Hm HeqS | ].
    inversion HeqS; subst.
    eapply ad_pat_consis__forall_syn with (L := L `union` {{β}}).
    intros α Hα. eapply H0; auto.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var; auto.
  -
    fold_def_split S0x HeqS; [ fold_def_no_var X0x β Hm HeqS | ].
    apply ad_pat_consis__ghostg; auto.
  -
    fold_def_split S0x HeqS; [ fold_def_no_var X0x β Hm HeqS | ].
    inversion HeqS; subst. apply ad_pat_consis__dot_univ_ghost; auto.
  -
    fold_def_split S0x HeqS; [ fold_def_no_var X0x β Hm HeqS | ].
    apply ad_pat_consis__ghost; auto.
  -
    fold_def_split S0x HeqS; [ fold_def_no_var X0x β Hm HeqS | ].
    inversion HeqS; subst. apply ad_pat_consis__univ_ghost; auto.
  -
    fold_def_split S0x HeqS; [ fold_def_no_var X0x β Hm HeqS | ].
    inversion HeqS; subst.
    eapply ad_pat_consis__univ_ghost_inh with (L := L);
      try (intros α Hα; eapply H0; auto; simpl; reflexivity).
  -
    fold_def_split S0x HeqS; [ fold_def_no_var X0x β Hm HeqS | ].
    inversion HeqS; subst. apply ad_pat_consis__univ_ghost_drop; auto.
  -
    fold_def_split S0x HeqS.
    destruct (eq_var X0x β) as [->|Hne].
    + apply ad_pat_consis__flex_l with (τ := τ); [ exact Hb | ].
      rewrite <- HeqS. eapply ad_pat_consis__flex_l; eauto.
    + inversion HeqS; subst. eapply ad_pat_consis__flex_l; eauto.
  -
    eapply ad_pat_consis__flex_r; eauto.
Qed.
