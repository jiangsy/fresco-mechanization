Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_metasubst_composition.

Set Implicit Arguments.

Fixpoint aenv_msubst (Θ : aenv) : metasubst :=
  match Θ with
  | nil => nil
  | (α, abind_flex_mono_def τ) :: Θ' =>
      (α, msubst_ptyp (aenv_msubst Θ') τ) :: aenv_msubst Θ'
  | (α, abind_flex_mono) :: Θ' =>
      (α, ptyp_var_f α) :: aenv_msubst Θ'
  | _ :: Θ' => aenv_msubst Θ'
  end.

Notation "⇓ᵗ[ Θ ] A" := (msubst_ptyp (aenv_msubst Θ) A)
  (at level 5, Θ at level 0, A at level 0, no associativity) : type_scope.
Notation "⇓ˢ[ Θ ] P" := (msubst_pskl (aenv_msubst Θ) P)
  (at level 5, Θ at level 0, P at level 0, no associativity) : type_scope.

Lemma aenv_msubst_tvar : forall α Θ,
  aenv_msubst ((α ~ abind_tvar) ++ Θ) = aenv_msubst Θ.
Proof. reflexivity. Qed.

Lemma aenv_msubst_var_typ : forall x A Θ,
  aenv_msubst ((x ~ abind_var_typ A) ++ Θ) = aenv_msubst Θ.
Proof. reflexivity. Qed.

Lemma aenv_msubst_var_skl : forall x P Θ,
  aenv_msubst ((x ~ abind_var_skl P) ++ Θ) = aenv_msubst Θ.
Proof. reflexivity. Qed.

Lemma dom_aenv_msubst : forall Θ,
  dom (aenv_msubst Θ) [<=] dom Θ.
Proof.
  induction Θ as [ | [α b] Θ' IH ]; simpl; [ fsetdec | ].
  destruct b; simpl; clear - IH; fsetdec.
Qed.

Lemma aenv_msubst_notin : forall Θ α,
  α `notin` dom Θ ->
  msubst_lookup (aenv_msubst Θ) α = ptyp_var_f α.
Proof.
  intros Θ α Hα. apply msubst_lookup_notin.
  pose proof (dom_aenv_msubst Θ). clear - Hα H. fsetdec.
Qed.

Lemma aenv_msubst_lookup_app : forall Θp Θs α,
  uniq (Θp ++ Θs) ->
  α `in` dom Θs ->
  msubst_lookup (aenv_msubst (Θp ++ Θs)) α = msubst_lookup (aenv_msubst Θs) α.
Proof.
  intros Θp; induction Θp as [ | [β b] Θp' IH ];
    intros Θs α Huniq Hα; simpl; [ reflexivity | ].
  simpl in Huniq.
  assert (HnotinY : β `notin` dom (Θp' ++ Θs))
    by (inversion Huniq; subst; assumption).
  assert (Huniq' : uniq (Θp' ++ Θs)) by (inversion Huniq; subst; assumption).
  assert (HYne : α <> β).
  { intros Heq. subst β. apply HnotinY.
    rewrite dom_app. clear - Hα. fsetdec. }
  destruct b; simpl;
    try (apply IH; assumption);
    (destruct (α == β) as [Heq | Hne];
     [ exfalso; apply HYne; exact Heq | apply IH; assumption ]).
Qed.

Lemma msubst_ptyp_open_rec_lc : forall κ,
  msubst_lc κ ->
  forall A A' k,
  msubst_ptyp κ (open_ptyp_wrt_ptyp_rec k A' A)
  = open_ptyp_wrt_ptyp_rec k (msubst_ptyp κ A') (msubst_ptyp κ A).
Proof.
  intros κ Hlc A; induction A; intros A' k; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - symmetry.
    apply open_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp.
    apply degree_ptyp_wrt_ptyp_O.
    apply degree_ptyp_wrt_ptyp_of_lc_ptyp.
    apply Hlc.
Qed.

Lemma msubst_ptyp_open_lc : forall κ A α,
  msubst_lc κ ->
  α `notin` dom κ ->
  msubst_ptyp κ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
  = open_ptyp_wrt_ptyp (msubst_ptyp κ A) (ptyp_var_f α).
Proof.
  intros κ A α Hlc Hα. unfold open_ptyp_wrt_ptyp.
  rewrite (msubst_ptyp_open_rec_lc Hlc A (ptyp_var_f α) 0).
  simpl. rewrite msubst_lookup_notin by exact Hα. reflexivity.
Qed.

Lemma msubst_ptyp_lc_lc : forall κ A,
  msubst_lc κ ->
  lc_ptyp A ->
  lc_ptyp (msubst_ptyp κ A).
Proof.
  intros κ A Hlc HA; induction HA; simpl.
  - constructor.
  - apply Hlc.
  - constructor; auto.
  - pick fresh α for (dom κ).
    apply lc_ptyp_all_exists with (α1 := α).
    erewrite <- msubst_ptyp_open_lc; [ apply H0 | exact Hlc | clear - Fr; fsetdec ].
Qed.

Lemma aenv_msubst_lc : forall Θ,
  {{ ⊢ Θ }}a ->
  msubst_lc (aenv_msubst Θ).
Proof.
  intros Θ Hwf; induction Hwf; intros α0; simpl.
  - constructor.
  - destruct (α0 == α) as [-> | Hne];
      [ constructor | apply IHHwf ].
  - destruct (α0 == α) as [-> | Hne];
      [ apply msubst_ptyp_lc_lc; [ exact IHHwf | apply mono_ptyp_lc; exact H1 ]
      | apply IHHwf ].
  - apply IHHwf.
  - apply IHHwf.
  - apply IHHwf.
Qed.

Lemma aenv_msubst_lookup_def : forall Θ α τ,
  {{ ⊢ Θ }}a ->
  binds α (abind_flex_mono_def τ) Θ ->
  msubst_lookup (aenv_msubst Θ) α = ⇓ᵗ[Θ] τ.
Proof.
  intros Θ α τ Hwf; revert α τ.
  induction Hwf as
    [ | β Θ' Hnd Hwf IH
      | β σ Θ' Hnd Hwpσ Hmσ Hwf IH
      | x P Θ' Hnd Hwp Hwf IH
      | x A Θ' Hnd Hwp Hwf IH
      | β Θ' Hnd Hwf IH ];
    intros α τ Hb; simpl in *.
  - inversion Hb.
  -
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb']; [ discriminate | ].
    assert (Hfr : β `notin` ftvar_in_ptyp τ)
      by (eapply a_wf_aenv_head_notin_def_ftv;
          [ apply a_wf_aenv__flex; eassumption | exact Hb' ]).
    rewrite msubst_ptyp_cons_notin by exact Hfr.
    destruct (α == β) as [Heqα | Hne].
    { exfalso. subst β. apply binds_In in Hb'. clear - Hb' Hnd. fsetdec. }
    apply IH; exact Hb'.
  -
    destruct (α == β) as [Heqα | Hne].
    + subst β.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'].
      * assert (Heqτ : τ = σ) by (inversion Heqb; reflexivity). subst σ.
        assert (Hfr : α `notin` ftvar_in_ptyp τ)
          by (eapply a_wf_aenv_def_head_fresh;
              apply a_wf_aenv__flex_def; eassumption).
        rewrite msubst_ptyp_cons_notin by exact Hfr.
        reflexivity.
      * exfalso. apply binds_In in Hb'. clear - Hb' Hnd. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqα ?] | Hb'];
        [ exfalso; apply Hne; exact Heqα | ].
      assert (Hfr : β `notin` ftvar_in_ptyp τ)
        by (eapply a_wf_aenv_head_notin_def_ftv;
            [ apply a_wf_aenv__flex_def; eassumption | exact Hb' ]).
      rewrite msubst_ptyp_cons_notin by exact Hfr.
      apply IH; exact Hb'.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb']; [ discriminate | ].
    apply IH; exact Hb'.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb']; [ discriminate | ].
    apply IH; exact Hb'.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb']; [ discriminate | ].
    apply IH; exact Hb'.
Qed.

Lemma a_tyequiv_downarrow : forall Θ A A',
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  ⇓ᵗ[Θ] A = ⇓ᵗ[Θ] A'.
Proof.
  intros Θ A A' Hwf Heq; induction Heq.
  - reflexivity.
  - symmetry; auto.
  - transitivity (⇓ᵗ[Θ] B); auto.
  - simpl. apply aenv_msubst_lookup_def; assumption.
  - simpl. f_equal; auto.
  - simpl. f_equal.
    pose proof (aenv_msubst_lc Hwf) as Hlc.
    pick fresh α for (L `union` dom (aenv_msubst Θ)
                        `union` ftvar_in_ptyp (⇓ᵗ[Θ] A)
                        `union` ftvar_in_ptyp (⇓ᵗ[Θ] B)).
    apply open_ptyp_wrt_ptyp_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | ].
    rewrite <- msubst_ptyp_open_lc by (first [ exact Hlc | clear - Fr; fsetdec ]).
    rewrite <- msubst_ptyp_open_lc by (first [ exact Hlc | clear - Fr; fsetdec ]).
    apply H0; [ clear - Fr; fsetdec | exact Hwf ].
Qed.

Lemma msubst_ptyp_outer_ext : forall ζ κ κ' A,
  (forall α, α `in` ftvar_in_ptyp A ->
     msubst_ptyp ζ (msubst_lookup κ α) = msubst_ptyp ζ (msubst_lookup κ' α)) ->
  msubst_ptyp ζ (msubst_ptyp κ A) = msubst_ptyp ζ (msubst_ptyp κ' A).
Proof.
  intros ζ κ κ' A; induction A; intros Hag; simpl.
  - reflexivity.
  - reflexivity.
  - apply Hag. simpl. fsetdec.
  - f_equal; [ apply IHA1 | apply IHA2 ];
      intros α Hα; apply Hag; simpl; fsetdec.
  - f_equal. apply IHA. intros α Hα; apply Hag; simpl; fsetdec.
Qed.

Lemma msubst_pskl_outer_ext : forall ζ κ κ' P,
  (forall α, α `in` ftvar_in_pskl P ->
     msubst_ptyp ζ (msubst_lookup κ α) = msubst_ptyp ζ (msubst_lookup κ' α)) ->
  msubst_pskl ζ (msubst_pskl κ P) = msubst_pskl ζ (msubst_pskl κ' P).
Proof.
  intros ζ κ κ' P;
    induction P as [ | n | β | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hag; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite !msubst_pskl_embed_ptyp. f_equal. apply Hag. simpl. fsetdec.
  - f_equal; [ apply IHa | apply IHb ];
      intros α Hα; apply Hag; simpl; fsetdec.
  - f_equal. apply IHall. intros α Hα; apply Hag; simpl; fsetdec.
  - reflexivity.
  - f_equal. apply IHt. intros α Hα; apply Hag; simpl; fsetdec.
Qed.

Lemma msubst_lookup_cons_eq : forall (α1 : atom) τ0 κ,
  msubst_lookup ((α1, τ0) :: κ) α1 = τ0.
Proof.
  intros α1 τ0 κ. simpl.
  destruct (α1 == α1) as [_ | Hc]; [ reflexivity | congruence ].
Qed.

Lemma msubst_lookup_cons_neq : forall (α α1 : atom) τ0 κ,
  α <> α1 ->
  msubst_lookup ((α1, τ0) :: κ) α = msubst_lookup κ α.
Proof.
  intros α α1 τ0 κ Hne. simpl.
  destruct (α == α1) as [Hc | _]; [ congruence | reflexivity ].
Qed.

Lemma msubst_ptyp_subst : forall κ τ α1 A,
  msubst_ptyp κ (subst_ptyp_in_ptyp τ α1 A)
  = msubst_ptyp ((α1, msubst_ptyp κ τ) :: κ) A.
Proof.
  intros κ τ α1 A;
    induction A as [ | n | β | A1 IH1 A2 IH2 | A0 IH0 ].
  - reflexivity.
  - reflexivity.
  - destruct (β == α1) as [Heq | Hne].
    + subst β. cbn [subst_ptyp_in_ptyp msubst_ptyp].
      destruct (α1 == α1) as [_ | Hc]; [ | congruence ].
      rewrite msubst_lookup_cons_eq. reflexivity.
    + cbn [subst_ptyp_in_ptyp msubst_ptyp].
      destruct (β == α1) as [Hc | _]; [ congruence | ].
      cbn [msubst_ptyp].
      rewrite msubst_lookup_cons_neq by exact Hne. reflexivity.
  - cbn [subst_ptyp_in_ptyp msubst_ptyp]. f_equal; auto.
  - cbn [subst_ptyp_in_ptyp msubst_ptyp]. f_equal; auto.
Qed.

Lemma msubst_pskl_subst : forall κ τ α1 P,
  msubst_pskl κ (subst_pskl_in_pskl (ptyp_to_pskl τ) α1 P)
  = msubst_pskl ((α1, msubst_ptyp κ τ) :: κ) P.
Proof.
  intros κ τ α1 P;
    induction P as [ | n | β | Pa IHa Pb IHb | Pall IHall | | Pt IHt ].
  - reflexivity.
  - reflexivity.
  - destruct (β == α1) as [Heq | Hne].
    + subst β. cbn [subst_pskl_in_pskl msubst_pskl].
      destruct (α1 == α1) as [_ | Hc]; [ | congruence ].
      rewrite msubst_lookup_cons_eq.
      apply msubst_pskl_embed_ptyp.
    + cbn [subst_pskl_in_pskl msubst_pskl].
      destruct (β == α1) as [Hc | _]; [ congruence | ].
      cbn [msubst_pskl].
      rewrite msubst_lookup_cons_neq by exact Hne. reflexivity.
  - cbn [subst_pskl_in_pskl msubst_pskl]. f_equal; auto.
  - cbn [subst_pskl_in_pskl msubst_pskl]. f_equal; auto.
  - reflexivity.
  - cbn [subst_pskl_in_pskl msubst_pskl]. f_equal; auto.
Qed.

Lemma downarrow_subst_ptyp : forall Θ κ0 α1 τ τ' A,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) }}a ->
  ⇓ᵗ[Θ] (msubst_ptyp κ0 (subst_ptyp_in_ptyp τ α1 A))
  = ⇓ᵗ[Θ] (msubst_ptyp ((α1, τ') :: κ0) A).
Proof.
  intros Θ κ0 α1 τ τ' A Hwf Heq.
  rewrite msubst_ptyp_subst.
  apply msubst_ptyp_outer_ext.
  intros α Hα. simpl.
  destruct (α == α1) as [-> | Hne]; [ | reflexivity ].
  symmetry. apply a_tyequiv_downarrow; assumption.
Qed.

Lemma downarrow_subst_pskl : forall Θ κ0 α1 τ τ' P,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) }}a ->
  ⇓ˢ[Θ] (msubst_pskl κ0 (subst_pskl_in_pskl (ptyp_to_pskl τ) α1 P))
  = ⇓ˢ[Θ] (msubst_pskl ((α1, τ') :: κ0) P).
Proof.
  intros Θ κ0 α1 τ τ' P Hwf Heq.
  rewrite msubst_pskl_subst.
  apply msubst_pskl_outer_ext.
  intros α Hα. simpl.
  destruct (α == α1) as [-> | Hne]; [ | reflexivity ].
  symmetry. apply a_tyequiv_downarrow; assumption.
Qed.

Corollary downarrow_subst_ptyp_size : forall Θ κ0 α1 τ τ' A,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) }}a ->
  size_ptyp (⇓ᵗ[Θ] (msubst_ptyp κ0 (subst_ptyp_in_ptyp τ α1 A)))
  = size_ptyp (⇓ᵗ[Θ] (msubst_ptyp ((α1, τ') :: κ0) A)).
Proof.
  intros. erewrite downarrow_subst_ptyp by eauto. reflexivity.
Qed.

Corollary downarrow_subst_pskl_size : forall Θ κ0 α1 τ τ' P,
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ τ' ≡ᵗ (msubst_ptyp κ0 τ) }}a ->
  size_pskl (⇓ˢ[Θ] (msubst_pskl κ0 (subst_pskl_in_pskl (ptyp_to_pskl τ) α1 P)))
  = size_pskl (⇓ˢ[Θ] (msubst_pskl ((α1, τ') :: κ0) P)).
Proof.
  intros. erewrite downarrow_subst_pskl by eauto. reflexivity.
Qed.

Lemma a_inc_equiv_dom : forall Θ0 κ1 κ2 Θ,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  dom κ1 [<=] dom Θ0 /\ dom κ2 [<=] dom Θ0.
Proof.
  intros Θ0 κ1 κ2 Θ Hie; induction Hie; simpl in *;
    try (destruct IHHie as [H1 H2]);
    split; try fsetdec.
Qed.

Lemma a_inc_equiv_lookup_tvar : forall Θ0 κ1 κ2 Θ,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  {{ ⊢ Θ0 }}a ->
  forall α', a_binds_tvar α' Θ0 ->
  {{ Θ ⊢ (msubst_lookup κ1 α') ≡ᵗ (msubst_lookup κ2 α') }}a.
Proof.
  intros Θ0 κ1 κ2 Θ Hie; induction Hie; intros Hwf α' Hbt.
  -
    destruct Hbt as [Hb | [Hb | [τ Hb]]]; inversion Hb.
  -
    assert (Hwf' : {{ ⊢ Θ }}a) by (inversion Hwf; auto).
    simpl. destruct (α' == α) as [-> | Hne];
      [ assumption | ].
    apply IHHie; [ exact Hwf' | ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq ?] | Hb'];
      try (exfalso; apply Hne; exact Heq);
      [ left | right; left | right; right; exists τ ]; exact Hb'.
  -
    assert (Hwf' : {{ ⊢ Θ }}a) by (inversion Hwf; auto).
    simpl. destruct (α' == α) as [-> | Hne];
      [ assumption | ].
    apply IHHie; [ exact Hwf' | ].
    destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq ?] | Hb'];
      try (exfalso; apply Hne; exact Heq);
      [ left | right; left | right; right; exists τ0 ]; exact Hb'.
  -
    assert (Hwf' : {{ ⊢ Θ }}a) by (inversion Hwf; auto).
    assert (Hbt' : a_binds_tvar α' Θ).
    { destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        try discriminate;
        [ left | right; left | right; right; exists τ0 ]; exact Hb'. }
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds in *;
        apply in_or_app; right; simpl; right; exact Hby
      | apply IHHie; assumption ].
  -
    assert (Hwf' : {{ ⊢ Θ }}a) by (inversion Hwf; auto).
    assert (Hbt' : a_binds_tvar α' Θ).
    { destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
        try discriminate;
        [ left | right; left | right; right; exists τ0 ]; exact Hb'. }
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds in *;
        apply in_or_app; right; simpl; right; exact Hby
      | apply IHHie; assumption ].
  -
    assert (Hnd : α `notin` dom Θ /\ {{ ⊢ Θ }}a) by (inversion Hwf; auto).
    destruct Hnd as [Hnd Hwf'].
    destruct (a_inc_equiv_dom Hie) as [Hd1 Hd2].
    destruct (α' == α) as [-> | Hne].
    + rewrite !msubst_lookup_notin
        by (first [ clear - Hnd Hd1; fsetdec | clear - Hnd Hd2; fsetdec ]).
      apply a_tyequiv__refl. constructor.
    + assert (Hbt' : a_binds_tvar α' Θ).
      { destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq ?] | Hb'];
          try (exfalso; apply Hne; exact Heq);
          [ left | right; left | right; right; exists τ0 ]; exact Hb'. }
      eapply a_tyequiv_weaken;
        [ intros y b Hby; unfold binds in *;
          apply in_or_app; right; simpl; right; exact Hby
        | apply IHHie; assumption ].
Qed.

Lemma a_inc_equiv_downarrow_pskl : forall Θ0 κ1 κ2 Θ P,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θ }}a ->
  a_scope_pskl Θ0 P ->
  ⇓ˢ[Θ] (msubst_pskl κ1 P) = ⇓ˢ[Θ] (msubst_pskl κ2 P).
Proof.
  intros Θ0 κ1 κ2 Θ P Hie Hwf0 Hwf HP.
  apply msubst_pskl_outer_ext. intros α Hα.
  apply a_tyequiv_downarrow; [ exact Hwf | ].
  eapply a_inc_equiv_lookup_tvar;
    [ exact Hie | exact Hwf0 | eapply a_scope_pskl_ftv_binds; eauto ].
Qed.

Corollary a_inc_equiv_downarrow_pskl_size : forall Θ0 κ1 κ2 Θ P,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θ }}a ->
  a_scope_pskl Θ0 P ->
  size_pskl (⇓ˢ[Θ] (msubst_pskl κ1 P)) = size_pskl (⇓ˢ[Θ] (msubst_pskl κ2 P)).
Proof.
  intros. erewrite a_inc_equiv_downarrow_pskl by eauto. reflexivity.
Qed.
