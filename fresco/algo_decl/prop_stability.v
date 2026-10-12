Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.basic.prop_inc.

Set Implicit Arguments.

Lemma a_isub_binds_tvarish : forall Θ Θ' α,
  Θ ⊴ Θ' ->
  a_binds_tvar α Θ ->
  a_binds_tvar α Θ'.
Proof.
  intros * [[κ [Hid Hinc]] _] Hb. eauto using a_inc_binds_tvarish.
Qed.

Lemma a_isub_binds_flex_def : forall Θ Θ' α τ,
  Θ ⊴ Θ' ->
  binds α (abind_flex_mono_def τ) Θ ->
  binds α (abind_flex_mono_def τ) Θ'.
Proof. intros * [_ Hd] Hb. auto. Qed.

Lemma a_isub_cons_tvar : forall Θ Θ' α',
  Θ ⊴ Θ' ->
  ((α' ~ abind_tvar) ++ Θ) ⊴ ((α' ~ abind_tvar) ++ Θ').
Proof.
  intros * [[κ [Hid Hinc]] Hd]. split.
  - exists κ. split; auto.
    apply (a_inc__tvar (Ξ := nil)); auto. constructor.
  - intros α τ Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    unfold binds; apply in_or_app; right. apply Hd; auto.
Qed.

Lemma a_wf_pskl_isub : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall Θ', Θ ⊴ Θ' ->
  {{ Θ' ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Δ P H Θ' Hle.
  apply (a_wf_pskl_tvar_mono H). eauto using a_isub_binds_tvarish.
Qed.

Lemma ad_pat_consis_isub : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Θ', Θ ⊴ Θ' ->
  {{ Ψ ⨟ Θ' ⊢ˢ R ∼ Q }}ad.
Proof.
  intros * H Θ' Hle. eapply ad_pat_consis_transport; [ exact H | | ];
    intros; eauto using a_isub_binds_tvarish, a_isub_binds_flex_def.
Qed.

Lemma ad_refine_syn_isub : forall Θ Δ Q Q',
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  forall Θ', Θ ⊴ Θ' ->
  {{ Θ' ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad.
Proof.
  intros * H Θ' Hle. eapply ad_refine_syn_defs_mono;
    [ exact H | intros; eapply a_isub_binds_flex_def; eauto ].
Qed.

Lemma ad_refine_pskl_isub : forall Θ Δ P P',
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad ->
  forall Θ', Θ ⊴ Θ' ->
  {{ Θ' ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad.
Proof.
  intros * H Θ' Hle. eapply ad_refine_pskl_defs_mono;
    [ exact H | intros; eapply a_isub_binds_flex_def; eauto ].
Qed.

Lemma ad_consis_join_isub : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
  forall Θ', Θ ⊴ Θ' ->
  {{ Ψ ⨟ Θ' ⊢ˢ R ∼ᵣ Q }}ad.
Proof.
  intros Ψ Θ R Q [Hc Hr] Θ' Hle. split.
  - eapply ad_pat_consis_isub; eassumption.
  - eapply ad_refine_pskl_isub; eassumption.
Qed.

Definition abind_is_tm (b : abind) : Prop :=
  match b with
  | abind_var_typ _ | abind_var_skl _ => True
  | abind_tvar | abind_flex_mono | abind_flex_mono_def _ => False
  end.

Definition aenv_tm_le (Θ Θ' : aenv) : Prop :=
  forall x b, abind_is_tm b -> binds x b Θ -> binds x b Θ'.

Lemma aenv_tm_le_refl : forall Θ, aenv_tm_le Θ Θ.
Proof. intros Θ x b _ H; exact H. Qed.

Lemma aenv_tm_le_trans : forall Θ1 Θ2 Θ3,
  aenv_tm_le Θ1 Θ2 -> aenv_tm_le Θ2 Θ3 -> aenv_tm_le Θ1 Θ3.
Proof. intros * H12 H23 x b Htm H; auto. Qed.

Lemma aenv_tm_le_cons : forall Θ Θ' y (c : abind),
  aenv_tm_le Θ Θ' -> aenv_tm_le ((y ~ c) ++ Θ) ((y ~ c) ++ Θ').
Proof.
  intros Θ Θ' y c Hle x b Htm Hb.
  apply binds_app_1 in Hb as [Hb | Hb]; [ apply binds_app_2; exact Hb | ].
  apply binds_app_3; auto.
Qed.

Lemma binds_tm_cons_inv : forall x (b : abind) y (c : abind) Θ,
  abind_is_tm b -> ~ abind_is_tm c ->
  binds x b ((y ~ c) ++ Θ) -> binds x b Θ.
Proof.
  intros * Htm Hc Hb.
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
    [ subst; contradiction | exact Hb' ].
Qed.

Lemma binds_tm_strip_suffix : forall Ξ x (b : abind) Θ,
  a_suffix Ξ -> abind_is_tm b ->
  binds x b (Ξ ++ Θ) -> binds x b Θ.
Proof.
  intros Ξ; induction Ξ as [ | [y c] Ξ' IH ]; intros x b Θ Hsuf Htm Hb.
  - exact Hb.
  - inversion Hsuf as [ | y0 c0 Ξ0 Hsuf' Hbind Heq ]; subst.
    apply (IH x b Θ Hsuf' Htm).
    eapply binds_tm_cons_inv with (y := y) (c := c);
      [ exact Htm | inversion Hbind; subst; intros [] | exact Hb ].
Qed.

Lemma aenv_tm_le_weaken_r : forall Ξ Θ Θ',
  aenv_tm_le Θ Θ' -> aenv_tm_le Θ (Ξ ++ Θ').
Proof. intros * Hle x b Htm Hb. apply binds_app_3; auto. Qed.

Lemma aenv_tm_le_src_cons_nontm : forall Θ Θ' y (c : abind),
  ~ abind_is_tm c ->
  aenv_tm_le Θ Θ' -> aenv_tm_le ((y ~ c) ++ Θ) Θ'.
Proof.
  intros * Hc Hle x b Htm Hb.
  apply Hle; [ exact Htm | eapply binds_tm_cons_inv; eauto ].
Qed.

Lemma aenv_tm_le_of_app_src : forall Ξ Θ Θ',
  aenv_tm_le (Ξ ++ Θ) Θ' -> aenv_tm_le Θ Θ'.
Proof.
  intros * Hle x b Htm Hb. apply Hle; [ exact Htm | apply binds_app_3; exact Hb ].
Qed.

Lemma aenv_tm_le_strip_suffix_tgt : forall Ξ Θ Θ',
  a_suffix Ξ ->
  aenv_tm_le Θ (Ξ ++ Θ') -> aenv_tm_le Θ Θ'.
Proof.
  intros * Hsuf Hle x b Htm Hb.
  eapply binds_tm_strip_suffix; [ exact Hsuf | exact Htm | auto ].
Qed.

Lemma aenv_tm_le_strip_cons_tgt : forall y (c : abind) Θ Θ',
  ~ abind_is_tm c ->
  aenv_tm_le Θ ((y ~ c) ++ Θ') -> aenv_tm_le Θ Θ'.
Proof.
  intros * Hc Hle x b Htm Hb.
  eapply binds_tm_cons_inv; [ exact Htm | exact Hc | auto ].
Qed.

Lemma aenv_tm_le_peel_cons_nontm : forall y (c : abind) Θ Θ',
  ~ abind_is_tm c ->
  aenv_tm_le ((y ~ c) ++ Θ) ((y ~ c) ++ Θ') -> aenv_tm_le Θ Θ'.
Proof.
  intros * Hc Hle.
  eapply aenv_tm_le_strip_cons_tgt; [ exact Hc | ].
  eapply aenv_tm_le_of_app_src with (Ξ := (y ~ c)); exact Hle.
Qed.

Lemma a_assign_unify_consis_tm_le :
  (forall Θ0 Ξ α P Θ1, {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> aenv_tm_le Θ0 Θ1) /\
  (forall Θ0 α β Θ1, {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> aenv_tm_le Θ0 Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P Q Θ1,
     a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 -> aenv_tm_le Θ0 Θ1).
Proof.
  apply a_assign_unify_consis_mutind.

  -  intros; apply aenv_tm_le_refl.
  -
    intros Θ0 Ξ α P βs τ Hαn Hg Hm Hu Hfr.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    repeat apply aenv_tm_le_weaken_r. apply aenv_tm_le_refl.
  -
    intros Θ0 Θ1 Ξ α β τ P Q Hflex Hβ Hc IH.
    apply aenv_tm_le_cons. eapply aenv_tm_le_of_app_src; exact IH.
  -
    intros Θ0 Θ1 Ξ α β P Hne Hβ Ha IH.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | exact IH ].
  -  intros; apply aenv_tm_le_cons; assumption.
  -  intros; apply aenv_tm_le_cons; assumption.
  -  intros; apply aenv_tm_le_cons; assumption.
  -  intros; apply aenv_tm_le_cons; assumption.

  -  intros; apply aenv_tm_le_refl.
  -
    intros Θ0 α β Hne Hβ.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    apply aenv_tm_le_weaken_r. apply aenv_tm_le_refl.
  -
    intros Θ0 α β Hne Hα.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    apply aenv_tm_le_weaken_r. apply aenv_tm_le_refl.
  -
    intros Θ0 Θ1 α1 τ α β Q Hfα Hfβ Hα1 Hc IH.
    apply aenv_tm_le_cons; exact IH.
  -  intros; apply aenv_tm_le_cons; assumption.
  -  intros; apply aenv_tm_le_cons; assumption.

  -  intros; apply aenv_tm_le_refl.
  -  intros; apply aenv_tm_le_refl.
  -  intros; apply aenv_tm_le_refl.
  -
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2.
    eapply aenv_tm_le_trans; eassumption.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar); [ intros [] | exact IH ].
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar); [ intros [] | exact IH ].
  -  intros; assumption.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hα Hc IH.
    eapply aenv_tm_le_peel_cons_nontm with (y := α) (c := abind_tvar); [ intros [] | exact IH ].
  -  intros; assumption.
  -  intros; assumption.
  -  intros; assumption.
  -  intros; assumption.
  -  intros; apply aenv_tm_le_refl.
  -  intros; assumption.
Qed.

Lemma a_consis_tm_le : forall Δ1 Δ2 Θ0 P0 P Q Θ1,
  a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 -> aenv_tm_le Θ0 Θ1.
Proof. intros; eapply (proj2 (proj2 a_assign_unify_consis_tm_le)); eauto. Qed.

Lemma a_consis_chk_tm_le : forall Θ0 P P0 Θ1,
  a_consis_chk Θ0 P P0 Θ1 -> aenv_tm_le Θ0 Θ1.
Proof. intros * [Q Hc]; eapply a_consis_tm_le; eauto. Qed.

Scheme a_sub_tm_sind := Induction for a_sub Sort Prop
  with a_sub_flex_tm_sind := Induction for a_sub_flex Sort Prop.
Combined Scheme a_sub_sub_flex_tm_mutind
  from a_sub_tm_sind, a_sub_flex_tm_sind.

Lemma a_sub_sub_flex_tm_le :
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 -> aenv_tm_le Θ0 Θ1) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 -> aenv_tm_le Θ0 Θ1).
Proof.
  apply a_sub_sub_flex_tm_mutind.

  -  intros; apply aenv_tm_le_refl.
  -
    intros Θ0 Θ1 A B Hgf1 Hgf2 Hg1 Hg2 Hchk.
    eapply a_consis_chk_tm_le; exact Hchk.
  -
    intros α Θ0 Θ1 Ξ A B Hgf Hsuf Huniq Hnotin Hrun IH.
    eapply aenv_tm_le_strip_cons_tgt with (y := α) (c := abind_tvar);
      [ intros [] | ].
    eapply aenv_tm_le_strip_suffix_tgt; [ exact Hsuf | ].
    eapply aenv_tm_le_of_app_src with (Ξ := (α ~ abind_tvar)); exact IH.
  -  intros; apply aenv_tm_le_refl.
  -  intros; assumption.
  -
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IH.
    eapply aenv_tm_le_trans; [ eapply a_consis_tm_le; exact Hc | exact IH ].
  -
    intros α NM M P0 Θ0 Θ1 P Q Ξ P1 Hm Hg Hα Hext Huniq Hwf Hs IH.
    eapply aenv_tm_le_of_app_src with (Ξ := Ξ); exact IH.
  -  intros; apply aenv_tm_le_refl.
  -  intros; assumption.

  -
    intros NM M P0 Θ0 Θ1 Ξ α0 α β Q Hne Hα Hβ Hs IH.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | ].
    do 4 eapply aenv_tm_le_of_app_src. exact IH.
  -
    intros NM M P0 Θ0 Θ1 Ξ α β τ Q Hβ Hs IH.
    apply aenv_tm_le_cons. eapply aenv_tm_le_of_app_src; exact IH.
  -
    intros NM M P0 Θ0 Θ1 Ξ α β Q Hne Hβ Hs IH.
    apply aenv_tm_le_src_cons_nontm; [ intros [] | exact IH ].
  -  intros; apply aenv_tm_le_cons; assumption.
  -  intros; apply aenv_tm_le_cons; assumption.
  -  intros; apply aenv_tm_le_cons; assumption.
  -  intros; apply aenv_tm_le_cons; assumption.
Qed.

Lemma a_sub_tm_le : forall NM M P0 Θ0 P Q Θ1,
  a_sub NM M P0 Θ0 P Q Θ1 -> aenv_tm_le Θ0 Θ1.
Proof. intros; eapply (proj1 a_sub_sub_flex_tm_le); eauto. Qed.

Lemma a_split_tm_le : forall Θ0 P0 P Q Θ1,
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a -> aenv_tm_le Θ0 Θ1.
Proof.
  intros * H; inversion H; subst; try apply aenv_tm_le_refl.

  match goal with
  | Hc : a_consis _ _ _ _ _ _ _ |- _ => apply a_consis_tm_le in Hc
  end.
  do 2 eapply aenv_tm_le_of_app_src; eassumption.
Qed.

Lemma aenv_tm_le_via_binder : forall Ξ x (bx : abind) Θ Θ',
  a_suffix Ξ ->
  aenv_tm_le ((x ~ bx) ++ Θ) (Ξ ++ (x ~ bx) ++ Θ') ->
  forall y b, abind_is_tm b -> y <> x -> binds y b Θ -> binds y b Θ'.
Proof.
  intros * Hsuf Hle y b Htm Hne Hb.
  assert (Hb1 : binds y b (Ξ ++ (x ~ bx) ++ Θ'))
    by (apply Hle; [ exact Htm | apply binds_app_3; exact Hb ]).
  apply binds_tm_strip_suffix in Hb1; [ | exact Hsuf | exact Htm ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[Heq _] | Hb2];
    [ subst; contradiction | exact Hb2 ].
Qed.

Lemma a_pat_tm_le : forall m Θ0 P0 e P Θ1,
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ P ⊣ Θ1 }}a -> aenv_tm_le Θ0 Θ1.
Proof.
  intros m Θ0 P0 e P Θ1 H; induction H.
  -  eapply a_sub_tm_le; eassumption.
  -  eapply a_sub_tm_le; eassumption.
  -  eapply a_sub_tm_le; eassumption.
  -  eapply a_sub_tm_le; eassumption.
  -  assumption.
  -
    intros y b Htm Hb.
    apply a_split_tm_le in H0.
    assert (Hb1 : binds y b Θ1) by (apply H0; [ exact Htm | exact Hb ]).
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H1 | exact IHa_pat | exact Htm | | exact Hb1 ].
    intros Heq; subst.
    apply binds_In in Hb1. simpl_env in H2. clear - H2 Hb1. fsetdec.
  -
    intros y b Htm Hb.
    apply a_split_tm_le in H0.
    apply a_consis_chk_tm_le in H1.
    assert (Hb2 : binds y b Θ2)
      by (apply H1; [ exact Htm | apply H0; [ exact Htm | exact Hb ] ]).
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H2 | exact IHa_pat | exact Htm | | exact Hb2 ].
    intros Heq; subst.
    apply binds_In in Hb2. simpl_env in H3. clear - H3 Hb2. fsetdec.
  -
    intros y b Htm Hb.
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H | exact IHa_pat | exact Htm | | exact Hb ].
    intros Heq; subst.
    apply binds_In in Hb. simpl_env in H0. clear - H0 Hb. fsetdec.
  -
    intros y b Htm Hb.
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H | exact IHa_pat | exact Htm | | exact Hb ].
    intros Heq; subst.
    apply binds_In in Hb. simpl_env in H0. clear - H0 Hb. fsetdec.
  -  eapply aenv_tm_le_trans; eassumption.
Qed.

Lemma a_typing_tm_le : forall m Θ0 P0 e A Θ1,
  {{ Θ0 ⊢[ m ; P0 ] e ⦂ A ⊣ Θ1 }}a -> aenv_tm_le Θ0 Θ1.
Proof.
  intros m Θ0 P0 e A Θ1 H; induction H.
  -  eapply a_sub_tm_le; eassumption.
  -  eapply a_sub_tm_le; eassumption.
  -
    eapply aenv_tm_le_trans; [ eassumption | eapply a_sub_tm_le; eassumption ].
  -
    eapply aenv_tm_le_trans;
      [ eassumption | eapply a_consis_chk_tm_le; eassumption ].
  -
    intros y b Htm Hb.
    apply a_split_tm_le in H0.
    assert (Hb1 : binds y b Θ1) by (apply H0; [ exact Htm | exact Hb ]).
    pose proof (binds_In _ y b _ Hb1) as Hy.
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H3 | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H4 Hy; rewrite !dom_app in H4; fsetdec
      | apply binds_app_3; exact Hb1 ].
  -
    intros y b Htm Hb.
    apply a_split_tm_le in H0.
    apply a_consis_chk_tm_le in H1.
    assert (Hb1 : binds y b Θ2)
      by (apply H1; [ exact Htm | apply H0; [ exact Htm | exact Hb ] ]).
    pose proof (binds_In _ y b _ Hb1) as Hy.
    apply binds_app_3.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H2 | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H3 Hy; rewrite !dom_app in H3; fsetdec
      | exact Hb1 ].
  -
    intros y b Htm Hb.
    pose proof (binds_In _ y b _ Hb) as Hy.
    eapply aenv_tm_le_via_binder with (x := α);
      [ exact H | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H2 Hy; rewrite !dom_app in H2; fsetdec
      | exact Hb ].
  -
    intros y b Htm Hb.
    apply a_split_tm_le in H.
    assert (Hb1 : binds y b Θ1) by (apply H; [ exact Htm | exact Hb ]).
    pose proof (binds_In _ y b _ Hb1) as Hy.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H0 | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H3 Hy; rewrite !dom_app in H3; fsetdec
      | exact Hb1 ].
  -
    intros y b Htm Hb.
    pose proof (binds_In _ y b _ Hb) as Hy.
    eapply aenv_tm_le_via_binder with (x := α);
      [ exact H | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H2 Hy; rewrite !dom_app in H2; fsetdec
      | exact Hb ].
  -
    intros y b Htm Hb.
    apply a_split_tm_le in H.
    apply a_consis_chk_tm_le in H0.
    assert (Hb1 : binds y b Θ2)
      by (apply H0; [ exact Htm | apply H; [ exact Htm | exact Hb ] ]).
    pose proof (binds_In _ y b _ Hb1) as Hy.
    eapply aenv_tm_le_via_binder with (x := x);
      [ exact H1 | exact IHa_typing | exact Htm
      | intros Heq; subst; clear - H4 Hy; rewrite !dom_app in H4; fsetdec
      | exact Hb1 ].
  -
    eapply aenv_tm_le_trans; [ eapply a_pat_tm_le; eassumption | ].
    eapply aenv_tm_le_trans; eassumption.
Qed.
