Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.def_typing.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.subtyping.prop_sub_msubst_equiv.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_gen.
Require Import src.fresco.algo.subtyping.prop_completeness_sub.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.consistency.prop_consis_rename.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.basic.prop_wf_preservation.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.algo.typing.prop_soundness_typing.
Require Import src.fresco.algo.basic.prop_suffix_erase.
Require Import src.fresco.algo_decl.prop_ctx_precision.

Set Implicit Arguments.

Corollary a_pat_output_wf : forall m Θ0 P0 e P Θ1,
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ P ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat m P0 ->
  {{ Θ0 ⊢ᵉ e }}a ->
  {{ Θ1 ⨟ empty ⊢ₚₛ P }}a.
Proof.
  intros * Hrun Hwf HwfP0 Hmod Hexp.
  destruct (a_pat_sound Hrun Hwf HwfP0 Hmod Hexp)
    as [Hle [Hwf1 [Qt [HeQt [Hpat _]]]]].
  rewrite <- HeQt. eapply ad_pat_target_wf; [ exact Hpat | exact Hwf1 ].
Qed.

Lemma a_inc_binds_var_skl_rev : forall Θ0 κ Θ x (P : pskl),
  κ ∷ Θ0 ⊑ Θ ->
  {{ ⊢ Θ0 }}a ->
  binds x (abind_var_skl P) Θ ->
  exists P0,
    binds x (abind_var_skl P0) Θ0 /\
    {{ Θ ⊢ P ≡ˢ (msubst_pskl κ P0) }}a.
Proof.
  intros Θ0 κ Θ x P Hinc; induction Hinc; intros Hwf Hb.
  -
    exfalso; eapply a_suffix_no_var_skl; eassumption.
  -
    inversion Hwf as [ | αz Θz Hα Hwf0 | | | | ]; subst.
    destruct (IHHinc Hwf0 Hb) as [P0 [Hb0 Heq]].
    exists P0. split; [ apply binds_cons_3; exact Hb0 | ].
    assert (Hfr : α `notin` ftvar_in_pskl P0).
    { pose proof (@a_wf_aenv_binds_var_skl_ftv _ _ _ Hwf0 Hb0) as Hs.
      clear - Hs Hα. fsetdec. }
    replace ((α, τ) :: κ) with (nil ++ ((α, τ) :: nil) ++ κ)
      by reflexivity.
    rewrite msubst_pskl_mid_skip;
      [ exact Heq
      | intros α0 Hα0; simpl in Hα0;
        assert (α0 = α) by (clear - Hα0; fsetdec); subst; exact Hfr ].
  -
    inversion Hwf as [ | | αz τz Θz Hα Hwfτ Hmz Hwf0 | | | ]; subst.
    destruct (IHHinc Hwf0 Hb) as [P0 [Hb0 Heq]].
    exists P0. split; [ apply binds_cons_3; exact Hb0 | ].
    assert (Hfr : α `notin` ftvar_in_pskl P0).
    { pose proof (@a_wf_aenv_binds_var_skl_ftv _ _ _ Hwf0 Hb0) as Hs.
      clear - Hs Hα. fsetdec. }
    replace ((α, τ') :: κ) with (nil ++ ((α, τ') :: nil) ++ κ)
      by reflexivity.
    rewrite msubst_pskl_mid_skip;
      [ exact Heq
      | intros α0 Hα0; simpl in Hα0;
        assert (α0 = α) by (clear - Hα0; fsetdec); subst; exact Hfr ].
  -
    inversion Hwf as [ | | | | xz Az Θz Hx HwfA Hwf0 | ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_skl; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp.
    + destruct (IHHinc Hwf0 Hb) as [P0 [Hb0 Heq]].
      exists P0. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_pskl_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
  -
    inversion Hwf as [ | | | xz Pz Θz Hx Hsc Hwf0 | | ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_skl; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp; subst.
      eexists. split; [ unfold binds; simpl; left; reflexivity | ].
      eapply a_pskl_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact H ].
    + destruct (IHHinc Hwf0 Hb) as [P1 [Hb0 Heq]].
      exists P1. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_pskl_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
  -
    inversion Hwf as [ | | | | | αz Θz Hα Hwf0 ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_skl; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp.
    + destruct (IHHinc Hwf0 Hb) as [P0 [Hb0 Heq]].
      exists P0. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_pskl_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
Qed.

Lemma a_inc_binds_var_typ_rev : forall Θ0 κ Θ x (A : ptyp),
  κ ∷ Θ0 ⊑ Θ ->
  {{ ⊢ Θ0 }}a ->
  binds x (abind_var_typ A) Θ ->
  exists A0,
    binds x (abind_var_typ A0) Θ0 /\
    {{ Θ ⊢ A ≡ᵗ (msubst_ptyp κ A0) }}a.
Proof.
  intros Θ0 κ Θ x A Hinc; induction Hinc; intros Hwf Hb.
  - exfalso; eapply a_suffix_no_var_typ; eassumption.
  -
    inversion Hwf as [ | αz Θz Hα Hwf0 | | | | ]; subst.
    destruct (IHHinc Hwf0 Hb) as [A0 [Hb0 Heq]].
    exists A0. split; [ apply binds_cons_3; exact Hb0 | ].
    assert (Hfr : α `notin` ftvar_in_ptyp A0).
    { pose proof (@a_wf_aenv_binds_var_typ_ftv _ _ _ Hwf0 Hb0) as Hs.
      clear - Hs Hα. fsetdec. }
    rewrite msubst_ptyp_cons_notin; [ exact Heq | exact Hfr ].
  -
    inversion Hwf as [ | | αz τz Θz Hα Hwfτ Hmz Hwf0 | | | ]; subst.
    destruct (IHHinc Hwf0 Hb) as [A0 [Hb0 Heq]].
    exists A0. split; [ apply binds_cons_3; exact Hb0 | ].
    assert (Hfr : α `notin` ftvar_in_ptyp A0).
    { pose proof (@a_wf_aenv_binds_var_typ_ftv _ _ _ Hwf0 Hb0) as Hs.
      clear - Hs Hα. fsetdec. }
    rewrite msubst_ptyp_cons_notin; [ exact Heq | exact Hfr ].
  -
    inversion Hwf as [ | | | | xz Az Θz Hx HwfA Hwf0 | ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_typ; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp; subst.
      eexists. split; [ unfold binds; simpl; left; reflexivity | ].
      eapply a_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact H ].
    + destruct (IHHinc Hwf0 Hb) as [A1 [Hb0 Heq]].
      exists A1. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
  -
    inversion Hwf as [ | | | xz Pz Θz Hx Hsc Hwf0 | | ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_typ; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp.
    + destruct (IHHinc Hwf0 Hb) as [A0 [Hb0 Heq]].
      exists A0. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
  -
    inversion Hwf as [ | | | | | αz Θz Hα Hwf0 ]; subst.
    apply binds_app_1 in Hb as [Hb | Hb];
      [ exfalso; eapply a_suffix_no_var_typ; eassumption | ].
    apply binds_app_1 in Hb as [Hb | Hb].
    + destruct Hb as [Hp | []]. inversion Hp.
    + destruct (IHHinc Hwf0 Hb) as [A0 [Hb0 Heq]].
      exists A0. split; [ apply binds_cons_3; exact Hb0 | ].
      eapply a_tyequiv_weaken;
        [ intros y c Hc; apply binds_app_3; apply binds_cons_3; exact Hc
        | exact Heq ].
Qed.

Lemma a_pskl_tyequiv_to_uskl : forall Θ P Q,
  {{ Θ ⊢ P ≡ˢ Q }}a ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ (pskl_to_uskl P) ≡ᵘ (pskl_to_uskl Q) }}a.
Proof.
  intros Θ P Q H; induction H; intros Hwf.
  -
    apply a_uskl_tyequiv_refl. apply pskl_to_uskl_lc. exact H.
  -
    apply a_uskl_tyequiv_sym. auto.
  -
    eapply a_uskl_tyequiv_trans; auto.
  -
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    change (pskl_to_uskl (pskl_var_f α))
      with (ptyp_to_uskl_syn (ptyp_var_f α)).
    rewrite pskl_to_uskl_ptyp.
    apply a_uskl_tyequiv__mono;
      [ apply mono_ptyp__var
      | exact Hm
      | apply a_wf_ptyp__var; right; right; eauto
      | eapply a_wf_aenv_binds_def_wf; eassumption
      | apply a_tyequiv__flex_def; exact H ].
  -
    simpl. apply a_uskl_tyequiv__arrow; auto.
  -
    simpl. apply a_uskl_tyequiv__all_syn with (L := L).
    intros α Hα.
    rewrite <- !pskl_to_uskl_open_var.
    apply H0; [ exact Hα | exact Hwf ].
  -
    simpl. apply a_uskl_tyequiv__univ_ghost. auto.
Qed.

Lemma msubst_pskl_to_uskl : forall κ P,
  pskl_to_uskl (msubst_pskl κ P) = msubst_uskl_syn κ (pskl_to_uskl P).
Proof.
  intros κ P; induction P; simpl; f_equal; auto.
  apply pskl_to_uskl_ptyp.
Qed.

Lemma msubst_ptyp_to_uskl_syn : forall κ A,
  ptyp_to_uskl_syn (msubst_ptyp κ A) = msubst_uskl_syn κ (ptyp_to_uskl_syn A).
Proof.
  intros κ A.
  rewrite <- !pskl_to_uskl_ptyp, <- msubst_pskl_to_uskl.
  f_equal. induction A; simpl; f_equal; auto.
Qed.

Lemma ptyp_to_uskl_syn_all : forall A,
  ptyp_to_uskl_syn (ptyp_all A) = uskl_all_syn (ptyp_to_uskl_syn A).
Proof. reflexivity. Qed.

Lemma a_tyequiv_to_uskl : forall Θ A B,
  {{ Θ ⊢ A ≡ᵗ B }}a ->
  {{ ⊢ Θ }}a ->
  {{ Θ ⊢ (ptyp_to_uskl_syn A) ≡ᵘ (ptyp_to_uskl_syn B) }}a.
Proof.
  intros Θ A B H; induction H; intros Hwf.
  -
    apply a_uskl_tyequiv_refl.
    rewrite <- pskl_to_uskl_ptyp. apply pskl_to_uskl_lc.
    apply ptyp_to_pskl_lc. exact H.
  -  apply a_uskl_tyequiv_sym; auto.
  -  eapply a_uskl_tyequiv_trans; auto.
  -
    assert (Hm : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    apply a_uskl_tyequiv__mono;
      [ apply mono_ptyp__var
      | exact Hm
      | apply a_wf_ptyp__var; right; right; eauto
      | eapply a_wf_aenv_binds_def_wf; eassumption
      | apply a_tyequiv__flex_def; exact H ].
  -
    rewrite !ptyp_to_uskl_syn_arrow.
    apply a_uskl_tyequiv__arrow; auto.
  -
    rewrite !ptyp_to_uskl_syn_all.
    apply a_uskl_tyequiv__all_syn with (L := L).
    intros α Hα.
    rewrite <- !ptyp_to_uskl_syn_open.
    apply H0; [ exact Hα | exact Hwf ].
Qed.

Lemma msubst_ptyp_rigid_id : forall Θ0 κ Θ A,
  κ ∷ Θ0 ⊑ Θ ->
  {{ ⊢ Θ0 }}a ->
  (forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0) ->
  msubst_ptyp κ A = A.
Proof.
  intros Θ0 κ Θ A Hinc Hwf Hrig.
  apply msubst_ptyp_notin. intros α Hα.
  eapply a_inc_tvar_notin_dom; [ exact Hinc | exact Hwf | apply Hrig; exact Hα ].
Qed.

Lemma slack_unit : forall Θ κ,
  {{ Θ ⊢ uskl_unit ≡ᵘ (msubst_uskl_syn κ (pskl_to_uskl pskl_unit)) }}a.
Proof. intros. simpl. apply a_uskl_tyequiv__unit. Qed.

Lemma slack_anno : forall Θ0 κ Θ A,
  κ ∷ Θ0 ⊑ Θ ->
  {{ ⊢ Θ0 }}a ->
  lc_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0) ->
  {{ Θ ⊢ (ptyp_to_uskl_syn A)
    ≡ᵘ (msubst_uskl_syn κ (pskl_to_uskl (ptyp_to_pskl A))) }}a.
Proof.
  intros Θ0 κ Θ A Hinc Hwf Hlc Hrig.
  rewrite pskl_to_uskl_ptyp, <- msubst_ptyp_to_uskl_syn.
  rewrite (@msubst_ptyp_rigid_id Θ0 κ Θ A Hinc Hwf Hrig).
  apply a_uskl_tyequiv_refl.
  rewrite <- pskl_to_uskl_ptyp. apply pskl_to_uskl_lc.
  apply ptyp_to_pskl_lc. exact Hlc.
Qed.

Lemma slack_var : forall Θ0 κ Θ x (b : abind) (P : pskl),
  κ ∷ Θ0 ⊑ Θ ->
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  binds x b Θ ->
  abind_to_pskl b = Some P ->
  exists (b0 : abind) (P0 : pskl),
    binds x b0 Θ0 /\ abind_to_pskl b0 = Some P0 /\
    {{ Θ ⊢ (pskl_to_uskl P) ≡ᵘ (msubst_uskl_syn κ (pskl_to_uskl P0)) }}a.
Proof.
  intros Θ0 κ Θ x b P Hinc Hwf0 HwfΘ Hb HP.
  destruct b; simpl in HP; try discriminate HP.
  -
    inversion HP; subst.
    destruct (@a_inc_binds_var_typ_rev Θ0 κ Θ x _ Hinc Hwf0 Hb) as [A0 [Hb0 Heq]].
    exists (abind_var_typ A0), (ptyp_to_pskl A0).
    split; [ exact Hb0 | ]. split; [ reflexivity | ].
    rewrite !pskl_to_uskl_ptyp, <- msubst_ptyp_to_uskl_syn.
    apply a_tyequiv_to_uskl; [ exact Heq | exact HwfΘ ].
  -
    inversion HP; subst.
    destruct (@a_inc_binds_var_skl_rev Θ0 κ Θ x _ Hinc Hwf0 Hb) as [P0 [Hb0 Heq]].
    exists (abind_var_skl P0), P0.
    split; [ exact Hb0 | ]. split; [ reflexivity | ].
    rewrite <- msubst_pskl_to_uskl.
    apply a_pskl_tyequiv_to_uskl; [ exact Heq | exact HwfΘ ].
Qed.

Lemma a_wf_ptyp_strip_tm_head : forall x (b : abind) Θ A,
  ~ abind_is_ty b ->
  a_wf_ptyp ((x ~ b) ++ Θ) A ->
  a_wf_ptyp Θ A.
Proof.
  intros x b Θ A Hty Hwa.
  eapply a_wf_ptyp_mono;
    [ exact Hwa | apply (@aenv_tbinds_le_strip_tm nil x b Θ); exact Hty ].
Qed.

Lemma a_inc_strip_tm_head : forall Ξ x (b b' : abind) Θ1 κ Θ,
  a_suffix Ξ ->
  ~ abind_is_ty b -> ~ abind_is_ty b' ->
  {{ ⊢ (Ξ ++ (x ~ b) ++ Θ1) }}a ->
  {{ ⊢ ((x ~ b') ++ Θ) }}a ->
  κ ∷ (Ξ ++ (x ~ b) ++ Θ1) ⊑ ((x ~ b') ++ Θ) ->
  κ ∷ (Ξ ++ Θ1) ⊑ Θ.
Proof.
  induction Ξ as [ | [α bΞ] Ξ' IH ];
    intros x b b' Θ1 κ Θ Hsuf Htm Htm' HwfS HwfT Hinc; simpl_env in *.
  -
    destruct b; simpl in Htm; try solve [ exfalso; apply Htm; exact I ].
    +
      destruct (a_inc_var_inv Hinc) as [Ξ2 [A' [Θ2 [Heq [Heqv [Hsuf2 Hrest]]]]]].
      destruct Ξ2 as [ | [y c] Ξ2' ]; simpl_env in Heq.
      * inversion Heq; subst. exact Hrest.
      *
        exfalso. inversion Heq; subst.
        inversion Hsuf2 as [ | ? ? ? ? Hbind ]; subst.
        apply Htm'. destruct Hbind; exact I.
    +
      destruct (a_inc_var_skl_inv Hinc)
        as [Ξ2 [P' [Θ2 [Heq [Heqv [Hsuf2 Hrest]]]]]].
      destruct Ξ2 as [ | [y c] Ξ2' ]; simpl_env in Heq.
      * inversion Heq; subst. exact Hrest.
      * exfalso. inversion Heq; subst.
        inversion Hsuf2 as [ | ? ? ? ? Hbind ]; subst.
        apply Htm'. destruct Hbind; exact I.
  -
    inversion Hsuf as [ | ? ? ? Hsuf' Hbind ]; subst.
    destruct Hbind as [ | τz ].
    +
      inversion HwfS as [ | αz Θz HαS HwfS' | | | | ]; subst.
      inversion Hinc as [ | Θq κq Θtq αq τq Hrest Hwfτ Hmτ
                        | | | | ]; subst.
      apply a_inc__flex;
        [ eapply IH;
            [ exact Hsuf' | exact Htm | exact Htm' | exact HwfS' | exact HwfT
            | exact Hrest ]
        | eapply a_wf_ptyp_strip_tm_head; [ exact Htm' | exact Hwfτ ]
        | exact Hmτ ].
    +
      inversion HwfS as [ | | αz τw Θz HαS HwfτS HmτS HwfS' | | | ]; subst.
      inversion Hinc as [ | | Θq κq Θtq αq τq τ'q Hrest Hwfτ' Hmτ' Heqv
                        | | | ]; subst.
      assert (Hrec : κq ∷ (Ξ' ++ Θ1) ⊑ Θ)
        by (eapply IH;
              [ exact Hsuf' | exact Htm | exact Htm' | exact HwfS' | exact HwfT
              | exact Hrest ]).
      assert (Hwfτ0 : a_wf_ptyp (Ξ' ++ Θ1) τz).
      { eapply a_wf_ptyp_mono;
          [ exact HwfτS
          | apply (@aenv_tbinds_le_strip_tm Ξ' x b Θ1); exact Htm ]. }
      apply a_inc__flex_def;
        [ exact Hrec
        | eapply a_wf_ptyp_strip_tm_head; [ exact Htm' | exact Hwfτ' ]
        | exact Hmτ'
        | ].

      eapply (@a_tyequiv_strengthen_mono_mid nil x b' Θ);
        [ simpl_env; exact HwfT
        | eapply a_wf_ptyp_strip_tm_head; [ exact Htm' | exact Hwfτ' ]
        | exact Hmτ'
        | eapply a_wf_ptyp_msubst;
            [ exact Hwfτ0 | eapply a_wf_aenv_strip_tm_mid; [ exact Htm | exact HwfS' ]
            | exact Hrec ]
        | apply msubst_ptyp_mono_pointwise;
            [ intros β; eapply a_inc_lookup_mono; exact Hrec | exact HmτS ]
        | simpl_env; exact Heqv ].
Qed.

Lemma msubst_bskl_syn_erase : forall ζ P,
  bskl_to_pskl (msubst_bskl ζ (pskl_to_bskl_syn P)) = msubst_pskl ζ P.
Proof.
  intros ζ P; induction P; simpl; f_equal; auto.
  apply bskl_to_pskl_pskl_to_bskl_syn.
Qed.

Lemma a_wf_ptyp_of_lc_tvarish : forall Θ A,
  lc_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  a_wf_ptyp Θ A.
Proof.
  intros Θ A Hlc; revert Θ; induction Hlc; intros Θ Hftv; simpl in Hftv.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. apply Hftv. clear; fsetdec.
  - apply a_wf_ptyp__arrow.
    + apply IHHlc1. intros α Hα; apply Hftv; clear - Hα; fsetdec.
    + apply IHHlc2. intros α Hα; apply Hftv; clear - Hα; fsetdec.
  - apply a_wf_ptyp__all with (L := dom Θ `union` ftvar_in_ptyp A).
    intros α Hα. apply H0.
    intros β Hβ.
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A (ptyp_var_f α)) as Hup.
    simpl in Hup.
    destruct (β == α) as [->|Hne];
      [ left; unfold binds; simpl; left; reflexivity | ].
    apply a_binds_tvar_weaken_cons.
    apply Hftv. clear - Hβ Hup Hne. fsetdec.
Qed.

Definition pat_complete_concl (M : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (κ : metasubst) (Θ : aenv) (Q : bskl) : Prop :=
  exists P1 Θ1,
    a_pat M Θ0 P0 e P1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl ζ P1) ⊑ (bskl_to_pskl Q) }}ad).

Definition pat_complete_ih (e : exp) : Prop :=
  forall M' Θ0' P0' κ' Θ' Q',
    {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
    {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
    a_sk_mode_compat M' P0' ->
    κ' ∷ Θ0' ⊑ Θ' ->
    (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0') ->
    lc_exp e ->
    {{ Θ' ⊢ˢ[ M' ] e ⦂ Q' }}ad ->
    {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0')) ⊳ Q' }}ad ->
    pat_complete_concl M' Θ0' P0' e κ' Θ' Q'.

Lemma a_pat_complete_unit : forall M Θ0 P0 κ Θ Q,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⊢ˢ[ M ] exp_unit ⦂ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  pat_complete_concl M Θ0 P0 exp_unit κ Θ Q.
Proof.
  intros M Θ0 P0 κ Θ Q Hwf0 HwfΘ HwfP0 Hmod Hinc Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub _ _ _ _ _ _ |- _ =>
      destruct (ad_pat_sub_to_fuel H) as [njoin Hjoin]
  end.
  match goal with
  | H : {{ _ ⨟ empty ⊢ₚₛ (bskl_to_pskl _) }}a |- _ => rename H into HwfQ
  end.
  destruct (@a_sub_complete njoin a_sub_mode_sk M Θ0 P0
              pskl_unit uskl_unit Θ κ Q
              Hwf0 HwfΘ HwfP0
              ltac:(apply a_wf_pskl__unit)
              ltac:(intros _; exact Hmod)
              ltac:(intros Hd0; discriminate)
              Hinc
              (slack_unit Θ κ)
              Hjoin Href HwfQ
              ltac:(intros Hd0; discriminate))
    as [P1 [Θ1 [Hrun Hopt]]].
  exists P1, Θ1. split; [ apply a_pat__unit; exact Hrun | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  rewrite <- msubst_bskl_syn_erase. exact Hprec.
Qed.

Lemma a_pat_complete_var : forall M Θ0 P0 x κ Θ Q,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⊢ˢ[ M ] (exp_var_f x) ⦂ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  pat_complete_concl M Θ0 P0 (exp_var_f x) κ Θ Q.
Proof.
  intros M Θ0 P0 x κ Θ Q Hwf0 HwfΘ HwfP0 Hmod Hinc Hd Href.
  pose proof (fun y Ps Hb => @a_wf_aenv_binds_var_skl_wf _ y Ps Hwf0 Hb)
    as Hskl.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub _ _ _ _ _ _ |- _ =>
      destruct (ad_pat_sub_to_fuel H) as [njoin Hjoin]
  end.
  match goal with
  | H : {{ _ ⨟ empty ⊢ₚₛ (bskl_to_pskl _) }}a |- _ => rename H into HwfQ
  end.
  match goal with
  | Hb : binds x ?b Θ, He : abind_to_pskl ?b = Some ?P |- _ =>
      destruct (@slack_var Θ0 κ Θ x b P Hinc Hwf0 HwfΘ Hb He)
        as [b0 [P0' [Hb0 [He0 Hslack]]]]
  end.
  assert (HwfP0' : {{ Θ0 ⨟ empty ⊢ₚₛ P0' }}a).
  { destruct b0; simpl in He0; try discriminate He0; inversion He0; subst.
    - apply a_wf_ptyp_to_wf_pskl.
      eapply a_wf_aenv_binds_var_typ_wf; [ exact Hwf0 | exact Hb0 ].
    - eapply Hskl; exact Hb0. }
  rewrite pskl_to_uskl_via_bskl_syn in Hjoin.
  destruct (@a_sub_complete njoin a_sub_mode_sk M Θ0 P0
              P0' (pskl_to_uskl P) Θ κ Q
              Hwf0 HwfΘ HwfP0 HwfP0'
              ltac:(intros _; exact Hmod)
              ltac:(intros Hd0; discriminate)
              Hinc Hslack Hjoin Href HwfQ
              ltac:(intros Hd0; discriminate))
    as [P1 [Θ1 [Hrun Hopt]]].
  exists P1, Θ1. split.
  { destruct b0; simpl in He0; try discriminate He0; inversion He0; subst.
    - eapply a_pat__var; [ exact Hb0 | exact Hrun ].
    - eapply a_pat__var_skl; [ exact Hb0 | exact Hrun ]. }
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  rewrite <- msubst_bskl_syn_erase. exact Hprec.
Qed.

Lemma a_pat_complete_anno : forall M Θ0 P0 e A κ Θ Q,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0) ->
  lc_ptyp A ->
  {{ Θ ⊢ˢ[ M ] (exp_anno e A) ⦂ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  pat_complete_concl M Θ0 P0 (exp_anno e A) κ Θ Q.
Proof.
  intros M Θ0 P0 e A κ Θ Q Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig HlcA Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub _ _ _ _ _ _ |- _ =>
      destruct (ad_pat_sub_to_fuel H) as [njoin Hjoin]
  end.
  match goal with
  | H : {{ _ ⨟ empty ⊢ₚₛ (bskl_to_pskl _) }}a |- _ => rename H into HwfQ
  end.
  assert (HwfpA : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a).
  { apply a_wf_ptyp_to_wf_pskl. apply a_wf_ptyp_of_lc_tvarish;
      [ exact HlcA
      | intros α Hα; left; apply Hrig; exact Hα ]. }
  rewrite pskl_to_uskl_via_bskl_syn in Hjoin.
  destruct (@a_sub_complete njoin a_sub_mode_sk M Θ0 P0
              (ptyp_to_pskl A) (ptyp_to_uskl_syn A) Θ κ Q
              Hwf0 HwfΘ HwfP0 HwfpA
              ltac:(intros _; exact Hmod)
              ltac:(intros Hd0; discriminate)
              Hinc
              (@slack_anno Θ0 κ Θ A Hinc Hwf0 HlcA Hrig)
              ltac:(rewrite pskl_to_uskl_ptyp in Hjoin; exact Hjoin)
              Href HwfQ
              ltac:(intros Hd0; discriminate))
    as [P1 [Θ1 [Hrun Hopt]]].
  exists P1, Θ1. split; [ eapply a_pat__anno; exact Hrun | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  rewrite <- msubst_bskl_syn_erase. exact Hprec.
Qed.

Lemma a_split_complete : forall M Θ0 P0,
  a_sk_mode_compat M P0 ->
  M <> mode_tc ->
  exists P1 Q1,
    ({{ Θ0 ⊲ P0 ▹ P1 ⇢ Q1 ⊣ Θ0 }}a) /\
    a_sk_mode_compat (decr_mode M) Q1 /\
    ((P0 = pskl_ghost /\ P1 = pskl_ghost /\ Q1 = pskl_ghost)
     \/ P0 = pskl_arrow P1 Q1).
Proof.
  intros M Θ0 P0 Hmod Hne; destruct Hmod.
  -
    exists pskl_ghost, pskl_ghost.
    split; [ apply a_split__ghost | ].
    split; [ apply a_sk_mode_compat__ti | ].
    left; repeat split; reflexivity.
  -
    exfalso; apply Hne; reflexivity.
  -
    exists P, Q.
    split; [ apply a_split__arrow | ].
    split; [ simpl; exact Hmod | ].
    right; reflexivity.
Qed.

Lemma a_pat_complete_freeze : forall Θ0 e κ Θ Q,
  (forall Q', {{ Θ ⊢ˢ[ mode_ti ] e ⦂ Q' }}ad ->
     {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ pskl_ghost)) ⊳ Q' }}ad ->
     pat_complete_concl mode_ti Θ0 pskl_ghost e κ Θ Q') ->
  {{ Θ ⊢ˢ[ mode_tc ] (exp_freeze e) ⦂ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ pskl_ghost)) ⊳ Q }}ad ->
  pat_complete_concl mode_tc Θ0 pskl_ghost (exp_freeze e) κ Θ Q.
Proof.
  intros Θ0 e κ Θ Q IH Hd Href.
  inversion Hd; subst.
  destruct (IH _ ltac:(eassumption) Href) as [P1 [Θ1 [Hrun Hopt]]].
  exists P1, Θ1. split; [ apply a_pat__freeze; exact Hrun | exact Hopt ].
Qed.

Lemma a_binds_tvar_tm_absurd : forall Θ x (b : abind),
  uniq Θ ->
  binds x b Θ ->
  abind_is_tm b ->
  a_binds_tvar x Θ ->
  False.
Proof.
  intros Θ x b Hu Hb Htm [Hb' | [Hb' | [τ Hb']]];
    pose proof (binds_unique _ _ _ _ _ Hb Hb' Hu) as ->; exact Htm.
Qed.

Lemma a_wf_pskl_notin_ftv_tm : forall Θ x (b : abind) P,
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  uniq Θ ->
  binds x b Θ ->
  abind_is_tm b ->
  x `notin` ftvar_in_pskl P.
Proof.
  intros Θ x b P Hwf Hu Hb Htm Hin.
  pose proof (a_wf_pskl_ftv_binds Hwf Hin) as Htv; eapply a_binds_tvar_tm_absurd; eassumption.
Qed.

Lemma a_wf_aenv_notin_ftv_tm_prefix : forall Ξ x (b : abind) Θ,
  a_suffix Ξ ->
  {{ ⊢ (Ξ ++ (x ~ b) ++ Θ) }}a ->
  abind_is_tm b ->
  x `notin` (dom Ξ `union` ftvar_in_aenv Ξ).
Proof.
  induction Ξ as [ | [α bΞ] Ξ' IH ]; intros x b Θ Hsuf Hwf Htm;
    [ simpl; clear; fsetdec | ].
  inversion Hsuf as [ | ? ? ? Hsuf' Hsb ]; subst.
  assert (Hx : binds x b (Ξ' ++ (x ~ b) ++ Θ))
    by (apply binds_app_3; apply binds_app_2; unfold binds; simpl; auto).
  destruct Hsb as [ | τ ].
  -
    inversion Hwf as [ | ? ? Hα Hwf' | | | | ]; subst.
    assert (Hαx : α <> x)
      by (intros ->; apply binds_In in Hx; clear - Hα Hx; fsetdec).
    pose proof (IH _ _ _ Hsuf' Hwf' Htm) as Hrec.
    simpl. clear - Hαx Hrec; fsetdec.
  -
    inversion Hwf as [ | | ? ? ? Hα Hτ Hm Hwf' | | | ]; subst.
    assert (Hαx : α <> x)
      by (intros ->; apply binds_In in Hx; clear - Hα Hx; fsetdec).
    pose proof (IH _ _ _ Hsuf' Hwf' Htm) as Hrec.
    assert (Hxτ : x `notin` ftvar_in_ptyp τ).
    { intros Hin.
      pose proof (a_wf_ptyp_ftv_tvarish Hτ Hin) as Htv.
      eapply a_binds_tvar_tm_absurd with (x := x);
        [ apply a_wf_aenv_uniq; exact Hwf' | exact Hx | exact Htm | exact Htv ]. }
    simpl. clear - Hαx Hrec Hxτ; fsetdec.
Qed.

Lemma a_wf_aenv_notin_ftv_tm_below : forall Ξ x (b : abind) Θ,
  {{ ⊢ (Ξ ++ (x ~ b) ++ Θ) }}a ->
  x `notin` (dom Θ `union` ftvar_in_aenv Θ).
Proof.
  intros Ξ x b Θ Hwf.
  assert (HwfT : {{ ⊢ Θ }}a)
    by (eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (x ~ b)); simpl_env; exact Hwf).
  assert (Hu : uniq (Ξ ++ (x ~ b) ++ Θ)) by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Hd : x `notin` dom Θ)
    by (clear - Hu; simpl_env in Hu; destruct_uniq;
        unfold disjoint in *; simpl_env in *; fsetdec).
  pose proof (a_wf_aenv_ftv_dom HwfT) as Hsub.
  clear - Hd Hsub; fsetdec.
Qed.

Lemma a_inc_id_msubst_unique : forall Θ0 κ Θ κ' Θ',
  κ ∷ Θ0 ⊑ Θ ->
  κ' ∷ Θ0 ⊑ Θ' ->
  is_id_msubst κ -> is_id_msubst κ' ->
  κ = κ'.
Proof.
  intros Θ0 κ Θ κ' Θ' H; revert κ' Θ'.
  induction H; intros κ' Θ'' Hinc' Hid Hid'.
  -
    inversion Hinc'; subst; reflexivity.
  -
    inversion Hinc'; subst.
    destruct (is_id_msubst_inv Hid) as [-> Hid2].
    destruct (is_id_msubst_inv Hid') as [-> Hid2'].
    f_equal. eapply IHa_inc; eassumption.
  -
    inversion Hinc'; subst.
    destruct (is_id_msubst_inv Hid) as [-> Hid2].
    destruct (is_id_msubst_inv Hid') as [-> Hid2'].
    f_equal. eapply IHa_inc; eassumption.
  -
    inversion Hinc'; subst. eapply IHa_inc; eassumption.
  -
    inversion Hinc'; subst. eapply IHa_inc; eassumption.
  -
    inversion Hinc'; subst. eapply IHa_inc; eassumption.
Qed.

Lemma a_inc_equiv_strip_tm_head : forall x (b : abind) Θ0 κ1 κ2 (b' : abind) Θ,
  a_inc_equiv ((x ~ b) ++ Θ0) κ1 κ2 ((x ~ b') ++ Θ) ->
  abind_is_tm b ->
  abind_is_tm b' ->
  a_inc_equiv Θ0 κ1 κ2 Θ.
Proof.
  intros x b Θ0 κ1 κ2 b' Θ Hie Htm0 Htm.
  destruct b; try contradiction Htm0;
  inversion Hie; subst;
  match goal with
  | Hsuf : a_suffix ?ΞS, HeqT : ?l = ?r |- _ =>
      first [ constr_eq l ((x ~ b') ++ Θ); symmetry in HeqT | idtac ];
      destruct ΞS as [ | [z bz] Ξ' ]; simpl_env in HeqT;
      [ inversion HeqT; subst; assumption
      | inversion HeqT; subst;
        inversion Hsuf as [ | ? ? ? ? Hsb ]; subst;
        exfalso; destruct Hsb; exact Htm ]
  end.
Qed.

Lemma a_wf_exp_of_tvarish : forall Θ e,
  lc_exp e ->
  (forall α, α `in` ftvar_in_exp e -> a_binds_tvar α Θ) ->
  {{ Θ ⊢ᵉ e }}a.
Proof.
  intros Θ e Hlc; induction Hlc; intros Hftv; simpl in Hftv.
  - apply a_wf_exp__unit.
  - apply a_wf_exp__var.
  - apply a_wf_exp__abs with (L := empty).
    intros x _. apply H0.
    intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup. apply Hftv. clear - Hα Hup; fsetdec.
  - apply a_wf_exp__abs_anno with (L := empty).
    + apply a_wf_ptyp_of_lc_tvarish;
        [ assumption
        | intros α Hα; apply Hftv; clear - Hα; fsetdec ].
    + intros x _. apply H1.
      intros α Hα.
      pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
      simpl in Hup. apply Hftv. clear - Hα Hup; fsetdec.
  - apply a_wf_exp__app;
      [ apply IHHlc1 | apply IHHlc2 ];
      intros α Hα; apply Hftv; clear - Hα; fsetdec.
  - apply a_wf_exp__anno.
    + apply a_wf_ptyp_of_lc_tvarish;
        [ assumption
        | intros α Hα; apply Hftv; clear - Hα; fsetdec ].
    + apply IHHlc. intros α Hα; apply Hftv; clear - Hα; fsetdec.
  - apply a_wf_exp__freeze.
    apply IHHlc. intros α Hα; apply Hftv; exact Hα.
Qed.

Lemma a_pat_run_under_tm_binder : forall x b Θ0 M P0 e Q Θ1,
  {{ ((x ~ b) ++ Θ0) ⊢ˢ[ M ; P0 ] e ⦂ Q ⊣ Θ1 }}a ->
  {{ ⊢ ((x ~ b) ++ Θ0) }}a ->
  {{ ((x ~ b) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat M P0 ->
  {{ ((x ~ b) ++ Θ0) ⊢ᵉ e }}a ->
  abind_is_tm b ->
  exists κid Ξ Θ2,
    Θ1 = Ξ ++ (x ~ b) ++ Θ2 /\
    is_id_msubst κid /\ (κid ∷ Θ0 ⊑ Θ2) /\ a_suffix Ξ /\
    {{ ⊢ (Ξ ++ (x ~ b) ++ Θ2) }}a /\
    x `notin` (dom Ξ `union` ftvar_in_aenv Ξ) /\
    x `notin` (dom Θ2 `union` ftvar_in_aenv Θ2).
Proof.
  intros x b Θ0 M P0 e Q Θ1 Hrun Hwf0x HwfP0 Hmod Hexp Htm.
  destruct (a_pat_sound Hrun Hwf0x HwfP0 Hmod Hexp) as [Hle [Hwf1 _]].
  destruct Hle as [[κid [Hid Hinc]] _].
  assert (Hbx : binds x b Θ1)
    by (eapply a_pat_tm_le; [ exact Hrun | exact Htm | unfold binds; simpl; auto ]).
  assert (Hshape : exists Ξ Θ2,
             Θ1 = Ξ ++ (x ~ b) ++ Θ2 /\ a_suffix Ξ /\ (κid ∷ Θ0 ⊑ Θ2)).
  { destruct b as [ | A | P | | τ ]; simpl in Htm; try contradiction.
    - destruct (a_inc_var_inv Hinc) as [Ξ [A' [Θ2 [-> [_ [Hsuf Hinc']]]]]].
      assert (Heq : abind_var_typ A = abind_var_typ A')
        by (eapply binds_mid_eq; [ exact Hbx | apply a_wf_aenv_uniq; exact Hwf1 ]).
      inversion Heq; subst. eauto.
    - destruct (a_inc_var_skl_inv Hinc) as [Ξ [P' [Θ2 [-> [_ [Hsuf Hinc']]]]]].
      assert (Heq : abind_var_skl P = abind_var_skl P')
        by (eapply binds_mid_eq; [ exact Hbx | apply a_wf_aenv_uniq; exact Hwf1 ]).
      inversion Heq; subst. eauto. }
  destruct Hshape as [Ξ [Θ2 [-> [Hsuf Hinc']]]].
  exists κid, Ξ, Θ2.
  refine (conj eq_refl (conj Hid (conj Hinc' (conj Hsuf (conj Hwf1 (conj _ _)))))).
  - eapply a_wf_aenv_notin_ftv_tm_prefix; [ exact Hsuf | exact Hwf1 | exact Htm ].
  - eapply a_wf_aenv_notin_ftv_tm_below. exact Hwf1.
Qed.

Lemma a_wf_exp_open_tm_binder : forall {Θ x} (b : abind) {e},
  lc_exp (open_exp_wrt_exp e (exp_var_f x)) ->
  (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ) ->
  (forall α, α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
     binds α abind_tvar ((x ~ b) ++ Θ)) /\
  {{ ((x ~ b) ++ Θ) ⊢ᵉ (open_exp_wrt_exp e (exp_var_f x)) }}a.
Proof.
  intros Θ x b e Hlc Hrig.
  assert (Hrigx : forall α,
             α `in` ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) ->
             binds α abind_tvar ((x ~ b) ++ Θ)).
  { intros α Hα.
    pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hup.
    simpl in Hup.
    apply binds_cons_3. apply Hrig. clear - Hα Hup; fsetdec. }
  split; [ exact Hrigx | ].
  apply a_wf_exp_of_tvarish; [ exact Hlc | ].
  intros α Hα. left. apply Hrigx. exact Hα.
Qed.

Lemma a_pat_complete_abs_check : forall Θ0 e κ Θ Q,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs e) ->
  (forall x, pat_complete_ih (open_exp_wrt_exp e (exp_var_f x))) ->
  {{ Θ ⊢ˢ[ mode_tc ] (exp_abs e) ⦂ Q }}ad ->
  pat_complete_concl mode_tc Θ0 pskl_ghost (exp_abs e) κ Θ Q.
Proof.
  intros Θ0 e κ Θ Q Hwf0 HwfΘ Hinc Hrig Hlc IH Hd.
  inversion Hd; subst; [ exfalso; auto | ].
  match goal with
  | H : forall x, x `notin` ?L0 -> {{ _ ⊢ˢ[ _ ] _ ⦂ _ }}ad |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  simpl in Hrig.

  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_pskl P)) as [x Hx].
  set (bx := abind_var_skl pskl_ghost).
  assert (Hwf0x : {{ ⊢ ((x ~ bx) ++ Θ0) }}a)
    by (apply a_wf_aenv__var;
        [ clear - Hx; fsetdec | apply a_wf_pskl__ghost | exact Hwf0 ]).
  assert (HwfΘx : {{ ⊢ ((x ~ bx) ++ Θ) }}a)
    by (apply a_wf_aenv__var;
        [ clear - Hx; fsetdec | apply a_wf_pskl__ghost | exact HwfΘ ]).
  assert (Hincx : κ ∷ ((x ~ bx) ++ Θ0) ⊑ ((x ~ bx) ++ Θ)).
  { apply (@a_inc__var_skl Θ0 κ Θ nil x pskl_ghost pskl_ghost);
      [ exact Hinc
      | apply a_pskl_tyequiv__refl; apply lc_pskl_ghost
      | apply a_suffix__nil ]. }
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (inversion Hlc; auto).
  destruct (a_wf_exp_open_tm_binder bx Hlcbody
              Hrig)
    as [Hrigx Hexpx].

  destruct (IH x mode_tc ((x ~ bx) ++ Θ0) pskl_ghost κ ((x ~ bx) ++ Θ)
              (pskl_to_bskl_syn P)
              Hwf0x HwfΘx
              ltac:(apply a_wf_pskl__ghost)
              ltac:(apply a_sk_mode_compat__tc)
              Hincx Hrigx Hlcbody
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(apply ad_refine_syn__ghost; clear; fsetdec))
    as [Q' [Θ1' [Hrun Hopt]]].

  destruct (a_pat_run_under_tm_binder Hrun Hwf0x (a_wf_pskl__ghost _ _)
              a_sk_mode_compat__tc Hexpx I)
    as [κid [Ξ [Θ2 [-> [Hidκ [Hincid' [Hsuf [Hwf1' [HxΞ HxΘ2]]]]]]]]].

  exists (pskl_univ_ghost (pskl_arrow pskl_ghost Q')), (Ξ ++ Θ2).
  split.
  {
    apply a_pat__abs_check with (x := x);
      [ exact Hsuf
      | clear - Hx HxΞ HxΘ2; simpl_env; solve_notin_auto
      | exact Hrun ]. }

  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κid)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincid' | exact Hid1 | exact Hidκ ]).
  assert (Hinc1x : κ1 ∷ ((x ~ bx) ++ Θ0) ⊑ (Ξ ++ (x ~ bx) ++ Θ2)).
  { apply (@a_inc__var_skl Θ0 κ1 Θ2 Ξ x pskl_ghost pskl_ghost);
      [ rewrite Heqκ; exact Hincid'
      | apply a_pskl_tyequiv__refl; apply lc_pskl_ghost
      | exact Hsuf ]. }
  destruct (Hopt κ1 Hid1 Hinc1x) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ.
  split.
  { exact (@a_inc_strip_tm_head Ξ x (abind_var_skl pskl_ghost)
             (abind_var_skl pskl_ghost) Θ2 ζ Θ Hsuf
             (fun h : abind_is_ty (abind_var_skl pskl_ghost) => h)
             (fun h : abind_is_ty (abind_var_skl pskl_ghost) => h)
             Hwf1' HwfΘx Hζ). }
  split.
  { eapply a_inc_equiv_strip_tm_head; [ exact Heqv | exact I | exact I ]. }
  {
    unfold ad_precise in Hprec |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    apply ad_refine_syn_univ_ghost_keep_intro.
    apply ad_refine_syn_arrow_intro.
    - apply (@ad_refine_syn__ghost Θ empty pskl_ghost).
      clear; fsetdec.
    - eapply ad_refine_syn_mono;
        [ exact Hprec
        | apply (@aenv_tbinds_le_strip_tm nil x bx Θ); intros h; exact h ]. }
Qed.

Lemma a_pat_complete_abs_anno_check : forall Θ0 A e κ Θ Q,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs_anno A e) ->
  (forall x, pat_complete_ih (open_exp_wrt_exp e (exp_var_f x))) ->
  {{ Θ ⊢ˢ[ mode_tc ] (exp_abs_anno A e) ⦂ Q }}ad ->
  pat_complete_concl mode_tc Θ0 pskl_ghost (exp_abs_anno A e) κ Θ Q.
Proof.
  intros Θ0 A e κ Θ Q Hwf0 HwfΘ Hinc Hrig Hlc IH Hd.
  inversion Hd; subst; [ exfalso; auto | ].
  match goal with
  | H : forall x, x `notin` ?L0 -> {{ _ ⊢ˢ[ _ ] _ ⦂ _ }}ad |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | H : a_wf_ptyp Θ A |- _ => rename H into HwfA
  end.
  simpl in Hrig.
  assert (HrigA : forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (HlcA : lc_ptyp A) by (inversion Hlc; assumption).
  assert (HwfA0 : a_wf_ptyp Θ0 A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA; exact Hα ]).
  assert (HmsA : msubst_ptyp κ A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hinc | exact Hwf0 | exact HrigA ]).

  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp A
                          `union` ftvar_in_pskl P)) as [x Hx].
  set (bx := abind_var_typ A).
  assert (Hwf0x : {{ ⊢ ((x ~ bx) ++ Θ0) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA0 | exact Hwf0 ]).
  assert (HwfΘx : {{ ⊢ ((x ~ bx) ++ Θ) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact HwfΘ ]).
  assert (Hincx : κ ∷ ((x ~ bx) ++ Θ0) ⊑ ((x ~ bx) ++ Θ)).
  { apply (@a_inc__var Θ0 κ Θ nil x A A);
      [ exact Hinc
      | rewrite HmsA; apply a_tyequiv__refl; exact HlcA
      | apply a_suffix__nil ]. }
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (inversion Hlc; auto).
  destruct (a_wf_exp_open_tm_binder bx Hlcbody
              (fun α Hα => Hrig α (union_3 _ Hα)))
    as [Hrigx Hexpx].

  destruct (IH x mode_tc ((x ~ bx) ++ Θ0) pskl_ghost κ ((x ~ bx) ++ Θ)
              (pskl_to_bskl_syn P)
              Hwf0x HwfΘx
              ltac:(apply a_wf_pskl__ghost)
              ltac:(apply a_sk_mode_compat__tc)
              Hincx Hrigx Hlcbody
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(apply ad_refine_syn__ghost; clear; fsetdec))
    as [Q' [Θ1' [Hrun Hopt]]].

  destruct (a_pat_run_under_tm_binder Hrun Hwf0x (a_wf_pskl__ghost _ _)
              a_sk_mode_compat__tc Hexpx I)
    as [κid [Ξ [Θ2 [-> [Hidκ [Hincid' [Hsuf [Hwf1' [HxΞ HxΘ2]]]]]]]]].

  exists (pskl_univ_ghost (pskl_arrow (ptyp_to_pskl A) Q')), (Ξ ++ Θ2).
  split.
  {
    apply a_pat__abs_anno_check with (x := x);
      [ exact Hsuf
      | clear - Hx HxΞ HxΘ2; simpl_env; solve_notin_auto
      | exact Hrun ]. }

  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κid)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincid' | exact Hid1 | exact Hidκ ]).
  assert (HmsA1 : msubst_ptyp κ1 A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hinc1 | exact Hwf0 | exact HrigA ]).
  assert (Hinc1x : κ1 ∷ ((x ~ bx) ++ Θ0) ⊑ (Ξ ++ (x ~ bx) ++ Θ2)).
  { apply (@a_inc__var Θ0 κ1 Θ2 Ξ x A A);
      [ rewrite Heqκ; exact Hincid'
      | rewrite HmsA1; apply a_tyequiv__refl; exact HlcA
      | exact Hsuf ]. }
  destruct (Hopt κ1 Hid1 Hinc1x) as [ζ [Hζ [Heqv Hprec]]].
  assert (Hζs : ζ ∷ (Ξ ++ Θ2) ⊑ Θ).
  { exact (@a_inc_strip_tm_head Ξ x (abind_var_typ A)
             (abind_var_typ A) Θ2 ζ Θ Hsuf
             (fun h : abind_is_ty (abind_var_typ A) => h)
             (fun h : abind_is_ty (abind_var_typ A) => h)
             Hwf1' HwfΘx Hζ). }
  exists ζ.
  split; [ exact Hζs | ].
  split.
  { eapply a_inc_equiv_strip_tm_head; [ exact Heqv | exact I | exact I ]. }
  {
    unfold ad_precise in Hprec |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
    rewrite btyp_to_bskl_ptyp_to_btyp_syn.
    rewrite !bskl_to_pskl_pskl_to_bskl_syn.
    rewrite msubst_pskl_embed_ptyp.
    assert (HmsAζ : msubst_ptyp ζ A = A).
    { eapply msubst_ptyp_rigid_id with (Θ0 := Ξ ++ Θ2);
        [ exact Hζs
        | exact (@a_wf_aenv_strip_tm_mid Ξ x (abind_var_typ A) Θ2
                   (fun h : abind_is_ty (abind_var_typ A) => h) Hwf1')
        | intros α Hα; apply binds_app_3;
          eapply a_inc_binds_tvar;
            [ exact Hincid' | apply HrigA; exact Hα ] ]. }
    rewrite HmsAζ.
    apply ad_refine_syn_univ_ghost_keep_intro.
    apply ad_refine_syn_arrow_intro.
    - apply ad_precise_refl.
      apply a_wf_ptyp_to_wf_pskl. exact HwfA.
    - eapply ad_refine_syn_mono;
        [ exact Hprec
        | apply (@aenv_tbinds_le_strip_tm nil x bx Θ); intros h; exact h ]. }
Qed.

Lemma ad_ctx_precise_refl : forall Θ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⪯ᶜᵗˣ Θ }}ad.
Proof.
  intros Θ Hwf; induction Hwf.
  - apply ad_ctx_precise__nil.
  - apply ad_ctx_precise__copy; [ intros h; exact h | exact IHHwf ].
  - apply ad_ctx_precise__copy; [ intros h; exact h | exact IHHwf ].
  - eapply ad_ctx_precise__tm with (P' := P) (P := P);
      [ simpl; reflexivity | simpl; reflexivity
      | apply ad_precise_refl; exact H0
      | exact IHHwf ].
  - eapply ad_ctx_precise__tm
      with (P' := ptyp_to_pskl A) (P := ptyp_to_pskl A);
      [ simpl; reflexivity | simpl; reflexivity
      | apply ad_precise_refl; apply a_wf_ptyp_to_wf_pskl; exact H0
      | exact IHHwf ].
  - apply ad_ctx_precise__copy; [ intros h; exact h | exact IHHwf ].
Qed.

Lemma ad_refine_msubst_compose_id : forall Θ0 Θmid Θ κ κb ζb P0 Q,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θmid }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  is_id_msubst κb -> κb ∷ Θ0 ⊑ Θmid ->
  ζb ∷ Θmid ⊑ Θ ->
  a_inc_equiv Θ0 κ (msubst_compose ζb κb) Θ ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl ζb P0)) ⊳ Q }}ad.
Proof.
  intros Θ0 Θmid Θ κ κb ζb P0 Q Hwf0 Hwfmid HwfΘ HwfP0 Hinc Hidb Hincb
         Hζb Heqvb HwfQ Href.
  assert (Hσ : msubst_compose ζb κb ∷ Θ0 ⊑ Θ)
    by (eapply a_inc_compose;
        [ exact Hincb | exact Hwf0 | exact Hwfmid | exact Hζb ]).
  rewrite <- (@msubst_compose_id_pskl Θ0 κb Θmid ζb Θ P0 Hwf0 Hwfmid Hidb
                Hincb Hζb (a_scope_pskl_of_wf HwfP0)).
  eapply ad_precise_preserves_refine;
    [ eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
        [ exact HwfP0 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ
        | exact Heqvb ]
    | exact Href | exact HwfΘ
    | intros α Hα; clear - Hα; fsetdec | exact HwfQ ].
Qed.

Lemma a_pat_complete_abs : forall M Θ0 P0 e κ Θ Q,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat M P0 ->
  M <> mode_tc ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs e) ->
  (forall x, pat_complete_ih (open_exp_wrt_exp e (exp_var_f x))) ->
  {{ Θ ⊢ˢ[ M ] (exp_abs e) ⦂ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  pat_complete_concl M Θ0 P0 (exp_abs e) κ Θ Q.
Proof.
  intros M Θ0 P0 e κ Θ Q Hwf0 HwfΘ HwfP0 Hmod HMne Hinc Hrig
         Hlc IH Hd Href.
  inversion Hd; subst; [ | exfalso; auto ].
  match goal with
  | H : forall x, x `notin` ?L0 -> {{ _ ⊢ˢ[ _ ] _ ⦂ _ }}ad |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | H : {{ Θ ⨟ empty ⊢ₚₛ ?PP }}a |- _ => rename H into HwfPrule; rename PP into P
  end.
  match goal with
  | H : {{ _ ⊢ˢ[ M ] exp_abs e ⦂ _ }}ad |- _ => clear H
  end.
  simpl in Hrig.

  destruct (a_split_complete Θ0 Hmod HMne)
    as [P1 [Q1 [Hsplit [HmodQ1 Hshape]]]].

  assert (Hpieces :
      ({{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl κ P1) ⊑ P }}ad) /\
      ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ Q1)) ⊳ Q0 }}ad) /\
      ({{ Θ0 ⨟ empty ⊢ₚₛ P1 }}a) /\ ({{ Θ0 ⨟ empty ⊢ₚₛ Q1 }}a)).
  { destruct Hshape as [[-> [-> ->]] | ->].
    -
      cbn [msubst_pskl pskl_to_bskl_inh] in Href.
      inversion Href; subst.
      match goal with
      | Hp : pskl_to_bskl_syn ?PF = _ |- _ =>
          destruct PF; simpl in Hp; try discriminate;
          inversion Hp; subst
      end.
      repeat split.
      + unfold ad_precise. cbn [msubst_pskl pskl_to_bskl_inh].
        match goal with
        | Hpa : pskl_to_bskl_syn ?Pa = pskl_to_bskl_inh P |- _ =>
            rewrite <- Hpa
        end.
        apply ad_refine_syn__ghost. clear; fsetdec.
      + cbn [msubst_pskl pskl_to_bskl_inh].
        apply ad_refine_syn__ghost. clear; fsetdec.
      + apply a_wf_pskl__ghost.
      + apply a_wf_pskl__ghost.
    -
      cbn [msubst_pskl pskl_to_bskl_inh] in Href.
      inversion Href; subst.
      inversion HwfP0; subst.
      repeat split; assumption. }
  destruct Hpieces as [Hprec13 [Href14 [HwfP1 HwfQ1]]].
  assert (HwfP1κ : {{ Θ ⨟ empty ⊢ₚₛ (msubst_pskl κ P1) }}a)
    by (eapply a_wf_pskl_msubst_inc;
        [ exact Hinc | exact Hwf0 | exact HwfP1
        | intros α Hα; clear - Hα; fsetdec
        | intros β γ _ _ _; clear; fsetdec ]).

  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_pskl P1 `union` ftvar_in_pskl Q1
                          `union` ftvar_in_pskl P)) as [x Hx].
  set (bq := abind_var_skl P1).
  set (bs := abind_var_skl (msubst_pskl κ P1)).
  assert (Hwf0x : {{ ⊢ ((x ~ bq) ++ Θ0) }}a).
  { apply a_wf_aenv__var;
      [ clear - Hx; fsetdec
      | exact HwfP1
      | exact Hwf0 ]. }
  assert (HwfΘx : {{ ⊢ ((x ~ bs) ++ Θ) }}a).
  { apply a_wf_aenv__var;
      [ clear - Hx; fsetdec
      | exact HwfP1κ
      | exact HwfΘ ]. }
  assert (HwfΘxP : {{ ⊢ ((x ~ abind_var_skl P) ++ Θ) }}a).
  { apply a_wf_aenv__var;
      [ clear - Hx; fsetdec
      | exact HwfPrule
      | exact HwfΘ ]. }
  assert (Hincx : κ ∷ ((x ~ bq) ++ Θ0) ⊑ ((x ~ bs) ++ Θ)).
  { apply (@a_inc__var_skl Θ0 κ Θ nil x P1 (msubst_pskl κ P1));
      [ exact Hinc
      | apply a_pskl_tyequiv__refl; eapply a_wf_pskl_lc; exact HwfP1κ
      | apply a_suffix__nil ]. }
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (inversion Hlc; auto).
  destruct (a_wf_exp_open_tm_binder bq Hlcbody
              Hrig)
    as [Hrigx Hexpx].

  assert (Hctx : {{ ((x ~ bs) ++ Θ) ⪯ᶜᵗˣ ((x ~ abind_var_skl P) ++ Θ) }}ad).
  { eapply ad_ctx_precise__tm
      with (P' := msubst_pskl κ P1) (P := P);
      [ simpl; reflexivity | simpl; reflexivity
      | exact Hprec13
      | apply ad_ctx_precise_refl; exact HwfΘ ]. }
  pose proof (ad_ctx_precise_pat (Hbody x ltac:(clear - Hx; solve_notin_auto))
                Hctx HwfΘxP HwfΘx) as Hbodyx.

  destruct (IH x (decr_mode M) ((x ~ bq) ++ Θ0) Q1 κ ((x ~ bs) ++ Θ) Q0
              Hwf0x HwfΘx
              ltac:(eapply a_wf_pskl_mono;
                    [ exact HwfQ1
                    | intros α c _ Hc; apply binds_cons_3; exact Hc ])
              HmodQ1 Hincx Hrigx Hlcbody Hbodyx
              ltac:(eapply ad_refine_syn_mono;
                    [ exact Href14
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [Q' [Θ1' [Hrun Hopt]]].

  assert (HwfQ1x : {{ ((x ~ bq) ++ Θ0) ⨟ empty ⊢ₚₛ Q1 }}a)
    by (eapply a_wf_pskl_mono;
        [ exact HwfQ1
        | intros α c _ Hc; apply binds_cons_3; exact Hc ]).
  destruct (a_pat_run_under_tm_binder Hrun Hwf0x HwfQ1x HmodQ1 Hexpx I)
    as [κid [Ξ [Θ2 [-> [Hidκ [Hincid' [Hsuf [Hwf1' [HxΞ HxΘ2]]]]]]]]].

  exists (pskl_arrow P1 Q'), (Ξ ++ Θ2).
  split.
  {
    eapply a_pat__abs with (x := x);
      [ exact HMne | exact Hsplit | exact Hsuf
      | clear - Hx HxΞ HxΘ2; simpl_env; solve_notin_auto
      | exact Hrun ]. }

  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κid)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincid' | exact Hid1 | exact Hidκ ]).
  assert (Hinc1x : κ1 ∷ ((x ~ bq) ++ Θ0) ⊑ (Ξ ++ (x ~ bq) ++ Θ2)).
  { apply (@a_inc__var_skl Θ0 κ1 Θ2 Ξ x P1 P1);
      [ rewrite Heqκ; exact Hincid'
      | rewrite (msubst_pskl_id P1 Hid1);
        apply a_pskl_tyequiv__refl; eapply a_wf_pskl_lc; exact HwfP1
      | exact Hsuf ]. }
  destruct (Hopt κ1 Hid1 Hinc1x) as [ζ [Hζ [Heqv Hprec]]].
  assert (Hζs : ζ ∷ (Ξ ++ Θ2) ⊑ Θ).
  { exact (@a_inc_strip_tm_head Ξ x bq bs Θ2 ζ Θ Hsuf
             (fun h : abind_is_ty bq => h)
             (fun h : abind_is_ty bs => h)
             Hwf1' HwfΘx Hζ). }
  assert (Heqvs : a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ)
    by (eapply a_inc_equiv_strip_tm_head; [ exact Heqv | exact I | exact I ]).
  exists ζ.
  split; [ exact Hζs | ].
  split; [ exact Heqvs | ].
  {
    assert (Hwfmid : {{ ⊢ (Ξ ++ Θ2) }}a)
      by (exact (@a_wf_aenv_strip_tm_mid Ξ x bq Θ2
                   (fun h : abind_is_ty bq => h) Hwf1')).
    assert (Hσ : msubst_compose ζ κ1 ∷ Θ0 ⊑ Θ)
      by (eapply a_inc_compose;
          [ exact Hinc1 | exact Hwf0 | exact Hwfmid | exact Hζs ]).
    assert (Hpp : {{ Θ ⨟ empty ⊢ₚᵣ
                    (msubst_pskl (msubst_compose ζ κ1) P1) ⊑ (msubst_pskl κ P1) }}ad).
    { eapply a_inc_equiv_precise_msubst_flip with (Θ0 := Θ0) (Δ0 := empty);
        [ exact HwfP1 | exact Hwf0 | exact HwfΘ | exact Hinc | exact Hσ
        | exact Heqvs ]. }
    assert (Hdom : {{ Θ ⨟ empty ⊢ᵣ
                     (pskl_to_bskl_inh (msubst_pskl (msubst_compose ζ κ1) P1))
                     ⊳ (pskl_to_bskl_inh P) }}ad).
    { eapply ad_precise_preserves_refine;
        [ exact Hpp
        | exact Hprec13
        | exact HwfΘ
        | intros α Hα; clear - Hα; fsetdec
        | rewrite bskl_to_pskl_pskl_to_bskl_inh; exact HwfPrule ]. }
    assert (Hms : msubst_pskl (msubst_compose ζ κ1) P1 = msubst_pskl ζ P1).
    { rewrite msubst_pskl_compose.
      - rewrite (msubst_pskl_id P1 Hid1). reflexivity.
      - intros α Hα.
        pose proof (a_wf_pskl_ftv_binds HwfP1 Hα) as Htv.
        destruct Htv as [Hb | [Hb | [τ Hb]]].
        + right.
          eapply a_inc_tvar_notin_dom;
            [ exact Hζs | exact Hwfmid
            | apply binds_app_3; eapply a_inc_binds_tvar;
                [ exact Hincid' | exact Hb ] ].
        + left. eapply a_inc_flex_dom;
            [ exact Hinc1 | exact Hwf0 | left; exact Hb ].
        + left. eapply a_inc_flex_dom;
            [ exact Hinc1 | exact Hwf0 | right; exists τ; exact Hb ]. }
    unfold ad_precise in Hprec |- *.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    apply ad_refine_syn_arrow_intro.
    - rewrite <- Hms. exact Hdom.
    - eapply ad_refine_syn_mono;
        [ exact Hprec
        | apply (@aenv_tbinds_le_strip_tm nil x bs Θ); intros h; exact h ]. }
Qed.

Lemma ad_pat_consis_syn_bid : forall Θ A,
  a_wf_ptyp Θ A ->
  forall B : btyp, btyp_to_ptyp B = A ->
  {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ (btyp_to_bskl B) }}ad.
Proof.
  intros Θ A Hwf; induction Hwf; intros B HB.
  - destruct B; simpl in HB; try discriminate.
    apply ad_pat_consis__unit. clear; fsetdec.
  - destruct B; simpl in HB; try discriminate.
    inversion HB; subst.
    apply ad_pat_consis__var; [ clear; fsetdec | assumption ].
  - destruct B; simpl in HB; try discriminate.
    inversion HB; subst.
    eapply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHwf1; reflexivity
      | apply IHHwf2; reflexivity
      | clear; fsetdec ].
  - destruct B as [ | | | | B0 | B0 ]; simpl in HB; try discriminate;
      inversion HB; subst.
    +
      apply ad_pat_consis__forall_syn
        with (L := L) (R := ptyp_to_uskl_syn (btyp_to_ptyp B0)).
      intros α Hα.
      rewrite <- ptyp_to_uskl_syn_open.
      change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
      rewrite <- btyp_to_bskl_open.
      apply H0; [ exact Hα | ].
      rewrite btyp_to_ptyp_open_var. reflexivity.
    +
      apply ad_pat_consis__forall_inh_untagged
        with (L := L) (R := ptyp_to_uskl_syn (btyp_to_ptyp B0)).
      intros α Hα.
      rewrite <- ptyp_to_uskl_syn_open.
      change (bskl_var_f α) with (btyp_to_bskl (btyp_var_f α)).
      rewrite <- btyp_to_bskl_open.
      apply H0; [ exact Hα | ].
      rewrite btyp_to_ptyp_open_var. reflexivity.
Qed.

Lemma a_pat_complete_abs_anno : forall M Θ0 P0 A e κ Θ Q,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat M P0 ->
  M <> mode_tc ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs_anno A e) ->
  (forall x, pat_complete_ih (open_exp_wrt_exp e (exp_var_f x))) ->
  {{ Θ ⊢ˢ[ M ] (exp_abs_anno A e) ⦂ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  pat_complete_concl M Θ0 P0 (exp_abs_anno A e) κ Θ Q.
Proof.
  intros M Θ0 P0 A e κ Θ Q Hwf0 HwfΘ HwfP0 Hmod HMne Hinc Hrig
         Hlc IH Hd Href.
  inversion Hd; subst; [ | exfalso; auto ].
  match goal with
  | H : forall x, x `notin` ?L0 -> {{ _ ⊢ˢ[ _ ] _ ⦂ _ }}ad |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | |- pat_complete_concl _ _ _ (exp_abs_anno (btyp_to_ptyp ?BB) _) _ _ _ =>
      try rename BB into B
  end.
  set (A := btyp_to_ptyp B) in *.
  assert (HBA : btyp_to_ptyp B = A) by reflexivity.
  match goal with
  | H : a_wf_ptyp Θ A |- _ => rename H into HwfA
  end.
  simpl in Hrig.
  assert (HrigA : forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (HlcA : lc_ptyp A) by (inversion Hlc; assumption).
  assert (HwfA0 : a_wf_ptyp Θ0 A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA; exact Hα ]).
  assert (HmsA : msubst_ptyp κ A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hinc | exact Hwf0 | exact HrigA ]).

  destruct (a_split_complete Θ0 Hmod HMne)
    as [P1 [Q1 [Hsplit [HmodQ1 Hshape]]]].

  assert (Hpieces :
      ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P1))
         ⊳ (btyp_to_bskl B) }}ad) /\
      ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ Q1)) ⊳ Q0 }}ad) /\
      ({{ Θ0 ⨟ empty ⊢ₚₛ P1 }}a) /\ ({{ Θ0 ⨟ empty ⊢ₚₛ Q1 }}a)).
  { destruct Hshape as [[-> [-> ->]] | ->].
    - cbn [msubst_pskl pskl_to_bskl_inh] in Href.
      inversion Href; subst.
      match goal with
      | Hp : pskl_to_bskl_syn ?PF = _ |- _ =>
          destruct PF; simpl in Hp; try discriminate;
          inversion Hp; subst
      end.
      repeat split.
      + cbn [msubst_pskl pskl_to_bskl_inh].
        first
          [ apply ad_refine_syn__ghost; clear; fsetdec
          | match goal with
            | Hpa : pskl_to_bskl_syn _ = btyp_to_bskl _ |- _ =>
                rewrite <- Hpa; apply ad_refine_syn__ghost; clear; fsetdec
            | Hpa : btyp_to_bskl _ = pskl_to_bskl_syn _ |- _ =>
                rewrite Hpa; apply ad_refine_syn__ghost; clear; fsetdec
            end ].
      + cbn [msubst_pskl pskl_to_bskl_inh].
        apply ad_refine_syn__ghost. clear; fsetdec.
      + apply a_wf_pskl__ghost.
      + apply a_wf_pskl__ghost.
    - cbn [msubst_pskl pskl_to_bskl_inh] in Href.
      inversion Href; subst.
      inversion HwfP0; subst.
      repeat split; assumption. }
  destruct Hpieces as [Href13 [Href14 [HwfP1 HwfQ1]]].
  assert (HwfpA0 : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfA0).

  assert (Hjoin : {{ empty ⨟ Θ ⊢ˢ
                    (pskl_to_uskl (msubst_pskl κ (ptyp_to_pskl A)))
                    ∼ (btyp_to_bskl B) }}ad).
  { rewrite msubst_pskl_embed_ptyp, HmsA, pskl_to_uskl_ptyp.
    apply (ad_pat_consis_syn_bid HwfA B HBA). }
  assert (Hrp : {{ Θ ⨟ empty ⊢ᵣₚ (msubst_pskl κ (ptyp_to_pskl A)) ⊳ (bskl_to_pskl (btyp_to_bskl B)) }}ad).
  { rewrite msubst_pskl_embed_ptyp, HmsA.
    rewrite bskl_to_pskl_btyp_to_bskl, HBA.
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl; exact HwfA. }
  destruct (a_consis_complete Hwf0 HwfP1 HwfpA0 Hinc HwfΘ Hjoin Href13 Hrp
              (@ad_pat_consis_msubst_target_wf _ _ _ _ _ Hjoin
                     ltac:(first [ exact I | apply ptyp_to_pskl_ghost_free ]) empty))
    as [Ac [Θmid [HcRun HoptC]]].
  destruct (a_consis_isub_wf_nil HcRun Hwf0 HwfP1 HwfpA0) as [Hlec Hwfmid].
  destruct Hlec as [[κc [Hidc Hincc]] _].
  destruct (HoptC κc Hidc Hincc) as [ζc0 [Hζc0 [Heqvc _]]].

  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` dom Θmid `union` ftvar_in_aenv Θmid
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp A
                          `union` ftvar_in_pskl P1 `union` ftvar_in_pskl Q1))
    as [x Hx].
  set (bA := abind_var_typ A).
  assert (HrigMid : forall α, α `in` ftvar_in_ptyp A ->
             binds α abind_tvar Θmid)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hincc | apply HrigA; exact Hα ]).
  assert (HwfAmid : a_wf_ptyp Θmid A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigMid; exact Hα ]).
  assert (Hwf0x : {{ ⊢ ((x ~ bA) ++ Θmid) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfAmid | exact Hwfmid ]).
  assert (HwfΘx : {{ ⊢ ((x ~ bA) ++ Θ) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact HwfΘ ]).
  assert (HmsAζc : msubst_ptyp ζc0 A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζc0 | exact Hwfmid | exact HrigMid ]).
  assert (Hincx : ζc0 ∷ ((x ~ bA) ++ Θmid) ⊑ ((x ~ bA) ++ Θ)).
  { apply (@a_inc__var Θmid ζc0 Θ nil x A A);
      [ exact Hζc0
      | rewrite HmsAζc; apply a_tyequiv__refl; exact HlcA
      | apply a_suffix__nil ]. }
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (inversion Hlc; auto).

  assert (HwfQb : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q0) }}a).
  { pose proof (ad_pat_target_wf (Hbody x ltac:(clear - Hx; solve_notin_auto)) HwfΘx)
      as Hw.
    eapply a_wf_pskl_mono;
      [ exact Hw
      | apply (@aenv_tbinds_le_strip_tm nil x bA Θ); intros h; exact h ]. }
  pose proof (ad_refine_msubst_compose_id Hwf0 Hwfmid HwfΘ HwfQ1 Hinc Hidc
                Hincc Hζc0 Heqvc HwfQb Href14) as Href14σ.

  destruct (a_wf_exp_open_tm_binder bA Hlcbody
              (fun α Hα => a_inc_binds_tvar α Hincc (Hrig α (union_3 _ Hα))))
    as [Hrigx Hexpx].
  assert (HwfQ1mid : {{ Θmid ⨟ empty ⊢ₚₛ Q1 }}a).
  { pose proof (a_wf_pskl_msubst_inc Hincc Hwf0 HwfQ1
                  ltac:(intros α Hα; clear - Hα; solve_notin_auto)
                  ltac:(intros β γ _ _ _; clear; fsetdec)) as Hw.
    rewrite (msubst_pskl_id Q1 Hidc) in Hw. exact Hw. }
  destruct (IH x (decr_mode M) ((x ~ bA) ++ Θmid) Q1 ζc0 ((x ~ bA) ++ Θ) Q0
              Hwf0x HwfΘx
              ltac:(eapply a_wf_pskl_mono;
                    [ exact HwfQ1mid
                    | intros α c _ Hc; apply binds_cons_3; exact Hc ])
              HmodQ1 Hincx Hrigx Hlcbody
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact Href14σ
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [Q' [Θ1' [HrunB HoptB]]].

  assert (HwfQ1midx : {{ ((x ~ bA) ++ Θmid) ⨟ empty ⊢ₚₛ Q1 }}a)
    by (eapply a_wf_pskl_mono;
        [ exact HwfQ1mid
        | intros α c _ Hc; apply binds_cons_3; exact Hc ]).
  destruct (a_pat_run_under_tm_binder HrunB Hwf0x HwfQ1midx HmodQ1 Hexpx I)
    as [κb [Ξ [Θ3 [-> [Hidb [Hincb' [Hsuf [HwfB' [HxΞ HxΘ3]]]]]]]]].

  exists (pskl_arrow (ptyp_to_pskl A) Q'), (Ξ ++ Θ3).
  split.
  {
    eapply a_pat__abs_anno with (x := x);
      [ exact HMne | exact Hsplit | exists Ac; exact HcRun | exact Hsuf
      | clear - Hx HxΞ HxΘ3; simpl_env; solve_notin_auto
      | exact HrunB ]. }

  intros κ1 Hid1 Hinc1.
  assert (Heqκc : κ1 = κc)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincc | exact Hid1 | exact Hidc ]).
  assert (Hinc1b : κb ∷ ((x ~ bA) ++ Θmid) ⊑ (Ξ ++ (x ~ bA) ++ Θ3)).
  { apply (@a_inc__var Θmid κb Θ3 Ξ x A A);
      [ exact Hincb'
      | rewrite (msubst_ptyp_id A Hidb);
        apply a_tyequiv__refl; exact HlcA
      | exact Hsuf ]. }
  destruct (HoptB κb Hidb Hinc1b) as [ζb [Hζb [Heqvb Hprecb]]].
  assert (Hζbs : ζb ∷ (Ξ ++ Θ3) ⊑ Θ).
  { exact (@a_inc_strip_tm_head Ξ x bA bA Θ3 ζb Θ Hsuf
             (fun h : abind_is_ty bA => h)
             (fun h : abind_is_ty bA => h)
             HwfB' HwfΘx Hζb). }
  assert (Heqvbs : a_inc_equiv Θmid ζc0 (msubst_compose ζb κb) Θ)
    by (eapply a_inc_equiv_strip_tm_head; [ exact Heqvb | exact I | exact I ]).
  assert (Hwffin : {{ ⊢ (Ξ ++ Θ3) }}a)
    by (exact (@a_wf_aenv_strip_tm_mid Ξ x bA Θ3
                 (fun h : abind_is_ty bA => h) HwfB')).

  assert (Hlcfin : lc_aenv Θ3)
    by (apply a_wf_aenv_lc_aenv; eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (x ~ bA));
        simpl_env; exact HwfB').
  destruct (a_inc_weaken_suffix_target Hincb' Hidb Hlcfin Hsuf)
    as [κb2 [Hidb2 Hincb2]].
  assert (Heqκb : κb2 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hincb2 | exact Hincb' | exact Hidb2 | exact Hidb ]).
  subst κb2.
  exists ζb.
  split; [ exact Hζbs | ].
  split.
  {
    assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζb κc) Θ).
    { eapply a_inc_equiv_glue with
        (Θmid := Θmid) (Θfin := Ξ ++ Θ3) (κ1b := κb) (ζ1 := ζc0);
        [ exact Hwf0 | exact Hwfmid | exact Hwffin | exact HwfΘ
        | exact Hidc | exact Hidb
        |
          intros α Hα;
          pose proof (a_inc_dom_flex Hincc Hα) as Hfα;
          eapply a_inc_flex_dom;
            [ exact Hincb2 | exact Hwfmid
            | eapply (proj2 (proj2 a_assign_unify_consis_flex_preserve));
                [ exact HcRun | exact Hfα ] ]
        | exact Hincc | exact Hincb2 | exact Hζc0 | exact Hζbs
        | exact Heqvc | exact Heqvbs ]. }
    rewrite Heqκc. exact Hglue. }
  {
    unfold ad_precise in Hprecb |- *.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh].
    rewrite bskl_to_pskl_btyp_to_bskl, HBA.
    rewrite msubst_pskl_embed_ptyp.
    assert (HmsAζb : msubst_ptyp ζb A = A).
    { eapply msubst_ptyp_rigid_id with (Θ0 := Ξ ++ Θ3);
        [ exact Hζbs | exact Hwffin
        | intros α Hα; apply binds_app_3;
          eapply a_inc_binds_tvar;
            [ exact Hincb' | apply HrigMid; exact Hα ] ]. }
    rewrite HmsAζb.
    apply ad_refine_syn_arrow_intro.
    - apply ad_precise_refl.
      apply a_wf_ptyp_to_wf_pskl. exact HwfA.
    - eapply ad_refine_syn_mono;
        [ exact Hprecb
        | apply (@aenv_tbinds_le_strip_tm nil x bA Θ); intros h; exact h ]. }
Qed.

Lemma a_flex_tvar_strip_nonflex_head : forall c (b : abind) Θ α,
  a_flex_tvar ((c ~ b) ++ Θ) α -> ~ a_suffix_binding b -> a_flex_tvar Θ α.
Proof.
  intros c b Θ α [Hb | [τ Hb]] Hnb;
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heq] | Hb'].
  - subst. exfalso. apply Hnb. constructor.
  - left. exact Hb'.
  - subst. exfalso. apply Hnb. constructor.
  - right. exists τ. exact Hb'.
Qed.

Lemma a_inc_var_image_flex : forall Θ κ Θ' α,
  κ ∷ Θ ⊑ Θ' ->
  α `notin` dom Θ ->
  a_wf_ptyp Θ' (ptyp_var_f α) ->
  a_flex_tvar Θ' α.
Proof.
  intros Θ κ Θ' α Hinc Hfr Hwfv.
  inversion Hwfv; subst.
  match goal with
  | Htv : a_binds_tvar _ _ |- _ => destruct Htv as [Hb1 | [Hb1 | [τ1 Hb1]]]
  end.
  - exfalso. apply Hfr. eapply binds_In.
    eapply a_inc_binds_tvar_rev; [ exact Hinc | exact Hb1 ].
  - left. exact Hb1.
  - right. exists τ1. exact Hb1.
Qed.

Lemma a_inc_id_flex_preserve : forall Θ0 κ Θ1 α,
  κ ∷ Θ0 ⊑ Θ1 ->
  is_id_msubst κ ->
  {{ ⊢ Θ0 }}a ->
  a_flex_tvar Θ0 α ->
  a_flex_tvar Θ1 α.
Proof.
  intros Θ0 κ Θ1 α Hinc; induction Hinc; intros Hid Hwf Hflex.
  -
    exfalso. destruct Hflex as [Hb | [τ' Hb]]; inversion Hb.
  -
    destruct (is_id_msubst_inv Hid) as [-> Hid'].
    inversion Hwf; subst.
    destruct (α == α0) as [-> | Hne].
    + eapply a_inc_var_image_flex; eassumption.
    + apply IHHinc; [ exact Hid' | assumption | ].
      exact (proj1 (a_flex_tvar_cons_other _ _ Hne) Hflex).
  -
    destruct (is_id_msubst_inv Hid) as [-> Hid'].
    inversion Hwf; subst.
    destruct (α == α0) as [-> | Hne].
    + eapply a_inc_var_image_flex; eassumption.
    + apply IHHinc; [ exact Hid' | assumption | ].
      exact (proj1 (a_flex_tvar_cons_other _ _ Hne) Hflex).
  -
    inversion Hwf; subst.
    do 2 apply a_flex_tvar_weaken_app.
    apply IHHinc; [ exact Hid | assumption | ].
    apply (a_flex_tvar_strip_nonflex_head Hflex). intros Hs; inversion Hs.
  -
    inversion Hwf; subst.
    do 2 apply a_flex_tvar_weaken_app.
    apply IHHinc; [ exact Hid | assumption | ].
    apply (a_flex_tvar_strip_nonflex_head Hflex). intros Hs; inversion Hs.
  -
    inversion Hwf; subst.
    do 2 apply a_flex_tvar_weaken_app.
    apply IHHinc; [ exact Hid | assumption | ].
    apply (a_flex_tvar_strip_nonflex_head Hflex). intros Hs; inversion Hs.
Qed.

Corollary a_inc_equiv_glue_id : forall Θ0 Θmid Θfin Θ κ κ1a κ1b ζ1 ζ2,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θmid }}a -> {{ ⊢ Θfin }}a -> {{ ⊢ Θ }}a ->
  is_id_msubst κ1a -> is_id_msubst κ1b ->
  κ1a ∷ Θ0 ⊑ Θmid ->
  κ1b ∷ Θmid ⊑ Θfin ->
  ζ1 ∷ Θmid ⊑ Θ ->
  ζ2 ∷ Θfin ⊑ Θ ->
  a_inc_equiv Θ0 κ (msubst_compose ζ1 κ1a) Θ ->
  a_inc_equiv Θmid ζ1 (msubst_compose ζ2 κ1b) Θ ->
  a_inc_equiv Θ0 κ (msubst_compose ζ2 κ1a) Θ.
Proof.
  intros Θ0 Θmid Θfin Θ κ κ1a κ1b ζ1 ζ2
         Hwf0 Hwfm Hwff HwfT Hida Hidb Ha Hb Hζ1 Hζ2 Hsub1 Hsub2.
  eapply a_inc_equiv_glue;
    [ exact Hwf0 | exact Hwfm | exact Hwff | exact HwfT
    | exact Hida | exact Hidb
    | | exact Ha | exact Hb | exact Hζ1 | exact Hζ2 | exact Hsub1 | exact Hsub2 ].
  intros α Hα.
  pose proof (a_inc_dom_flex Ha Hα) as Hfα.
  eapply a_inc_flex_dom;
    [ exact Hb | exact Hwfm
    | eapply a_inc_id_flex_preserve;
        [ exact Ha | exact Hida | exact Hwf0 | exact Hfα ] ].
Qed.

Lemma a_pat_complete_app : forall M Θ0 P0 e1 e2 κ Θ Q,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_app e1 e2) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_app e1 e2) ->
  pat_complete_ih e2 ->
  pat_complete_ih e1 ->
  {{ Θ ⊢ˢ[ M ] (exp_app e1 e2) ⦂ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  pat_complete_concl M Θ0 P0 (exp_app e1 e2) κ Θ Q.
Proof.
  intros M Θ0 P0 e1 e2 κ Θ Q Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
         Hlc IH2 IH1 Hd Href.
  inversion Hd; subst.
  match goal with
  | H : {{ Θ ⊢ˢ[ mode_tc ] e2 ⦂ pskl_to_bskl_syn ?PP }}ad |- _ =>
      rename H into Hd2; rename PP into Pn
  end.
  match goal with
  | H : {{ Θ ⨟ empty ⊢ᵣ pskl_to_bskl_inh Pn ⊳ ?QQ }}ad |- _ =>
      rename H into Hrefb; rename QQ into Qdom
  end.
  match goal with
  | H : {{ Θ ⊢ˢ[ mode_fn M ] e1 ⦂ bskl_arrow Qdom ?QQ }}ad |- _ =>
      rename H into Hd1
  end.
  simpl in Hrig.
  assert (Hrig2 : forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hrig1 : forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlc2 : lc_exp e2) by (inversion Hlc; assumption).
  assert (Hlc1 : lc_exp e1) by (inversion Hlc; assumption).

  assert (Hwfarr : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (bskl_arrow Qdom Q)) }}a)
    by (exact (ad_pat_target_wf Hd1 HwfΘ)).
  cbn [bskl_to_pskl] in Hwfarr.
  inversion Hwfarr; subst.
  match goal with
  | H : {{ Θ ⨟ empty ⊢ₚₛ bskl_to_pskl Qdom }}a |- _ => rename H into HwfQdom
  end.
  match goal with
  | H : {{ Θ ⨟ empty ⊢ₚₛ bskl_to_pskl Q }}a |- _ => rename H into HwfQcod
  end.

  destruct (IH2 mode_tc Θ0 pskl_ghost κ Θ (pskl_to_bskl_syn Pn)
              Hwf0 HwfΘ
              ltac:(apply a_wf_pskl__ghost)
              ltac:(apply a_sk_mode_compat__tc)
              Hinc Hrig2 Hlc2 Hd2
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    apply ad_refine_syn__ghost; clear; fsetdec))
    as [P1 [Θ1 [Hrun2 Hopt2]]].

  assert (Hexp2 : {{ Θ0 ⊢ᵉ e2 }}a).
  { apply a_wf_exp_of_tvarish; [ exact Hlc2 | ].
    intros α Hα. left. apply Hrig2. exact Hα. }
  destruct (a_pat_sound Hrun2 Hwf0
              ltac:(apply a_wf_pskl__ghost)
              ltac:(apply a_sk_mode_compat__tc)
              Hexp2)
    as [Hle2 [Hwf1 _]].
  destruct Hle2 as [[κa [Hida Hinca]] _].
  destruct (Hopt2 κa Hida Hinca) as [ζ1 [Hζ1 [Heqv1 Hprec1]]].
  rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec1.

  assert (Hh : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl ζ1 P1)) ⊳ Qdom }}ad).
  { eapply ad_precise_preserves_refine;
      [ exact Hprec1 | exact Hrefb | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfQdom ]. }

  pose proof (ad_refine_msubst_compose_id Hwf0 Hwf1 HwfΘ HwfP0 Hinc Hida
                Hinca Hζ1 Heqv1 HwfQcod Href) as Hi.

  assert (HwfP1 : {{ Θ1 ⨟ empty ⊢ₚₛ P1 }}a)
    by (eapply a_pat_output_wf;
        [ exact Hrun2 | exact Hwf0
        | apply a_wf_pskl__ghost | apply a_sk_mode_compat__tc | exact Hexp2 ]).
  assert (HwfP0mid : {{ Θ1 ⨟ empty ⊢ₚₛ P0 }}a).
  { pose proof (a_wf_pskl_msubst_inc Hinca Hwf0 HwfP0
                  ltac:(intros α Hα; clear - Hα; solve_notin_auto)
                  ltac:(intros β γ _ _ _; clear; fsetdec)) as Hw.
    rewrite (msubst_pskl_id P0 Hida) in Hw. exact Hw. }
  assert (Hrig1mid : forall α, α `in` ftvar_in_exp e1 ->
             binds α abind_tvar Θ1)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hinca | apply Hrig1; exact Hα ]).
  destruct (IH1 (mode_fn M) Θ1 (pskl_arrow P1 P0) ζ1 Θ (bskl_arrow Qdom Q)
              Hwf1 HwfΘ
              ltac:(apply a_wf_pskl__arrow; [ exact HwfP1 | exact HwfP0mid ])
              ltac:(apply a_sk_mode_compat__fn; exact Hmod)
              Hζ1 Hrig1mid Hlc1 Hd1
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    apply ad_refine_syn_arrow_intro; [ exact Hh | exact Hi ]))
    as [P2 [Θ2 [Hrun1 Hopt1]]].

  assert (Hexp1 : {{ Θ1 ⊢ᵉ e1 }}a).
  { apply a_wf_exp_of_tvarish; [ exact Hlc1 | ].
    intros α Hα. left. apply Hrig1mid. exact Hα. }
  destruct (a_pat_sound Hrun1 Hwf1
              ltac:(apply a_wf_pskl__arrow; [ exact HwfP1 | exact HwfP0mid ])
              ltac:(apply a_sk_mode_compat__fn; exact Hmod)
              Hexp1)
    as [Hle1 [Hwf2 [Qt [HeQt [Hpat1 _]]]]].
  pose proof (ad_pat_mod_comp_sk Hpat1) as Hmc.
  inversion Hmc; subst.
  destruct Hle1 as [[κb [Hidb Hincb]] _].

  match goal with
  | Hm : mod_comp_sk (bskl_arrow ?QA ?QB) (mode_fn M) |- _ =>
      rename QA into Qa; rename QB into Qb
  end.
  exists (bskl_to_pskl Qb), Θ2.
  split.
  { eapply a_pat__app; [ exact Hrun2 | exact Hrun1 ]. }

  intros κ1 Hid1 Hinc1.
  assert (Heqκa : κ1 = κa)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hinca | exact Hid1 | exact Hida ]).
  destruct (Hopt1 κb Hidb Hincb) as [ζ2 [Hζ2 [Heqv2 Hprec2]]].
  exists ζ2.
  split; [ exact Hζ2 | ].
  split.
  { assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζ2 κa) Θ).
    { eapply a_inc_equiv_glue_id with
        (Θmid := Θ1) (Θfin := Θ2) (κ1b := κb) (ζ1 := ζ1);
        [ exact Hwf0 | exact Hwf1 | exact Hwf2 | exact HwfΘ        | exact Hida | exact Hidb        | exact Hinca | exact Hincb | exact Hζ1 | exact Hζ2        | exact Heqv1 | exact Heqv2 ]. }
    rewrite Heqκa. exact Hglue. }
  {
    unfold ad_precise in Hprec2 |- *.
    cbn [msubst_pskl bskl_to_pskl pskl_to_bskl_inh] in Hprec2.
    destruct (ad_refine_syn_arrow_inv Hprec2) as [_ Hcod].
    exact Hcod. }
Qed.

Lemma a_pat_complete_gen : forall n e M Θ0 P0 κ Θ Q,
  size_exp e < n ->
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
  lc_exp e ->
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  pat_complete_concl M Θ0 P0 e κ Θ Q.
Proof.
  induction n as [ | n IHn ];
    intros e M Θ0 P0 κ Θ Q Hsz Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
           Hlc Hd Href;
    [ exfalso; clear - Hsz; lia | ].
  destruct e as [ | m | x | e0 | A e0 | e1 e2 | e0 A | e0 ]; simpl in Hsz.
  -  apply a_pat_complete_unit; assumption.
  -  inversion Hd.
  -  apply a_pat_complete_var; assumption.
  -
    destruct M as [ | | M' ].
    + apply a_pat_complete_abs; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
    + inversion Hmod; subst.
      apply a_pat_complete_abs_check; try assumption.
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
    + apply a_pat_complete_abs; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
  -
    destruct M as [ | | M' ].
    + apply a_pat_complete_abs_anno; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
    + inversion Hmod; subst.
      apply a_pat_complete_abs_anno_check; try assumption.
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
    + apply a_pat_complete_abs_anno; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption.
      rewrite size_exp_open_exp_wrt_exp_var. clear - Hsz; lia.
  -
    pose proof (size_exp_min e1) as Hm1.
    pose proof (size_exp_min e2) as Hm2.
    apply a_pat_complete_app; try assumption.
    + intros M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption. clear - Hsz Hm1; lia.
    + intros M2 Θ02 P02 κ2 Θ2 Q2; intros.
      apply IHn; try assumption. clear - Hsz Hm2; lia.
  -
    apply a_pat_complete_anno; try assumption.
    + intros α Hα. apply Hrig. simpl. clear - Hα; fsetdec.
    + inversion Hlc; assumption.
  -
    destruct M as [ | | M' ]; [ inversion Hd | | inversion Hd ].
    inversion Hmod; subst.
    apply a_pat_complete_freeze; [ | exact Hd | exact Href ].
    intros Q' Hd' Href'.
    apply IHn; try assumption;
      try solve [ clear - Hsz; lia
                | apply a_wf_pskl__ghost
                | apply a_sk_mode_compat__ti
                | inversion Hlc; assumption ].
Qed.

Theorem a_pat_complete : forall e M Θ0 P0 κ Θ Q,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
  lc_exp e ->
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  exists P1 Θ1,
    a_pat M Θ0 P0 e P1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl ζ P1) ⊑ (bskl_to_pskl Q) }}ad).
Proof.
  intros e M Θ0 P0 κ Θ Q Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hlc Had Href.
  eapply a_pat_complete_gen with (n := S (size_exp e)); try eassumption.
  clear; lia.
Qed.
