Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_mod_compat.
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
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import Coq.micromega.Lia.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.algo.typing.prop_soundness_pat.
Require Import src.fresco.algo.basic.prop_suffix_erase.
Require Import src.fresco.algo.typing.prop_soundness_typing.
Require Import src.fresco.algo_decl.prop_ctx_precision.
Require Import src.fresco.algo.typing.prop_completeness_pat.
Require Import src.fresco.algo.typing.prop_typing_rigidity.
Require Import src.fresco.algo.typing.prop_typing_shape.
Require Import src.fresco.algo.typing.prop_typing_scope.
Require Import src.fresco.algo.typing.prop_completeness_typing.
Require Import src.fresco.algo_decl.prop_conservativity.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.decl.prop_syntax_directed.

Set Implicit Arguments.

Lemma a_typing_sound_nil : forall m P0 e A Θ1,
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat m P0 ->
  {{ nil ⊢[ m ; P0 ] e ⦂ A ⊣ Θ1 }}a ->
  nil ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  exists Bt, btyp_to_ptyp Bt = A /\ mod_comp_ty Bt m /\
    ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ (btyp_to_bskl Bt) }}ad) /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ msubst_mono ζ /\
      ({{ nil ⊢ˢᵈ[ m ] e ⦂ (msubst_btyp ζ Bt) }}d) /\
      ({{ nil ⊢[ m ] e ⦂ (msubst_btyp ζ Bt) }}d).
Proof.
  intros m P0 e A Θ1 Hexp HwfP0 Hmod Hrun.
  destruct (a_typing_sound Hrun a_wf_aenv__nil HwfP0 Hmod Hexp)
    as [Hisub [Hwf1 [HwfA [Bt [HBt [Hd Href]]]]]].
  split; [ exact Hisub | ]. split; [ exact Hwf1 | ]. split; [ exact HwfA | ].
  exists Bt. split; [ exact HBt | ].
  split; [ exact (ad_sd_typing_mod_comp_ty Hd Hwf1) | ]. split; [ exact Href | ].

  assert (Hsuf : a_suffix Θ1)
    by (destruct Hisub as [[κ [_ Hinc]] _]; exact (a_inc_nil_suffix κ Θ1 Hinc)).
  assert (Hftv : ftvar_in_exp e [<=] empty)
    by (pose proof (a_wf_exp_ftv_dom Hexp) as Hx; simpl in Hx; exact Hx).
  destruct (ad_sd_typing_close_suffix Θ1 Hsuf Hwf1 m e Bt Hd Hftv)
    as [ζ [Hinc [Hmo [_ Hdnil]]]].
  exists ζ. split; [ exact Hinc | ]. split; [ exact Hmo | ].
  assert (Hsd : {{ nil ⊢ˢᵈ[ m ] e ⦂ (msubst_btyp ζ Bt) }}d)
    by exact (ad_sd_typing_to_d m nil e (msubst_btyp ζ Bt) Hdnil nil eq_refl).
  split; [ exact Hsd | apply d_sd_typing_sound; exact Hsd ].
Qed.

Corollary a_typing_sound_infer : forall e A Θ1,
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_ti ; pskl_ghost ] e ⦂ A ⊣ Θ1 }}a ->
  nil ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  ({{ Θ1 ⨟ empty ⊢ᵣ bskl_ghost ⊳ (btyp_to_bskl (ptyp_to_btyp_syn A)) }}ad) /\
  exists ζ, ζ ∷ Θ1 ⊑ nil /\
    ({{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ A)) }}d) /\
    ({{ nil ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ A)) }}d).
Proof.
  intros e A Θ1 Hexp Hrun.
  destruct (a_typing_sound_nil Hexp (a_wf_pskl__ghost _ _)
              a_ty_mode_compat__ti Hrun)
    as [Hisub [Hwf1 [HwfA [Bt [HBt [Hmc [Href [ζ [Hinc [Hmo [Hsd Hty]]]]]]]]]]].

  assert (HBteq : Bt = ptyp_to_btyp_syn A)
    by (rewrite <- HBt; apply btyp_syn_colouring_inv;
        apply mod_comp_ty_ti_inv; exact Hmc).
  subst Bt. rewrite msubst_btyp_ptyp_to_btyp_syn in Hsd, Hty.
  split; [ exact Hisub | ]. split; [ exact Hwf1 | ]. split; [ exact HwfA | ].
  split; [ exact Href | ]. exists ζ. split; [ exact Hinc | ].
  split; [ exact Hsd | exact Hty ].
Qed.

Corollary a_typing_sound_check : forall e A0 A Θ1,
  {{ nil ⊢ᵉ e }}a ->
  a_wf_ptyp nil A0 ->
  {{ nil ⊢[ mode_tc ; (ptyp_to_pskl A0) ] e ⦂ A ⊣ Θ1 }}a ->
  nil ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (ptyp_to_pskl A0))
     ⊳ (btyp_to_bskl (ptyp_to_btyp_inh A)) }}ad) /\
  exists ζ, ζ ∷ Θ1 ⊑ nil /\
    ({{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ (ptyp_to_btyp_inh (msubst_ptyp ζ A)) }}d) /\
    ({{ nil ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh (msubst_ptyp ζ A)) }}d).
Proof.
  intros e A0 A Θ1 Hexp HwfA0 Hrun.
  destruct (a_typing_sound_nil Hexp (a_wf_ptyp_to_wf_pskl empty HwfA0)
              (a_ty_mode_compat__tc A0) Hrun)
    as [Hisub [Hwf1 [HwfA [Bt [HBt [Hmc [Href [ζ [Hinc [Hmo [Hsd Hty]]]]]]]]]]].
  assert (HBteq : Bt = ptyp_to_btyp_inh A)
    by (rewrite <- HBt; apply btyp_inh_painting_inv;
        apply mod_comp_ty_tc_inv; exact Hmc).
  subst Bt. rewrite (msubst_btyp_ptyp_to_btyp_inh ζ A Hmo) in Hsd, Hty.
  split; [ exact Hisub | ]. split; [ exact Hwf1 | ]. split; [ exact HwfA | ].
  split; [ exact Href | ]. exists ζ. split; [ exact Hinc | ].
  split; [ exact Hsd | exact Hty ].
Qed.

Lemma a_typing_complete_nil : forall m P0 e (B : btyp),
  {{ nil ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat m P0 ->
  {{ nil ⊢ˢᵈ[ m ] e ⦂ B }}ad ->
  {{ nil ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ (btyp_to_bskl B) }}ad ->
  exists A1 Θ1,
    {{ nil ⊢[ m ; P0 ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros m P0 e B HwfP0 Hmod Hd Href.
  pose proof (ad_sd_typing_wf_exp Hd) as Hexp.
  pose proof (a_wf_exp_ftv_dom Hexp) as Hftv. simpl in Hftv.
  assert (Hrig : forall α, α `in` ftvar_in_exp e -> binds α abind_tvar nil)
    by (intros α Hα; exfalso; clear - Hα Hftv; fsetdec).
  assert (Hinc : nil ∷ nil ⊑ nil)
    by (apply a_inc__empty; apply a_suffix__nil).
  rewrite <- (msubst_pskl_nil P0) in Href.
  destruct (a_typing_complete a_wf_aenv__nil a_wf_aenv__nil HwfP0 Hmod
              Hinc Hrig Hd Href) as [A1 [Θ1 [Hrun Hopt]]].
  exists A1, Θ1. split; [ exact Hrun | ].
  destruct (a_typing_sound Hrun a_wf_aenv__nil HwfP0 Hmod Hexp)
    as [[[κ1 [Hid1 Hinc1]] _] _].
  destruct (Hopt κ1 Hid1 Hinc1) as [ζ [Hζ [_ Heq]]].
  exists ζ. split; [ exact Hζ | exact Heq ].
Qed.

Corollary a_typing_complete_infer : forall e (B : btyp),
  {{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ B }}ad ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_ghost ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hd.
  eapply a_typing_complete_nil;
    [ apply a_wf_pskl__ghost | apply a_ty_mode_compat__ti | exact Hd | ].

  assert (HB : B = ptyp_to_btyp_syn (btyp_to_ptyp B)).
  { apply btyp_syn_colouring_inv. apply mod_comp_ty_ti_inv.
    eapply ad_sd_typing_mod_comp_ty; [ exact Hd | apply a_wf_aenv__nil ]. }
  rewrite HB, btyp_to_bskl_ptyp_to_btyp_syn. cbn [pskl_to_bskl_inh].
  apply ad_refine_syn__ghost. clear. fsetdec.
Qed.

Corollary a_typing_complete_check : forall e (B : btyp),
  {{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ B }}ad ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hd.
  assert (HwfB : a_wf_ptyp nil (btyp_to_ptyp B))
    by (eapply ad_sd_typing_target_wf; [ exact Hd | apply a_wf_aenv__nil ]).
  eapply a_typing_complete_nil;
    [ apply a_wf_ptyp_to_wf_pskl; exact HwfB | apply a_ty_mode_compat__tc
    | exact Hd | ].

  assert (HB : B = ptyp_to_btyp_inh (btyp_to_ptyp B)).
  { apply btyp_inh_painting_inv. apply mod_comp_ty_tc_inv.
    eapply ad_sd_typing_mod_comp_ty; [ exact Hd | apply a_wf_aenv__nil ]. }
  replace (btyp_to_bskl B)
    with (btyp_to_bskl (ptyp_to_btyp_inh (btyp_to_ptyp B)))
    by (rewrite <- HB; reflexivity).
  rewrite btyp_to_bskl_ptyp_to_btyp_inh.
  apply ad_refine_syn_refl_inh. apply a_wf_ptyp_to_wf_pskl. exact HwfB.
Qed.

Corollary a_typing_complete_sd_infer : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_ghost ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hwfe Hd.
  apply a_typing_complete_infer.
  exact (d_sd_typing_to_ad mode_ti nil e B Hd d_wf_denv__nil Hwfe).
Qed.

Corollary a_typing_complete_sd_check : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hwfe Hd.
  apply a_typing_complete_check.
  exact (d_sd_typing_to_ad mode_tc nil e B Hd d_wf_denv__nil Hwfe).
Qed.

Corollary a_typing_complete_decl_infer : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_ti ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_ghost ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hwfe Hd.
  apply a_typing_complete_sd_infer;
    [ exact Hwfe | apply d_sd_typing_complete; [ exact Hd | apply d_wf_denv__nil ] ].
Qed.

Corollary a_typing_complete_decl_check : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_tc ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hwfe Hd.
  apply a_typing_complete_sd_check;
    [ exact Hwfe | apply d_sd_typing_complete; [ exact Hd | apply d_wf_denv__nil ] ].
Qed.
