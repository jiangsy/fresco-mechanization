Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
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
Require Import src.fresco.algo.subtyping.prop_completeness_extract.
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

Set Implicit Arguments.

Definition typ_complete_concl (M : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (κ : metasubst) (Θ : aenv) (B : btyp) : Prop :=
  exists A1 Θ1,
    a_typing M Θ0 P0 e A1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         {{ Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a).

Definition typ_complete_ih (e : exp) : Prop :=
  forall M' Θ0' P0' κ' Θ' B',
    {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
    {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
    a_ty_mode_compat M' P0' ->
    κ' ∷ Θ0' ⊑ Θ' ->
    (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0') ->
    lc_exp e ->
    {{ Θ' ⊢ˢᵈ[ M' ] e ⦂ B' }}ad ->
    {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
      ⊳ (btyp_to_bskl B') }}ad ->
    typ_complete_concl M' Θ0' P0' e κ' Θ' B'.

Lemma a_wf_pskl_msubst_inc_empty : forall Θ0 κ Θ P,
  κ ∷ Θ0 ⊑ Θ ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ (msubst_pskl κ P) }}a.
Proof.
  intros Θ0 κ Θ P Hinc Hwf0 HwfP.
  eapply a_wf_pskl_msubst_inc;
    [ exact Hinc | exact Hwf0 | exact HwfP
    | intros α Hα; exfalso; clear - Hα; fsetdec
    | intros; clear; fsetdec ].
Qed.

Lemma typ_counterpart_wf : forall M Ψ Θ A (B : btyp),
  {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_ty | M ] (ptyp_to_uskl_syn A) ⩽ (btyp_to_bskl B) }}ad ->
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B)) }}a.
Proof.
  intros M Ψ Θ A B Hj.
  rewrite bskl_to_pskl_btyp_to_bskl.
  apply a_wf_ptyp_to_wf_pskl.
  eapply a_wf_ptyp_of_scope_pskl;
    [ | rewrite <- bskl_to_pskl_btyp_to_bskl; reflexivity ].
  eapply ad_pat_sub_target_scope_ty; [ exact Hj | apply uskl_no_ghost_ptyp ].
Qed.

Lemma typ_opt_tail : forall Θ ζ A1 (B : btyp),
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ empty ⊢ₚᵣ
    (bskl_to_pskl (msubst_bskl ζ (pskl_to_bskl_syn (ptyp_to_pskl A1))))
    ⊑ (bskl_to_pskl (btyp_to_bskl B)) }}ad ->
  {{ Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros Θ ζ A1 B HwfΘ Hprec.
  rewrite msubst_bskl_syn_erase, msubst_pskl_embed_ptyp, bskl_to_pskl_btyp_to_bskl
    in Hprec.
  unfold ad_precise in Hprec.
  rewrite <- (btyp_to_bskl_ptyp_to_btyp_inh (btyp_to_ptyp B)) in Hprec.
  pose proof (ad_refine_syn_inh_tyequiv Hprec HwfΘ
                (msubst_ptyp ζ A1) (ptyp_to_btyp_inh (btyp_to_ptyp B))
                eq_refl eq_refl) as Heqc.
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh in Heqc.
  exact Heqc.
Qed.

Lemma a_typing_complete_unit : forall M Θ0 P0 κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⊢ˢᵈ[ M ] exp_unit ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 exp_unit κ Θ B.
Proof.
  intros M Θ0 P0 κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub _ _ _ _ _ _ |- _ =>
      destruct (ad_pat_sub_to_fuel H) as [njoin Hjoin]
  end.
  assert (HwfQ : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B)) }}a)
    by (eapply typ_counterpart_wf;
        exact (ad_pat_sub_of_fuel Hjoin)).
  destruct (@a_sub_complete njoin a_sub_mode_ty M Θ0 P0
              pskl_unit (ptyp_to_uskl_syn ptyp_unit) Θ κ (btyp_to_bskl B)
              Hwf0 HwfΘ HwfP0
              ltac:(apply a_wf_pskl__unit)
              ltac:(intros Hc; discriminate)
              ltac:(intros _; exact Hmod)
              Hinc
              (slack_unit Θ κ)
              Hjoin Href HwfQ
              ltac:(intros _; rewrite <- pskl_to_uskl_ptyp;
                    apply pskl_to_uskl_ptyp_ghost_free; apply lc_ptyp_unit))
    as [P1 [Θ1 [Hrun Hopt]]].

  assert (HgfP1 : pskl_ghost_free P1)
    by (eapply a_sub_ty_ghost_free_output; [ exact Hrun | exact I ]).
  destruct (pskl_ghost_free_to_ptyp P1 HgfP1) as [A1 ->].
  exists A1, Θ1. split; [ apply a_typing__unit; exact Hrun | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  apply typ_opt_tail; [ exact HwfΘ | exact Hprec ].
Qed.

Lemma a_typing_complete_var : forall M Θ0 P0 x κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⊢ˢᵈ[ M ] (exp_var_f x) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 (exp_var_f x) κ Θ B.
Proof.
  intros M Θ0 P0 x κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub _ _ _ _ _ _ |- _ =>
      destruct (ad_pat_sub_to_fuel H) as [njoin Hjoin]
  end.
  match goal with
  | H : binds x (abind_var_typ _) Θ |- _ => rename H into Hb
  end.

  destruct (@a_inc_binds_var_typ_rev Θ0 κ Θ x A Hinc Hwf0 Hb) as [A0 [Hb0 Heq]].
  assert (HwfA0 : a_wf_ptyp Θ0 A0)
    by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
  assert (HwfA : a_wf_ptyp Θ A)
    by (eapply a_wf_aenv_binds_var_typ_wf; eassumption).
  destruct (@a_sub_complete njoin a_sub_mode_ty M Θ0 P0
              (ptyp_to_pskl A0) (ptyp_to_uskl_syn A) Θ κ (btyp_to_bskl B)
              Hwf0 HwfΘ HwfP0
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA0)
              ltac:(intros Hc; discriminate)
              ltac:(intros _; exact Hmod)
              Hinc
              ltac:(rewrite pskl_to_uskl_ptyp, <- msubst_ptyp_to_uskl_syn;
                    apply a_tyequiv_to_uskl; [ exact Heq | exact HwfΘ ])
              Hjoin Href
              ltac:(eapply typ_counterpart_wf;
                    exact (ad_pat_sub_of_fuel Hjoin))
              ltac:(intros _; rewrite <- pskl_to_uskl_ptyp;
                    apply pskl_to_uskl_ptyp_ghost_free;
                    eapply a_wf_ptyp_lc; exact HwfA))
    as [P1 [Θ1 [Hrun Hopt]]].
  assert (HgfP1 : pskl_ghost_free P1)
    by (eapply a_sub_ty_ghost_free_output;
        [ exact Hrun | apply ptyp_to_pskl_ghost_free ]).
  destruct (pskl_ghost_free_to_ptyp P1 HgfP1) as [A1 ->].
  exists A1, Θ1.
  split; [ eapply a_typing__var; [ exact Hb0 | exact Hrun ] | ].
  intros κ1 Hid Hinc1.
  destruct (Hopt κ1 Hid Hinc1) as [ζ [Hζ [Heqv Hprec]]].
  exists ζ. split; [ exact Hζ | ]. split; [ exact Heqv | ].
  apply typ_opt_tail; [ exact HwfΘ | exact Hprec ].
Qed.

Lemma a_typing_complete_anno : forall M Θ0 P0 e A κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_anno e A) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_anno e A) ->
  typ_complete_ih e ->
  {{ Θ ⊢ˢᵈ[ M ] (exp_anno e A) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 (exp_anno e A) κ Θ B.
Proof.
  intros M Θ0 P0 e A κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hlc
         IH Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat_sub _ _ _ _ _ _ |- _ =>
      destruct (ad_pat_sub_to_fuel H) as [njoin Hjoin]
  end.
  match goal with
  | H : ad_sd_typing mode_tc Θ e _ |- _ => rename H into Hde
  end.
  simpl in Hrig.
  assert (Hrige : forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (HrigA : forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlce : lc_exp e) by (inversion Hlc; assumption).
  assert (HlcA : lc_ptyp A) by (inversion Hlc; assumption).
  assert (HwfA0 : a_wf_ptyp Θ0 A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA; exact Hα ]).
  assert (HwfAΘ : a_wf_ptyp Θ A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA
        | intros α Hα; left; eapply a_inc_binds_tvar;
            [ exact Hinc | apply HrigA; exact Hα ] ]).
  assert (HmsA : msubst_ptyp κ A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hinc | exact Hwf0 | exact HrigA ]).
  assert (HwfpA0 : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfA0).

  destruct (IH mode_tc Θ0 (ptyp_to_pskl A) κ Θ (ptyp_to_btyp_inh A)
              Hwf0 HwfΘ HwfpA0
              (a_ty_mode_compat__tc A)
              Hinc Hrige Hlce Hde
              ltac:(rewrite msubst_pskl_embed_ptyp, HmsA,
                      (btyp_to_bskl_ptyp_to_btyp_inh A);
                    apply ad_refine_syn_refl_inh;
                    apply a_wf_ptyp_to_wf_pskl; exact HwfAΘ))
    as [A1' [Θmid [HrunB HoptB]]].

  assert (HA1' : A1' = A).
  { eapply a_typing_tc_rigid_output; [ exact HrunB | ].
    intros α Hα.
    pose proof (a_wf_aenv_uniq Hwf0) as Hu.
    split; [ apply HrigA; exact Hα | ].
    split.
    - intros Hb.
      pose proof (binds_unique _ _ _ _ _ Hb (HrigA α Hα) Hu) as Hc.
      discriminate Hc.
    - intros τ Hb.
      pose proof (binds_unique _ _ _ _ _ Hb (HrigA α Hα) Hu) as Hc.
      discriminate Hc. }
  subst A1'.

  assert (Hexpe : {{ Θ0 ⊢ᵉ e }}a)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlce | intros α Hα; left; apply Hrige; exact Hα ]).
  destruct (a_typing_sound HrunB Hwf0 HwfpA0
              (a_ty_mode_compat__tc A) Hexpe)
    as [HleB [Hwfmid _]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (HoptB κb Hidb Hincb) as [ζb [Hζb [Heqvb _]]].
  assert (HrigMid : forall α, α `in` ftvar_in_ptyp A ->
             binds α abind_tvar Θmid)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hincb | apply HrigA; exact Hα ]).
  assert (HwfAmid : a_wf_ptyp Θmid A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigMid; exact Hα ]).
  assert (HmsAζb : msubst_ptyp ζb A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζb | exact Hwfmid | exact HrigMid ]).
  assert (HwfP0mid : {{ Θmid ⨟ empty ⊢ₚₛ P0 }}a).
  { pose proof (a_wf_pskl_msubst_inc_empty Hincb Hwf0 HwfP0) as Hw.
    rewrite (msubst_pskl_id P0 Hidb) in Hw. exact Hw. }

  assert (HwfQ : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B)) }}a)
    by (eapply typ_counterpart_wf;
        exact (ad_pat_sub_of_fuel Hjoin)).
  pose proof (ad_refine_msubst_compose_id Hwf0 Hwfmid HwfΘ HwfP0 Hinc Hidb
                Hincb Hζb Heqvb HwfQ Href) as HrefT.

  destruct (@a_sub_complete njoin a_sub_mode_ty M Θmid P0
              (ptyp_to_pskl A) (ptyp_to_uskl_syn A) Θ ζb (btyp_to_bskl B)
              Hwfmid HwfΘ HwfP0mid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAmid)
              ltac:(intros Hc; discriminate)
              ltac:(intros _; exact Hmod)
              Hζb
              ltac:(rewrite pskl_to_uskl_ptyp, <- msubst_ptyp_to_uskl_syn,
                      HmsAζb;
                    apply a_uskl_tyequiv_refl;
                    rewrite <- pskl_to_uskl_ptyp; apply pskl_to_uskl_lc;
                    apply ptyp_to_pskl_lc; exact HlcA)
              Hjoin HrefT HwfQ
              ltac:(intros _; rewrite <- pskl_to_uskl_ptyp;
                    apply pskl_to_uskl_ptyp_ghost_free; exact HlcA))
    as [P1 [Θ2 [HrunS HoptS]]].
  assert (HgfP1 : pskl_ghost_free P1)
    by (eapply a_sub_ty_ghost_free_output;
        [ exact HrunS | apply ptyp_to_pskl_ghost_free ]).
  destruct (pskl_ghost_free_to_ptyp P1 HgfP1) as [B1 ->].

  exists B1, Θ2.
  split; [ eapply a_typing__anno; [ exact HrunB | exact HrunS ] | ].

  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincb | exact Hid1 | exact Hidb ]).
  destruct (proj1 a_sub_output_wf_bundle _ _ _ _ _ _ _ HrunS
              Hwfmid HwfP0mid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAmid))
    as [HleS [Hwf2 _]].
  destruct HleS as [[κs [Hids Hincs]] _].
  destruct (HoptS κs Hids Hincs) as [ζs [Hζs [Heqvs Hprecs]]].
  exists ζs.
  split; [ exact Hζs | ].
  split.
  { assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζs κb) Θ).
    { eapply a_inc_equiv_glue_id with
        (Θmid := Θmid) (Θfin := Θ2) (κ1b := κs) (ζ1 := ζb);
        [ exact Hwf0 | exact Hwfmid | exact Hwf2 | exact HwfΘ        | exact Hidb | exact Hids        | exact Hincb | exact Hincs | exact Hζb | exact Hζs        | exact Heqvb | exact Heqvs ]. }
    rewrite Heqκ. exact Hglue. }
  apply typ_opt_tail; [ exact HwfΘ | exact Hprecs ].
Qed.

Lemma a_tyequiv_wf_iff : forall Θ A B,
  {{ Θ ⊢ A ≡ᵗ B }}a ->
  forall Θ',
  (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  {{ ⊢ Θ' }}a ->
  (a_wf_ptyp Θ' A -> a_wf_ptyp Θ' B) /\
  (a_wf_ptyp Θ' B -> a_wf_ptyp Θ' A).
Proof.
  intros Θ A B H; induction H; intros Θ' Hincl Hwf'.
  - split; intros HA; exact HA.
  - destruct (IHa_tyequiv Θ' Hincl Hwf') as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - destruct (IHa_tyequiv1 Θ' Hincl Hwf') as [H1l H1r].
    destruct (IHa_tyequiv2 Θ' Hincl Hwf') as [H2l H2r].
    split;
      [ intros HA; exact (H2l (H1l HA))
      | intros HC; exact (H1r (H2r HC)) ].
  - split.
    + intros _. eapply a_wf_aenv_binds_def_wf; [ exact Hwf' | ].
      apply Hincl. exact H.
    + intros _. apply a_wf_ptyp__var.
      right; right. exists τ. apply Hincl. exact H.
  - split; intros HA; inversion HA; subst;
      apply a_wf_ptyp__arrow;
      first [ eapply (proj1 (IHa_tyequiv1 Θ' Hincl Hwf')); eassumption
            | eapply (proj2 (IHa_tyequiv1 Θ' Hincl Hwf')); eassumption
            | eapply (proj1 (IHa_tyequiv2 Θ' Hincl Hwf')); eassumption
            | eapply (proj2 (IHa_tyequiv2 Θ' Hincl Hwf')); eassumption ].
  - split; intros HA; inversion HA; subst;
    match goal with
    | Hfam : forall α, α `notin` ?L1 ->
               a_wf_ptyp _ (open_ptyp_wrt_ptyp _ _) |- _ =>
        apply a_wf_ptyp__all with (L := L `union` L1 `union` dom Θ');
        intros α Hα;
        (assert (Hwfx : {{ ⊢ ((α ~ abind_tvar) ++ Θ') }}a)
          by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf' ]));
        (assert (Hinclx : forall x (b : abind),
                   binds x b Θ -> binds x b ((α ~ abind_tvar) ++ Θ'))
          by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb));
        first
          [ eapply (proj1 (H0 α ltac:(clear - Hα; solve_notin_auto) _ Hinclx Hwfx));
            apply Hfam; clear - Hα; fsetdec
          | eapply (proj2 (H0 α ltac:(clear - Hα; solve_notin_auto) _ Hinclx Hwfx));
            apply Hfam; clear - Hα; fsetdec ]
    end.
Qed.

Lemma ad_sd_typing_target_wf : forall M Θ e (B : btyp),
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  {{ ⊢ Θ }}a ->
  a_wf_ptyp Θ (btyp_to_ptyp B).
Proof.
  intros M Θ e B H; induction H; intros Hwf;
    try match goal with
        | Hj : ad_pat_sub _ _ _ _ _ _ |- _ =>
            eapply a_wf_ptyp_of_scope_pskl;
              [ | rewrite <- bskl_to_pskl_btyp_to_bskl; reflexivity ];
            eapply ad_pat_sub_target_scope_ty;
              [ exact Hj | apply uskl_no_ghost_ptyp ]
        end.
  -
    rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
    specialize (IHad_sd_typing Hwf).
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in IHad_sd_typing.
    eapply (proj1 (a_tyequiv_wf_iff H0 (fun x b h => h) Hwf)).
    exact IHad_sd_typing.
  -
    simpl.
    apply a_wf_ptyp__all with (L := L `union` dom Θ).
    intros α Hα.
    rewrite <- btyp_to_ptyp_open_var.
    apply H0; [ clear - Hα; fsetdec | ].
    apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ].
  -
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite btyp_to_ptyp_ptyp_to_btyp_inh. exact H.
    + apply (@a_wf_ptyp_strip_tm_head x (abind_var_typ A)); [ intros [] | ].
      apply H2; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H | exact Hwf ].
  -
    simpl.
    apply a_wf_ptyp__all with (L := L `union` dom Θ).
    intros α Hα.
    rewrite <- btyp_to_ptyp_open_var.
    apply H0; [ clear - Hα; fsetdec | ].
    apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ].
  -
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
      eapply (proj1 (a_tyequiv_wf_iff H0 (fun y b h => h) Hwf)).
      exact H.
    + apply (@a_wf_ptyp_strip_tm_head x (abind_var_typ A)); [ intros [] | ].
      apply H3; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H | exact Hwf ].
  -
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite btyp_to_ptyp_ptyp_to_btyp_inh. exact H0.
    + apply (@a_wf_ptyp_strip_tm_head x (abind_var_typ A)); [ intros [] | ].
      apply H3; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H0 | exact Hwf ].
  -
    simpl.
    destruct (atom_fresh (L `union` dom Θ)) as [x Hx].
    apply a_wf_ptyp__arrow.
    + rewrite H2.
      eapply (proj1 (a_tyequiv_wf_iff H1 (fun y b h => h) Hwf)).
      exact H0.
    + apply (@a_wf_ptyp_strip_tm_head x (abind_var_typ A)); [ intros [] | ].
      apply H5; [ clear - Hx; fsetdec | ].
      apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact H0 | exact Hwf ].
  -
    specialize (IHad_sd_typing1 Hwf).
    simpl in IHad_sd_typing1.
    inversion IHad_sd_typing1; subst.
    assumption.
Qed.

Lemma a_typing_complete_freeze : forall Θ0 P0 e κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_freeze e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_freeze e) ->
  typ_complete_ih e ->
  {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_freeze e) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl mode_tc Θ0 P0 (exp_freeze e) κ Θ B.
Proof.
  intros Θ0 P0 e κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Hlc
         IH Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_sd_typing mode_ti Θ e (ptyp_to_btyp_syn ?BB) |- _ =>
      rename H into Hde; rename BB into B0
  end.
  match goal with
  | H : {{ Θ ⊢ B0 ≡ᵗ ?AA }}a |- _ => rename H into Heq0; rename AA into A
  end.
  inversion Hmod; subst.
  match goal with
  | |- typ_complete_concl _ _ (ptyp_to_pskl ?AP) _ _ _ _ => rename AP into Ap
  end.
  simpl in Hrig.
  assert (Hlce : lc_exp e) by (inversion Hlc; assumption).

  assert (HwfB0 : a_wf_ptyp Θ B0).
  { pose proof (ad_sd_typing_target_wf Hde HwfΘ) as Hw.
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Hw. exact Hw. }
  assert (HwfA : a_wf_ptyp Θ A)
    by (eapply (proj1 (a_tyequiv_wf_iff Heq0 (fun x b h => h) HwfΘ));
        exact HwfB0).

  destruct (IH mode_ti Θ0 pskl_ghost κ Θ (ptyp_to_btyp_syn B0)
              Hwf0 HwfΘ (a_wf_pskl__ghost _ _) a_ty_mode_compat__ti Hinc
              Hrig Hlce Hde
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    rewrite btyp_to_bskl_ptyp_to_btyp_syn;
                    apply ad_refine_syn_ghost_empty))
    as [B' [Θmid [HrunB HoptB]]].
  assert (Hexpe : {{ Θ0 ⊢ᵉ e }}a)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlce | intros α Hα; left; apply Hrig; exact Hα ]).
  destruct (a_typing_sound HrunB Hwf0 (a_wf_pskl__ghost _ _)
              a_ty_mode_compat__ti Hexpe)
    as [HleB [Hwfmid [HwfB'mid _]]].
  destruct HleB as [[κb [Hidb Hincb]] _].
  destruct (HoptB κb Hidb Hincb) as [ζb [Hζb [Heqvb HeqB']]].
  rewrite btyp_to_ptyp_ptyp_to_btyp_syn in HeqB'.
  assert (HeqAll : {{ Θ ⊢ (msubst_ptyp ζb B') ≡ᵗ A }}a)
    by (eapply a_tyequiv__trans; [ exact HeqB' | exact Heq0 ]).
  assert (HwfApmid : {{ Θmid ⨟ empty ⊢ₚₛ (ptyp_to_pskl Ap) }}a).
  { pose proof (a_wf_pskl_msubst_inc_empty Hincb Hwf0 HwfP0) as Hw.
    rewrite (msubst_pskl_id _ Hidb) in Hw. exact Hw. }

  set (Qb := btyp_to_bskl (ptyp_to_btyp_inh A)) in *.
  assert (HwfQb : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Qb) }}a).
  { unfold Qb. rewrite bskl_to_pskl_btyp_to_bskl, btyp_to_ptyp_ptyp_to_btyp_inh.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA. }
  pose proof (ad_refine_msubst_compose_id Hwf0 Hwfmid HwfΘ HwfP0 Hinc Hidb
                Hincb Hζb Heqvb HwfQb Href) as HrefT.
  assert (Heqs : {{ Θ ⊢ (ptyp_to_pskl (msubst_ptyp ζb B')) ≡ˢ (ptyp_to_pskl A) }}a)
    by (apply a_tyequiv_pskl; exact HeqAll).
  assert (Hjoin : {{ empty ⨟ Θ ⊢ˢ
                    (pskl_to_uskl (msubst_pskl ζb (ptyp_to_pskl B'))) ∼ Qb }}ad).
  { rewrite msubst_pskl_embed_ptyp.
    eapply (proj2 (skl_tyequiv_consis_transport Heqs HwfΘ
                     (fun x b h => h))).
    rewrite pskl_to_uskl_ptyp.
    apply (ad_pat_consis_syn_bid HwfA (ptyp_to_btyp_inh A)
             (btyp_to_ptyp_ptyp_to_btyp_inh A)). }
  assert (Hrp : {{ Θ ⨟ empty ⊢ᵣₚ (msubst_pskl ζb (ptyp_to_pskl B')) ⊳ (bskl_to_pskl Qb) }}ad).
  { rewrite msubst_pskl_embed_ptyp.
    eapply (proj2 (skl_tyequiv_refine_pskl_transport Heqs HwfΘ
                     (fun x b h => h))).
    unfold Qb. rewrite bskl_to_pskl_btyp_to_bskl, btyp_to_ptyp_ptyp_to_btyp_inh.
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA. }

  destruct (a_consis_complete Hwfmid HwfApmid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfB'mid)
              Hζb HwfΘ Hjoin
              ltac:(exact HrefT)
              Hrp (@ad_pat_consis_msubst_target_wf _ _ _ _ _ Hjoin
                     ltac:(first [ exact I | apply ptyp_to_pskl_ghost_free ]) empty))
    as [Qc [Θ2 [HcRun HoptC]]].

  exists Ap, Θ2.
  split;
    [ eapply a_typing__freeze; [ exact HrunB | exists Qc; exact HcRun ] | ].

  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincb | exact Hid1 | exact Hidb ]).
  destruct (a_consis_isub_wf_nil HcRun Hwfmid HwfApmid
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfB'mid))
    as [HleC Hwf2].
  destruct HleC as [[κs [Hids Hincs]] _].
  destruct (HoptC κs Hids Hincs) as [ζs [Hζs [Heqvs _]]].
  exists ζs.
  split; [ exact Hζs | ].
  split.
  { assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζs κb) Θ).
    { eapply a_inc_equiv_glue_id with
        (Θmid := Θmid) (Θfin := Θ2) (κ1b := κs) (ζ1 := ζb);
        [ exact Hwf0 | exact Hwfmid | exact Hwf2 | exact HwfΘ        | exact Hidb | exact Hids        | exact Hincb | exact Hincs | exact Hζb | exact Hζs        | exact Heqvb | exact Heqvs ]. }
    rewrite Heqκ. exact Hglue. }

  assert (HwfApP : a_wf_ptyp Θmid Ap).
  { eapply a_wf_ptyp_of_scope_pskl; [ | reflexivity ].
    exact (a_scope_pskl_of_wf HwfApmid). }
  assert (HeqIO : {{ Θ2 ⊢ B' ≡ᵗ Ap }}a)
    by (eapply a_consis_chk_tyequiv;
        [ exists Qc; exact HcRun | exact Hwfmid | exact HwfApP
        | exact HwfB'mid ]).
  assert (HeqIOΘ : {{ Θ ⊢ (msubst_ptyp ζs B') ≡ᵗ (msubst_ptyp ζs Ap) }}a)
    by (eapply a_tyequiv_msubst; [ exact HeqIO | exact Hwf2 | exact Hζs ]).
  assert (HmsB' : msubst_ptyp (msubst_compose ζs κs) B' = msubst_ptyp ζs B')
    by (eapply msubst_compose_id_ptyp;
        [ exact Hwfmid | exact Hwf2 | exact Hids | exact Hincs | exact Hζs
        | exact HwfB'mid ]).
  assert (HeqW : {{ Θ ⊢ (msubst_ptyp ζb B') ≡ᵗ (msubst_ptyp ζs B') }}a).
  { rewrite <- HmsB'.
    apply (@a_inc_equiv_msubst_ptyp B' Θmid ζb (msubst_compose ζs κs) Θ
             HwfB'mid Heqvs Hwfmid
             ltac:(eapply a_inc_msubst_lc; exact Hζb)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζs
                   | exact (is_id_msubst_values_lc Hids) ])). }
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact HeqIOΘ | ].
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact HeqW | exact HeqAll ].
Qed.

Lemma msubst_compose_id_id : forall κb κc,
  is_id_msubst κb ->
  is_id_msubst κc ->
  msubst_compose κc κb = κb.
Proof.
  intros κb κc Hb Hc.
  induction κb as [ | [α τ] κb' IH ]; [ reflexivity | ].
  apply is_id_msubst_inv in Hb as [-> Hb'].
  unfold msubst_compose in *. simpl.
  rewrite (IH Hb'). f_equal. f_equal.
  clear IH Hb'.
  induction κc as [ | [β σ] κc' IHc ]; [ reflexivity | ].
  apply is_id_msubst_inv in Hc as [-> Hc'].
  simpl. destruct (α == β) as [-> | Hne]; [ reflexivity | exact (IHc Hc') ].
Qed.

Lemma a_typing_complete_app : forall M Θ0 P0 e1 e2 κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_app e1 e2) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_app e1 e2) ->

  typ_complete_ih e1 ->

  typ_complete_ih e2 ->
  {{ Θ ⊢ˢᵈ[ M ] (exp_app e1 e2) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 (exp_app e1 e2) κ Θ B.
Proof.
  intros M Θ0 P0 e1 e2 κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
         Hlc IH1 IH2 Hd Href.
  inversion Hd; subst.
  match goal with
  | H : ad_pat mode_tc Θ e2 (pskl_to_bskl_syn ?PP) |- _ =>
      rename H into Hd2s; rename PP into P
  end.
  match goal with
  | H : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl ?BB) }}ad |- _ =>
      rename H into HrefP; rename BB into B1
  end.
  match goal with
  | H : ad_sd_typing (mode_fn M) Θ e1 (btyp_arrow B1 ?BB) |- _ =>
      rename H into Hd1; rename BB into B2
  end.
  match goal with
  | H : {{ Θ ⊢ (btyp_to_ptyp B1) ≡ᵗ ?AA }}a |- _ =>
      rename H into HeqA2; rename AA into A2
  end.
  match goal with
  | H : ad_sd_typing mode_tc Θ e2 (ptyp_to_btyp_inh A2) |- _ =>
      rename H into Hd2
  end.
  simpl in Hrig.
  assert (Hrig1 : forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hrig2 : forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlc1 : lc_exp e1) by (inversion Hlc; assumption).
  assert (Hlc2 : lc_exp e2) by (inversion Hlc; assumption).
  assert (Hexp2 : {{ Θ0 ⊢ᵉ e2 }}a)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc2 | intros α Hα; left; apply Hrig2; exact Hα ]).

  assert (HwfArr : a_wf_ptyp Θ (btyp_to_ptyp (btyp_arrow B1 B2)))
    by (eapply ad_sd_typing_target_wf; [ exact Hd1 | exact HwfΘ ]).
  simpl in HwfArr.
  inversion HwfArr; subst.
  match goal with
  | H1 : a_wf_ptyp Θ (btyp_to_ptyp B1),
    H2 : a_wf_ptyp Θ (btyp_to_ptyp B2) |- _ =>
      rename H1 into HwfB1; rename H2 into HwfB2
  end.

  destruct (@a_pat_complete e2 mode_tc Θ0 pskl_ghost κ Θ (pskl_to_bskl_syn P)
              Hwf0 HwfΘ (a_wf_pskl__ghost _ _) a_sk_mode_compat__tc Hinc
              Hrig2 Hlc2 Hd2s
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh];
                    apply ad_refine_syn_ghost_empty))
    as [P' [Θ1' [Hrun1 Hopt1]]].
  destruct (a_pat_sound Hrun1 Hwf0 (a_wf_pskl__ghost _ _)
              a_sk_mode_compat__tc Hexp2)
    as [Hle1 [Hwf1 _]].
  destruct Hle1 as [[κ1b [Hid1b Hinc1b]] _].
  destruct (Hopt1 κ1b Hid1b Hinc1b) as [ζ1 [Hζ1 [Heqv1 Hprec1]]].
  rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec1.

  assert (HwfP' : {{ Θ1' ⨟ empty ⊢ₚₛ P' }}a)
    by (eapply a_pat_output_wf;
        [ exact Hrun1 | exact Hwf0
        | apply a_wf_pskl__ghost | apply a_sk_mode_compat__tc | exact Hexp2 ]).
  assert (HwfP0m : {{ Θ1' ⨟ empty ⊢ₚₛ P0 }}a).
  { pose proof (a_wf_pskl_msubst_inc_empty Hinc1b Hwf0 HwfP0) as Hw.
    rewrite (msubst_pskl_id P0 Hid1b) in Hw. exact Hw. }
  assert (Hrig1m : forall α, α `in` ftvar_in_exp e1 -> binds α abind_tvar Θ1')
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hinc1b | apply Hrig1; exact Hα ]).

  assert (HwfQ2 : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B2)) }}a).
  { rewrite bskl_to_pskl_btyp_to_bskl.
    apply a_wf_ptyp_to_wf_pskl. exact HwfB2. }
  pose proof (ad_refine_msubst_compose_id Hwf0 Hwf1 HwfΘ HwfP0 Hinc Hid1b
                Hinc1b Hζ1 Heqv1 HwfQ2 Href) as Hcod.
  assert (HwfB1e : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B1)) }}a).
  { rewrite bskl_to_pskl_btyp_to_bskl.
    apply a_wf_ptyp_to_wf_pskl. exact HwfB1. }
  assert (Hdom : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl ζ1 P'))
                   ⊳ (btyp_to_bskl B1) }}ad).
  { eapply ad_precise_preserves_refine;
      [ exact Hprec1 | exact HrefP | exact HwfΘ
      | intros α Hα; clear - Hα; fsetdec | exact HwfB1e ]. }
  destruct (IH1 (mode_fn M) Θ1' (pskl_arrow P' P0) ζ1 Θ (btyp_arrow B1 B2)
              Hwf1 HwfΘ
              ltac:(apply a_wf_pskl__arrow; [ exact HwfP' | exact HwfP0m ])
              ltac:(apply a_ty_mode_compat__fn; exact Hmod)
              Hζ1 Hrig1m Hlc1 Hd1
              ltac:(cbn [msubst_pskl pskl_to_bskl_inh btyp_to_bskl];
                    apply ad_refine_syn_arrow_intro; [ exact Hdom | exact Hcod ]))
    as [C [Θ2' [Hrun2 Hopt2]]].

  pose proof (a_typing_fn_arrow_shape Hrun2) as Hshape.
  inversion Hshape; subst.
  match goal with
  | Hs : fn_arrow_shape M ?BB |- _ => idtac
  end.
  match goal with
  | H : a_typing (mode_fn M) Θ1' _ e1 (ptyp_arrow ?AA ?BB) _ |- _ =>
      rename AA into Af; rename BB into Bf
  end.

  assert (Hexp1 : {{ Θ1' ⊢ᵉ e1 }}a)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc1 | intros α Hα; left; apply Hrig1m; exact Hα ]).
  destruct (a_typing_sound Hrun2 Hwf1
              ltac:(apply a_wf_pskl__arrow; [ exact HwfP' | exact HwfP0m ])
              ltac:(apply a_ty_mode_compat__fn; exact Hmod)
              Hexp1)
    as [Hle2 [Hwf2 [HwfC _]]].
  destruct Hle2 as [[κ2b [Hid2b Hinc2b]] _].
  destruct (Hopt2 κ2b Hid2b Hinc2b) as [ζ2 [Hζ2 [Heqv2 Heq2]]].
  simpl in Heq2.

  inversion HwfC; subst.
  match goal with
  | H1 : a_wf_ptyp Θ2' Af, H2 : a_wf_ptyp Θ2' Bf |- _ =>
      rename H1 into HwfAf; rename H2 into HwfBf
  end.
  destruct (a_tyequiv_arrow_inv HwfΘ
              ltac:(eapply msubst_ptyp_lc;
                    [ exact Hζ2 | eapply a_wf_ptyp_lc; exact HwfAf ])
              ltac:(eapply msubst_ptyp_lc;
                    [ exact Hζ2 | eapply a_wf_ptyp_lc; exact HwfBf ])
              ltac:(eapply a_wf_ptyp_lc; exact HwfB1)
              ltac:(eapply a_wf_ptyp_lc; exact HwfB2)
              Heq2)
    as [HeqDom HeqCod].

  assert (HwfA2 : a_wf_ptyp Θ A2)
    by (eapply (proj1 (a_tyequiv_wf_iff HeqA2 (fun x b h => h) HwfΘ));
        exact HwfB1).
  assert (Hrig2m : forall α, α `in` ftvar_in_exp e2 -> binds α abind_tvar Θ2')
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hinc2b
        | eapply a_inc_binds_tvar;
            [ exact Hinc1b | apply Hrig2; exact Hα ] ]).
  assert (Hexp2m : {{ Θ2' ⊢ᵉ e2 }}a)
    by (apply a_wf_exp_of_tvarish;
        [ exact Hlc2 | intros α Hα; left; apply Hrig2m; exact Hα ]).
  assert (HeqChain : {{ Θ ⊢ (msubst_ptyp ζ2 Af) ≡ᵗ A2 }}a)
    by (eapply a_tyequiv__trans; [ exact HeqDom | exact HeqA2 ]).
  assert (Heqs : {{ Θ ⊢ (ptyp_to_pskl (msubst_ptyp ζ2 Af)) ≡ˢ (ptyp_to_pskl A2) }}a)
    by (apply a_tyequiv_pskl; exact HeqChain).
  assert (Href3 : {{ Θ ⨟ empty ⊢ᵣ
                    (pskl_to_bskl_inh (msubst_pskl ζ2 (ptyp_to_pskl Af)))
                    ⊳ (btyp_to_bskl (ptyp_to_btyp_inh A2)) }}ad).
  { rewrite msubst_pskl_embed_ptyp, (btyp_to_bskl_ptyp_to_btyp_inh A2).
    eapply (proj2 (skl_tyequiv_refine_syn_transport Heqs HwfΘ
                     (fun x b h => h))).
    apply ad_refine_syn_refl_inh.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA2. }
  destruct (IH2 mode_tc Θ2' (ptyp_to_pskl Af) ζ2 Θ (ptyp_to_btyp_inh A2)
              Hwf2 HwfΘ
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAf)
              (a_ty_mode_compat__tc Af)
              Hζ2 Hrig2m Hlc2 Hd2 Href3)
    as [A3 [Θ3' [Hrun3 Hopt3]]].

  exists Bf, Θ3'.
  split.
  { eapply a_typing__app; [ exact Hrun1 | exact Hrun2 | exact Hrun3 ]. }

  intros κ1 Hκid Hκinc.
  assert (Heqκ : κ1 = κ1b)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hκinc | exact Hinc1b | exact Hκid | exact Hid1b ]).
  destruct (a_typing_sound Hrun3 Hwf2
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfAf)
              (a_ty_mode_compat__tc Af) Hexp2m)
    as [Hle3 [Hwf3 _]].
  destruct Hle3 as [[κ3b [Hid3b Hinc3b]] _].
  destruct (Hopt3 κ3b Hid3b Hinc3b) as [ζ3 [Hζ3 [Heqv3 _]]].
  exists ζ3.
  split; [ exact Hζ3 | ].
  split.
  {
    assert (Hglue23 : a_inc_equiv Θ1' ζ1 (msubst_compose ζ3 κ2b) Θ).
    { eapply a_inc_equiv_glue_id with
        (Θmid := Θ2') (Θfin := Θ3') (κ1b := κ3b) (ζ1 := ζ2);
        [ exact Hwf1 | exact Hwf2 | exact Hwf3 | exact HwfΘ        | exact Hid2b | exact Hid3b        | exact Hinc2b | exact Hinc3b | exact Hζ2 | exact Hζ3        | exact Heqv2 | exact Heqv3 ]. }
    assert (Hinc23 : msubst_compose κ3b κ2b ∷ Θ1' ⊑ Θ3')
      by (eapply a_inc_compose;
          [ exact Hinc2b | exact Hwf1 | exact Hwf2 | exact Hinc3b ]).
    rewrite (msubst_compose_id_id Hid2b Hid3b) in Hinc23.
    assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζ3 κ1b) Θ).
    { eapply a_inc_equiv_glue_id with
        (Θmid := Θ1') (Θfin := Θ3') (κ1b := κ2b) (ζ1 := ζ1);
        [ exact Hwf0 | exact Hwf1 | exact Hwf3 | exact HwfΘ        | exact Hid1b | exact Hid2b        | exact Hinc1b | exact Hinc23 | exact Hζ1 | exact Hζ3        | exact Heqv1 | exact Hglue23 ]. }
    rewrite Heqκ. exact Hglue. }

  assert (HmsBf : msubst_ptyp (msubst_compose ζ3 κ3b) Bf = msubst_ptyp ζ3 Bf)
    by (eapply msubst_compose_id_ptyp;
        [ exact Hwf2 | exact Hwf3 | exact Hid3b | exact Hinc3b | exact Hζ3
        | exact HwfBf ]).
  assert (HeqW : {{ Θ ⊢ (msubst_ptyp ζ2 Bf) ≡ᵗ (msubst_ptyp ζ3 Bf) }}a).
  { rewrite <- HmsBf.
    apply (@a_inc_equiv_msubst_ptyp Bf Θ2' ζ2 (msubst_compose ζ3 κ3b) Θ
             HwfBf Heqv3 Hwf2
             ltac:(eapply a_inc_msubst_lc; exact Hζ2)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζ3
                   | exact (is_id_msubst_values_lc Hid3b) ])). }
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact HeqW | exact HeqCod ].
Qed.

Lemma uniq_app_of : forall (Ξ1 Ξ2 : aenv),
  uniq Ξ1 -> uniq Ξ2 ->
  (forall α, α `in` dom Ξ1 -> α `notin` dom Ξ2) ->
  uniq (Ξ1 ++ Ξ2).
Proof.
  intros Ξ1 Ξ2 Hu1 Hu2 Hdj. apply uniq_app_4; [ exact Hu1 | exact Hu2 | ].
  unfold disjoint. rewrite (inter_empty_pointwise _ _ Hdj). reflexivity.
Qed.

Lemma a_guess_mono_exists : forall P Θ L,
  lc_pskl P ->
  exists Ξ A,
    a_guess_mono Θ P Ξ A /\
    a_decls Ξ /\ uniq Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L).
Proof.
  intros P Θ L Hlc; revert Θ L; induction Hlc; intros Θ L.
  -
    exists nil, ptyp_unit. repeat split;
      [ apply a_guess_mono__unit | apply a_decls__nil | apply uniq_nil
      | intros β Hβ; simpl in Hβ; clear - Hβ; fsetdec ].
  -
    exists nil, (ptyp_var_f α). repeat split;
      [ apply a_guess_mono__var | apply a_decls__nil | apply uniq_nil
      | intros β Hβ; simpl in Hβ; clear - Hβ; fsetdec ].
  -
    destruct (IHHlc1 Θ L) as [Ξ1 [A [Hg1 [Hd1 [Hu1 Hav1]]]]].
    destruct (IHHlc2 Θ (L `union` dom Ξ1)) as [Ξ2 [B [Hg2 [Hd2 [Hu2 Hav2]]]]].
    exists (Ξ1 ++ Ξ2), (ptyp_arrow A B).
    repeat split.
    + apply a_guess_mono__arrow; [ exact Hg1 | exact Hg2 ].
    + apply a_decls_app; assumption.
    + apply uniq_app_of; [ exact Hu1 | exact Hu2 | ].
      intros α Hα Hα2.
      pose proof (Hav2 α Hα2) as Hn. clear - Hn Hα; fsetdec.
    + intros α Hα. rewrite dom_app in Hα.
      destruct (AtomSetImpl.union_1 Hα) as [H1 | H2];
        [ apply Hav1; exact H1 | apply Hav2 in H2; clear - H2; fsetdec ].
  -
    destruct (atom_fresh (ftvar_in_aenv Θ `union` ftvar_in_pskl P1 `union` L))
      as [β Hβ].
    destruct (H0 β ((β ~ abind_tvar) ++ Θ) L) as [Ξ [A [Hg [Hd [Hu Hav]]]]].
    exists Ξ, (ptyp_all (close_ptyp_wrt_ptyp β A)).
    repeat split;
      [ apply a_guess_mono__forall;
          [ clear - Hβ; fsetdec | exact Hg ]
      | exact Hd | exact Hu | exact Hav ].
  -
    destruct (atom_fresh (ftvar_in_aenv Θ `union` L)) as [α Hα].
    exists ((α ~ abind_flex_mono) ++ nil), (ptyp_var_f α).
    repeat split;
      [ apply a_guess_mono__ghost; clear - Hα; fsetdec
      | apply a_decls__cons; apply a_decls__nil
      | apply uniq_cons; [ apply uniq_nil | simpl; clear; fsetdec ]
      | intros β Hβ; simpl in Hβ;
        assert (β = α) by (clear - Hβ; fsetdec); subst;
        clear - Hα; fsetdec ].
  -
    destruct (IHHlc Θ L) as [Ξ [A [Hg [Hd [Hu Hav]]]]].
    exists Ξ, A.
    repeat split;
      [ apply a_guess_mono__univ_ghost; exact Hg
      | exact Hd | exact Hu | exact Hav ].
Qed.

Lemma syn_painting_ityp_inv : forall (Bt : btyp) Pf,
  btyp_to_bskl Bt = pskl_to_bskl_syn Pf ->
  is_ityp Bt ->
  exists τ, mono_ptyp τ /\ Pf = ptyp_to_pskl τ /\ btyp_to_ptyp Bt = τ.
Proof.
  intros Bt; induction Bt; intros Pf Heq Hit; simpl in Heq;
    destruct Pf; simpl in Heq; try discriminate; inversion Hit; subst.
  - exists ptyp_unit.
    split; [ apply mono_ptyp__unit | split; reflexivity ].
  - inversion Heq; subst.
    eexists.
    split; [ apply mono_ptyp__var | split; reflexivity ].
  - inversion Heq; subst.
    match goal with
    | H1 : btyp_to_bskl Bt1 = pskl_to_bskl_syn ?p1,
      H2 : btyp_to_bskl Bt2 = pskl_to_bskl_syn ?p2 |- _ =>
        destruct (IHBt1 _ H1 ltac:(assumption)) as [τ1 [Hm1 [-> He1]]];
        destruct (IHBt2 _ H2 ltac:(assumption)) as [τ2 [Hm2 [-> He2]]]
    end.
    exists (ptyp_arrow τ1 τ2).
    split; [ apply mono_ptyp__arrow; assumption | ].
    split; [ reflexivity | simpl; rewrite He1, He2; reflexivity ].
Qed.

Lemma a_inc_extend_flex_block : forall (Ξg : aenv) (ζg κ : metasubst) Θ1 Θ,
  κ ∷ Θ1 ⊑ Θ ->
  List.map fst ζg = List.map fst Ξg ->
  a_decls Ξg ->
  (forall α τ, In (α, τ) ζg -> mono_ptyp τ /\ a_wf_ptyp Θ τ) ->
  (ζg ++ κ) ∷ (Ξg ++ Θ1) ⊑ Θ.
Proof.
  intros Ξg; induction Ξg as [ | [α b] Ξg' IH ];
    intros ζg κ Θ1 Θ Hinc Hmap Hd Hwf.
  - destruct ζg; simpl in Hmap; [ exact Hinc | discriminate ].
  - destruct ζg as [ | [α' τ] ζg' ]; simpl in Hmap; [ discriminate | ].
    inversion Hmap; subst α'.
    inversion Hd; subst.
    simpl_env.
    apply a_inc__flex.
    + apply IH; try assumption.
      intros β τ2 Hin. apply (Hwf β τ2). right. exact Hin.
    + assert (Hin : In (α, τ) ((α, τ) :: ζg')) by (left; reflexivity).
      exact (proj2 (Hwf _ _ Hin)).
    + assert (Hin : In (α, τ) ((α, τ) :: ζg')) by (left; reflexivity).
      exact (proj1 (Hwf _ _ Hin)).
Qed.

Lemma guess_complete_var_image : forall Θ Δ κ β (Bt : btyp) Θg Ξg A',
  ad_refine_syn Θ Δ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β)))
    (btyp_to_bskl Bt) ->
  {{ ⊢ Θ }}a ->
  a_guess_mono Θg (pskl_var_f β) Ξg A' ->
  Ξg = nil /\ {{ Θ ⊢ (msubst_ptyp κ A') ≡ᵗ (btyp_to_ptyp Bt) }}a.
Proof.
  intros Θ Δ κ β Bt Θg Ξg A' Href HwfΘ Hg.
  inversion Hg; subst.
  split; [ reflexivity | ].
  change (pskl_var_f β) with (ptyp_to_pskl (ptyp_var_f β)) in Href.
  rewrite msubst_pskl_embed_ptyp in Href.
  exact (ad_refine_syn_inh_tyequiv Href HwfΘ
           (msubst_ptyp κ (ptyp_var_f β)) Bt eq_refl eq_refl).
Qed.

Lemma guess_complete_var_case : forall {Θ Δ κ β} {Bt : btyp} {Θg Ξg A'},
  {{ ⊢ Θ }}a ->
  a_guess_mono Θg (pskl_var_f β) Ξg A' ->
  ad_refine_syn Θ Δ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β)))
    (btyp_to_bskl Bt) ->
  exists ζg,
    List.map fst ζg = List.map fst Ξg /\
    (forall α τ, In (α, τ) ζg -> mono_ptyp τ /\ a_wf_ptyp Θ τ /\
       (forall γ, γ `in` ftvar_in_ptyp τ -> γ `notin` Δ)) /\
    {{ Θ ⊢ (msubst_ptyp (ζg ++ κ) A') ≡ᵗ (btyp_to_ptyp Bt) }}a.
Proof.
  intros Θ Δ κ β Bt Θg Ξg A' HwfΘ Hg Href.
  destruct (@guess_complete_var_image Θ Δ κ β Bt Θg Ξg A' Href HwfΘ Hg)
    as [-> Heqc].
  exists nil. split; [ reflexivity | ].
  split; [ intros α2 τ2 Hin; inversion Hin | exact Heqc ].
Qed.

Lemma msubst_ptyp_ftv_notin_inc : forall A (κg : metasubst) Θ1 Θ α0,
  κg ∷ Θ1 ⊑ Θ ->
  α0 `notin` ftvar_in_ptyp A ->
  α0 `notin` dom Θ ->
  α0 `notin` ftvar_in_ptyp (msubst_ptyp κg A).
Proof.
  intros A κg Θ1 Θ α0 Hinc HA Hd Hc.
  destruct (msubst_ptyp_ftv _ _ Hc) as [β [Hβ Hl]].
  pose proof (a_inc_lookup_ftv β Hinc) as Hsc.
  destruct (α0 == β) as [-> | Hne];
    [ contradiction | apply Hsc in Hl; clear - Hl Hd Hne; fsetdec ].
Qed.

Lemma a_guess_mono_complete_gen : forall Θ Δ Qs Qt,
  ad_refine_syn Θ Δ Qs Qt ->
  forall P0 (Bt : btyp) Θg Ξg A' κ Θ1,
  {{ ⊢ Θ }}a ->
  a_wf_ptyp Θ (btyp_to_ptyp Bt) ->
  Qs = pskl_to_bskl_inh (msubst_pskl κ P0) ->
  Qt = btyp_to_bskl Bt ->
  is_ityp Bt ->
  a_guess_mono Θg P0 Ξg A' ->
  κ ∷ Θ1 ⊑ Θ ->
  uniq Ξg ->
  (forall α, α `in` dom Ξg ->
     α `notin` ftvar_in_pskl P0 `union` dom κ
       `union` dom Θ `union` ftvar_in_aenv Θ) ->
  exists ζg,
    List.map fst ζg = List.map fst Ξg /\
    (forall α τ, In (α, τ) ζg -> mono_ptyp τ /\ a_wf_ptyp Θ τ /\
       (forall γ, γ `in` ftvar_in_ptyp τ -> γ `notin` Δ)) /\
    {{ Θ ⊢ (msubst_ptyp (ζg ++ κ) A') ≡ᵗ (btyp_to_ptyp Bt) }}a.
Proof.
  intros Θ Δ Qs Qt Href.

  induction Href;
    intros P0 Bt Θg Ξg A' κ Θ1 HwfΘ HwfBt HeqS HeqT Hit Hg Hinc Huq Hav.
  -
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    +
      inversion Hg; subst.
      destruct Bt; simpl in HeqT; try discriminate.
      exists nil. split; [ reflexivity | ].
      split; [ intros α2 τ2 Hin; inversion Hin | ].
      simpl. apply a_tyequiv__refl. apply lc_ptyp_unit.
    +
      apply (guess_complete_var_case HwfΘ Hg).
      simpl. rewrite <- HeqS, <- HeqT. apply ad_refine_syn__unit.
  -
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    apply (guess_complete_var_case HwfΘ Hg).
    simpl. rewrite <- HeqS, <- HeqT. apply ad_refine_syn__var; assumption.
  -
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    +
      apply (guess_complete_var_case HwfΘ Hg).
      simpl. rewrite <- HeqS, <- HeqT. apply ad_refine_syn_arrow_intro; assumption.
    +
      inversion HeqS; subst Q1 Q2.
      destruct Bt as [ | n | γ | B1 B2 | B0 | B0 ]; simpl in HeqT;
        try discriminate HeqT.
      inversion HeqT; subst Q3 Q4.
      simpl in HwfBt; inversion HwfBt; subst.
      inversion Hit; subst.
      inversion Hg; subst.
      match goal with
      | H1 : a_guess_mono _ Pa ?X1 ?AA, H2 : a_guess_mono _ Pb ?X2 ?BB |- _ =>
          rename H1 into Hg1; rename H2 into Hg2;
          rename X1 into Ξ1; rename X2 into Ξ2;
          rename AA into A1; rename BB into A2
      end.
      assert (Hu1 : uniq Ξ1) by (clear - Huq; solve_uniq).
      assert (Hu2 : uniq Ξ2) by (clear - Huq; solve_uniq).
      destruct (IHHref1 Pa B1 Θg Ξ1 A1 κ Θ1 HwfΘ ltac:(assumption) eq_refl eq_refl
                  ltac:(assumption) Hg1 Hinc Hu1
                  ltac:(intros α Hα; simpl in Hav;
                        pose proof (Hav α ltac:(rewrite dom_app;
                                                clear - Hα; solve_notin_auto)) as Hn;
                        clear - Hn; fsetdec))
        as [ζg1 [Hmap1 [Hent1 Heqc1]]].
      destruct (IHHref2 Pb B2 Θg Ξ2 A2 κ Θ1 HwfΘ ltac:(assumption) eq_refl eq_refl
                  ltac:(assumption) Hg2 Hinc Hu2
                  ltac:(intros α Hα; simpl in Hav;
                        pose proof (Hav α ltac:(rewrite dom_app;
                                                clear - Hα; solve_notin_auto)) as Hn;
                        clear - Hn; fsetdec))
        as [ζg2 [Hmap2 [Hent2 Heqc2]]].
      pose proof (keys_eq_dom _ _ Hmap1) as Hd1.
      pose proof (keys_eq_dom _ _ Hmap2) as Hd2.
      pose proof (a_guess_mono_ftv Hg1) as Hftv1.
      pose proof (a_guess_mono_ftv Hg2) as Hftv2.
      assert (Hdisj : dom Ξ1 ∩ dom Ξ2 [=] empty)
        by (clear - Huq; solve_uniq).
      exists (ζg1 ++ ζg2).
      split; [ rewrite !List.map_app, Hmap1, Hmap2; reflexivity | ].
      split.
      { intros α τ Hin.
        apply in_app_or in Hin as [Hin | Hin];
          [ exact (Hent1 _ _ Hin) | exact (Hent2 _ _ Hin) ]. }
      simpl.
      apply a_tyequiv__arrow.
      * rewrite app_assoc.
        erewrite (msubst_ptyp_agree (ζg1 ++ ζg2 ++ κ) (ζg1 ++ κ));
          [ exact Heqc1 | ].
        intros α Hα.
        apply msubst_lookup_app_agree.
        apply msubst_lookup_app_notin.
        assert (HαP : α `in` ftvar_in_pskl Pa `union` dom Ξ1)
          by (clear - Hα Hftv1; fsetdec).
        intros Hc. rewrite Hd2 in Hc.
        simpl in Hav.
        pose proof (Hav α ltac:(rewrite dom_app; clear - Hc; solve_notin_auto)) as Hn.
        clear - Hn HαP Hc Hdisj. fsetdec.
      * rewrite app_assoc.
        erewrite (msubst_ptyp_agree (ζg1 ++ ζg2 ++ κ) (ζg2 ++ κ));
          [ exact Heqc2 | ].
        intros α Hα.
        apply msubst_lookup_app_notin.
        assert (HαP : α `in` ftvar_in_pskl Pb `union` dom Ξ2)
          by (clear - Hα Hftv2; fsetdec).
        intros Hc. rewrite Hd1 in Hc.
        simpl in Hav.
        pose proof (Hav α ltac:(rewrite dom_app; clear - Hc; solve_notin_auto)) as Hn.
        clear - Hn HαP Hc Hdisj. fsetdec.
  -
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    +
      exfalso.
      pose proof (a_inc_lookup_mono βv Hinc) as Hm.
      destruct Hm; simpl in HeqS; discriminate HeqS.
    +
      inversion HeqS; subst Q.
      destruct Bt as [ | n | γ | B1 B2 | B0 | B0 ]; simpl in HeqT;
        try discriminate HeqT.
      inversion HeqT; subst Q'.
      inversion Hit; subst.
      match goal with
      | Hfam : forall α, α `notin` ?LL ->
                 is_ityp (open_btyp_wrt_btyp _ _) |- _ =>
          rename Hfam into Hit1; rename LL into L2
      end.
      simpl in HwfBt; inversion HwfBt; subst.
      match goal with
      | Hfam : forall α, α `notin` ?LL ->
                 a_wf_ptyp _ (open_ptyp_wrt_ptyp _ _) |- _ =>
          rename Hfam into HwfB0; rename LL into L3
      end.
      inversion Hg; subst.
      match goal with
      | Hg1 : a_guess_mono ((?bb ~ abind_tvar) ++ _) _ _ ?AA,
        Hfr : ?bb `notin` _ |- _ =>
          rename Hg1 into Hg0; rename Hfr into Hfrβ;
          rename bb into β; rename AA into A0
      end.
      destruct (atom_fresh (L `union` L2 `union` L3 `union` dom Ξg
                  `union` ftvar_in_pskl Pw `union` ftvar_in_aenv Θg
                  `union` dom κ `union` dom Θ `union` ftvar_in_aenv Θ
                  `union` ftvar_in_ptyp (close_ptyp_wrt_ptyp β A0)
                  `union` ftvar_in_btyp B0 `union` singleton β)) as [α0 Hα0].
      assert (Hgα0 : a_guess_mono ((α0 ~ abind_tvar) ++ Θg)
                       (open_pskl_wrt_pskl Pw (pskl_var_f α0)) Ξg
                       (open_ptyp_wrt_ptyp (close_ptyp_wrt_ptyp β A0)
                          (ptyp_var_f α0))).
      { apply a_guess_mono_open_at;
          [ apply a_guess_mono__forall with (β := β);
              [ exact Hfrβ | exact Hg0 ]
          | clear - Hα0; solve_notin_auto ]. }
      destruct (H1 α0 ltac:(clear - Hα0; solve_notin_auto)
                  (open_pskl_wrt_pskl Pw (pskl_var_f α0))
                  (open_btyp_wrt_btyp B0 (btyp_var_f α0))
                  ((α0 ~ abind_tvar) ++ Θg) Ξg
                  (open_ptyp_wrt_ptyp (close_ptyp_wrt_ptyp β A0)
                     (ptyp_var_f α0))
                  κ ((α0 ~ abind_tvar) ++ Θ1)
                  ltac:(apply a_wf_aenv__tvar;
                        [ clear - Hα0; solve_notin_auto | exact HwfΘ ])
                  ltac:(rewrite btyp_to_ptyp_open_var;
                        apply HwfB0; clear - Hα0; solve_notin_auto)
                  ltac:(assert (Hfr0 : α0 `notin` dom κ)
                          by (clear - Hα0; solve_notin_auto);
                        rewrite (@msubst_pskl_open Θ1 κ Θ Pw α0 Hinc Hfr0);
                        rewrite pskl_to_bskl_inh_open; reflexivity)
                  ltac:(rewrite btyp_to_bskl_open; reflexivity)
                  (Hit1 α0 ltac:(clear - Hα0; solve_notin_auto))
                  Hgα0
                  ltac:(apply (@a_inc__tvar Θ1 κ Θ nil α0);
                        [ exact Hinc | apply a_suffix__nil ])
                  Huq
                  ltac:(intros α Hα;
                        pose proof (Hav α Hα) as Hn;
                        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                      Pw (pskl_var_f α0)) as Hup;
                        simpl in Hup, Hn |- *;
                        assert (Hne : α <> α0)
                          by (intros ->; apply Hα0; clear - Hα; fsetdec);
                        clear - Hn Hup Hne; fsetdec))
        as [ζg [Hmap [Hentx Heqc0]]].

      assert (Hent' : forall α τ, In (α, τ) ζg -> mono_ptyp τ /\
                 a_wf_ptyp Θ τ /\
                 (forall γ, γ `in` ftvar_in_ptyp τ -> γ `notin` Δ)).
      { intros α τ Hin.
        destruct (Hentx α τ Hin) as [Hm [Hw Hav']].
        split; [ exact Hm | split ].
        - eapply a_wf_ptyp_strip_prefix with (Ξ := α0 ~ abind_tvar);
            [ exact Hw | ].
          intros γ Hγ Hc. apply (Hav' γ Hc). clear - Hγ; simpl in Hγ; fsetdec.
        - intros γ Hγ Hc. apply (Hav' γ Hγ). clear - Hc; fsetdec. }
      assert (Hent : forall α τ, In (α, τ) ζg -> mono_ptyp τ /\ a_wf_ptyp Θ τ)
        by (intros α τ Hin; destruct (Hent' α τ Hin) as [? [? _]]; split; assumption).
      pose proof (@a_tyequiv_strengthen_tvar_cons _ _ _ Heqc0 α0 Θ eq_refl)
        as Heqc1.
      clear Heqc0; rename Heqc1 into Heqc0.
      exists ζg.
      split; [ exact Hmap | ].
      split; [ exact Hent' | ].
      assert (Hincg : (ζg ++ κ) ∷ (Ξg ++ Θ1) ⊑ Θ)
        by (apply a_inc_extend_flex_block;
            [ exact Hinc | exact Hmap
            | eapply a_guess_mono_decls; exact Hg0 | exact Hent ]).
      pose proof (keys_eq_dom _ _ Hmap) as Hdζ.
      assert (Hfrg : α0 `notin` dom (ζg ++ κ))
        by (rewrite dom_app; rewrite Hdζ; clear - Hα0; solve_notin_auto).
      rewrite (@msubst_ptyp_open (Ξg ++ Θ1) (ζg ++ κ) Θ
                 (close_ptyp_wrt_ptyp β A0) α0 Hincg Hfrg)
        in Heqc0.
      rewrite btyp_to_ptyp_open_var in Heqc0.
      simpl.
      set (X := msubst_ptyp (ζg ++ κ) (close_ptyp_wrt_ptyp β A0)) in *.
      apply a_tyequiv__all with
        (L := ftvar_in_ptyp X `union` ftvar_in_ptyp (btyp_to_ptyp B0)
                `union` singleton α0 `union` dom Θ `union` ftvar_in_aenv Θ).
      intros α Hα.
      pose proof (a_tyequiv_swap α0 α _ _ _ Heqc0) as Hsw.
      assert (Hfe1 : α0 `notin` (dom Θ `union` ftvar_in_aenv Θ))
        by (clear - Hα0; solve_notin_auto).
      assert (Hfe2 : α `notin` (dom Θ `union` ftvar_in_aenv Θ))
        by (clear - Hα; fsetdec).
      rewrite (@swap_aenv_fresh_eq α0 α Θ Hfe1 Hfe2) in Hsw.
      rewrite !swap_ptyp_open in Hsw.
      cbn [swap_ptyp] in Hsw.
      rewrite swap_atom_l in Hsw.
      rewrite (swap_ptyp_fresh_id α0 α X) in Hsw;
        [ | | clear - Hα; fsetdec ].
      2:{
        unfold X.
        eapply msubst_ptyp_ftv_notin_inc;
          [ exact Hincg | clear - Hα0; solve_notin_auto | clear - Hα0; solve_notin_auto ]. }
      rewrite (swap_ptyp_fresh_id α0 α (btyp_to_ptyp B0)) in Hsw;
        [ | | clear - Hα; fsetdec ].
      2:{ rewrite ftvar_btyp_to_ptyp. clear - Hα0; solve_notin_auto. }
      exact Hsw.
  -
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    +
      exfalso.
      pose proof (a_inc_lookup_mono βv Hinc) as Hm.
      destruct Hm; simpl in HeqS; discriminate HeqS.
    +
      inversion Hg; subst.
      destruct (@syn_painting_ityp_inv Bt P (eq_sym HeqT) Hit)
        as [τ [Hmτ [-> Hbtτ]]].
      assert (Hwfτ : a_wf_ptyp Θ τ) by (rewrite <- Hbtτ; exact HwfBt).
      assert (Havτ : forall γ, γ `in` ftvar_in_ptyp τ -> γ `notin` Δ).
      { intros γ Hγ Hc.
        match goal with
        | Hd : Δ ∩ ftvar_in_pskl (ptyp_to_pskl τ) [=] empty |- _ =>
            pose proof (ftvar_ptyp_to_pskl τ) as Hft;
            clear - Hd Hft Hγ Hc; fsetdec
        end. }
      eexists ((_, τ) :: nil).
      split; [ reflexivity | ].
      split.
      { intros α2 τ2 Hin.
        destruct Hin as [Heq2 | []].
        inversion Heq2; subst. split; [ | split ]; assumption. }
      simpl.
      destruct (α == α) as [_ | Hc]; [ | exfalso; apply Hc; reflexivity ].
      rewrite Hbtτ.
      apply a_tyequiv__refl. eapply a_wf_ptyp_lc; exact Hwfτ.
  -
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    +
      exfalso.
      pose proof (a_inc_lookup_mono βv Hinc) as Hm.
      destruct Hm; simpl in HeqS; discriminate HeqS.
    +
      inversion HeqS; subst Q.
      inversion Hg; subst.
      match goal with
      | Hg1 : a_guess_mono _ Pt _ _ |- _ => rename Hg1 into Hg0
      end.
      destruct (IHHref Pt Bt Θg Ξg A' κ Θ1 HwfΘ HwfBt eq_refl eq_refl Hit Hg0
                  Hinc Huq
                  ltac:(intros α Hα; exact (Hav α Hα)))
        as [ζg [Hmap [Hent Heqc]]].
      exists ζg. split; [ exact Hmap | split; [ exact Hent | exact Heqc ] ].
  -
    destruct Bt; simpl in HeqT; try discriminate HeqT.
    inversion Hit.
  -
    destruct Bt; simpl in HeqT; discriminate HeqT.
  -
    destruct P0 as [ | nb | βv | Pa Pb | Pw | | Pt ]; simpl in HeqS;
      try discriminate HeqS.
    apply (guess_complete_var_case HwfΘ Hg).
    simpl. rewrite <- HeqS, <- HeqT. eapply ad_refine_syn__flex_l; eassumption.
  -
    destruct Bt as [ | n | γ | B1 B2 | B0 | B0 ]; simpl in HeqT;
      try discriminate HeqT.
    inversion HeqT; subst γ.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    destruct (IHHref P0 (ptyp_to_btyp_syn τ) Θg Ξg A' κ Θ1 HwfΘ
                ltac:(rewrite btyp_to_ptyp_ptyp_to_btyp_syn;
                      eapply a_wf_aenv_binds_def_wf; eassumption)
                HeqS
                ltac:(rewrite btyp_to_bskl_ptyp_to_btyp_syn;
                      unfold ptyp_to_bskl_syn; reflexivity)
                (mono_ptyp_to_btyp_syn_is_ityp Hmτ)
                Hg Hinc Huq Hav)
      as [ζg [Hmap [Hent Heqc]]].
    exists ζg. split; [ exact Hmap | split; [ exact Hent | ] ].
    rewrite btyp_to_ptyp_ptyp_to_btyp_syn in Heqc.
    simpl.
    eapply a_tyequiv__trans;
      [ exact Heqc
      | apply a_tyequiv__sym; apply a_tyequiv__flex_def; assumption ].
Qed.

Lemma a_guess_mono_complete : forall Θ Δ Qs Qt,
  ad_refine_syn Θ Δ Qs Qt ->
  forall P0 (Bt : btyp) Θg Ξg A' κ Θ1,
  {{ ⊢ Θ }}a ->
  a_wf_ptyp Θ (btyp_to_ptyp Bt) ->
  Qs = pskl_to_bskl_inh (msubst_pskl κ P0) ->
  Qt = btyp_to_bskl Bt ->
  is_ityp Bt ->
  a_guess_mono Θg P0 Ξg A' ->
  κ ∷ Θ1 ⊑ Θ ->
  uniq Ξg ->
  (forall α, α `in` dom Ξg ->
     α `notin` ftvar_in_pskl P0 `union` dom κ
       `union` dom Θ `union` ftvar_in_aenv Θ) ->
  exists ζg,
    List.map fst ζg = List.map fst Ξg /\
    (forall α τ, In (α, τ) ζg -> mono_ptyp τ /\ a_wf_ptyp Θ τ) /\
    {{ Θ ⊢ (msubst_ptyp (ζg ++ κ) A') ≡ᵗ (btyp_to_ptyp Bt) }}a.
Proof.
  intros * Href P0 Bt Θg Ξg A' κ Θ1 HwfΘ HwfBt HeqS HeqT Hit Hg Hinc Huq Hav.
  destruct (a_guess_mono_complete_gen Href HwfΘ HwfBt HeqS HeqT Hit Hg Hinc
              Huq Hav) as [ζg [Hmap [Hent Heqc]]].
  exists ζg. split; [ exact Hmap | split; [ | exact Heqc ] ].
  intros α τ Hin. destruct (Hent α τ Hin) as [? [? _]]. split; assumption.
Qed.

Lemma a_inc_strip_decls_head : forall (Ξg : aenv) (κ : metasubst) Θ0 Θ,
  a_decls Ξg ->
  κ ∷ (Ξg ++ Θ0) ⊑ Θ ->
  exists κp κ0,
    κ = κp ++ κ0 /\ length κp = length Ξg /\ κ0 ∷ Θ0 ⊑ Θ.
Proof.
  intros Ξg; induction Ξg as [ | [α b] Ξg' IH ]; intros κ Θ0 Θ Hd Hinc.
  - exists nil, κ.
    split; [ reflexivity | split; [ reflexivity | exact Hinc ] ].
  - inversion Hd; subst.
    simpl_env in Hinc.
    pose proof (@a_inc_strip_flex_mid nil α (Ξg' ++ Θ0) κ Θ
                  a_decls__nil Hinc) as Hstrip.
    destruct Hstrip
      as [κ1 [τ [κ2 [Heqκ [Hlen1 [_ [_ [Hwfτ [Hmτ Hinc2]]]]]]]]].
    destruct κ1 as [ | p κ1' ]; [ | simpl in Hlen1; discriminate Hlen1 ].
    simpl in Heqκ. subst κ.
    match goal with
    | Hd' : a_decls Ξg' |- _ =>
        destruct (IH _ _ _ Hd' Hinc2) as [κp [κ0 [-> [Hlen Hinc0]]]]
    end.
    exists ((α, τ) :: κp), κ0.
    split; [ reflexivity | ].
    split; [ simpl; rewrite Hlen; reflexivity | exact Hinc0 ].
Qed.

Lemma a_inc_equiv_strip_decls_head : forall (Ξg : aenv) Θ0 κ1 κ2 Θ,
  a_decls Ξg ->
  a_inc_equiv (Ξg ++ Θ0) κ1 κ2 Θ ->
  exists κ1p κ1t κ2p κ2t,
    κ1 = κ1p ++ κ1t /\ κ2 = κ2p ++ κ2t /\
    length κ1p = length Ξg /\ length κ2p = length Ξg /\
    a_inc_equiv Θ0 κ1t κ2t Θ.
Proof.
  intros Ξg; induction Ξg as [ | [α b] Ξg' IH ]; intros Θ0 κ1 κ2 Θ Hd Heqv.
  - exists nil, κ1, nil, κ2.
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ reflexivity | ]. split; [ reflexivity | exact Heqv ].
  - inversion Hd; subst.
    simpl_env in Heqv.
    inversion Heqv; subst.
    match goal with
    | Hd' : a_decls Ξg' |- _ =>
        match goal with
        | Hi : a_inc_equiv _ _ _ _ |- _ =>
            destruct (IH _ _ _ _ Hd' Hi)
              as [κ1p [κ1t [κ2p [κ2t [-> [-> [Hl1 [Hl2 Heqv0]]]]]]]]
        end
    end.
    eexists ((_, _) :: κ1p), κ1t, ((_, _) :: κ2p), κ2t.
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ simpl; rewrite Hl1; reflexivity | ].
    split; [ simpl; rewrite Hl2; reflexivity | exact Heqv0 ].
Qed.

Lemma a_split_identity_of_refine_arrow : forall M Θ0 P0 κ Θ (B1 B2 : btyp),
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  M <> mode_tc ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_arrow B1 B2)) }}ad ->
  exists P Q,
    {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ0 }}a /\
    a_ty_mode_compat (decr_mode M) Q /\
    ({{ Θ0 ⨟ empty ⊢ₚₛ P }}a) /\ ({{ Θ0 ⨟ empty ⊢ₚₛ Q }}a) /\
    ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P))
       ⊳ (btyp_to_bskl B1) }}ad) /\
    ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ Q))
       ⊳ (btyp_to_bskl B2) }}ad).
Proof.
  intros M Θ0 P0 κ Θ B1 B2 HwfP0 Hmod HMne Href.
  inversion Hmod; subst.
  - exists pskl_ghost, pskl_ghost.
    cbn [msubst_pskl pskl_to_bskl_inh] in Href |- *.
    inversion Href; subst.
    match goal with
    | Hp : pskl_to_bskl_syn ?PF = _ |- _ =>
        destruct PF; simpl in Hp; try discriminate;
        inversion Hp; subst
    end.
    cbn [decr_mode].
    repeat split; try apply a_split__ghost; try apply a_wf_pskl__ghost;
      [ apply a_ty_mode_compat__ti | | ].
    + first [ apply ad_refine_syn_ghost_empty
            | match goal with
              | Hpa : pskl_to_bskl_syn _ = btyp_to_bskl _ |- _ =>
                  rewrite <- Hpa; apply ad_refine_syn_ghost_empty
              end ].
    + first [ apply ad_refine_syn_ghost_empty
            | match goal with
              | Hpb : pskl_to_bskl_syn _ = btyp_to_bskl B2 |- _ =>
                  rewrite <- Hpb; apply ad_refine_syn_ghost_empty
              end ].
  - exfalso; apply HMne; reflexivity.
  - match goal with
    | |- exists _ _, (a_split _ (pskl_arrow ?PP ?QQ) _ _ _) /\ _ =>
        exists PP, QQ
    end.
    cbn [msubst_pskl pskl_to_bskl_inh] in Href.
    inversion Href; subst.
    inversion HwfP0; subst.
    cbn [decr_mode].
    repeat split; try apply a_split__arrow; try assumption.
Qed.

Lemma a_typing_run_under_tm_binder : forall {x A Θ0 M P0 e B Θ1},
  {{ ((x ~ abind_var_typ A) ++ Θ0) ⊢[ M ; P0 ] e ⦂ B ⊣ Θ1 }}a ->
  {{ ⊢ ((x ~ abind_var_typ A) ++ Θ0) }}a ->
  {{ ((x ~ abind_var_typ A) ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  {{ ((x ~ abind_var_typ A) ++ Θ0) ⊢ᵉ e }}a ->
  exists κb (Ξ Θ2 : aenv),
    Θ1 = Ξ ++ (x ~ abind_var_typ A) ++ Θ2 /\
    is_id_msubst κb /\ (κb ∷ Θ0 ⊑ Θ2) /\ a_suffix Ξ /\
    ({{ ⊢ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) }}a) /\
    a_wf_ptyp (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) B /\
    x `notin` (dom Ξ `union` ftvar_in_aenv Ξ) /\
    x `notin` (dom Θ2 `union` ftvar_in_aenv Θ2).
Proof.
  intros x A Θ0 M P0 e B Θ1 Hrun Hwf0x HwfP0 Hmod Hexp.
  destruct (a_typing_sound Hrun Hwf0x HwfP0 Hmod Hexp) as [Hle [Hwf1 [HwfB _]]].
  destruct Hle as [[κb [Hid Hinc]] _].
  destruct (a_inc_var_inv Hinc) as [Ξ [A' [Θ2 [-> [_ [Hsuf Hinc']]]]]].
  assert (Heq : abind_var_typ A = abind_var_typ A').
  { eapply binds_mid_eq; [ | apply a_wf_aenv_uniq; exact Hwf1 ].
    eapply a_typing_tm_le; [ exact Hrun | exact I | unfold binds; simpl; auto ]. }
  inversion Heq; subst A'.
  exists κb, Ξ, Θ2.
  refine (conj eq_refl (conj Hid (conj Hinc' (conj Hsuf
            (conj Hwf1 (conj HwfB (conj _ _))))))).
  - eapply a_wf_aenv_notin_ftv_tm_prefix; [ exact Hsuf | exact Hwf1 | exact I ].
  - eapply a_wf_aenv_notin_ftv_tm_below. exact Hwf1.
Qed.

Lemma a_typing_complete_abs : forall M Θ0 P0 e κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  M <> mode_tc ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs e) ->
  (forall x, typ_complete_ih (open_exp_wrt_exp e (exp_var_f x))) ->
  {{ Θ ⊢ˢᵈ[ M ] (exp_abs e) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 (exp_abs e) κ Θ B.
Proof.
  intros M Θ0 P0 e κ Θ B Hwf0 HwfΘ HwfP0 Hmod HMne Hinc Hrig
         Hlc IH Hd Href.
  inversion Hd; subst; [ exfalso; auto | exfalso; auto | ].
  match goal with
  | H : forall x, x `notin` ?L0 -> ad_sd_typing _ _ _ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | H : a_wf_ptyp Θ ?AA |- _ => rename H into HwfA; rename AA into A
  end.
  match goal with
  | H : mod_comp_ty _ _ |- _ => rename H into Hmc
  end.
  match goal with
  | |- typ_complete_concl _ _ _ _ _ _ (btyp_arrow _ ?BB) => rename BB into Bc
  end.
  simpl in Hrig.
  assert (Hlce : forall x, lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (intros x; inversion Hlc; auto).

  destruct (@a_split_identity_of_refine_arrow _ _ _ _ _ _ _ HwfP0 Hmod HMne Href)
    as [P [Q [Hsplit [HmodQ [HwfP [HwfQ [HrefD HrefC]]]]]]].

  destruct (@a_guess_mono_exists P Θ0
              (dom Θ0 `union` ftvar_in_aenv Θ0
                 `union` dom Θ `union` ftvar_in_aenv Θ
                 `union` dom κ `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                 `union` fvar_in_exp e `union` ftvar_in_exp e)
              ltac:(eapply a_wf_pskl_lc; exact HwfP))
    as [Ξg [A' [Hguess [Hdecls [Huqb Havb]]]]].

  destruct (@a_guess_mono_complete Θ empty _ _ HrefD
              P (ptyp_to_btyp_inh A) Θ0 Ξg A' κ Θ0 HwfΘ
              ltac:(rewrite btyp_to_ptyp_ptyp_to_btyp_inh; exact HwfA)
              eq_refl eq_refl
              (is_ityp_ptyp_to_btyp_inh (a_wf_ptyp_lc HwfA))
              Hguess Hinc Huqb
              ltac:(intros α Hα;
                    pose proof (Havb α Hα) as Hn; clear - Hn; solve_notin_auto))
    as [ζg [Hmap [Hents HeqA']]].
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh in HeqA'.
  set (κg := ζg ++ κ) in *.
  assert (Hincg : κg ∷ (Ξg ++ Θ0) ⊑ Θ)
    by (apply a_inc_extend_flex_block;
        [ exact Hinc | exact Hmap | exact Hdecls | exact Hents ]).
  pose proof (keys_eq_dom _ _ Hmap) as Hdζ.

  assert (HrefCg : {{ Θ ⨟ empty ⊢ᵣ
                     (pskl_to_bskl_inh (msubst_pskl κg Q))
                     ⊳ (btyp_to_bskl Bc) }}ad).
  { assert (Hag : msubst_pskl κg Q = msubst_pskl κ Q).
    { apply msubst_pskl_agree.
      intros α Hα.
      apply msubst_lookup_app_notin.
      rewrite Hdζ.
      intros Hc.
      pose proof (Havb α Hc) as Hn. clear - Hn Hα; destruct_notin; fsetdec. }
    rewrite Hag. exact HrefC. }

  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` dom Ξg
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp A `union` ftvar_in_ptyp A'
                          `union` ftvar_in_pskl P `union` ftvar_in_pskl Q))
    as [x Hx].
  assert (HwfΞg : {{ ⊢ (Ξg ++ Θ0) }}a).
  { apply a_wf_aenv_prepend_decls; [ exact Hdecls | exact Huqb | | exact Hwf0 ].
    intros α Hα. pose proof (Havb α Hα) as Hn. clear - Hn; fsetdec. }
  assert (HwfA' : a_wf_ptyp (Ξg ++ Θ0) A').
  { eapply a_guess_mono_wf; [ exact Hguess | | ].
    - intros α Hα.
      destruct (a_wf_pskl_ftv_binds HwfP Hα) as [Hr | [Hm | [τ Hdf]]];
        [ left; apply binds_app_3; exact Hr
        | right; left; apply binds_app_3; exact Hm
        | right; right; exists τ; apply binds_app_3; exact Hdf ].
    - intros α1 Hb. right; left. apply binds_app_2; exact Hb. }
  assert (Hwf0x : {{ ⊢ ((x ~ abind_var_typ A') ++ Ξg ++ Θ0) }}a)
    by (apply a_wf_aenv__var_typ;
        [ rewrite dom_app; clear - Hx; fsetdec | exact HwfA' | exact HwfΞg ]).
  assert (HwfΘx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact HwfΘ ]).
  assert (Hincx : κg ∷ ((x ~ abind_var_typ A') ++ Ξg ++ Θ0)
                    ⊑ ((x ~ abind_var_typ A) ++ Θ)).
  { apply (@a_inc__var (Ξg ++ Θ0) κg Θ nil x A' A);
      [ exact Hincg
      | apply a_tyequiv__sym; exact HeqA'
      | apply a_suffix__nil ]. }

  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (apply Hlce).
  destruct (a_wf_exp_open_tm_binder (abind_var_typ A') Hlcbody
              (fun α Hα => binds_app_3 _ _ _ Ξg _ (Hrig α Hα)))
    as [Hrigx Hexpx].
  assert (HwfQx : {{ ((x ~ abind_var_typ A') ++ Ξg ++ Θ0) ⨟ empty ⊢ₚₛ Q }}a)
    by (eapply a_wf_pskl_mono;
        [ exact HwfQ
        | intros α c _ Hc; apply binds_cons_3; apply binds_app_3; exact Hc ]).

  destruct (IH x (decr_mode M) ((x ~ abind_var_typ A') ++ Ξg ++ Θ0) Q κg
              ((x ~ abind_var_typ A) ++ Θ) Bc
              Hwf0x HwfΘx HwfQx HmodQ Hincx Hrigx Hlcbody
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact HrefCg
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [B' [Θout [HrunB HoptB]]].

  destruct (a_typing_run_under_tm_binder HrunB Hwf0x HwfQx HmodQ Hexpx)
    as [κb [Ξ [Θ2 [-> [Hidb [Hincb' [Hsuf [HwfOut [_ [HxΞ HxΘ2]]]]]]]]]].

  exists (ptyp_arrow A' B'), (Ξ ++ Θ2).
  split.
  { eapply a_typing__abs with (x := x) (Ξ := Ξ) (Θ2 := Θ2)
      (P := P) (Q := Q) (αs := Ξg) (Θ1 := Θ0).
    - exact HMne.
    - exact Hsplit.
    - exact Hguess.
    - apply uniq_app_of;
        [ exact Huqb | apply a_wf_aenv_uniq; exact Hwf0
        | intros α Hα Hc;
          pose proof (Havb α Hα) as Hn;
          assert (Hd0 : α `in` dom Θ0) by (clear - Hc; fsetdec);
          clear - Hn Hd0; destruct_notin; fsetdec ].
    - exact Hsuf.
    - rewrite !dom_app. clear - Hx HxΞ HxΘ2. solve_notin.
    - exact HrunB. }

  intros κ1 Hid1 Hinc1.

  assert (Hinc1b : κb ∷ ((x ~ abind_var_typ A') ++ Ξg ++ Θ0)
                     ⊑ (Ξ ++ (x ~ abind_var_typ A') ++ Θ2)).
  { apply (@a_inc__var (Ξg ++ Θ0) κb Θ2 Ξ x A' A');
      [ exact Hincb'
      | rewrite (msubst_ptyp_id A' Hidb);
        apply a_tyequiv__refl; eapply a_guess_mono_lc; exact Hguess
      | exact Hsuf ]. }
  destruct (HoptB κb Hidb Hinc1b) as [ζb [Hζb [Heqvb Heqcb]]].
  assert (Hζbs : ζb ∷ (Ξ ++ Θ2) ⊑ Θ).
  { exact (@a_inc_strip_tm_head Ξ x (abind_var_typ A') (abind_var_typ A)
             Θ2 ζb Θ Hsuf
             (fun h : abind_is_ty (abind_var_typ A') => h)
             (fun h : abind_is_ty (abind_var_typ A) => h)
             HwfOut HwfΘx Hζb). }
  assert (Heqvbs : a_inc_equiv (Ξg ++ Θ0) κg (msubst_compose ζb κb) Θ)
    by (eapply a_inc_equiv_strip_tm_head; [ exact Heqvb | exact I | exact I ]).

  destruct (@a_inc_strip_decls_head Ξg κb Θ0 Θ2 Hdecls Hincb')
    as [κbp [κbt [Heqκb [Hlenb Hincbt]]]].
  destruct (@a_inc_equiv_strip_decls_head Ξg Θ0 κg (msubst_compose ζb κb) Θ Hdecls Heqvbs)
    as [κ1p [κ1t [κ2p [κ2t [Hspl1 [Hspl2 [Hl1 [Hl2 Heqv0]]]]]]]].

  assert (Hlenζg : length ζg = length Ξg).
  { pose proof (f_equal (@length atom) Hmap) as Hl.
    rewrite !List.length_map in Hl. exact Hl. }

  destruct (app_split_by_head_length _ _ _ _ Hspl1
              ltac:(rewrite Hl1; exact Hlenζg))
    as [Heqp1 Heqt1].
  assert (Hκ1t : κ1t = κ) by (clear - Heqt1; congruence).
  subst κ1t.

  rewrite Heqκb in Hspl2.
  unfold msubst_compose in Hspl2.
  rewrite List.map_app in Hspl2.
  destruct (app_split_by_head_length _ _ _ _ Hspl2
              ltac:(rewrite Hl2, List.length_map; exact Hlenb))
    as [Heqp2 Heqt2].

  assert (Hidbt : is_id_msubst κbt)
    by (rewrite Heqκb in Hidb; apply Forall_app in Hidb as [_ Hidb]; exact Hidb).
  assert (Heqκ1 : κ1 = κbt)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincbt | exact Hid1 | exact Hidbt ]).
  exists ζb.
  split; [ exact Hζbs | ].
  split.
  { rewrite Heqκ1.
    unfold msubst_compose.
    rewrite Heqt2.
    exact Heqv0. }
  assert (Hwffin : {{ ⊢ (Ξ ++ Θ2) }}a)
    by (exact (@a_wf_aenv_strip_tm_mid Ξ x (abind_var_typ A') Θ2
                 (fun h : abind_is_ty (abind_var_typ A') => h) HwfOut)).
  assert (Hpush : {{ Θ ⊢ (msubst_ptyp κg A') ≡ᵗ
                    (msubst_ptyp (msubst_compose ζb κb) A') }}a).
  { apply (@a_inc_equiv_msubst_ptyp A' (Ξg ++ Θ0) κg
             (msubst_compose ζb κb) Θ HwfA' Heqvbs HwfΞg
             ltac:(eapply a_inc_msubst_lc; exact Hincg)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζbs
                   | exact (is_id_msubst_values_lc Hidb) ])). }
  assert (Hlcfin2 : lc_aenv Θ2)
    by (apply a_wf_aenv_lc_aenv;
        eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (x ~ abind_var_typ A'));
        simpl_env; exact HwfOut).
  destruct (a_inc_weaken_suffix_target Hincb' Hidb Hlcfin2 Hsuf)
    as [κb2 [Hidb2 Hincb2]].
  assert (Heqκb2 : κb2 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hincb2 | exact Hincb' | exact Hidb2 | exact Hidb ]).
  subst κb2.
  assert (Hcid : msubst_ptyp (msubst_compose ζb κb) A' = msubst_ptyp ζb A')
    by (eapply msubst_compose_id_ptyp;
        [ exact HwfΞg | exact Hwffin | exact Hidb | exact Hincb2
        | exact Hζbs | exact HwfA' ]).
  rewrite Hcid in Hpush.
  simpl.
  apply a_tyequiv__arrow.
  - rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
    eapply a_tyequiv__trans;
      [ apply a_tyequiv__sym; exact Hpush | exact HeqA' ].
  - eapply a_tyequiv_ctx_mono;
      [ exact Heqcb
      | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ A) Θ);
        intros h; exact h ].
Qed.

Lemma a_typing_complete_abs_anno : forall M Θ0 P0 A e κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  M <> mode_tc ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs_anno A e) ->
  (forall x, typ_complete_ih (open_exp_wrt_exp e (exp_var_f x))) ->
  {{ Θ ⊢ˢᵈ[ M ] (exp_abs_anno A e) ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 (exp_abs_anno A e) κ Θ B.
Proof.
  intros M Θ0 P0 A e κ Θ B Hwf0 HwfΘ HwfP0 Hmod HMne Hinc Hrig
         Hlc IH Hd Href.
  inversion Hd; subst; [ exfalso; auto | exfalso; auto | ].
  match goal with
  | H : forall x, x `notin` ?L0 -> ad_sd_typing _ _ _ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | H : {{ Θ ⊢ A ≡ᵗ (btyp_to_ptyp ?BB) }}a |- _ =>
      rename H into HeqAA'; rename BB into B1
  end.
  set (A' := btyp_to_ptyp B1) in *.
  match goal with
  | |- typ_complete_concl _ _ _ _ _ _ (btyp_arrow _ ?BB) => rename BB into B2
  end.
  match goal with
  | H : a_wf_ptyp Θ A |- _ => rename H into HwfA
  end.
  simpl in Hrig.
  assert (HrigA : forall α, α `in` ftvar_in_ptyp A -> binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlce : forall x, lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (intros x; inversion Hlc; auto).
  assert (HlcA : lc_ptyp A) by (inversion Hlc; assumption).
  assert (HwfA0 : a_wf_ptyp Θ0 A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA; exact Hα ]).
  assert (HmsA : msubst_ptyp κ A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hinc | exact Hwf0 | exact HrigA ]).
  assert (HwfA' : a_wf_ptyp Θ A')
    by (eapply (proj1 (a_tyequiv_wf_iff HeqAA' (fun x b h => h) HwfΘ));
        exact HwfA).
  assert (HB1 : btyp_to_ptyp B1 = A') by reflexivity.

  destruct (@a_split_identity_of_refine_arrow _ _ _ _ _ _ _ HwfP0 Hmod HMne Href)
    as [P [Q [Hsplit [HmodQ [HwfP [HwfQ [HrefD HrefC]]]]]]].

  assert (HwfpA0 : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfA0).
  assert (Heqs : {{ Θ ⊢ (ptyp_to_pskl A) ≡ˢ (ptyp_to_pskl A') }}a)
    by (apply a_tyequiv_pskl; exact HeqAA').
  assert (Hjoin : {{ empty ⨟ Θ ⊢ˢ
                    (pskl_to_uskl (msubst_pskl κ (ptyp_to_pskl A)))
                    ∼ (btyp_to_bskl B1) }}ad).
  { rewrite msubst_pskl_embed_ptyp, HmsA.
    eapply (proj2 (skl_tyequiv_consis_transport Heqs HwfΘ
                     (fun x b h => h))).
    rewrite pskl_to_uskl_ptyp.
    apply (ad_pat_consis_syn_bid HwfA' B1 HB1). }
  assert (Hrp : {{ Θ ⨟ empty ⊢ᵣₚ (msubst_pskl κ (ptyp_to_pskl A)) ⊳ (bskl_to_pskl (btyp_to_bskl B1)) }}ad).
  { rewrite msubst_pskl_embed_ptyp, HmsA.
    rewrite bskl_to_pskl_btyp_to_bskl, HB1.
    eapply (proj2 (skl_tyequiv_refine_pskl_transport Heqs HwfΘ
                     (fun x b h => h))).
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl. exact HwfA'. }
  destruct (a_consis_complete Hwf0 HwfP HwfpA0 Hinc HwfΘ Hjoin
              ltac:(exact HrefD)
              Hrp (@ad_pat_consis_msubst_target_wf _ _ _ _ _ Hjoin
                     ltac:(first [ exact I | apply ptyp_to_pskl_ghost_free ]) empty))
    as [Qc [Θmid [HcRun HoptC]]].
  destruct (a_consis_isub_wf_nil HcRun Hwf0 HwfP HwfpA0) as [HleC Hwfmid].
  destruct HleC as [[κc [Hidc Hincc]] _].
  destruct (HoptC κc Hidc Hincc) as [ζc [Hζc [Heqvc _]]].

  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` dom Θmid `union` ftvar_in_aenv Θmid
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp A
                          `union` ftvar_in_pskl P `union` ftvar_in_pskl Q))
    as [x Hx].
  assert (HrigMid : forall α, α `in` ftvar_in_ptyp A ->
             binds α abind_tvar Θmid)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hincc | apply HrigA; exact Hα ]).
  assert (HwfAmid : a_wf_ptyp Θmid A)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigMid; exact Hα ]).
  assert (Hwf0x : {{ ⊢ ((x ~ abind_var_typ A) ++ Θmid) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfAmid | exact Hwfmid ]).
  assert (HwfΘx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact HwfΘ ]).
  assert (HmsAζc : msubst_ptyp ζc A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζc | exact Hwfmid | exact HrigMid ]).
  assert (Hincx : ζc ∷ ((x ~ abind_var_typ A) ++ Θmid)
                    ⊑ ((x ~ abind_var_typ A) ++ Θ)).
  { apply (@a_inc__var Θmid ζc Θ nil x A A);
      [ exact Hζc
      | rewrite HmsAζc; apply a_tyequiv__refl; exact HlcA
      | apply a_suffix__nil ]. }

  assert (HwfQB2 : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B2)) }}a).
  { pose proof (ad_sd_typing_target_wf Hd HwfΘ) as Hw.
    simpl in Hw. inversion Hw; subst.
    rewrite bskl_to_pskl_btyp_to_bskl.
    apply a_wf_ptyp_to_wf_pskl. assumption. }
  pose proof (ad_refine_msubst_compose_id Hwf0 Hwfmid HwfΘ HwfQ Hinc Hidc
                Hincc Hζc Heqvc HwfQB2 HrefC) as HrefCζ.

  destruct (a_wf_exp_open_tm_binder (abind_var_typ A) (Hlce x)
              (fun α Hα => a_inc_binds_tvar α Hincc (Hrig α (union_3 _ Hα))))
    as [Hrigx Hexpx].
  assert (HwfQmid : {{ Θmid ⨟ empty ⊢ₚₛ Q }}a).
  { pose proof (a_wf_pskl_msubst_inc_empty Hincc Hwf0 HwfQ) as Hw.
    rewrite (msubst_pskl_id Q Hidc) in Hw. exact Hw. }

  destruct (IH x (decr_mode M) ((x ~ abind_var_typ A) ++ Θmid) Q ζc
              ((x ~ abind_var_typ A) ++ Θ) B2
              Hwf0x HwfΘx
              ltac:(eapply a_wf_pskl_mono;
                    [ exact HwfQmid
                    | intros α c _ Hc; apply binds_cons_3; exact Hc ])
              HmodQ Hincx Hrigx (Hlce x)
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact HrefCζ
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [B' [Θout [HrunB HoptB]]].

  assert (HwfQx : {{ ((x ~ abind_var_typ A) ++ Θmid) ⨟ empty ⊢ₚₛ Q }}a)
    by (eapply a_wf_pskl_mono;
        [ exact HwfQmid
        | intros α c _ Hc; apply binds_cons_3; exact Hc ]).
  destruct (a_typing_run_under_tm_binder HrunB Hwf0x HwfQx HmodQ Hexpx)
    as [κb [Ξ [Θ3 [-> [Hidb [Hincb' [Hsuf [HwfOut [_ [HxΞ HxΘ3]]]]]]]]]].

  exists (ptyp_arrow A B'), (Ξ ++ Θ3).
  split.
  { eapply a_typing__abs_anno with (x := x) (Ξ := Ξ) (Θ3 := Θ3)
      (P := P) (Θ1 := Θ0) (Θ2 := Θmid).
    - exact HMne.
    - exact Hsplit.
    - exists Qc; exact HcRun.
    - exact Hsuf.
    - rewrite !dom_app. clear - Hx HxΞ HxΘ3. solve_notin.
    - exact HrunB. }

  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κc)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincc | exact Hid1 | exact Hidc ]).
  assert (Hinc1b : κb ∷ ((x ~ abind_var_typ A) ++ Θmid)
                     ⊑ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3)).
  { apply (@a_inc__var Θmid κb Θ3 Ξ x A A);
      [ exact Hincb'
      | rewrite (msubst_ptyp_id A Hidb);
        apply a_tyequiv__refl; exact HlcA
      | exact Hsuf ]. }
  destruct (HoptB κb Hidb Hinc1b) as [ζb [Hζb [Heqvb Heqcb]]].
  assert (Hζbs : ζb ∷ (Ξ ++ Θ3) ⊑ Θ).
  { exact (@a_inc_strip_tm_head Ξ x (abind_var_typ A) (abind_var_typ A)
             Θ3 ζb Θ Hsuf
             (fun h : abind_is_ty (abind_var_typ A) => h)
             (fun h : abind_is_ty (abind_var_typ A) => h)
             HwfOut HwfΘx Hζb). }
  assert (Heqvbs : a_inc_equiv Θmid ζc (msubst_compose ζb κb) Θ)
    by (eapply a_inc_equiv_strip_tm_head; [ exact Heqvb | exact I | exact I ]).
  assert (Hwffin : {{ ⊢ (Ξ ++ Θ3) }}a)
    by (exact (@a_wf_aenv_strip_tm_mid Ξ x (abind_var_typ A) Θ3
                 (fun h : abind_is_ty (abind_var_typ A) => h) HwfOut)).
  assert (Hlcfin : lc_aenv Θ3)
    by (apply a_wf_aenv_lc_aenv;
        eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (x ~ abind_var_typ A));
        simpl_env; exact HwfOut).
  destruct (a_inc_weaken_suffix_target Hincb' Hidb Hlcfin Hsuf)
    as [κb2 [Hidb2 Hincb2]].
  assert (Heqκb2 : κb2 = κb)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hincb2 | exact Hincb' | exact Hidb2 | exact Hidb ]).
  subst κb2.
  exists ζb.
  split; [ exact Hζbs | ].
  split.
  { assert (Hglue : a_inc_equiv Θ0 κ (msubst_compose ζb κc) Θ).
    { eapply a_inc_equiv_glue_id with
        (Θmid := Θmid) (Θfin := Ξ ++ Θ3) (κ1b := κb) (ζ1 := ζc);
        [ exact Hwf0 | exact Hwfmid | exact Hwffin | exact HwfΘ        | exact Hidc | exact Hidb        | exact Hincc | exact Hincb2 | exact Hζc | exact Hζbs        | exact Heqvc | exact Heqvbs ]. }
    rewrite Heqκ. exact Hglue. }

  assert (HrigFin : forall α, α `in` ftvar_in_ptyp A ->
             binds α abind_tvar (Ξ ++ Θ3)).
  { intros α Hα. apply binds_app_3.
    eapply a_inc_binds_tvar; [ exact Hincb' | apply HrigMid; exact Hα ]. }
  assert (HmsAζb : msubst_ptyp ζb A = A)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζbs | exact Hwffin | exact HrigFin ]).
  simpl.
  apply a_tyequiv__arrow.
  - rewrite HmsAζb, HB1.
    exact HeqAA'.
  - eapply a_tyequiv_ctx_mono;
      [ exact Heqcb
      | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ A) Θ);
        intros h; exact h ].
Qed.

Lemma a_inc_strip_tvar_head : forall α Θ0 κ Θ,
  κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑ ((α ~ abind_tvar) ++ Θ) ->
  κ ∷ Θ0 ⊑ Θ.
Proof. intros; eapply a_inc_tvar_head_inv; eassumption. Qed.

Lemma a_inc_equiv_strip_tvar_head : forall α Θ0 κ1 κ2 Θ,
  a_inc_equiv ((α ~ abind_tvar) ++ Θ0) κ1 κ2 ((α ~ abind_tvar) ++ Θ) ->
  a_inc_equiv Θ0 κ1 κ2 Θ.
Proof. intros; eapply a_inc_equiv_tvar_head_inv; eassumption. Qed.

Lemma a_typing_complete_check_step_of_rule : forall t L Θ0 P0 κ Θ B,
  (forall α Θ0 Θ1 A0 A Ξ,
     a_suffix Ξ ->
     uniq (Ξ ++ Θ0) ->
     (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
     α `notin` dom (Ξ ++ Θ0) `union` dom Θ1 `union`
       ftvar_in_ptyp A0 `union` ftvar_in_ptyp A `union` ftvar_in_exp t ->
     {{ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
       t ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
       ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}a ->
     {{ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ] t ⦂ (ptyp_all A) ⊣ Θ1 }}a) ->
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp t -> binds α abind_tvar Θ0) ->
  lc_exp t ->
  (forall M' Θ0' P0' κ' Θ' B',
     size_btyp B' < size_btyp (btyp_all_inh B) ->
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp t -> binds α abind_tvar Θ0') ->
     lc_exp t ->
     {{ Θ' ⊢ˢᵈ[ M' ] t ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' t κ' Θ' B') ->
  (forall α, α `notin` L ->
     {{ ((α ~ abind_tvar) ++ Θ) ⊢ˢᵈ[ mode_tc ] t
       ⦂ (open_btyp_wrt_btyp B (btyp_var_f α)) }}ad) ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_all_inh B)) }}ad ->
  typ_complete_concl mode_tc Θ0 P0 t κ Θ (btyp_all_inh B).
Proof.
  intros t L Θ0 P0 κ Θ B Hrule Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
         Hlc IH Hbody Href.

  inversion Hmod; subst.
  match goal with
  | |- typ_complete_concl _ _ (ptyp_to_pskl ?AA) _ _ _ _ => rename AA into Ap
  end.
  rewrite msubst_pskl_embed_ptyp in Href.
  destruct Ap as [ | n | β | Aa Ab | A0 ]; simpl in Href.
  -
    exfalso.
    eapply ad_refine_syn_guarded_src_all_inh_absurd with (Θ := Θ);
      [ exact HwfΘ
      | exact Href
      | apply guarded_bskl__unit ].
  -
    simpl in HwfP0. inversion HwfP0.
  -
    exfalso.
    pose proof (a_inc_lookup_mono β Hinc) as Hm.
    rewrite (ptyp_to_bskl_inh_syn_eq Hm) in Href.
    eapply ad_refine_syn_guarded_src_all_inh_absurd with (Θ := Θ);
      [ exact HwfΘ
      | exact Href
      | apply mono_bskl_guarded; apply mono_ptyp_to_bskl_syn; exact Hm ].
  -
    exfalso.
    simpl in HwfP0. inversion HwfP0; subst.
    match goal with
    | Hw1 : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Aa) }}a,
      Hw2 : {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Ab) }}a |- _ =>
        rename Hw1 into Hwfa; rename Hw2 into Hwfb
    end.
    assert (Hlca : lc_bskl (pskl_to_bskl_inh (ptyp_to_pskl (msubst_ptyp κ Aa)))).
    { apply lc_pskl_to_bskl_inh.
      rewrite <- msubst_pskl_embed_ptyp.
      eapply a_wf_pskl_lc.
      exact (a_wf_pskl_msubst_inc_empty Hinc Hwf0 Hwfa). }
    assert (Hlcb : lc_bskl (pskl_to_bskl_inh (ptyp_to_pskl (msubst_ptyp κ Ab)))).
    { apply lc_pskl_to_bskl_inh.
      rewrite <- msubst_pskl_embed_ptyp.
      eapply a_wf_pskl_lc.
      exact (a_wf_pskl_msubst_inc_empty Hinc Hwf0 Hwfb). }
    eapply ad_refine_syn_guarded_src_all_inh_absurd with (Θ := Θ);
      [ exact HwfΘ
      | exact Href
      | apply guarded_bskl__arrow; [ exact Hlca | exact Hlcb ] ].
  -
    inversion Href; subst.
    match goal with
    | H : forall α, α `notin` ?L0 ->
            ad_refine_syn _ _ (open_bskl_wrt_bskl _ _) _ |- _ =>
        rename H into HrefF; rename L0 into L1
    end.
    simpl in HwfP0.
    inversion HwfP0; subst.
    match goal with
    | H : forall α, α `notin` ?L0 -> a_wf_pskl _ _ _ |- _ =>
        rename H into HwfF; rename L0 into L2
    end.

    destruct (atom_fresh (L `union` L1 `union` L2
                `union` dom Θ0 `union` dom Θ `union` ftvar_in_aenv Θ
                `union` dom κ `union` ftvar_in_ptyp A0
                `union` ftvar_in_btyp B `union` ftvar_in_exp t)) as [α Hα].
    assert (Hwf0x : {{ ⊢ ((α ~ abind_tvar) ++ Θ0) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf0 ]).
    assert (HwfΘx : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact HwfΘ ]).
    assert (HwfP0x : {{ ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛ
                       (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) }}a).
    { rewrite ptyp_to_pskl_open.
      eapply a_wf_pskl_delta_mono;
        [ apply (HwfF α ltac:(clear - Hα; solve_notin_auto))
        | intros β _ Hβ; clear - Hβ; fsetdec ]. }
    assert (Hincx : κ ∷ ((α ~ abind_tvar) ++ Θ0) ⊑ ((α ~ abind_tvar) ++ Θ))
      by (apply (@a_inc__tvar Θ0 κ Θ nil α);
          [ exact Hinc | apply a_suffix__nil ]).
    assert (Hrigx : forall β, β `in` ftvar_in_exp (t) ->
               binds β abind_tvar ((α ~ abind_tvar) ++ Θ0))
      by (intros β Hβ; apply binds_cons_3; apply Hrig; exact Hβ).

    assert (Hrefx : {{ ((α ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                      (pskl_to_bskl_inh
                         (msubst_pskl κ
                            (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))))
                      ⊳ (btyp_to_bskl (open_btyp_wrt_btyp B (btyp_var_f α))) }}ad).
    { rewrite msubst_pskl_embed_ptyp.
      rewrite (@msubst_ptyp_open Θ0 κ Θ A0 α Hinc
                 ltac:(clear - Hα; solve_notin_auto)).
      rewrite ptyp_to_pskl_open.
      rewrite pskl_to_bskl_inh_open.
      rewrite btyp_to_bskl_open. simpl.
      eapply ad_refine_syn_delta_mono;
        [ apply (HrefF α ltac:(clear - Hα; solve_notin_auto)) | clear; fsetdec ]. }

    destruct (IH mode_tc ((α ~ abind_tvar) ++ Θ0)
                (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
                κ ((α ~ abind_tvar) ++ Θ)
                (open_btyp_wrt_btyp B (btyp_var_f α))
                ltac:(rewrite size_btyp_open_btyp_wrt_btyp_var;
                      simpl; lia)
                Hwf0x HwfΘx HwfP0x (a_ty_mode_compat__tc _) Hincx Hrigx
                Hlc
                (Hbody α ltac:(clear - Hα; solve_notin_auto)) Hrefx)
      as [A1 [Θrun [HrunB HoptB]]].

    assert (Hexpx : {{ ((α ~ abind_tvar) ++ Θ0) ⊢ᵉ (t) }}a).
    { apply a_wf_exp_of_tvarish; [ exact Hlc | ].
      intros β Hβ. left. apply Hrigx. exact Hβ. }
    destruct (a_typing_sound HrunB Hwf0x HwfP0x
                (a_ty_mode_compat__tc _) Hexpx)
      as [HleB [HwfOut [HwfA1out _]]].
    destruct HleB as [[κb [Hidb Hincb]] _].
    destruct (a_inc_tvar_inv Hincb) as [Ξ [Θ2 [-> [Hsuf Hincb']]]].

    pose proof (@a_typing_scope_tvar_nil _ _ _ _ _ _ _ HrunB Hwf0x
                  HwfP0x Hexpx HwfOut Hsuf) as Hscope.

    assert (HuOut : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ2))
      by (apply a_wf_aenv_uniq; exact HwfOut).
    assert (HuΞ : uniq Ξ) by (clear - HuOut; solve_uniq).
    assert (HαΞΘ2 : α `notin` dom Ξ `union` dom Θ2)
      by (clear - HuOut; destruct_uniq; unfold disjoint in *;
          simpl_env in *; fsetdec).
    assert (HΞΘ2 : forall γ, γ `in` dom Ξ -> γ `notin` dom Θ2)
      by (clear - HuOut; intros γ Hγ; destruct_uniq;
          unfold disjoint in *; simpl_env in *; fsetdec).
    assert (Hdom02 : dom Θ0 [<=] dom Θ2)
      by (eapply a_inc_id_dom_sub_scope; [ exact Hincb' | exact Hidb ]).

    exists (ptyp_all (close_ptyp_wrt_ptyp α A1)), Θ2.
    split.
    { eapply Hrule with (α := α) (Ξ := Ξ).
      - exact Hsuf.
      - apply uniq_app_of;
          [ exact HuΞ | apply a_wf_aenv_uniq; exact Hwf0 | ].
        intros γ Hγ Hc.
        exact (HΞΘ2 γ Hγ (Hdom02 _ Hc)).
      -
        intros γ Hγ.
        rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp.
        pose proof (Hscope γ Hγ) as Hn. clear - Hn; fsetdec.
      - rewrite dom_app.
        rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp.
        simpl. clear - Hα HαΞΘ2. solve_notin.
      - rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp.
        exact HrunB. }

    intros κ1 Hid1 Hinc1.
    assert (Hinc1x : κ1 ∷ ((α ~ abind_tvar) ++ Θ0)
                       ⊑ (Ξ ++ (α ~ abind_tvar) ++ Θ2))
      by (apply (@a_inc__tvar Θ0 κ1 Θ2 Ξ α); [ exact Hinc1 | exact Hsuf ]).
    destruct (HoptB κ1 Hid1 Hinc1x) as [ζb [Hζb [Heqvb Heqcb]]].
    destruct (@a_inc_peel_suffix Ξ ((α ~ abind_tvar) ++ Θ2) ζb
                ((α ~ abind_tvar) ++ Θ) Hsuf Hζb)
      as [ζbp [ζbt [-> [Hdomζp Hζbt0]]]].
    pose proof (@a_inc_strip_tvar_head α Θ2 ζbt Θ Hζbt0) as Hstrip.
    pose proof (@a_inc_equiv_strip_tvar_head α Θ0 κ
                  (msubst_compose (ζbp ++ ζbt) κ1) Θ Heqvb) as Heqv0.
    assert (Hnotinζp : forall β, β `in` dom κ1 -> β `notin` dom ζbp).
    { intros β Hβ.
      rewrite Hdomζp.
      intros Hc.
      pose proof (a_inc_dom_sub Hinc1 Hβ) as Hβ0.
      exact (HΞΘ2 β Hc (Hdom02 _ Hβ0)). }
    rewrite (@msubst_compose_id_app_agree κ1 ζbp ζbt Hid1 Hnotinζp) in Heqv0.
    exists ζbt.
    split; [ exact Hstrip | ].
    split; [ exact Heqv0 | ].

    assert (Hagree : msubst_ptyp (ζbp ++ ζbt) A1 = msubst_ptyp ζbt A1).
    { apply msubst_ptyp_agree.
      intros γ Hγ.
      apply msubst_lookup_app_notin.
      rewrite Hdomζp. intros Hc.
      exact (Hscope γ Hc Hγ). }
    rewrite Hagree in Heqcb.
    rewrite btyp_to_ptyp_open_var in Heqcb.
    assert (Hαζbt : α `notin` dom ζbt).
    { intros Hc.
      pose proof (a_inc_dom_sub Hstrip Hc) as Hc2.
      clear - Hc2 HαΞΘ2; fsetdec. }
    assert (Heq1 : msubst_ptyp ζbt A1
                   = open_ptyp_wrt_ptyp
                       (msubst_ptyp ζbt (close_ptyp_wrt_ptyp α A1))
                       (ptyp_var_f α)).
    { rewrite <- (@msubst_ptyp_open Θ2 ζbt Θ
                    (close_ptyp_wrt_ptyp α A1) α Hstrip Hαζbt).
      rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp. reflexivity. }
    rewrite Heq1 in Heqcb.
    pose proof (a_tyequiv_strengthen_tvar_cons Heqcb eq_refl) as Heqc1.
    simpl.
    set (X := msubst_ptyp ζbt (close_ptyp_wrt_ptyp α A1)) in *.
    assert (HαX : α `notin` ftvar_in_ptyp X).
    { unfold X.
      eapply msubst_ptyp_ftv_notin_inc;
        [ exact Hstrip
        | rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp; clear; fsetdec
        | clear - Hα; fsetdec ]. }
    assert (HαB : α `notin` ftvar_in_ptyp (btyp_to_ptyp B))
      by (rewrite ftvar_btyp_to_ptyp; clear - Hα; fsetdec).
    apply a_tyequiv__all with
      (L := ftvar_in_ptyp X `union` ftvar_in_ptyp (btyp_to_ptyp B)
              `union` singleton α `union` dom Θ `union` ftvar_in_aenv Θ).
    intros β Hβ.
    pose proof (a_tyequiv_swap α β _ _ _ Heqc1) as Hsw.
    assert (Hfe1 : α `notin` (dom Θ `union` ftvar_in_aenv Θ))
      by (clear - Hα; fsetdec).
    assert (Hfe2 : β `notin` (dom Θ `union` ftvar_in_aenv Θ))
      by (clear - Hβ; fsetdec).
    rewrite (@swap_aenv_fresh_eq α β Θ Hfe1 Hfe2) in Hsw.
    rewrite !swap_ptyp_open in Hsw.
    cbn [swap_ptyp] in Hsw.
    rewrite swap_atom_l in Hsw.
    rewrite (swap_ptyp_fresh_id α β X) in Hsw;
      [ | exact HαX | clear - Hβ; fsetdec ].
    rewrite (swap_ptyp_fresh_id α β (btyp_to_ptyp B)) in Hsw;
      [ | exact HαB | clear - Hβ; fsetdec ].
    exact Hsw.
Qed.

Lemma a_typing_complete_abs_check_step : forall Θ0 P0 e κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs e) ->
  (forall M' Θ0' P0' κ' Θ' B',
     size_btyp B' < size_btyp (btyp_all_inh B) ->
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0') ->
     lc_exp (exp_abs e) ->
     {{ Θ' ⊢ˢᵈ[ M' ] (exp_abs e) ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' (exp_abs e) κ' Θ' B') ->
  {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_all_inh B) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_all_inh B)) }}ad ->
  typ_complete_concl mode_tc Θ0 P0 (exp_abs e) κ Θ (btyp_all_inh B).
Proof.
  intros Θ0 P0 e κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
         Hlc IH Hd Href.
  inversion Hd; subst.
  eapply a_typing_complete_check_step_of_rule; try eassumption.
  intros; eapply a_typing__abs_check_step; eassumption.
Qed.

Lemma a_typing_complete_abs_anno_check_step : forall Θ0 P0 A e κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs_anno A e) ->
  (forall M' Θ0' P0' κ' Θ' B',
     size_btyp B' < size_btyp (btyp_all_inh B) ->
     {{ ⊢ Θ0' }}a -> {{ ⊢ Θ' }}a ->
     {{ Θ0' ⨟ empty ⊢ₚₛ P0' }}a ->
     a_ty_mode_compat M' P0' ->
     κ' ∷ Θ0' ⊑ Θ' ->
     (forall α, α `in` ftvar_in_exp (exp_abs_anno A e) ->
        binds α abind_tvar Θ0') ->
     lc_exp (exp_abs_anno A e) ->
     {{ Θ' ⊢ˢᵈ[ M' ] (exp_abs_anno A e) ⦂ B' }}ad ->
     {{ Θ' ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ' P0'))
       ⊳ (btyp_to_bskl B') }}ad ->
     typ_complete_concl M' Θ0' P0' (exp_abs_anno A e) κ' Θ' B') ->
  {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_all_inh B) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_all_inh B)) }}ad ->
  typ_complete_concl mode_tc Θ0 P0 (exp_abs_anno A e) κ Θ (btyp_all_inh B).
Proof.
  intros Θ0 P0 A e κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
         Hlc IH Hd Href.
  inversion Hd; subst.
  eapply a_typing_complete_check_step_of_rule; try eassumption.
  intros; eapply a_typing__abs_anno_check_step; eassumption.
Qed.

Lemma msubst_compose_cons : forall ζ α τ κ,
  msubst_compose ζ ((α, τ) :: κ) = (α, msubst_ptyp ζ τ) :: msubst_compose ζ κ.
Proof. reflexivity. Qed.

Lemma mono_refine_arrow_inv : forall Θ Δ Qs Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  forall τ0 R1 R2,
  {{ ⊢ Θ }}a ->
  a_wf_ptyp Θ τ0 ->
  mono_ptyp τ0 ->
  Qs = ptyp_to_bskl_syn τ0 ->
  Qt = bskl_arrow R1 R2 ->
  exists τ1 τ2,
    mono_ptyp τ1 /\ mono_ptyp τ2 /\
    a_wf_ptyp Θ τ1 /\ a_wf_ptyp Θ τ2 /\
    {{ Θ ⊢ τ0 ≡ᵗ (ptyp_arrow τ1 τ2) }}a /\
    ({{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn τ1) ⊳ R1 }}ad) /\
    ({{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn τ2) ⊳ R2 }}ad).
Proof.
  intros Θ Δ Qs Qt H; induction H;
    intros τ0 R1 R2 Hwf Hwfτ Hm HeqS HeqT;
    unfold ptyp_to_bskl_syn in *;
    try solve [ destruct τ0; simpl in HeqS; discriminate
              | discriminate HeqT ].
  -
    destruct τ0 as [ | n | α | τa τb | τc ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst. inversion HeqT; subst.
    inversion Hm; subst. inversion Hwfτ; subst.
    exists τa, τb.
    repeat split; try assumption.
    apply a_tyequiv__refl. apply mono_ptyp_lc. exact Hm.
  -
    destruct τ0 as [ | n | α0 | τa τb | τc ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf | exact H ]).
    assert (Hwfτ' : a_wf_ptyp Θ τ)
      by (eapply prop_context.a_wf_aenv_binds_def_wf; [ exact Hwf | exact H ]).
    destruct (IHad_refine_syn τ R1 R2 Hwf Hwfτ' Hmτ eq_refl eq_refl)
      as [τ1 [τ2 [Hm1 [Hm2 [Hw1 [Hw2 [Heqv [Hr1 Hr2]]]]]]]].
    exists τ1, τ2.
    repeat split; try assumption.
    eapply a_tyequiv__trans; [ apply a_tyequiv__flex_def; exact H | exact Heqv ].
Qed.

Lemma refine_var_arrow_flex_def : forall Θ Δ Qs Qt,
  {{ Θ ⨟ Δ ⊢ᵣ Qs ⊳ Qt }}ad ->
  forall β R1 R2, Qs = bskl_var_f β -> Qt = bskl_arrow R1 R2 ->
  exists τ, binds β (abind_flex_mono_def τ) Θ.
Proof.
  intros Θ Δ Qs Qt H; induction H; intros β0 R1 R2 HeqS HeqT;
    try solve [ discriminate HeqS | discriminate HeqT ].
  inversion HeqS; subst. exists τ. assumption.
Qed.

Lemma a_split_complete_tc : forall Θ0 A0 κ Θ A (B1 : btyp),
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (ptyp_to_pskl A0) }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ (ptyp_to_pskl A0)))
    ⊳ (btyp_to_bskl (btyp_arrow (ptyp_to_btyp_inh A) B1)) }}ad ->
  exists Ad Bc Θ1 κs ζ,
    ({{ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl Ad) ⇢ (ptyp_to_pskl Bc) ⊣ Θ1 }}a) /\
    {{ ⊢ Θ1 }}a /\
    a_wf_ptyp Θ1 Ad /\ a_wf_ptyp Θ1 Bc /\
    is_id_msubst κs /\ κs ∷ Θ0 ⊑ Θ1 /\
    ζ ∷ Θ1 ⊑ Θ /\
    a_inc_equiv Θ0 κ (msubst_compose ζ κs) Θ /\
    {{ Θ ⊢ (msubst_ptyp ζ Ad) ≡ᵗ A }}a /\
    ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl ζ (ptyp_to_pskl Bc)))
       ⊳ (btyp_to_bskl B1) }}ad).
Proof.
  intros Θ0 A0 κ Θ A B1 Hwf0 HwfΘ HwfP0 Hinc Href.
  cbn [btyp_to_bskl] in Href.
  assert (Hbuilt : exists Ad Bc Θ1 ζ,
             ({{ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl Ad)
                 ⇢ (ptyp_to_pskl Bc) ⊣ Θ1 }}a) /\
             ζ ∷ Θ1 ⊑ Θ /\
             (forall κs, is_id_msubst κs -> κs ∷ Θ0 ⊑ Θ1 ->
                a_inc_equiv Θ0 κ (msubst_compose ζ κs) Θ) /\
             {{ Θ ⊢ (msubst_ptyp ζ Ad) ≡ᵗ A }}a /\
             ({{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl ζ (ptyp_to_pskl Bc)))
                ⊳ (btyp_to_bskl B1) }}ad)).
  { destruct A0 as [ | n | β | Aa Ab | Ac ];
      rewrite msubst_pskl_embed_ptyp in Href.
    -
      exfalso. cbn in Href. inversion Href.
    -
      exfalso. cbn in HwfP0. inversion HwfP0.
    -
      cbn [ptyp_to_pskl] in HwfP0.
      assert (Hbt : a_binds_tvar β Θ0)
        by (inversion HwfP0 as [ | ? ? ? Hb | | | | ]; subst; exact Hb).
      pose proof (a_inc_lookup_mono β Hinc) as Hmτ.
      pose proof (@a_inc_lookup_wf Θ0 κ Θ β Hinc Hwf0 Hbt) as Hwfτ.
      cbn [ptyp_to_pskl msubst_ptyp] in Href.
      rewrite (ptyp_to_bskl_inh_syn_eq Hmτ) in Href.
      destruct Hbt as [Hrig | Hflex].
      {
        exfalso.
        assert (Hid : msubst_lookup κ β = ptyp_var_f β).
        { change (msubst_lookup κ β) with (msubst_ptyp κ (ptyp_var_f β)).
          eapply msubst_ptyp_rigid_id;
            [ exact Hinc | exact Hwf0
            | intros γ Hγ; cbn in Hγ;
              assert (Hγβ : γ = β) by (clear - Hγ; fsetdec); subst;
              exact Hrig ]. }
        rewrite Hid in Href.
        unfold ptyp_to_bskl_syn in Href.
        cbn [ptyp_to_pskl pskl_to_bskl_syn] in Href.
        destruct (refine_var_arrow_flex_def Href eq_refl eq_refl) as [τx Hb].
        assert (Hrt : binds β abind_tvar Θ)
          by (eapply a_inc_binds_tvar; [ exact Hinc | exact Hrig ]).
        pose proof (binds_unique _ _ _ _ _ Hb Hrt (a_wf_aenv_uniq HwfΘ)) as Hc.
        discriminate Hc. }

      destruct (mono_refine_arrow_inv Href HwfΘ Hwfτ Hmτ eq_refl eq_refl)
        as [τ1 [τ2 [Hm1 [Hm2 [Hw1 [Hw2 [Heqτ [Hr1 Hr2]]]]]]]].

      destruct (atom_fresh (ftvar_in_aenv Θ0 `union` dom Θ0 `union` dom κ
                              `union` dom Θ `union` ftvar_in_aenv Θ))
        as [β1 Hβ1].
      destruct (atom_fresh (add β1 (ftvar_in_aenv Θ0) `union` dom Θ0
                              `union` dom κ `union` dom Θ
                              `union` ftvar_in_aenv Θ)) as [α1 Hα1].
      assert (Hne : α1 <> β1) by (clear - Hα1; fsetdec).
      assert (Hfrβ1 : β1 `notin` dom Θ0) by (clear - Hβ1; fsetdec).
      assert (Hfrα1 : α1 `notin` dom Θ0) by (clear - Hα1; fsetdec).
      assert (Hwf0' : {{ ⊢ ((α1 ~ abind_flex_mono)
                                  ++ (β1 ~ abind_flex_mono) ++ Θ0) }}a).
      { apply a_wf_aenv__flex;
          [ simpl_env; repeat rewrite dom_app; simpl;
            clear - Hfrα1 Hne; fsetdec | ].
        apply a_wf_aenv__flex; [ clear - Hfrβ1; fsetdec | exact Hwf0 ]. }
      assert (Hinc' : ((α1, τ2) :: (β1, τ1) :: κ)
                        ∷ ((α1 ~ abind_flex_mono)
                             ++ (β1 ~ abind_flex_mono) ++ Θ0) ⊑ Θ).
      { apply a_inc__flex; [ | exact Hw2 | exact Hm2 ].
        apply a_inc__flex; [ exact Hinc | exact Hw1 | exact Hm1 ]. }
      assert (Hne1 : β1 <> α1) by (intros Hc; apply Hne; symmetry; exact Hc).
      assert (Hlkβ1 : msubst_lookup ((α1, τ2) :: (β1, τ1) :: κ) β1 = τ1)
        by (rewrite (@msubst_lookup_cons_neq β1 α1 τ2 ((β1, τ1) :: κ) Hne1);
            apply msubst_lookup_cons_eq).
      assert (Hlkα1 : msubst_lookup ((α1, τ2) :: (β1, τ1) :: κ) α1 = τ2)
        by (apply msubst_lookup_cons_eq).
      assert (Hβdom : β `in` dom Θ0)
        by (destruct Hflex as [Hb | [τx Hb]]; eapply binds_In; eassumption).
      assert (Hβα1 : β <> α1)
        by (intros Hc; rewrite Hc in Hβdom; clear - Hfrα1 Hβdom; fsetdec).
      assert (Hββ1 : β <> β1)
        by (intros Hc; rewrite Hc in Hβdom; clear - Hfrβ1 Hβdom; fsetdec).
      assert (Hlkβ : msubst_lookup ((α1, τ2) :: (β1, τ1) :: κ) β
                     = msubst_lookup κ β)
        by (rewrite (@msubst_lookup_cons_neq β α1 τ2 ((β1, τ1) :: κ) Hβα1),
                    (@msubst_lookup_cons_neq β β1 τ1 κ Hββ1); reflexivity).
      assert (HwfA12 : a_wf_ptyp Θ (ptyp_arrow τ1 τ2))
        by (apply a_wf_ptyp__arrow; assumption).
      assert (Hm12 : mono_ptyp (ptyp_arrow τ1 τ2))
        by (apply mono_ptyp__arrow; assumption).
      assert (Heqs : {{ Θ ⊢ (ptyp_to_pskl (msubst_lookup κ β))
                       ≡ˢ (ptyp_to_pskl (ptyp_arrow τ1 τ2)) }}a)
        by (apply a_tyequiv_pskl; exact Heqτ).

      assert (Hjoin : {{ empty ⨟ Θ ⊢ˢ
                        (pskl_to_uskl (msubst_pskl ((α1, τ2) :: (β1, τ1) :: κ)
                                         (pskl_var_f β)))
                        ∼ (ptyp_to_bskl_syn (ptyp_arrow τ1 τ2)) }}ad).
      { cbn [msubst_pskl]. rewrite Hlkβ.
        eapply (proj2 (skl_tyequiv_consis_transport Heqs HwfΘ
                         (fun x b (h : binds x b Θ) => h))).
        rewrite pskl_to_uskl_ptyp.
        pose proof (ad_pat_consis_syn_bid HwfA12
                      (ptyp_to_btyp_syn (ptyp_arrow τ1 τ2))
                      (btyp_to_ptyp_ptyp_to_btyp_syn _)) as Hc.
        rewrite btyp_to_bskl_ptyp_to_btyp_syn in Hc.
        exact Hc. }

      assert (Hrs : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh
                         (msubst_pskl ((α1, τ2) :: (β1, τ1) :: κ)
                            (pskl_arrow (pskl_var_f β1) (pskl_var_f α1)))) ⊳ (ptyp_to_bskl_syn (ptyp_arrow τ1 τ2)) }}ad).
      { cbn [msubst_pskl]. rewrite Hlkβ1, Hlkα1.
        change (pskl_arrow (ptyp_to_pskl τ1) (ptyp_to_pskl τ2))
          with (ptyp_to_pskl (ptyp_arrow τ1 τ2)).
        rewrite <- (ptyp_to_bskl_inh_syn_eq Hm12).
        apply ad_refine_syn_refl_inh.
        apply a_wf_ptyp_to_wf_pskl; exact HwfA12. }
      assert (Hrp : {{ Θ ⨟ empty ⊢ᵣₚ (msubst_pskl ((α1, τ2) :: (β1, τ1) :: κ) (pskl_var_f β)) ⊳ (bskl_to_pskl (ptyp_to_bskl_syn (ptyp_arrow τ1 τ2))) }}ad).
      { cbn [msubst_pskl]. rewrite Hlkβ.
        unfold ptyp_to_bskl_syn.
        rewrite bskl_to_pskl_pskl_to_bskl_syn.
        eapply (proj2 (skl_tyequiv_refine_pskl_transport Heqs HwfΘ
                         (fun x b (h : binds x b Θ) => h))).
        apply ad_refine_pskl_refl.
        apply a_wf_ptyp_to_wf_pskl; exact HwfA12. }

      destruct (a_consis_complete Hwf0'
                  ltac:(apply a_wf_pskl__arrow; apply a_wf_pskl__var;
                        right; left;
                        [ unfold binds; simpl; right; left; reflexivity
                        | unfold binds; simpl; left; reflexivity ])
                  ltac:(apply a_wf_pskl__var;
                        destruct Hflex as [Hb | [τx Hb]];
                        [ right; left | right; right; exists τx ];
                        repeat apply binds_cons_3; exact Hb)
                  Hinc' HwfΘ Hjoin Hrs Hrp (@ad_pat_consis_msubst_target_wf _ _ _ _ _ Hjoin
                     ltac:(first [ exact I | apply ptyp_to_pskl_ghost_free ]) empty))
        as [P1 [Θ1 [Hcons Hopt]]].

      assert (Hsplit : {{ Θ0 ⊲ (pskl_var_f β) ▹ (pskl_var_f β1)
                          ⇢ (pskl_var_f α1) ⊣ Θ1 }}a)
        by (apply a_split__flex with (Q := P1);
            [ clear - Hβ1; fsetdec | clear - Hα1; fsetdec | exact Hcons ]).

      destruct (a_split_wf Hsplit Hwf0 HwfP0)
        as [Hle01 [Hwf1 [HwfAd HwfBc]]].
      destruct Hle01 as [[κs [Hids Hincs]] _].
      assert (Hincs' : ((α1, ptyp_var_f α1) :: (β1, ptyp_var_f β1) :: κs)
                         ∷ ((α1 ~ abind_flex_mono)
                              ++ (β1 ~ abind_flex_mono) ++ Θ0) ⊑ Θ1).
      { apply a_inc__flex;
          [ | apply a_wf_ptyp__var;
              inversion HwfBc as [ | ? ? ? Hb | | | | ]; subst;
              exact Hb
            | apply mono_ptyp__var ].
        apply a_inc__flex;
          [ exact Hincs
          | apply a_wf_ptyp__var;
            inversion HwfAd as [ | ? ? ? Hb | | | | ]; subst;
            exact Hb
          | apply mono_ptyp__var ]. }
      assert (Hids' : is_id_msubst
                        ((α1, ptyp_var_f α1) :: (β1, ptyp_var_f β1) :: κs))
        by (repeat (apply Forall_cons; [ reflexivity | ]); exact Hids).
      destruct (Hopt _ Hids' Hincs') as [ζ [Hζ [Heqv Hprec]]].

      rewrite !msubst_compose_cons in Heqv.
      cbn [msubst_ptyp] in Heqv.
      inversion Heqv as [ | Θx κx1 κx2 Θy αx σ1 σ2 Heqv1 Hteq1
                            Heqa Heqb Heqc Heqd | | | | ]; subst.
      inversion Heqv1 as [ | Θx' κx1' κx2' Θy' αx' σ1' σ2' Heqv0 Hteq0
                             Heqa' Heqb' Heqc' Heqd' | | | | ]; subst.
      exists (ptyp_var_f β1), (ptyp_var_f α1), Θ1, ζ.
      split; [ exact Hsplit | ].
      split; [ exact Hζ | ].
      split.
      {
        intros κs0 Hid0 Hinc0.
        assert (Heqκ : κs0 = κs)
          by (eapply a_inc_id_msubst_unique;
              [ exact Hinc0 | exact Hincs | exact Hid0 | exact Hids ]).
        subst κs0. exact Heqv0. }
      split.
      {
        cbn [msubst_ptyp].
        eapply a_tyequiv__trans;
          [ apply a_tyequiv__sym; exact Hteq0 | ].
        rewrite <- (btyp_to_ptyp_ptyp_to_btyp_inh A).
        eapply ad_refine_syn_inh_tyequiv;
          [ exact Hr1 | exact HwfΘ
          | rewrite <- (ptyp_to_bskl_inh_syn_eq Hm1); reflexivity
          | reflexivity ]. }
      {
        cbn [msubst_pskl ptyp_to_pskl].
        eapply (proj1 (skl_tyequiv_refine_syn_transport
                         (a_tyequiv_pskl Hteq1) HwfΘ
                         (fun x b (h : binds x b Θ) => h))).
        rewrite (ptyp_to_bskl_inh_syn_eq Hm2).
        exact Hr2. }
    -
      exists Aa, Ab, Θ0, κ.
      cbn [ptyp_to_pskl msubst_ptyp pskl_to_bskl_inh] in Href.
      destruct (ad_refine_syn_arrow_inv Href) as [HrD HrC].
      split; [ apply a_split__arrow | ].
      split; [ exact Hinc | ].
      split.
      { intros κs Hids Hincs.
        rewrite (msubst_compose_is_id_r Hwf0 Hids Hincs Hinc).
        apply a_inc_equiv_refl; exact Hinc. }
      split.
      { rewrite <- (btyp_to_ptyp_ptyp_to_btyp_inh A).
        eapply ad_refine_syn_inh_tyequiv;
          [ exact HrD | exact HwfΘ | reflexivity | reflexivity ]. }
      { rewrite msubst_pskl_embed_ptyp. exact HrC. }
    -
      exfalso. cbn in Href. inversion Href. }

  destruct Hbuilt as [Ad [Bc [Θ1 [ζ [Hsplit [Hζ [Heqv [Heqd Hrefc]]]]]]]].
  destruct (a_split_wf Hsplit Hwf0 HwfP0) as [Hle01 [Hwf1 [HwfAd HwfBc]]].
  destruct Hle01 as [[κs [Hids Hincs]] _].
  exists Ad, Bc, Θ1, κs, ζ.
  repeat split; try assumption.
  - eapply a_wf_ptyp_of_scope_pskl;
      [ exact (a_scope_pskl_of_wf HwfAd)
      | reflexivity ].
  - eapply a_wf_ptyp_of_scope_pskl;
      [ exact (a_scope_pskl_of_wf HwfBc)
      | reflexivity ].
  - apply Heqv; assumption.
Qed.

Lemma a_typing_complete_strip_tm_suffix :
  forall Ξ x Ad A Θm Θ2 κb ζm ζb Θ B1',
  a_suffix Ξ ->
  {{ ⊢ (Ξ ++ (x ~ abind_var_typ Ad) ++ Θ2) }}a ->
  {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a ->
  is_id_msubst κb ->
  κb ∷ Θm ⊑ Θ2 ->
  (forall γ, γ `in` dom Ξ -> γ `notin` dom Θ2) ->
  dom Θm [<=] dom Θ2 ->
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1') ->
  ζb ∷ (Ξ ++ (x ~ abind_var_typ Ad) ++ Θ2) ⊑ ((x ~ abind_var_typ A) ++ Θ) ->
  a_inc_equiv ((x ~ abind_var_typ Ad) ++ Θm) ζm (msubst_compose ζb κb)
    ((x ~ abind_var_typ A) ++ Θ) ->
  exists ζbt,
    ζbt ∷ Θ2 ⊑ Θ /\
    a_inc_equiv Θm ζm (msubst_compose ζbt κb) Θ /\
    msubst_ptyp ζb B1' = msubst_ptyp ζbt B1'.
Proof.
  intros Ξ x Ad A Θm Θ2 κb ζm ζb Θ B1' Hsuf HwfOut HwfΘx Hidb Hincb'
         HΞΘ2 Hdom12 Hscope Hζb Heqvb.
  assert (Hζbm : ζb ∷ (Ξ ++ Θ2) ⊑ Θ)
    by (exact (@a_inc_strip_tm_head Ξ x (abind_var_typ Ad) (abind_var_typ A)
                 Θ2 ζb Θ Hsuf
                 (fun h : abind_is_ty (abind_var_typ Ad) => h)
                 (fun h : abind_is_ty (abind_var_typ A) => h)
                 HwfOut HwfΘx Hζb)).
  destruct (@a_inc_peel_suffix Ξ Θ2 ζb Θ Hsuf Hζbm)
    as [ζbp [ζbt [Heqζb [Hdomζp Hζbt]]]].
  assert (Heqvbs : a_inc_equiv Θm ζm (msubst_compose ζb κb) Θ)
    by (eapply a_inc_equiv_strip_tm_head; [ exact Heqvb | exact I | exact I ]).
  assert (Hnotinζp : forall β, β `in` dom κb -> β `notin` dom ζbp).
  { intros β Hβ.
    rewrite Hdomζp.
    intros Hc.
    pose proof (a_inc_dom_sub Hincb' Hβ) as Hβ1.
    exact (HΞΘ2 β Hc (Hdom12 _ Hβ1)). }
  assert (Hcz : msubst_compose ζb κb = msubst_compose ζbt κb)
    by (rewrite Heqζb;
        apply (@msubst_compose_id_app_agree κb ζbp ζbt Hidb Hnotinζp)).
  rewrite Hcz in Heqvbs.
  exists ζbt.
  split; [ exact Hζbt | ].
  split; [ exact Heqvbs | ].
  rewrite Heqζb.
  apply msubst_ptyp_agree.
  intros γ Hγ.
  apply msubst_lookup_app_notin.
  rewrite Hdomζp. intros Hc.
  exact (Hscope γ Hc Hγ).
Qed.

Lemma a_typing_complete_check_base_arrow :
  forall {Θ1 Θf Θ ζ ζbt κ' Ad A x Ax B1'} {B1 : btyp},
  {{ ⊢ Θ1 }}a -> {{ ⊢ Θf }}a -> a_wf_ptyp Θ1 Ad ->
  is_id_msubst κ' -> κ' ∷ Θ1 ⊑ Θf ->
  ζ ∷ Θ1 ⊑ Θ -> ζbt ∷ Θf ⊑ Θ ->
  a_inc_equiv Θ1 ζ (msubst_compose ζbt κ') Θ ->
  {{ Θ ⊢ (msubst_ptyp ζ Ad) ≡ᵗ A }}a ->
  {{ ((x ~ abind_var_typ Ax) ++ Θ) ⊢ (msubst_ptyp ζbt B1') ≡ᵗ (btyp_to_ptyp B1) }}a ->
  {{ Θ ⊢ (msubst_ptyp ζbt (ptyp_arrow Ad B1'))
       ≡ᵗ (btyp_to_ptyp (btyp_arrow (ptyp_to_btyp_inh A) B1)) }}a.
Proof.
  intros Θ1 Θf Θ ζ ζbt κ' Ad A x Ax B1' B1 Hwf1 Hwff HwfAd Hid Hinc Hζ Hζbt
         Heqv Heqd Heqcb.
  assert (Hpush : {{ Θ ⊢ (msubst_ptyp ζ Ad)
                    ≡ᵗ (msubst_ptyp (msubst_compose ζbt κ') Ad) }}a).
  { apply (@a_inc_equiv_msubst_ptyp Ad Θ1 ζ (msubst_compose ζbt κ') Θ
             HwfAd Heqv Hwf1
             ltac:(eapply a_inc_msubst_lc; exact Hζ)
             ltac:(apply msubst_lc_compose;
                   [ eapply a_inc_msubst_lc; exact Hζbt
                   | exact (is_id_msubst_values_lc Hid) ])). }
  assert (Hcid : msubst_ptyp (msubst_compose ζbt κ') Ad = msubst_ptyp ζbt Ad)
    by (eapply msubst_compose_id_ptyp;
        [ exact Hwf1 | exact Hwff | exact Hid | exact Hinc
        | exact Hζbt | exact HwfAd ]).
  rewrite Hcid in Hpush.
  simpl.
  rewrite btyp_to_ptyp_ptyp_to_btyp_inh.
  apply a_tyequiv__arrow.
  - eapply a_tyequiv__trans; [ apply a_tyequiv__sym; exact Hpush | exact Heqd ].
  - eapply a_tyequiv_ctx_mono;
      [ exact Heqcb
      | apply (@aenv_tbinds_le_strip_tm nil x (abind_var_typ Ax) Θ);
        intros h; exact h ].
Qed.

Lemma a_typing_body_suffix_facts : forall {Ξ x Ad Θc Θo κb},
  {{ ⊢ (Ξ ++ (x ~ abind_var_typ Ad) ++ Θo) }}a ->
  is_id_msubst κb -> κb ∷ Θc ⊑ Θo -> {{ ⊢ Θc }}a ->
  (forall γ, γ `in` dom Ξ -> γ `notin` dom Θo) /\ dom Θc [<=] dom Θo /\
  ({{ ⊢ Θo }}a) /\ uniq (Ξ ++ Θc).
Proof.
  intros Ξ x Ad Θc Θo κb HwfOut Hidb Hincb Hwfc.
  assert (HuOut : uniq (Ξ ++ (x ~ abind_var_typ Ad) ++ Θo))
    by (apply a_wf_aenv_uniq; exact HwfOut).
  assert (HΞΘo : forall γ, γ `in` dom Ξ -> γ `notin` dom Θo)
    by (clear - HuOut; intros γ Hγ; destruct_uniq;
        unfold disjoint in *; simpl_env in *; fsetdec).
  assert (Hdom : dom Θc [<=] dom Θo)
    by (eapply a_inc_id_dom_sub_scope; [ exact Hincb | exact Hidb ]).
  split; [ exact HΞΘo | ]. split; [ exact Hdom | ].
  split.
  - eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (x ~ abind_var_typ Ad)).
    simpl_env; exact HwfOut.
  - apply uniq_app_of;
      [ clear - HuOut; solve_uniq | apply a_wf_aenv_uniq; exact Hwfc
      | intros γ Hγ Hc; exact (HΞΘo γ Hγ (Hdom _ Hc)) ].
Qed.

Lemma a_typing_complete_abs_check_base : forall Θ0 P0 e κ Θ Ba (B1 : btyp),
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs e) -> binds α abind_tvar Θ0) ->
  lc_exp (exp_abs e) ->
  (forall x, typ_complete_ih (open_exp_wrt_exp e (exp_var_f x))) ->
  {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_arrow Ba B1) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_arrow Ba B1)) }}ad ->
  typ_complete_concl mode_tc Θ0 P0 (exp_abs e) κ Θ (btyp_arrow Ba B1).
Proof.
  intros Θ0 P0 e κ Θ Ba B1 Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
         Hlc IH Hd Href.
  inversion Hd; subst; [ | exfalso; auto ].
  match goal with
  | H : forall x, x `notin` ?L0 -> ad_sd_typing _ _ _ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | H : a_wf_ptyp Θ ?AA |- _ => rename H into HwfA; rename AA into A
  end.
  inversion Hmod; subst.
  match goal with
  | |- typ_complete_concl _ _ (ptyp_to_pskl ?AA) _ _ _ _ => rename AA into Ain
  end.
  simpl in Hrig.
  assert (Hlce : forall x, lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (intros x; inversion Hlc; auto).

  destruct (@a_split_complete_tc Θ0 Ain κ Θ A B1 Hwf0 HwfΘ HwfP0 Hinc Href)
    as [Ad [Bc [Θ1 [κs [ζ [Hsplit [Hwf1 [HwfAd [HwfBc
       [Hids [Hincs [Hζ [Heqvs [Heqd Hrefc]]]]]]]]]]]]]].
  destruct (a_split_wf Hsplit Hwf0 HwfP0) as [Hles _].

  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ1 `union` ftvar_in_aenv Θ1
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp A `union` ftvar_in_ptyp Ad
                          `union` ftvar_in_ptyp Bc)) as [x Hx].
  assert (Hwf0x : {{ ⊢ ((x ~ abind_var_typ Ad) ++ Θ1) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfAd | exact Hwf1 ]).
  assert (HwfΘx : {{ ⊢ ((x ~ abind_var_typ A) ++ Θ) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfA | exact HwfΘ ]).
  assert (Hincx : ζ ∷ ((x ~ abind_var_typ Ad) ++ Θ1)
                    ⊑ ((x ~ abind_var_typ A) ++ Θ)).
  { apply (@a_inc__var Θ1 ζ Θ nil x Ad A);
      [ exact Hζ | apply a_tyequiv__sym; exact Heqd | apply a_suffix__nil ]. }
  assert (Hlcbody : lc_exp (open_exp_wrt_exp e (exp_var_f x))) by (apply Hlce).
  destruct (a_wf_exp_open_tm_binder (abind_var_typ Ad) Hlcbody
              (fun α Hα => a_inc_binds_tvar α Hincs (Hrig α Hα)))
    as [Hrigx Hexpx].
  assert (HwfBcx : {{ ((x ~ abind_var_typ Ad) ++ Θ1) ⨟ empty ⊢ₚₛ
                     (ptyp_to_pskl Bc) }}a)
    by (apply a_wf_pskl_weaken_cons; apply a_wf_ptyp_to_wf_pskl; exact HwfBc).

  destruct (IH x mode_tc ((x ~ abind_var_typ Ad) ++ Θ1) (ptyp_to_pskl Bc) ζ
              ((x ~ abind_var_typ A) ++ Θ) B1
              Hwf0x HwfΘx HwfBcx (a_ty_mode_compat__tc _) Hincx Hrigx
              Hlcbody
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact Hrefc
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [B1' [Θout [HrunB HoptB]]].

  destruct (a_typing_run_under_tm_binder HrunB Hwf0x HwfBcx
              (a_ty_mode_compat__tc _) Hexpx)
    as [κb [Ξ [Θ2 [-> [Hidb [Hincb' [Hsuf [HwfOut [_ [HxΞ HxΘ2]]]]]]]]]].

  pose proof (@a_typing_scope_tm_nil x Ad Θ1 Bc
                (open_exp_wrt_exp e (exp_var_f x)) B1' Ξ Θ2
                HrunB Hwf0x HwfBcx Hexpx HwfOut Hsuf) as Hscope.

  destruct (a_typing_body_suffix_facts HwfOut Hidb Hincb' Hwf1)
    as [HΞΘ2 [Hdom12 [Hwf2 HuΞΘ1]]].

  exists (ptyp_arrow Ad B1'), Θ2.
  split.
  { eapply a_typing__abs_check_base with (x := x) (Ξ := Ξ) (Θ1 := Θ1).
    - exact Hsplit.
    - exact Hsuf.
    - exact HuΞΘ1.
    - exact Hscope.
    - rewrite !dom_app. clear - Hx HxΞ HxΘ2. solve_notin.
    - exact HrunB. }

  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κs)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincs | exact Hid1 | exact Hids ]).
  assert (Hinc1b : κb ∷ ((x ~ abind_var_typ Ad) ++ Θ1)
                     ⊑ (Ξ ++ (x ~ abind_var_typ Ad) ++ Θ2)).
  { apply (@a_inc__var Θ1 κb Θ2 Ξ x Ad Ad);
      [ exact Hincb'
      | rewrite (msubst_ptyp_id Ad Hidb);
        apply a_tyequiv__refl; eapply a_wf_ptyp_lc; exact HwfAd
      | exact Hsuf ]. }
  destruct (HoptB κb Hidb Hinc1b) as [ζb [Hζb [Heqvb Heqcb]]].

  destruct (@a_typing_complete_strip_tm_suffix _ _ _ _ _ _ _ _ _ _ _ Hsuf HwfOut HwfΘx Hidb Hincb'
              HΞΘ2 Hdom12 Hscope Hζb Heqvb)
    as [ζbt [Hζbt [Heqvbs Hagree]]].
  exists ζbt.
  split; [ exact Hζbt | ].
  split.
  { rewrite Heqκ.
    eapply a_inc_equiv_glue with
      (Θmid := Θ1) (Θfin := Θ2) (κ1b := κb) (ζ1 := ζ);
      [ exact Hwf0 | exact Hwf1 | exact Hwf2 | exact HwfΘ
      | exact Hids | exact Hidb
      | intros α Hα;
        pose proof (a_inc_dom_flex Hincs Hα) as Hfα;
        eapply a_inc_flex_dom;
          [ exact Hincb' | exact Hwf1
          | eapply a_inc_id_flex_preserve;
              [ exact Hincs | exact Hids | exact Hwf0 | exact Hfα ] ]
      | exact Hincs | exact Hincb' | exact Hζ | exact Hζbt
      | exact Heqvs | exact Heqvbs ]. }

  rewrite Hagree in Heqcb.
  exact (a_typing_complete_check_base_arrow Hwf1 Hwf2 HwfAd Hidb Hincb' Hζ Hζbt
           Heqvbs Heqd Heqcb).
Qed.

Lemma a_typing_complete_abs_anno_check_base :
  forall Θ0 P0 Aan e κ Θ Ba (B1 : btyp),
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat mode_tc P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp (exp_abs_anno Aan e) ->
     binds α abind_tvar Θ0) ->
  lc_exp (exp_abs_anno Aan e) ->
  (forall x, typ_complete_ih (open_exp_wrt_exp e (exp_var_f x))) ->
  {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno Aan e) ⦂ (btyp_arrow Ba B1) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0))
    ⊳ (btyp_to_bskl (btyp_arrow Ba B1)) }}ad ->
  typ_complete_concl mode_tc Θ0 P0 (exp_abs_anno Aan e) κ Θ (btyp_arrow Ba B1).
Proof.
  intros Θ0 P0 Aan e κ Θ Ba B1 Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
         Hlc IH Hd Href.
  inversion Hd; subst; [ | exfalso; auto ].
  match goal with
  | H : forall x, x `notin` ?L0 -> ad_sd_typing _ _ _ _ |- _ =>
      rename H into Hbody; rename L0 into L
  end.
  match goal with
  | H : {{ Θ ⊢ Aan ≡ᵗ ?AA }}a |- _ => rename H into HeqAA'; rename AA into Adec
  end.
  match goal with
  | H : a_wf_ptyp Θ Aan |- _ => rename H into HwfAanΘ
  end.
  inversion Hmod; subst.
  match goal with
  | |- typ_complete_concl _ _ (ptyp_to_pskl ?AA) _ _ _ _ => rename AA into Ain
  end.
  simpl in Hrig.
  assert (HrigA : forall α, α `in` ftvar_in_ptyp Aan ->
             binds α abind_tvar Θ0)
    by (intros α Hα; apply Hrig; clear - Hα; fsetdec).
  assert (Hlce : forall x, lc_exp (open_exp_wrt_exp e (exp_var_f x)))
    by (intros x; inversion Hlc; auto).
  assert (HlcA : lc_ptyp Aan) by (inversion Hlc; assumption).

  destruct (@a_split_complete_tc Θ0 Ain κ Θ Adec B1 Hwf0 HwfΘ HwfP0 Hinc Href)
    as [Ad [Bc [Θ1 [κs [ζ [Hsplit [Hwf1 [HwfAd [HwfBc
       [Hids [Hincs [Hζ [Heqvs [Heqd Hrefc]]]]]]]]]]]]]].
  destruct (a_split_wf Hsplit Hwf0 HwfP0) as [Hles _].
  assert (HrigA1 : forall α, α `in` ftvar_in_ptyp Aan ->
             binds α abind_tvar Θ1)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hincs | apply HrigA; exact Hα ]).
  assert (HwfAan1 : a_wf_ptyp Θ1 Aan)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA1; exact Hα ]).
  assert (HmsAζ : msubst_ptyp ζ Aan = Aan)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζ | exact Hwf1 | exact HrigA1 ]).

  assert (HeqdA : {{ Θ ⊢ (msubst_ptyp ζ Ad) ≡ᵗ Aan }}a)
    by (eapply a_tyequiv__trans;
        [ exact Heqd | apply a_tyequiv__sym; exact HeqAA' ]).
  assert (Heqs : {{ Θ ⊢ (ptyp_to_pskl (msubst_ptyp ζ Ad))
                   ≡ˢ (ptyp_to_pskl Aan) }}a)
    by (apply a_tyequiv_pskl; exact HeqdA).
  assert (Hjoin : {{ empty ⨟ Θ ⊢ˢ
                    (pskl_to_uskl (msubst_pskl ζ (ptyp_to_pskl Ad)))
                    ∼ (btyp_to_bskl (ptyp_to_btyp_inh Aan)) }}ad).
  { rewrite msubst_pskl_embed_ptyp.
    eapply (proj2 (skl_tyequiv_consis_transport Heqs HwfΘ
                     (fun x b (h : binds x b Θ) => h))).
    rewrite pskl_to_uskl_ptyp.
    apply (ad_pat_consis_syn_bid HwfAanΘ (ptyp_to_btyp_inh Aan)
             (btyp_to_ptyp_ptyp_to_btyp_inh Aan)). }
  assert (Hrs : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl ζ (ptyp_to_pskl Aan))) ⊳ (btyp_to_bskl (ptyp_to_btyp_inh Aan)) }}ad).
  { rewrite msubst_pskl_embed_ptyp, HmsAζ.
    rewrite (btyp_to_bskl_ptyp_to_btyp_inh Aan).
    apply ad_refine_syn_refl_inh.
    apply a_wf_ptyp_to_wf_pskl; exact HwfAanΘ. }
  assert (Hrp : {{ Θ ⨟ empty ⊢ᵣₚ (msubst_pskl ζ (ptyp_to_pskl Ad)) ⊳ (bskl_to_pskl (btyp_to_bskl (ptyp_to_btyp_inh Aan))) }}ad).
  { rewrite msubst_pskl_embed_ptyp.
    rewrite bskl_to_pskl_btyp_to_bskl, btyp_to_ptyp_ptyp_to_btyp_inh.
    eapply (proj2 (skl_tyequiv_refine_pskl_transport Heqs HwfΘ
                     (fun x b (h : binds x b Θ) => h))).
    apply ad_refine_pskl_refl.
    apply a_wf_ptyp_to_wf_pskl; exact HwfAanΘ. }
  assert (HwfAanP1 : {{ Θ1 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Aan) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfAan1).
  assert (HwfAdP1 : {{ Θ1 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Ad) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfAd).
  assert (HwfBcP1 : {{ Θ1 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Bc) }}a)
    by (apply a_wf_ptyp_to_wf_pskl; exact HwfBc).
  destruct (a_consis_complete Hwf1 HwfAanP1 HwfAdP1 Hζ HwfΘ Hjoin Hrs Hrp
              (@ad_pat_consis_msubst_target_wf _ _ _ _ _ Hjoin
                     ltac:(first [ exact I | apply ptyp_to_pskl_ghost_free ]) empty))
    as [Qc [Θ2 [HcRun HoptC]]].
  destruct (a_consis_isub_wf_nil HcRun Hwf1 HwfAanP1 HwfAdP1) as [HleC Hwf2].
  destruct HleC as [[κc [Hidc Hincc]] _].
  destruct (HoptC κc Hidc Hincc) as [ζc [Hζc [Heqvc _]]].

  destruct (atom_fresh (L `union` dom Θ0 `union` ftvar_in_aenv Θ0
                          `union` dom Θ1 `union` ftvar_in_aenv Θ1
                          `union` dom Θ2 `union` ftvar_in_aenv Θ2
                          `union` dom Θ `union` ftvar_in_aenv Θ
                          `union` fvar_in_exp e `union` ftvar_in_exp e
                          `union` ftvar_in_ptyp Aan `union` ftvar_in_ptyp Ad
                          `union` ftvar_in_ptyp Bc)) as [x Hx].
  assert (HrigA2 : forall α, α `in` ftvar_in_ptyp Aan ->
             binds α abind_tvar Θ2)
    by (intros α Hα; eapply a_inc_binds_tvar;
        [ exact Hincc | apply HrigA1; exact Hα ]).
  assert (HwfAan2 : a_wf_ptyp Θ2 Aan)
    by (apply a_wf_ptyp_of_lc_tvarish;
        [ exact HlcA | intros α Hα; left; apply HrigA2; exact Hα ]).
  assert (Hwf0x : {{ ⊢ ((x ~ abind_var_typ Aan) ++ Θ2) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfAan2 | exact Hwf2 ]).
  assert (HwfΘx : {{ ⊢ ((x ~ abind_var_typ Aan) ++ Θ) }}a)
    by (apply a_wf_aenv__var_typ;
        [ clear - Hx; fsetdec | exact HwfAanΘ | exact HwfΘ ]).
  assert (HmsAζc : msubst_ptyp ζc Aan = Aan)
    by (eapply msubst_ptyp_rigid_id;
        [ exact Hζc | exact Hwf2 | exact HrigA2 ]).
  assert (Hincx : ζc ∷ ((x ~ abind_var_typ Aan) ++ Θ2)
                    ⊑ ((x ~ abind_var_typ Aan) ++ Θ)).
  { apply (@a_inc__var Θ2 ζc Θ nil x Aan Aan);
      [ exact Hζc
      | rewrite HmsAζc; apply a_tyequiv__refl; exact HlcA
      | apply a_suffix__nil ]. }

  assert (HwfQB1 : {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl (btyp_to_bskl B1)) }}a).
  { pose proof (ad_sd_typing_target_wf Hd HwfΘ) as Hw.
    simpl in Hw. inversion Hw; subst.
    rewrite bskl_to_pskl_btyp_to_bskl.
    apply a_wf_ptyp_to_wf_pskl. assumption. }
  pose proof (ad_refine_msubst_compose_id Hwf1 Hwf2 HwfΘ HwfBcP1 Hζ Hidc
                Hincc Hζc Heqvc HwfQB1 Hrefc) as HrefCζ.

  destruct (a_wf_exp_open_tm_binder (abind_var_typ Aan) (Hlce x)
              (fun α Hα => a_inc_binds_tvar α Hincc
                             (a_inc_binds_tvar α Hincs (Hrig α (union_3 _ Hα)))))
    as [Hrigx Hexpx].
  assert (HwfBc2 : {{ Θ2 ⨟ empty ⊢ₚₛ (ptyp_to_pskl Bc) }}a).
  { pose proof (a_wf_pskl_msubst_inc_empty Hincc Hwf1 HwfBcP1) as Hw.
    rewrite (msubst_pskl_id (ptyp_to_pskl Bc) Hidc) in Hw. exact Hw. }
  assert (HwfBcx : {{ ((x ~ abind_var_typ Aan) ++ Θ2) ⨟ empty ⊢ₚₛ
                     (ptyp_to_pskl Bc) }}a)
    by (apply a_wf_pskl_weaken_cons; exact HwfBc2).

  destruct (IH x mode_tc ((x ~ abind_var_typ Aan) ++ Θ2) (ptyp_to_pskl Bc) ζc
              ((x ~ abind_var_typ Aan) ++ Θ) B1
              Hwf0x HwfΘx HwfBcx (a_ty_mode_compat__tc _) Hincx Hrigx
              (Hlce x)
              (Hbody x ltac:(clear - Hx; solve_notin_auto))
              ltac:(eapply ad_refine_syn_mono;
                    [ exact HrefCζ
                    | intros α c Hty Hc; apply binds_cons_3; exact Hc ]))
    as [B1' [Θout [HrunB HoptB]]].

  destruct (a_typing_run_under_tm_binder HrunB Hwf0x HwfBcx
              (a_ty_mode_compat__tc _) Hexpx)
    as [κb [Ξ [Θ3 [-> [Hidb [Hincb' [Hsuf [HwfOut [_ [HxΞ HxΘ3]]]]]]]]]].
  pose proof (@a_typing_scope_tm_nil x Aan Θ2 Bc
                (open_exp_wrt_exp e (exp_var_f x)) B1' Ξ Θ3
                HrunB Hwf0x HwfBcx Hexpx HwfOut Hsuf) as Hscope.

  destruct (a_typing_body_suffix_facts HwfOut Hidb Hincb' Hwf2)
    as [HΞΘ3 [Hdom23 [Hwf3 HuΞΘ2]]].

  exists (ptyp_arrow Ad B1'), Θ3.
  split.
  { eapply a_typing__abs_anno_check_base with (x := x) (Ξ := Ξ)
      (Θ1 := Θ1) (Θ2 := Θ2).
    - exact Hsplit.
    - exists Qc; exact HcRun.
    - exact Hsuf.
    - exact HuΞΘ2.
    - exact Hscope.
    - rewrite !dom_app. clear - Hx HxΞ HxΘ3. solve_notin.
    - exact HrunB. }

  intros κ1 Hid1 Hinc1.
  assert (Heqκ : κ1 = κs)
    by (eapply a_inc_id_msubst_unique;
        [ exact Hinc1 | exact Hincs | exact Hid1 | exact Hids ]).
  assert (Hinc1b : κb ∷ ((x ~ abind_var_typ Aan) ++ Θ2)
                     ⊑ (Ξ ++ (x ~ abind_var_typ Aan) ++ Θ3)).
  { apply (@a_inc__var Θ2 κb Θ3 Ξ x Aan Aan);
      [ exact Hincb'
      | rewrite (msubst_ptyp_id Aan Hidb);
        apply a_tyequiv__refl; exact HlcA
      | exact Hsuf ]. }
  destruct (HoptB κb Hidb Hinc1b) as [ζb [Hζb [Heqvb Heqcb]]].
  destruct (@a_typing_complete_strip_tm_suffix _ _ _ _ _ _ _ _ _ _ _ Hsuf HwfOut HwfΘx Hidb Hincb'
              HΞΘ3 Hdom23 Hscope Hζb Heqvb)
    as [ζbt [Hζbt [Heqvbs Hagree]]].

  assert (Hglue23 : a_inc_equiv Θ1 ζ (msubst_compose ζbt κc) Θ).
  { eapply a_inc_equiv_glue with
      (Θmid := Θ2) (Θfin := Θ3) (κ1b := κb) (ζ1 := ζc);
      [ exact Hwf1 | exact Hwf2 | exact Hwf3 | exact HwfΘ
      | exact Hidc | exact Hidb
      | intros α Hα;
        pose proof (a_inc_dom_flex Hincc Hα) as Hfα;
        eapply a_inc_flex_dom;
          [ exact Hincb' | exact Hwf2
          | eapply a_inc_id_flex_preserve;
              [ exact Hincc | exact Hidc | exact Hwf1 | exact Hfα ] ]
      | exact Hincc | exact Hincb' | exact Hζc | exact Hζbt
      | exact Heqvc | exact Heqvbs ]. }
  assert (Hinc23 : msubst_compose κb κc ∷ Θ1 ⊑ Θ3)
    by (eapply a_inc_compose;
        [ exact Hincc | exact Hwf1 | exact Hwf2 | exact Hincb' ]).
  rewrite (msubst_compose_id_id Hidc Hidb) in Hinc23.
  exists ζbt.
  split; [ exact Hζbt | ].
  split.
  { rewrite Heqκ.
    eapply a_inc_equiv_glue_id with
      (Θmid := Θ1) (Θfin := Θ3) (κ1b := κc) (ζ1 := ζ);
      [ exact Hwf0 | exact Hwf1 | exact Hwf3 | exact HwfΘ      | exact Hids | exact Hidc      | exact Hincs | exact Hinc23 | exact Hζ | exact Hζbt      | exact Heqvs | exact Hglue23 ]. }

  rewrite Hagree in Heqcb.
  exact (a_typing_complete_check_base_arrow Hwf1 Hwf3 HwfAd Hidc Hinc23 Hζ Hζbt
           Hglue23 Heqd Heqcb).
Qed.

Lemma a_typing_complete_gen : forall n m e M Θ0 P0 κ Θ B,
  size_exp e < n -> size_btyp B < m ->
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
  lc_exp e ->
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  typ_complete_concl M Θ0 P0 e κ Θ B.
Proof.
  induction n as [ | n IHn ];
    [ intros m e M Θ0 P0 κ Θ B Hszn; exfalso; clear - Hszn; lia | ].
  induction m as [ | m IHm ];
    intros e M Θ0 P0 κ Θ B Hszn Hszm Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig
           Hlc Hd Href;
    [ exfalso; clear - Hszm; lia | ].
  destruct e as [ | i | x | e0 | Aan e0 | e1 e2 | e0 Aan | e0 ];
    simpl in Hszn.
  -  apply a_typing_complete_unit; assumption.
  -  inversion Hd.
  -  apply a_typing_complete_var; assumption.
  -
    destruct M as [ | | M' ].
    +
      apply a_typing_complete_abs; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                  | clear; lia ].
    +
      destruct B as [ | i2 | γ | Bd Bc | B' | B' ];
        try solve [ inversion Hd ]; simpl in Hszm.
      *
        apply a_typing_complete_abs_check_base; try assumption.
        intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
        apply IHn with (m := S (size_btyp B2)); try assumption;
          try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                    | clear; lia ].
      *
        apply a_typing_complete_abs_check_step; try assumption.
        intros M2 Θ02 P02 κ2 Θ2 B2 HszB2; intros.
        apply IHm; try assumption;
          try solve [ simpl; clear - Hszn; lia
                    | clear - Hszm HszB2; simpl in HszB2; lia ].
    +
      apply a_typing_complete_abs; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                  | clear; lia ].
  -
    destruct M as [ | | M' ].
    + apply a_typing_complete_abs_anno; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                  | clear; lia ].
    + destruct B as [ | i2 | γ | Bd Bc | B' | B' ];
        try solve [ inversion Hd ]; simpl in Hszm.
      * apply a_typing_complete_abs_anno_check_base; try assumption.
        intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
        apply IHn with (m := S (size_btyp B2)); try assumption;
          try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                    | clear; lia ].
      * apply a_typing_complete_abs_anno_check_step; try assumption.
        intros M2 Θ02 P02 κ2 Θ2 B2 HszB2; intros.
        apply IHm; try assumption;
          try solve [ simpl; clear - Hszn; lia
                    | clear - Hszm HszB2; simpl in HszB2; lia ].
    + apply a_typing_complete_abs_anno; try assumption;
        [ intros Hc; discriminate Hc | ].
      intros x2 M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ rewrite size_exp_open_exp_wrt_exp_var; clear - Hszn; lia
                  | clear; lia ].
  -
    pose proof (size_exp_min e1) as Hm1.
    pose proof (size_exp_min e2) as Hm2.
    apply a_typing_complete_app; try assumption.
    + intros M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ clear - Hszn Hm2; lia | clear; lia ].
    + intros M2 Θ02 P02 κ2 Θ2 B2; intros.
      apply IHn with (m := S (size_btyp B2)); try assumption;
        try solve [ clear - Hszn Hm1; lia | clear; lia ].
  -
    apply a_typing_complete_anno; try assumption.
    intros M2 Θ02 P02 κ2 Θ2 B2; intros.
    apply IHn with (m := S (size_btyp B2)); try assumption;
      try solve [ clear - Hszn; lia | clear; lia ].
  -
    destruct M as [ | | M' ]; [ inversion Hd | | inversion Hd ].
    inversion Hmod; subst.
    apply a_typing_complete_freeze; try assumption.
    intros M2 Θ02 P02 κ2 Θ2 B2; intros.
    apply IHn with (m := S (size_btyp B2)); try assumption;
      try solve [ clear - Hszn; lia | clear; lia ].
Qed.

Theorem a_typing_complete : forall e M Θ0 P0 κ Θ B,
  {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat M P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
  exists A1 Θ1,
    a_typing M Θ0 P0 e A1 Θ1 /\
    (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
       exists ζ,
         ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
         {{ Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a).
Proof.
  intros e M Θ0 P0 κ Θ B Hwf0 HwfΘ HwfP0 Hmod Hinc Hrig Had Href.
  pose proof (a_wf_exp_lc (ad_sd_typing_wf_exp Had)) as Hlc.
  eapply a_typing_complete_gen
    with (n := S (size_exp e)) (m := S (size_btyp B));
    try eassumption;
    clear; lia.
Qed.
